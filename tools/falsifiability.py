#!/usr/bin/env python3
"""The falsifiability gate for db25-logical-plan.

WHY THIS EXISTS. Every increment in this repo has claimed "all mutations killed"
in its commit message, and every one of those claims was a HAND-RUN act: edit the
source, rebuild, watch a test fail, put the source back, write it down. That
makes the claim true on the day and unenforceable thereafter. Nothing stops a
later change from weakening the test that did the killing, and nothing re-runs
the experiment. The umbrella repo has an automated gate (harness/harness.cpp, `kMutants[]`) and
db25-physical-plan grew one; this repo had neither. Its suites were never shown
to notice anything in particular.

So: the catalog below IS the record of those experiments, and running this file
re-performs them. A mutation that stops being caught fails CI.

WHAT IT DOES. For each mutant: apply it to the source, rebuild, run ctest, record
which test binaries failed, restore the source. A mutant caught by nobody is a
GATE FAILURE - the behaviour it breaks is no longer defended by any test.

THE RULE THIS TOOL EXISTS TO ENFORCE ON ITSELF. A mutation that does not APPLY
looks exactly like a mutation that was not caught: both show a green suite. That
happened twice while this catalog was being written by hand, and both times the
false result was believed for several minutes. So every mutation asserts its
find-string occurs EXACTLY ONCE before it is applied, and a catalog entry whose
pattern has drifted out of the source is a hard error, never a skip.

WHAT IT DOES NOT DO. It kills at TEST-BINARY granularity, not per test case -
this repo's suites are separate executables with their own main(), not a named
registry the way the umbrella's are. So it detects "this behaviour is defended by
no binary", not "this behaviour is defended by no individual assertion". The
vacuity half of the umbrella's gate (every test killed by some mutant) is
reported below as coverage rather than enforced, because a cost-model catalog
aimed at the optimizer's passes cannot kill the expression-lowering tests, and
pretending otherwise would mean
either an allowlist nobody maintains or a gate somebody disables.
"""
import argparse, pathlib, re, shutil, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# THE CATALOG - the authority, and the record of experiments previously run by
# hand. Each entry names the behaviour it removes; `find` must occur exactly once.
# ---------------------------------------------------------------------------
# RETIRED MUTANTS - kept as a record, because deleting an experiment silently is
# how a catalog becomes a list of things that happen to pass.
#
#   M2 "the second boolean simplification is dropped" - optimize() calls
#   simplify_booleans twice, and its comment justifies the second call as making
#   "a reduced predicate feed pushdown". Removing that call changes NOTHING: not
#   the three suites here, not the umbrella's eighteen, not its ninety-two corpus
#   goldens, the staged round-trip, the injection gate or the SQL surface check.
#
#   That is not a test gap. A mutation that alters no output for any input the
#   project has is not removing a behaviour, it is revealing that there is none
#   to remove - the call is unobservable today because decorrelation rebuilds a
#   predicate from surviving conjuncts and never introduces a boolean identity
#   for the second pass to reduce.
#
#   It is retired rather than left failing, and the call is left in place rather
#   than deleted: "no current input reaches it" is a weak reason to remove a
#   defensive pass, and a strong reason to write down that its justification is
#   currently unverifiable. If decorrelation ever produces a simplifiable
#   predicate, this becomes a real mutant again.

MUTANTS = [
    # The optimizer's five passes. optimize() runs them in a stated order, and the
    # ORDER is itself a claim - its comment says the sequence is what lets the
    # decorrelation fixpoint be reached in one call, so that is mutated too.
    dict(id="M1", name="constant folding disabled (a constant predicate is never reduced)",
         file="src/optimizer.cpp",
         find="""        fold_constants(plan.get());
        simplify_booleans(plan.get());
        // Decorrelate,""",
         repl="""        simplify_booleans(plan.get());
        // Decorrelate,"""),
    dict(id="M2", name="decorrelation disabled (EXISTS stays a correlated subquery)",
         file="src/optimizer.cpp",
         find="        decorrelate_exists(plan);",
         repl="        if (false) decorrelate_exists(plan);"),
    dict(id="M3", name="filter pushdown disabled (predicates stay above the join)",
         file="src/optimizer.cpp",
         find="        push_down_filters(plan);",
         repl="        if (false) push_down_filters(plan);"),
    dict(id="M4", name="column pruning disabled (unreferenced columns survive)",
         file="src/optimizer.cpp",
         find="        prune_columns(plan);",
         repl="        if (false) prune_columns(plan);"),
    dict(id="M5", name="decorrelation runs BEFORE fold/simplify, breaking the one-call fixpoint",
         file="src/optimizer.cpp",
         find="""        fold_constants(plan.get());
        simplify_booleans(plan.get());
        // Decorrelate, so the later passes optimize the resulting joins; fold""",
         repl="        // Decorrelate, so the later passes optimize the resulting joins; fold"),
    # --- the binder's schema guarantees. These are not optimizations: a wrong
    # answer here is a plan that describes the wrong relation, so each one should
    # be defended by something. ---
    dict(id="M6", name="an outer join does not make the null-supplied side nullable",
         file="src/binder.cpp",
         find="""    const bool null_right = jt == ast::JoinType::Left || jt == ast::JoinType::Full ||
                            jt == ast::JoinType::LeftLateral;""",
         repl="    const bool null_right = false;"),
    dict(id="M7", name="a RIGHT/FULL join does not make the LEFT side nullable",
         file="src/binder.cpp",
         find="    const bool null_left = jt == ast::JoinType::Right || jt == ast::JoinType::Full;\n    // LeftLateral is LEFT JOIN LATERAL",
         repl="    const bool null_left = false;\n    // LeftLateral is LEFT JOIN LATERAL"),
    dict(id="M8", name="hidden USING/NATURAL copies are counted as user columns (false ambiguity)",
         file="src/binder.cpp",
         find="                if (!c.hidden && iequals(c.name, name)) ++n;",
         repl="                if (iequals(c.name, name)) ++n;"),
]


def sh(cmd, **kw):
    return subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True, text=True, **kw)


def build(builddir):
    return sh(f"cmake --build {builddir} -j4").returncode == 0


def failing_tests(builddir):
    """Names of the ctest targets that FAILED. Empty set == suite is green."""
    r = sh(f"ctest --test-dir {builddir} --output-on-failure")
    out = set()
    for line in r.stdout.splitlines():
        line = line.strip()
        if " - " in line and "(Failed)" in line:
            out.add(line.split(" - ", 1)[1].replace(" (Failed)", "").strip())
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--build-dir", default="build")
    ap.add_argument("--only", default="", help="run one mutant by id")
    ap.add_argument("--self-test", action="store_true",
                    help="inject a mutation NOTHING can catch and require this gate to fail. "
                         "A gate that has never been seen to fail is not known to be a gate.")
    args = ap.parse_args()
    bd = args.build_dir

    print("=" * 70)
    print(" db25-logical-plan falsifiability gate")
    print("=" * 70)

    # Preflight: verify EVERY catalog pattern resolves before spending a single
    # rebuild. Finding a drifted anchor after fifteen minutes of building teaches
    # the same thing as finding it in two seconds.
    drift = []
    for m in MUTANTS:
        n = (ROOT / m["file"]).read_text().count(m["find"])
        if n != 1:
            drift.append(f"  {m['id']}: pattern occurs {n}x in {m['file']} (expected exactly 1)")
    if drift:
        print("GATE FAIL: the catalog has drifted from the source.")
        print("\n".join(drift))
        print("\nFix the entries. Deleting them silently retires the experiment they record.")
        return 1
    print(f"[preflight] all {len(MUTANTS)} catalog patterns resolve uniquely")

    if not build(bd):
        print("GATE FAIL: the tree does not build clean before any mutation")
        return 1
    clean_failures = failing_tests(bd)
    if clean_failures:
        print(f"GATE FAIL: {len(clean_failures)} test(s) fail CLEAN: {sorted(clean_failures)}")
        return 1
    print(f"[clean] suite is green\n")

    if args.self_test:
        # A change no assertion depends on: a comment. If the gate reports this
        # as CAUGHT, its notion of "caught" is picking up build noise rather than
        # test failure, and every other result it has ever printed is suspect.
        probe = dict(id="PROBE", name="a comment edit, which no test can possibly detect",
                     file="src/optimizer.cpp",
                     find="// ---- Predicate pushdown helpers ---------------------------------------------",
                     repl="// ---- Predicate pushdown helpers (self-test probe) ----------------------------")
        chosen = [probe]
    else:
        chosen = [m for m in MUTANTS if not args.only or m["id"] == args.only]
    survivors, killers = [], {}

    for m in chosen:
        path = ROOT / m["file"]
        original = path.read_text()
        # A mutation that does not apply is indistinguishable from one that is
        # not caught. Both show green. So this is a hard error, never a skip.
        n = original.count(m["find"])
        if n != 1:
            print(f"GATE FAIL: {m['id']} pattern occurs {n} times in {m['file']} (expected exactly 1).")
            print("           The catalog has drifted from the source. Fix the entry, do not delete it.")
            return 1
        path.write_text(original.replace(m["find"], m["repl"], 1))
        try:
            if not build(bd):
                # A mutation that does not compile has not tested anything.
                print(f"  {m['id']:<4} BUILD FAIL - mutation does not compile; not a result")
                survivors.append(m)
                continue
            failed = failing_tests(bd)
        finally:
            path.write_text(original)
        if failed:
            print(f"  {m['id']:<4} killed by {', '.join(sorted(failed))}")
            for t in failed:
                killers.setdefault(t, []).append(m["id"])
        else:
            print(f"  {m['id']:<4} *** SURVIVED *** {m['name']}")
            survivors.append(m)

    build(bd)  # leave the tree as we found it

    print()
    if args.self_test:
        if survivors:
            print("SELF-TEST PASSED: the probe survived, so this gate can report failure.")
            print("  (the run above shows the GATE FAILED path working)")
            return 0
        print("SELF-TEST FAILED: a comment edit was reported as CAUGHT.")
        print("  This gate cannot distinguish a test failure from noise; do not trust its results.")
        return 1

    if survivors:
        print(f"GATE FAILED: {len(survivors)} mutant(s) survived:")
        for m in survivors:
            print(f"  {m['id']}: {m['name']}")
        return 1

    print(f"GATE PASSED: all {len(chosen)} mutants caught.")
    print("\n[coverage] which binaries did the killing (information, not a gate):")
    for t, ids in sorted(killers.items()):
        print(f"  {t:<22} {len(ids):>2} mutant(s)")
    # Which binaries never did any killing. NOT a gate - see the module docstring -
    # but printed so the hole is visible and shrinking it is a visible improvement
    # rather than an invisible one.
    all_tests = sh(f"ctest --test-dir {bd} -N").stdout
    # ctest RIGHT-ALIGNS the number ("Test  #1:", two spaces, but "Test #10:"),
    # so a literal "Test #" match silently drops tests 1-9. It did, in the sibling
    # parser gate this code was shared with: that report claimed 30 of a 39-binary
    # suite. Hence the cross-check below - a parsed count that does not agree with
    # ctest's own total is a hard error, not a quietly shorter list.
    known = {m.group(1).strip() for m in
             (re.match(r"\s*Test\s+#\d+:\s*(.+)$", l) for l in all_tests.splitlines()) if m}
    declared = re.search(r"Total Tests:\s*(\d+)", all_tests)
    if declared and int(declared.group(1)) != len(known):
        print(f"GATE FAIL: parsed {len(known)} test names but ctest declares "
              f"{declared.group(1)} - the coverage report would understate its own scope.")
        return 1
    never = sorted(known - set(killers))
    if never:
        print(f"\n[uncovered] {len(never)} binary/binaries this catalog cannot kill:")
        print("  " + ", ".join(never))
        print("  Not a failure: a catalog has a scope, and this prints what it is.")
        print("  It is the measure of how much of the suite this gate currently defends.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
