# Full-Pipeline Verification — Tokenizer → Parser → Analyzer → Binder → Optimizer

**Date:** 2026-07-21
**Scope:** 10 hand-picked SQL queries pushed end-to-end through every stage of the
front end, each verified stage-by-stage for correctness (not just "it ran"). Three
queries are at the maximum complexity the stack currently supports. Verification was
run in **parallel — one agent per query** — each independently reasoning about
semantics-preservation (NULL handling, cardinality, positional-index consistency),
not merely transcribing output.

**Result: 10 / 10 PASS.** No correctness defect found at any stage on any query.

---

## Methodology

- **Harness.** A single parametric driver (`pipeq <N>`) runs one query through
  tokenizer → parser → analyzer → binder → optimizer and dumps every stage: the token
  stream, the parser AST (with resolved types), the analyzer's resolved projection +
  error state, the bound logical plan, and the optimized logical plan.
- **Catalog.**
  - `users(id NOT NULL, name?, age?, city?)`
  - `orders(id NOT NULL, user_id?, total?, status?)`
  - `products(id NOT NULL, name?, price?, category?)`
  - `emp(id NOT NULL, name?, dept?, mgr_id?, salary?)`  (`?` = nullable)
- **Optimizer pipeline (fixed order):** `decorrelate → fold_constants →
  simplify_booleans → push_down_filters → prune_columns`.
- **Parallel verification.** Ten independent reviewer agents ran concurrently, one per
  query, each given the IR conventions and the expected transform, and each instructed
  to hunt for anomalies (wrong index, dropped-but-needed column, semantics inversion,
  cardinality inflation, use-after-free, etc.).

### IR conventions (how to read the plans)

- Every operator carries an explicit **output schema**, shown as `[col:Type?]`
  (`?` = nullable).
- Column references are **positional**: `#i` is an index into the operator's *input*
  schema. A `Join`'s input frame is `left.output ++ right.output`.
- A correlated outer reference is `outerN#i` — depth `N`, index `i` in the enclosing
  block.
- Decorrelation targets: `EXISTS → SemiJoin`, `NOT EXISTS → AntiJoin`,
  `x [NOT] IN (…) → Semi/AntiJoin`, correlated aggregate scalar subquery →
  `LEFT JOIN` against the inner relation grouped by the correlation key. Anything
  outside a handled shape is left as a represented subquery (a safe no-op).

---

## Summary

| # | Query focus | Complexity | Stages exercised | Verdict |
|---|-------------|------------|------------------|---------|
| Q1 | INNER join + fold + simplify + pushdown + prune | medium | all 5 optimizer passes | **PASS** |
| Q2 | correlated `EXISTS` → SemiJoin | medium | decorrelate | **PASS** |
| Q3 | `IN (subquery)` → SemiJoin, local filter preserved | medium | decorrelate + prune | **PASS** |
| Q4 | correlated scalar `SUM` → LEFT JOIN + GROUP BY | medium | decorrelate + prune | **PASS** |
| Q5 | correlated `NOT EXISTS` → AntiJoin | medium | decorrelate (negation) | **PASS** |
| Q6 | window `ROW_NUMBER() OVER (…)` | medium | binder Window op | **PASS** |
| Q7 | `UNION` (set operation) | medium | binder SetOp + conservative prune | **PASS** |
| Q8 | join + correlated scalar `AVG` + `CASE` + folded `WHERE` | **HIGH** | all 5 passes together | **PASS** |
| Q9 | nested/skip-level correlation (`EXISTS` over a correlated scalar) | **HIGH** | decorrelate (conservative decline) | **PASS** |
| Q10 | `DISTINCT` + correlated scalar `MAX` + join + `IN` + `ORDER BY` | **HIGH** | two composed decorrelations + fold + prune | **PASS** |

---

## Q1 — core pipeline: fold + simplify + pushdown + prune
**SQL:** `SELECT u.name, o.total FROM users u JOIN orders o ON u.id=o.user_id WHERE o.total>5 AND 1=1`

| Stage | Produced / what to notice |
|---|---|
| **Tokenizer** | 32 tokens, correctly classified (`SELECT/FROM/JOIN/ON/WHERE/AND` keywords; dotted refs as ident-`.`-ident triples; `5,1,1` numbers). |
| **Parser** | Well-formed `SelectStmt`; WhereClause a right-leaning `AND` of `o.total>5` and `1=1`; refs by NAME. |
| **Analyzer** | `errors: none`. Projection `name:VarChar NULL (tbl=1,col=2)`, `total:Double NULL (tbl=2,col=3)`; the two `id` columns disambiguated by distinct table ids. |
| **Binder** | Join frame `[id,name,age,city]++[id,user_id,total,status]`; ON `#0=#5` (users.id = orders.user_id, *not* orders.id=#4); Filter `(#6>5) AND (1=1)`; Project `#1,#6`. All indices correct. |
| **Optimizer** | fold `1=1→TRUE`; simplify `AND TRUE` away; pushdown `total>5` onto orders (`#6 → #2` in orders' local frame, INNER-side only); prune drops `age,city,orders.id,status`, reindexing to Project `#1,#3` over Join `#0=#2`. |

**Verdict: PASS** — all indices consistent, rewrite semantics-preserving, final projection still yields `(name, total)`.

## Q2 — correlated EXISTS → SemiJoin
**SQL:** `SELECT u.name FROM users u WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id=u.id)`

- **Tokenizer (24 tok):** `EXISTS` correctly a keyword; nesting parens intact.
- **Parser:** WhereClause `UnaryExpr 'EXISTS'` wrapping the inner `SelectStmt`; correlation `u.id` present by name.
- **Analyzer:** `errors: none`; projection `name:VarChar NULL`; subquery flagged **correlated** (binds `u.id` in the enclosing scope).
- **Binder:** `Filter Subquery[EXISTS,correlated]` over `Scan users`; sub-plan `Project(1) → Filter(#1 = outer1#0) → Scan orders` — `#1`=o.user_id, `outer1#0`=u.id.
- **Optimizer:** → `SemiJoin ON (#5 = #0)`: `#0`=u.id (left), `#5`=o.user_id (inner idx 1 + left width 4). Output = **users schema only**; no residual subquery. Emitting each users row with ≥1 matching order is exactly EXISTS.

**Verdict: PASS** — hoisted indices exact, output schema left-only, EXISTS→SemiJoin polarity correct.

## Q3 — IN (subquery) → SemiJoin (local filter preserved)
**SQL:** `SELECT u.name FROM users u WHERE u.id IN (SELECT o.user_id FROM orders o WHERE o.total>50)`

- **Tokenizer (27 tok):** `IN`, subquery parens, `o.total>50` all clean.
- **Parser:** `InExpr` with probe `u.id` (child 0) and `Subquery` (child 1).
- **Analyzer:** `errors: none`; subquery references only `orders` ⇒ confirmed **uncorrelated** (no correlation to hoist).
- **Binder:** `Filter Subquery[IN]` (tagged uncorrelated) over `Scan users`; probe at `#0`; sub-plan projects `o.user_id` (`#1`) and keeps `o.total>50` (`#2`).
- **Optimizer:** → `SemiJoin ON (#0 = #5)` (probe u.id `#0`; projected o.user_id remapped `1 + left-width 4 = #5`). Local `o.total>50` survives as `Filter(#2>50)` on the **right** input. Output = users only; no residual subquery. Positive IN drops on FALSE and UNKNOWN alike, matching an equi-semijoin.

**Verdict: PASS** — IN equality index correct, local filter correctly retained on the right, output schema left-only.

## Q4 — correlated scalar subquery → LEFT JOIN + GROUP BY
**SQL:** `SELECT u.name, (SELECT SUM(o.total) FROM orders o WHERE o.user_id=u.id) AS spent FROM users u`

- **Tokenizer (30 tok):** scalar-subquery nesting opens with `Delimiter (` before inner `SELECT`; `AS spent` clean.
- **Parser:** `Subquery:Double` sibling to `u.name`; inner `SUM(o.total)` with correlation `o.user_id=u.id`.
- **Analyzer:** `errors: none`; projection `name`, `spent:Double NULL` (nullable, as SUM-over-empty must be expressible as NULL).
- **Binder:** canonical pre-decorrelation shape — `Project(#1, Subquery[SCALAR,correlated])` with sub-plan `Aggregate group=() aggs=(SUM(#2)) → Filter(#1 = outer1#0) → Scan orders`.
- **Optimizer:** → `Join(LEFT) ON (#0 = #2)`; right input `Aggregate group=(#0) aggs=(SUM(#1))` (formerly `group=()` — correlation key became the group key); `spent` now `ColumnRef #3` (= left-width 2 + 1 group key), nullable.
  - **(a)** SUM ∈ NULL-over-empty class → non-match LEFT-JOIN NULL reproduces SUM-over-empty=NULL. ✔
  - **(b)** GROUP BY on the key ⇒ empty input → 0 groups → NULL (not a spurious all-NULL row); group keys = join keys ⇒ ≤1 match ⇒ cardinality preserved. ✔
  - **(c)** correlation reproduced as equi-JOIN `=`, inheriting NULL exclusion. ✔

**Verdict: PASS** — agg column index correct (`#3`), aggregate is grouped (no cardinality bug), no COUNT slip-through, `spent` nullable.

## Q5 — correlated NOT EXISTS → AntiJoin
**SQL:** `SELECT u.name FROM users u WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.user_id=u.id)`

- **Tokenizer (25 tok):** `NOT` and `EXISTS` two distinct keywords.
- **Parser:** WhereClause is a single `UnaryExpr 'EXISTS'` — **no visible `NOT` child**; negation carried as a *semantic flag*, not a tree node (the historically bug-prone encoding).
- **Analyzer:** `errors: none`; correlated subquery; projection `name`.
- **Binder:** `Filter Subquery[EXISTS,correlated]` (negated internally) over `Scan users`; sub-plan `Filter(#1 = outer1#0) → Scan orders`.
- **Optimizer:** → **`AntiJoin ON (#5 = #0)`** — AntiJoin, *not* SemiJoin (the negation flag was honored; a SemiJoin here would invert the query). Correlation reconstructed (`#0`=users.id, `#5`=orders.user_id); output = users only; no residual subquery. AntiJoin = left rows with no matching order = precisely NOT EXISTS.

**Verdict: PASS** — no SemiJoin/AntiJoin inversion, indices correct, semantics preserved.

## Q6 — window function (ROW_NUMBER OVER …)
**SQL:** `SELECT u.name, ROW_NUMBER() OVER (PARTITION BY u.city ORDER BY u.age) AS rn FROM users u`

- **Tokenizer (26 tok):** `OVER/PARTITION/BY/ORDER` keywords; `ROW_NUMBER` an identifier (function name).
- **Parser:** `FunctionCall 'ROW_NUMBER'` with a nested `WindowSpec` carrying PARTITION BY `u.city` and ORDER BY `u.age`.
- **Analyzer:** `errors: none`; `rn : BigInt NOT NULL` (ROW_NUMBER always produces a value).
- **Binder:** a `Window` operator inserted **below Project, above Scan**, appending one column: input `[id,name,age,city]` → `[id,name,age,city,rn]`; PARTITION `#3` (city), ORDER `#2` (age); Project references `rn` at `#4`.
- **Optimizer:** structurally unchanged (no subquery/constant). Prune did not fire (mildly conservative — `id` retained) but that is sound; the window's partition/order columns and the appended window column all survive with intact indices.

**Verdict: PASS** — window column index correct, partition/order columns retained, ROW_NUMBER lowered correctly.

## Q7 — set operation (UNION)
**SQL:** `SELECT name FROM users UNION SELECT name FROM products`

- **Tokenizer (9 tok):** single `UNION` between two symmetric SELECT runs; no `ALL` ⇒ duplicate-eliminating.
- **Parser:** `UnionStmt` with exactly two `SelectStmt` arms, neither dropped nor mis-nested.
- **Analyzer:** `errors: none`; unified projection `name : VarChar NULL` — type/nullability merged across the two arms (both VarChar nullable).
- **Binder:** `SetOp (UNION) [name:VarChar?]` over two `Project(#1)` arms; each projects `name` at position `#1` despite the two scans having different layouts (`users[id,name,age,city]`, `products[id,name,price,category]`) — index correct in both.
- **Optimizer:** byte-for-byte identical to the bound plan — the correct conservative behavior for set operations; both arms remain well-formed and still project `#1→name`; output schema intact.

**Verdict: PASS** — no arm dropped or mis-pruned, type unification correct, no index drift between the asymmetric arm schemas.

---

## Q8 (COMPLEX) — join + correlated scalar (AVG) + CASE + folded WHERE
**SQL:** `SELECT u.name, o.total, (SELECT AVG(o2.total) FROM orders o2 WHERE o2.user_id=u.id) AS avg_spent, CASE WHEN o.total > 100 THEN 'big' ELSE 'small' END AS bucket FROM users u JOIN orders o ON u.id=o.user_id WHERE o.status='paid' AND 2>1`

- **Tokenizer (70 tok):** scalar subquery lexically nested; `CASE/WHEN/THEN/ELSE/END` keywords; string literals; `2>1` numeric comparison.
- **Parser:** SelectList of exactly 4 items (`u.name`, `o.total`, `Subquery`, `CaseExpr`); WHERE a two-conjunct `AND`, unfolded (correct — folding is the optimizer's job).
- **Analyzer:** `errors: none`; projection `name:VarChar?`, `total:Double?`, `avg_spent:Double?` (nullable, tbl=0 derived), `bucket:Text NOT NULL` (CASE with ELSE ⇒ non-null); subquery correlated.
- **Binder:** `Project` (4 items incl. `Subquery[SCALAR,correlated]` and `CASE(#6>100,'big','small')`) over `Filter((#7='paid') AND (2>1))` over `Join(INNER) ON #0=#5`. Refs verified: `#7`=status, `#0`=users.id, `#5`=orders.user_id, `#1`=name, `#6`=total.
- **Optimizer — pass by pass:**
  1. **decorrelate:** AVG scalar → `Join(LEFT) ON #0=#5` with right `Aggregate group=(#0) aggs=(AVG(#1))`; `avg_spent` now a nullable `ColumnRef`. Left input of the LEFT join = the filtered INNER join. group key = join key ⇒ ≤1 match; empty ⇒ NULL = AVG-over-empty. ✔
  2. **fold:** `2>1 → TRUE`. ✔
  3. **simplify:** `status='paid' AND TRUE → status='paid'`. ✔
  4. **pushdown:** `status='paid'` sank onto the **INNER-join orders scan** and — critically — did **NOT** pass through the LEFT join into the `o2` aggregate. (Had it leaked, `avg_spent` would wrongly average only paid orders.) ✔
  5. **prune + reindex:** scans narrowed; every index re-checked end-to-end. The CASE operand reindexed `#6 → #3` (still `total`); `avg_spent` = `#6` (the AVG); final tuple `(name, total, avg_spent, bucket)` with schema `[VarChar?, Double?, Double?, Text]` = analyzer output. ✔

**Verdict: PASS** — the semantics-critical point (filter not leaking into the null-supplying LEFT-join side) holds; CASE operand and avg_spent indices correct after composed rewrites; AVG (not COUNT) so empty→NULL is correct.

## Q9 (COMPLEX) — nested/skip-level correlation (EXISTS containing a correlated scalar)
**SQL:** `SELECT u.name FROM users u WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id=u.id AND o.total > (SELECT AVG(o3.total) FROM orders o3 WHERE o3.user_id=u.id))`

- **Tokenizer (49 tok):** both nested subquery parens and the `AVG(` call tokenized correctly.
- **Parser:** faithful double nesting — EXISTS body's WHERE is `AND` of `(o.user_id=u.id)` and `(o.total > Subquery)`; the innermost `Subquery` computes `AVG(o3.total)` with `o3.user_id=u.id`.
- **Analyzer:** `errors: none`; projection `name`; both subqueries correlated.
- **Binder — the crux:** outer correlation `outer1#0` (u.id) at **depth 1**; the innermost scalar's correlation to `u.id` is `outer2#0` at **depth 2** — the skip-level reference (jumping over `o`'s scope) is correctly recorded as depth-2, not depth-1.
- **Optimizer — correctly conservative:**
  - **Outer EXISTS left as a represented subquery** (not a SemiJoin): its correlation predicate embeds a subquery (`o.total > (scalar)`), so it is not a hoistable single-Filter equi-correlation. Declining is a safe no-op.
  - **Inner scalar also left as a subquery:** its depth-2 correlation is not decorrelated (only depth-1 is). The engine decides correlation by *actual OuterRef presence*, so the skip-level ref is neither dropped nor mis-hoisted.
  - Only transformation: pruning `o3` to `[user_id,total]` with AVG/Filter indices re-indexed consistently; `outer1#0` (depth 1) and `outer2#0` (depth 2) both survive intact.

**Verdict: PASS** — no conditionless SemiJoin dropped a correlation; both OuterRefs preserved at correct depth; the conservative decline is correct and semantics-preserving. (This is the exact skip-level trap that motivated deciding correlation by real OuterRef presence rather than an immediate-level flag.)

## Q10 (COMPLEX) — DISTINCT + correlated scalar (MAX) + join + IN + ORDER BY
**SQL:** `SELECT DISTINCT u.city, (SELECT MAX(o.total) FROM orders o WHERE o.user_id=u.id) AS mx FROM users u JOIN products p ON u.city=p.category WHERE u.id IN (SELECT o.user_id FROM orders o WHERE o.total>10 AND 1=1) ORDER BY u.city`

- **Tokenizer (71 tok):** `DISTINCT`, both subquery groupings, `JOIN/ON`, `IN`, `ORDER/BY`, `1=1` all correct.
- **Parser:** SelectList `city` + correlated `MAX` subquery; INNER join on `u.city=p.category`; WHERE `InExpr` whose subquery WHERE is `(o.total>10) AND (1=1)`; ORDER BY `city`.
- **Analyzer:** `errors: none`; projection `city:VarChar?`, `mx:Double?` (nullable MAX). Correlation classification right: MAX subquery **correlated**, IN subquery **uncorrelated**.
- **Binder:** `Sort(#0 ASC) → Distinct → Project(#3, Subquery[SCALAR,correlated]) → Filter(Subquery[IN]) → Join(INNER, #3=#7)`. IN sub-plan tagged uncorrelated with `(#2>10) AND (1=1)`; scalar sub-plan `Aggregate group=() MAX(#2) → Filter(#1 = outer1#0)`.
- **Optimizer — two composed decorrelations + fold + prune:**
  - IN → `SemiJoin ON (#0 = #9)` (u.id = o.user_id); left-only output ⇒ no row multiplication; local `o.total>10` preserved as `Filter(#2>10)` on the right.
  - `1=1 → TRUE`, `AND TRUE` gone.
  - MAX scalar → `Join(LEFT) ON (#0 = #8)` with right `Aggregate group=(#0) aggs=(MAX(#1))`; ≤1 match per user; unmatched → NULL; `mx` = `ColumnRef #9`, nullable.
  - DISTINCT schema-preserving; `Sort keys=(#0 ASC)` on city; neither `city` nor `mx` pruned.
  - **Cardinality:** INNER `users⋈products` can multiply, but the SemiJoin doesn't multiply, the grouped LEFT JOIN matches ≤1, and DISTINCT dedups `(city, mx)` — matching `SELECT DISTINCT`.

**Verdict: PASS** — no interaction bug between the two decorrelations, IN local filter intact, `1=1` folded away, MAX nullable, no DISTINCT/Sort column pruned, no cardinality inflation.

---

## Boundary findings — where the chain *stops* (queries that challenge it)

The candidate sweep also included queries that push past the current front end. These
are **not defects in the 10 passing queries** — they map the supported envelope. Each
boundary claim below was **re-confirmed with a clean (named-parser) harness**, because
the first sweep ran with a use-after-free (see note) that produced at least one
*spurious* failure. Every genuine boundary fails *safely* — a clean diagnostic, never
a crash or a wrong plan:

| Query | Where it stops | Nature |
|-------|----------------|--------|
| `SELECT o.user_id, SUM(o.total) FROM orders o GROUP BY o.user_id HAVING SUM(o.total) > 100` | **Binder**: `o.total` in HAVING "resolves to no input or enclosing slot" | **Real limitation.** HAVING that recomputes an aggregate over a base column doesn't match it to the already-computed SELECT aggregate; it tries to resolve `o.total` against the post-aggregate schema and fails. Note the contrast: `HAVING COUNT(*) > 2` **binds fine** — the gap is specifically aggregate-expression matching in HAVING. Worth a follow-up. |
| `… SUM(o.total) AS s … HAVING s > 100` | **Analyzer**: `has_errors` | Referring to a SELECT **alias** in HAVING is rejected at analysis (consistent with the earlier finding that GROUP BY/HAVING alias & ordinal resolution is out of scope). |
| `SELECT DISTINCT u.city FROM users u ORDER BY u.age DESC LIMIT 10` | **Binder**: "ORDER BY item must appear in the SELECT list (DISTINCT)" | **Correct rejection** — SQL forbids ORDER BY on a non-selected column under DISTINCT. The chain is right to refuse. |
| `… RANK() OVER (ORDER BY SUM(o.total) DESC) … GROUP BY … HAVING COUNT(*) > 2 …` | **Analyzer**: `has_errors` | An aggregate inside a window's ORDER BY over a grouped query — a complex interaction the analyzer rejects rather than mis-resolves. |

**Corrected non-finding:** the initial sweep reported `SELECT u.name FROM users u WHERE
u.age > 30` failing to bind ("statement kind not yet lowered"). That was **spurious** —
re-run with a named parser it **binds fine**. The bogus error was an artifact of the
use-after-free below, a good reminder to distrust a single failing run of a
memory-unsafe harness.

**One real use-after-free was found and fixed — in the test harness, not the engine:**
the driver initially constructed the parser as a temporary (`Parser{}.parse(sql)`),
but the parser owns the AST's arena, so the tree was freed before traversal (random
segfaults, and at least one bogus bind error). Using a named parser that outlives AST
use resolved it. Worth recording as a usage contract: **the `Parser` must outlive any
use of the AST it returns.**

---

## Conclusion

Across 10 queries spanning the full front end — from a trivial filter to three
maximum-complexity queries composing joins, correlated scalar/`IN`/`EXISTS`
subqueries, `CASE`, `DISTINCT`, window functions, set operations, constant folding,
and multi-pass optimization — **every stage produced correct output and every
optimizer rewrite was verified semantics-preserving.** The decorrelation machinery in
particular held up under adversarial scrutiny: it fired precisely where sound
(EXISTS/NOT EXISTS/IN/scalar) and *correctly declined* where a rewrite would be unsafe
(nested/skip-level correlation, filter leakage into a null-supplying join side). The
boundary sweep additionally confirmed that unsupported constructs fail with clean
diagnostics rather than crashes or wrong plans — with one genuine binder gap
(aggregate-expression matching in `HAVING`, e.g. `HAVING SUM(col) > k`, while
`HAVING COUNT(*)` works) noted for follow-up.
