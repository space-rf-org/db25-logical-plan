// DB25 Logical Plan - Optimizer
//
// Semantics-preserving rewrites over the owned, typed logical plan (LogicalNode
// + Expr). The optimizer consumes a bound plan and returns an equivalent plan
// that is cheaper to execute or simpler to reason about. It operates entirely on
// the owned IR - it never re-reads the parser AST or the analyzer.
//
// The pass pipeline is intentionally small and explicit for now: `optimize()`
// runs each pass in turn. Individual passes are exposed so they can be unit-
// tested in isolation. Every pass must preserve the plan's observable result
// (its output schema and the rows it produces).
//
// Passes implemented today:
//   * constant folding - evaluate an expression whose operands are all constant
//     literals into a single literal (a safe, arity- and type-preserving
//     rewrite of the owned Expr trees).
//   * boolean simplification - apply the AND / OR identities with a boolean
//     literal operand and eliminate double negation (`NOT (NOT x)` -> x). Runs
//     after folding so a folded `1 = 1` -> `true` feeds these identities.
//
// The build matches the rest of the stack: C++23, -fno-exceptions.

#pragma once

#include "db25/plan/logical_plan.hpp"

namespace db25::plan {

// Run the logical-optimization pipeline over a bound plan and return the
// optimized plan. Ownership of `plan` is taken and the (possibly rewritten) plan
// is returned; the rewrite is in place, so the returned pointer is the same
// object unless a future pass replaces the root.
[[nodiscard]] LogicalNodePtr optimize(LogicalNodePtr plan);

// ---- Individual passes (exposed for testing) ----

// Constant folding: fold every expression sub-tree whose operands are all
// constant literals into a single literal, throughout `node` and its children
// (including expressions inside embedded subquery sub-plans). In place.
void fold_constants(LogicalNode* node);

// Boolean simplification: rewrite `x AND true`->x, `x AND false`->false,
// `x OR true`->true, `x OR false`->x (all valid under SQL three-valued logic,
// including when x is NULL), and `NOT (NOT x)`->x, throughout `node` and its
// children (including embedded subquery sub-plans). In place.
void simplify_booleans(LogicalNode* node);

}  // namespace db25::plan
