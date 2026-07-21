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
//   * predicate pushdown - split a Filter's conjuncts and push each below an
//     INNER / CROSS Join to the side whose columns it references (remapping the
//     positional slots), merge adjacent Filters, and drop a Filter whose
//     predicate simplified to constant `true`.
//   * column pruning - drop columns that no operator above consumes, narrowing
//     Scans and Projects and remapping the positional slots throughout. Conserv-
//     ative around operators whose column flow is intricate (set operations,
//     VALUES, DML) and around any operator carrying an embedded subquery.
//   * subquery decorrelation - rewrite a Filter whose whole predicate is a
//     [NOT] EXISTS or a `x [NOT] IN (subquery)` into a Semi / Anti join,
//     hoisting a correlated subquery's correlation predicate (and, for IN, the
//     IN equality) into the join condition. NOT IN is only turned into an
//     AntiJoin when neither side can be NULL. Handled shapes only; anything else
//     is left as a represented subquery (still correct).
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

// Column pruning: drop output columns that no ancestor consumes, narrowing the
// data that flows through the plan. Scans and Projects shed unreferenced columns
// outright; passthrough operators, Joins, and Aggregates keep only the columns
// their consumers or their own expressions need, with every positional column
// slot remapped to the compacted layout. The root's output is fully preserved
// (it is the query result). Set operations, VALUES, DML, and any operator that
// carries an embedded subquery are treated conservatively (their inputs are kept
// intact) so a correlated outer reference can never lose the column it needs.
// Embedded subquery sub-plans are pruned independently. In place; takes `node`
// by owning reference because pruning can shrink the root's own layout.
void prune_columns(LogicalNodePtr& node);

// Subquery decorrelation: rewrite a Filter whose entire predicate is a
// `[NOT] EXISTS (subquery)` or a `x [NOT] IN (subquery)` into a SemiJoin
// (EXISTS / IN) or AntiJoin (NOT EXISTS / NOT IN) whose left input is the
// filter's child and whose right input is the subquery's relation.
//
// For a correlated subquery whose correlation lives in a single top Filter (all
// OuterRefs at depth 1, no nested subquery in the correlation, and nothing
// correlated below that Filter), the correlation predicate is hoisted into the
// join condition (OuterRef -> a left column, inner column -> a right column).
// For IN, the join condition also carries the IN equality
// `x = <the subquery's single projected column>` (remapped into the right
// frame), and any local WHERE inside the subquery stays as a Filter on the right
// input. Positive IN is always safe to make a SemiJoin (in a Filter, FALSE and
// UNKNOWN both drop the row); NOT IN is only turned into an AntiJoin when both
// the probe value and the projected column are provably NOT NULL.
//
// Any shape not matching this is left untouched as a represented subquery, so
// the rewrite is always either a valid decorrelation or a no-op. Takes `node` by
// owning reference (the Filter is replaced by the join) and recurses children and
// embedded subquery sub-plans.
void decorrelate_exists(LogicalNodePtr& node);

// Predicate pushdown: for a Filter over an INNER / CROSS Join, split the
// predicate into conjuncts and push each conjunct that references only one
// join input down into that input (remapping right-side positional column
// slots by the left input's width); conjuncts spanning both sides, or carrying
// a subquery / outer reference, stay above the Join. Also merges a Filter
// directly over a Filter and removes a Filter whose predicate is constant
// `true`. Takes `node` by owning reference because a pushed-empty Filter is
// replaced by its child. Recurses children and embedded subquery sub-plans.
void push_down_filters(LogicalNodePtr& node);

}  // namespace db25::plan
