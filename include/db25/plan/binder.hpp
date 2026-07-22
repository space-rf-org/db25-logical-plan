// DB25 Logical Plan - Binder
//
// Lowers a parsed + analyzed SELECT statement into a LogicalNode tree.
//
// The binder is a *consumer* of the semantic analyzer: it never re-derives
// types or resolves names itself. It reads the analyzer's results
// (projection_of / type_of / nullability_of) and the catalog (for base-table
// scan schemas) and assembles the relational-algebra pipeline.
//
// Pipeline shape (bottom-up), the classic logical lowering of a SELECT block:
//
//     Scan(s)  ->  [Join]  ->  [Filter (WHERE)]  ->  [Aggregate (GROUP BY)]
//              ->  Project (SELECT list)  ->  [Sort (ORDER BY)]  ->  [Limit]
//
// Bracketed stages appear only when the corresponding clause is present.

#pragma once

#include "db25/plan/expr_ir.hpp"
#include "db25/plan/logical_plan.hpp"

#include "db25/ast/ast_node.hpp"
#include "db25/semantic/analyzer.hpp"
#include "db25/semantic/catalog.hpp"

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace db25::plan {

// Test-only accessor (defined in the test TU) for the private lowering surface.
struct BinderExprTestAccess;

// A precomputed-column frame for lowering the expressions that sit directly
// above an Aggregate (its Project, HAVING filter, and hidden ORDER BY keys).
// Each entry pairs a producing AST expression - a GROUP BY key or an aggregate
// call - with the slot of its result column in the Aggregate output
// (group_keys ++ aggregates). A subexpression lowered above the aggregate that
// structurally matches a producer becomes a ColumnRef into that slot instead of
// being re-lowered against base columns the aggregate no longer exposes (so
// `SELECT SUM(x)+1` keeps the `+1`, and `SELECT COUNT(*), dept GROUP BY dept`
// reorders correctly). Matching is structural, not by name, because a call's
// name is not unique - `SUM(x)` and `SUM(y)` share the text "SUM".
struct AggregateFrame {
    std::vector<std::pair<const db25::ast::ASTNode*, std::uint32_t>> producers;
};

// Outcome of binding. On success `root` is the plan tree and `ok` is true. On
// failure `root` is null and `error` explains why (no exceptions are thrown -
// the whole stack is built -fno-exceptions).
struct BindResult {
    LogicalNodePtr root;
    bool ok = false;
    std::string error;
};

class Binder {
public:
    // `analyzer` must already have analyze()d the statement passed to bind().
    // `catalog` is the same catalog the analyzer used; it supplies base-table
    // scan schemas. Both are borrowed and must outlive the Binder and any plan
    // it produces (as must the Parser that owns the AST).
    Binder(const db25::semantic::Analyzer& analyzer,
           const db25::semantic::Catalog& catalog)
        : analyzer_(analyzer), catalog_(catalog) {}

    // Lower a statement (SELECT, a set operation, or INSERT/UPDATE/DELETE) into
    // a plan.
    [[nodiscard]] BindResult bind(const db25::ast::ASTNode* stmt);

private:
    // Dispatch a row-producing query block: a SELECT or a set operation. Used at
    // the top level, for derived tables, and for INSERT ... SELECT sources.
    LogicalNodePtr bind_query(const db25::ast::ASTNode* query, std::string& error);
    LogicalNodePtr bind_select(const db25::ast::ASTNode* select_stmt, std::string& error);
    LogicalNodePtr bind_setop(const db25::ast::ASTNode* setop, std::string& error);

    // DML entry points.
    LogicalNodePtr bind_insert(const db25::ast::ASTNode* insert_stmt, std::string& error);
    LogicalNodePtr bind_update(const db25::ast::ASTNode* update_stmt, std::string& error);
    LogicalNodePtr bind_delete(const db25::ast::ASTNode* delete_stmt, std::string& error);

    // FROM clause -> Scan / Join subtree. Returns null on unsupported shapes.
    LogicalNodePtr bind_from(const db25::ast::ASTNode* from_clause,
                             std::string& error);
    // A single FROM relation: a base table (Scan) or a derived table / subquery
    // (its inner plan). Returns null on unsupported shapes.
    LogicalNodePtr bind_relation(const db25::ast::ASTNode* relation,
                                 std::string& error);
    LogicalNodePtr bind_table_ref(const db25::ast::ASTNode* table_ref,
                                  std::string& error);
    LogicalNodePtr bind_join(LogicalNodePtr left,
                             const db25::ast::ASTNode* join_node,
                             std::string& error);

    // Build a Scan output schema from the catalog for a base table. `alias` is
    // the relation's correlation name (or its table name when unaliased); it is
    // stamped on every column so a self-join's otherwise-identical column
    // references can be disambiguated by their qualifier.
    [[nodiscard]] Schema scan_schema(const db25::semantic::TableInfo& table,
                                     std::uint32_t table_id,
                                     std::string_view alias) const;

    // If `stmt` (an INSERT / UPDATE / DELETE) carries a RETURNING clause, wrap
    // `dml` in a Returning node whose output schema is resolved against the
    // target table's catalog columns. Returns `dml` unchanged when there is no
    // RETURNING clause. On error returns null and sets `error`.
    LogicalNodePtr wrap_returning(LogicalNodePtr dml, const db25::ast::ASTNode* stmt,
                                  std::string& error);

    // ------------------------------------------------------------------
    // AST -> owned, typed Expr lowering (expr_lower.cpp).
    //
    // The single place that reads the analyzer + AST and emits an owned Expr:
    // it dispatches on node_type, bakes type / nullability once, resolves a
    // ColumnRef to a flat `input_index` into `input` (the owning operator's
    // input schema; for a Join, child0.output ++ child1.output), lowers an
    // embedded subquery inline into an owned `sub_plan`, and represents a
    // correlated outer-column reference as an `OuterRef` resolved against an
    // enclosing input on `outer_inputs_`. Returns null and sets `error` on an
    // unlowerable shape (the whole stack is -fno-exceptions).
    //
    // ADDITIVE (migration steps 1-2): not yet called by the operator-building
    // code, so it does not change any existing plan behavior.
    [[nodiscard]] ExprPtr lower_expr(const db25::ast::ASTNode* n, const Schema& input,
                                     std::string& error);

    // If `call` is an aggregate / window call whose result a child Aggregate /
    // Window node already produced (matched by output name in `input`), return a
    // ColumnRef reading that precomputed output column; otherwise null. This is
    // the producer map applied inside expression lowering, so an aggregate that
    // surfaces *above* its Aggregate node - referenced in HAVING or ORDER BY,
    // e.g. `HAVING SUM(x) > 10` - resolves to the already-computed column instead
    // of being re-lowered as a fresh call whose base-column arguments are no
    // longer in scope. Self-gating: it only matches when `input` actually carries
    // a same-named column, so lowering an aggregate against its pre-aggregation
    // input (where no such column exists) is unaffected.
    [[nodiscard]] ExprPtr lower_precomputed_aggregate(const db25::ast::ASTNode* call,
                                                      const Schema& input) const;

    // If `n` structurally matches a producer in the active Aggregate frame
    // (`agg_frame_`), return that producer's output slot; otherwise -1. This is
    // the aggregate producer map applied inside expression lowering: an aggregate
    // call or group-key expression that surfaces above its Aggregate node - in
    // the SELECT list, HAVING, or ORDER BY - resolves to the already-computed
    // column instead of being re-lowered against base columns that are no longer
    // in scope. Returns -1 when no frame is active.
    [[nodiscard]] int aggregate_frame_slot(const db25::ast::ASTNode* n) const;

    // Structural equality of two producer expressions (an aggregate call or a
    // group key) for Aggregate-frame matching and aggregate dedup. A column
    // reference compares by resolved (table_id, column_id) so a qualifier or
    // alias difference still matches the same base column; other nodes compare
    // on node_type + operator text with structurally-equal children. This tells
    // `SUM(x)` and `SUM(y)` apart, which by-name matching cannot.
    [[nodiscard]] static bool same_producer_expr(const db25::ast::ASTNode* a,
                                                 const db25::ast::ASTNode* b);

    // Lower a SELECT-list / RETURNING projection into owned expressions, one per
    // output column, appended to `out`. `child` is the operator feeding the
    // projection (its `output` is the input schema against which items are
    // lowered). A `*` expands to one positional ColumnRef per covered column; a
    // projected item that names a precomputed group/aggregate/window output of
    // `child` lowers to a ColumnRef into that child column (the producer map)
    // rather than a re-evaluated expression. Returns false and sets `error` on
    // an unlowerable shape (e.g. a qualified `t.*`, not yet supported).
    [[nodiscard]] bool lower_projection(const db25::ast::ASTNode* select_list,
                                        const LogicalNode* child,
                                        std::vector<ExprPtr>& out, std::string& error);

    // Lower a single non-star projected item against `input` (the child's output
    // schema). Over an Aggregate the active `agg_frame_` resolves a group key or
    // aggregate call (including one wrapped in a larger expression like
    // `SUM(x)+1`) to a ColumnRef into the precomputed output; a precomputed
    // window item is referenced by output name; anything else is lowered as a
    // fresh expression. Returns null on failure.
    [[nodiscard]] ExprPtr lower_projection_item(const db25::ast::ASTNode* item,
                                                const Schema& input, std::string& error);

    // Fold a scalar / IN / EXISTS subquery into an owned Subquery Expr: bind the
    // inner block into `sub_plan` (with `input` pushed as an enclosing schema for
    // correlated resolution) and record its correlation flag. `left` (IN only) is
    // the already-lowered left operand, kept as children[0].
    [[nodiscard]] ExprPtr lower_subquery(const db25::ast::ASTNode* subquery,
                                         SubqueryKind kind, bool negated, ExprPtr left,
                                         db25::ast::DataType type, std::uint8_t nullability,
                                         const Schema& input, std::string& error);

    // Lower an AST WindowSpec (the OVER (...) clause) into an owned WindowSpecIR.
    [[nodiscard]] bool lower_window_spec(const db25::ast::ASTNode* window_spec,
                                         const Schema& input, WindowSpecIR& out,
                                         std::string& error);

    const db25::semantic::Analyzer& analyzer_;
    const db25::semantic::Catalog& catalog_;

    // Enclosing operators' input schemas, for resolving correlated outer-column
    // references while lowering a subquery body. Ordered outermost-first, so the
    // immediately-enclosing block is back(): OuterRef depth 1 is `outer_inputs_`
    // back(), depth 2 the one before it, and so on.
    std::vector<const Schema*> outer_inputs_;

    // The Aggregate frame active while lowering the Project / HAVING / hidden
    // ORDER BY expressions directly above an Aggregate (see AggregateFrame).
    // Null everywhere else - including while lowering the aggregate's own
    // group-key / aggregate payloads against its pre-aggregation input, and
    // while lowering an ORDER BY key against the visible Project output (a
    // different frame). bind_select saves and restores it so a nested block (a
    // scalar subquery in a select item) does not clobber the enclosing frame.
    const AggregateFrame* agg_frame_ = nullptr;

    // Maps each window-call SELECT item to the output slot the child Window node
    // computed for it, so the Project references the RIGHT column. Resolving a
    // window item by output name would collide - two un-aliased calls of the same
    // function (SUM(a) OVER, SUM(b) OVER) both produce a column named "SUM", so a
    // by-name lookup would point both at the first one. bind_select saves and
    // restores this so a nested block does not clobber the enclosing map.
    std::vector<std::pair<const db25::ast::ASTNode*, std::uint32_t>> window_slots_;

    friend struct BinderExprTestAccess;
};

}  // namespace db25::plan
