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

#include <string>
#include <vector>

namespace db25::plan {

// Test-only accessor (defined in the test TU) for the private lowering surface.
struct BinderExprTestAccess;

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

    // Lower a single non-star projected item at ordinal `index` against `input`
    // (the child's output schema). When the child is an Aggregate its output is
    // 1:1 with the select list, so the item maps positionally; otherwise a
    // precomputed aggregate / window item is referenced by output name (the
    // producer map) and anything else is lowered as a fresh expression. Returns
    // null on failure.
    [[nodiscard]] ExprPtr lower_projection_item(const db25::ast::ASTNode* item,
                                                const Schema& input, std::size_t index,
                                                bool child_is_aggregate, std::string& error);

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

    friend struct BinderExprTestAccess;
};

}  // namespace db25::plan
