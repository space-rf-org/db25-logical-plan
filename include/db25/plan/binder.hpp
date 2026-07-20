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

#include "db25/plan/logical_plan.hpp"

#include "db25/ast/ast_node.hpp"
#include "db25/semantic/analyzer.hpp"
#include "db25/semantic/catalog.hpp"

#include <string>

namespace db25::plan {

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

    // Build a Scan output schema from the catalog for a base table.
    [[nodiscard]] Schema scan_schema(const db25::semantic::TableInfo& table,
                                     std::uint32_t table_id) const;

    const db25::semantic::Analyzer& analyzer_;
    const db25::semantic::Catalog& catalog_;
};

}  // namespace db25::plan
