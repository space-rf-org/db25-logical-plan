// DB25 Logical Plan - Binder implementation
//
// See include/db25/plan/binder.hpp for the contract and pipeline shape.

#include "db25/plan/binder.hpp"

#include "db25/ast/ast_node.hpp"
#include "db25/ast/node_types.hpp"
#include "db25/semantic/ast_helpers.hpp"  // first_child / find_child / alias_of / split_column_ref

#include <charconv>
#include <memory>
#include <string>
#include <string_view>
#include <utility>

namespace db25::plan {

using db25::ast::ASTNode;
using db25::ast::DataType;
using db25::ast::NodeType;
using db25::semantic::alias_of;
using db25::semantic::find_child;
using db25::semantic::first_child;
using db25::semantic::ResolvedColumn;
using db25::semantic::split_column_ref;
using db25::semantic::TableInfo;

namespace {

LogicalNodePtr make_node(LogicalOp op) {
    return std::make_unique<LogicalNode>(op);
}

// Convert an analyzer ResolvedColumn to an IR ColumnSchema (field-for-field).
ColumnSchema to_schema(const ResolvedColumn& c) {
    return ColumnSchema{c.name, c.type, c.nullable, c.table_id, c.column_id};
}

bool is_join_node(NodeType t) {
    switch (t) {
        case NodeType::JoinClause:
        case NodeType::InnerJoin:
        case NodeType::LeftJoin:
        case NodeType::RightJoin:
        case NodeType::FullJoin:
        case NodeType::CrossJoin:
        case NodeType::LateralJoin:
            return true;
        default:
            return false;
    }
}

// A derived table / subquery used as a FROM relation.
bool is_derived_node(NodeType t) {
    return t == NodeType::Subquery || t == NodeType::SubqueryExpr;
}

// A set-operation node (UNION / INTERSECT / EXCEPT).
bool is_setop_node(NodeType t) {
    return t == NodeType::UnionStmt || t == NodeType::IntersectStmt ||
           t == NodeType::ExceptStmt;
}

// The inner query block of a subquery / derived table: a SELECT block or a
// nested set operation.
const ASTNode* subquery_body(const ASTNode* node) {
    if (ASTNode* sel = find_child(node, NodeType::SelectStmt)) {
        return sel;
    }
    for (const ASTNode* c = first_child(node); c != nullptr; c = c->next_sibling) {
        if (is_setop_node(c->node_type)) {
            return c;
        }
    }
    return nullptr;
}

// Map a set-operation AST node to the IR SetOp, honoring UNION ALL (the ALL
// flag) vs. distinct UNION.
ast::SetOp setop_kind(const ASTNode* n) {
    const bool all = n->has_flag(ast::NodeFlags::All);
    switch (n->node_type) {
        case NodeType::UnionStmt:     return all ? ast::SetOp::UnionAll : ast::SetOp::Union;
        case NodeType::IntersectStmt: return ast::SetOp::Intersect;
        case NodeType::ExceptStmt:    return ast::SetOp::Except;
        default:                      return ast::SetOp::Union;
    }
}

// Build a binary Join node over two already-bound inputs, producing the
// concatenated (left ++ right) output schema with outer-join nullability applied
// to the null-supplying side. Used for explicit joins without USING and for
// comma / CROSS joins.
LogicalNodePtr make_join_node(LogicalNodePtr left, LogicalNodePtr right,
                              ast::JoinType jt, const ASTNode* predicate) {
    auto join = std::make_unique<LogicalNode>(LogicalOp::Join);
    join->join_type = jt;
    join->predicate = predicate;
    const bool null_left = jt == ast::JoinType::Right || jt == ast::JoinType::Full;
    const bool null_right = jt == ast::JoinType::Left || jt == ast::JoinType::Full;
    Schema out;
    out.reserve(left->output.size() + right->output.size());
    for (const auto& col : left->output) {
        ColumnSchema c = col;
        c.nullable = c.nullable || null_left;
        out.push_back(std::move(c));
    }
    for (const auto& col : right->output) {
        ColumnSchema c = col;
        c.nullable = c.nullable || null_right;
        out.push_back(std::move(c));
    }
    join->output = std::move(out);
    join->add_child(std::move(left));
    join->add_child(std::move(right));
    return join;
}

std::string upper(std::string_view s) {
    std::string out;
    out.reserve(s.size());
    for (const char ch : s) {
        out.push_back((ch >= 'a' && ch <= 'z') ? static_cast<char>(ch - 32) : ch);
    }
    return out;
}

// Map a join AST node to a JoinType. Dedicated node types win; a generic
// JoinClause carries the kind in its primary_text (e.g. "LEFT OUTER JOIN").
ast::JoinType join_type_of(const ASTNode* join) {
    switch (join->node_type) {
        case NodeType::InnerJoin: return ast::JoinType::Inner;
        case NodeType::LeftJoin:  return ast::JoinType::Left;
        case NodeType::RightJoin: return ast::JoinType::Right;
        case NodeType::FullJoin:  return ast::JoinType::Full;
        case NodeType::CrossJoin: return ast::JoinType::Cross;
        case NodeType::LateralJoin: return ast::JoinType::Lateral;
        default: break;
    }
    const std::string kind = upper(join->primary_text);
    if (kind.find("FULL") != std::string::npos) return ast::JoinType::Full;
    if (kind.find("LEFT") != std::string::npos) return ast::JoinType::Left;
    if (kind.find("RIGHT") != std::string::npos) return ast::JoinType::Right;
    if (kind.find("CROSS") != std::string::npos) return ast::JoinType::Cross;
    return ast::JoinType::Inner;
}

// Minimal aggregate-function recognizer. The analyzer has a richer private list;
// this covers the standard SQL set which is all the binder needs to separate
// grouping keys from aggregate outputs in a SELECT list.
bool is_aggregate_call(const ASTNode* n) {
    if (n == nullptr) {
        return false;
    }
    if (n->node_type != NodeType::FunctionCall &&
        n->node_type != NodeType::FunctionExpr) {
        return false;
    }
    const std::string name = upper(n->primary_text);
    return name == "COUNT" || name == "SUM" || name == "AVG" ||
           name == "MIN" || name == "MAX" || name == "TOTAL" ||
           name == "GROUP_CONCAT" || name == "STRING_AGG";
}

// Parse a LIMIT / OFFSET operand. Only a non-negative integer literal yields a
// value; anything else (parameter, expression) leaves `out` untouched and
// returns false so the caller records "no static bound".
bool parse_int_literal(const ASTNode* op, std::int64_t& out) {
    if (op == nullptr || op->node_type != NodeType::IntegerLiteral) {
        return false;
    }
    const std::string_view t = op->primary_text;
    std::int64_t v = 0;
    const auto [ptr, ec] = std::from_chars(t.data(), t.data() + t.size(), v);
    if (ec != std::errc{} || ptr != t.data() + t.size() || v < 0) {
        return false;
    }
    out = v;
    return true;
}

// The output name of a projected select-list item: its alias if any, else the
// (undotted) column name for a column reference, else its literal/primary text.
std::string item_output_name(const ASTNode* item) {
    const std::string_view alias = alias_of(item);
    if (!alias.empty()) {
        return std::string{alias};
    }
    if (item->node_type == NodeType::ColumnRef) {
        return std::string{split_column_ref(item->primary_text).column};
    }
    return std::string{item->primary_text};
}

}  // namespace

Schema Binder::scan_schema(const TableInfo& table, std::uint32_t table_id) const {
    Schema schema;
    schema.reserve(table.columns.size());
    for (const auto& c : table.columns) {
        schema.push_back(ColumnSchema{c.name, c.type, c.nullable, table_id, c.column_id});
    }
    return schema;
}

LogicalNodePtr Binder::bind_table_ref(const ASTNode* table_ref, std::string& error) {
    const std::string_view name = table_ref->primary_text;
    const TableInfo* table = catalog_.find_table(name);
    if (table == nullptr) {
        error = "unresolved table '" + std::string{name} + "'";
        return nullptr;
    }
    auto scan = make_node(LogicalOp::Scan);
    scan->table_name = std::string{name};
    scan->alias = std::string{alias_of(table_ref)};
    scan->output = scan_schema(*table, table->table_id);
    return scan;
}

LogicalNodePtr Binder::bind_relation(const ASTNode* relation, std::string& error) {
    if (relation->node_type == NodeType::TableRef) {
        return bind_table_ref(relation, error);
    }
    if (is_derived_node(relation->node_type)) {
        // Derived table / subquery in FROM: bind the inner query block and use
        // its plan as the Scan-equivalent input. Its output schema is the
        // derived projection (analyzer-resolved); the alias labels the relation.
        const ASTNode* body = subquery_body(relation);
        if (body == nullptr) {
            error = "derived table without a query body";
            return nullptr;
        }
        auto inner = bind_query(body, error);
        if (!inner) {
            return nullptr;
        }
        inner->alias = std::string{alias_of(relation)};
        return inner;
    }
    error = "unsupported FROM relation kind (TODO)";
    return nullptr;
}

LogicalNodePtr Binder::bind_join(LogicalNodePtr left, const ASTNode* join_node,
                                 std::string& error) {
    // A join node's children are the right-hand relation plus either an ON
    // predicate or a USING clause. Bind the first relation child as the right
    // input; the first non-relation, non-USING child is the ON condition.
    const ASTNode* right_ref = nullptr;
    const ASTNode* predicate = nullptr;
    const ASTNode* using_clause = nullptr;
    for (const ASTNode* c = first_child(join_node); c != nullptr; c = c->next_sibling) {
        if (c->node_type == NodeType::TableRef || is_derived_node(c->node_type)) {
            if (right_ref == nullptr) {
                right_ref = c;
            }
        } else if (is_join_node(c->node_type)) {
            error = "nested join in a single join node not yet lowered (TODO)";
            return nullptr;
        } else if (c->node_type == NodeType::UsingClause) {
            using_clause = c;
        } else if (predicate == nullptr) {
            predicate = c;  // the ON expression
        }
    }
    if (right_ref == nullptr) {
        error = "join without a right-hand relation not yet lowered (TODO)";
        return nullptr;
    }

    auto right = bind_relation(right_ref, error);
    if (!right) {
        return nullptr;
    }

    const ast::JoinType jt = join_type_of(join_node);
    if (using_clause == nullptr) {
        return make_join_node(std::move(left), std::move(right), jt, predicate);
    }

    // JOIN ... USING (cols): the named columns are shared and collapse to a
    // single merged output column. Keep the left copy and drop the right's
    // duplicate. The join stays predicate-less (the equality is implied).
    std::vector<std::string_view> merged;
    for (const ASTNode* col = first_child(using_clause); col != nullptr;
         col = col->next_sibling) {
        merged.push_back(split_column_ref(col->primary_text).column);
    }
    const auto is_merged = [&merged](std::string_view name) {
        for (const std::string_view m : merged) {
            if (m == name) {
                return true;
            }
        }
        return false;
    };

    auto join = make_node(LogicalOp::Join);
    join->join_type = jt;
    join->predicate = nullptr;
    const bool null_left = jt == ast::JoinType::Right || jt == ast::JoinType::Full;
    const bool null_right = jt == ast::JoinType::Left || jt == ast::JoinType::Full;
    Schema out;
    for (const auto& col : left->output) {
        ColumnSchema c = col;
        c.nullable = c.nullable || null_left;
        out.push_back(std::move(c));
    }
    for (const auto& col : right->output) {
        if (is_merged(col.name)) {
            continue;  // merged into the left copy
        }
        ColumnSchema c = col;
        c.nullable = c.nullable || null_right;
        out.push_back(std::move(c));
    }
    join->output = std::move(out);
    join->add_child(std::move(left));
    join->add_child(std::move(right));
    return join;
}

LogicalNodePtr Binder::bind_from(const ASTNode* from_clause, std::string& error) {
    const ASTNode* item = first_child(from_clause);
    if (item == nullptr) {
        error = "empty FROM clause";
        return nullptr;
    }
    LogicalNodePtr current = bind_relation(item, error);
    if (!current) {
        return nullptr;
    }
    for (item = item->next_sibling; item != nullptr; item = item->next_sibling) {
        if (is_join_node(item->node_type)) {
            current = bind_join(std::move(current), item, error);
            if (!current) {
                return nullptr;
            }
        } else if (item->node_type == NodeType::TableRef ||
                   is_derived_node(item->node_type)) {
            // A comma-separated FROM item is a CROSS join of the two relations.
            auto right = bind_relation(item, error);
            if (!right) {
                return nullptr;
            }
            current = make_join_node(std::move(current), std::move(right),
                                     ast::JoinType::Cross, nullptr);
        }
        // Other node kinds at FROM level are ignored (defensive).
    }
    return current;
}

BindResult Binder::bind(const ASTNode* stmt) {
    BindResult result;
    if (stmt == nullptr) {
        result.error = "null statement";
        return result;
    }
    switch (stmt->node_type) {
        case NodeType::SelectStmt:
        case NodeType::UnionStmt:
        case NodeType::IntersectStmt:
        case NodeType::ExceptStmt:
            result.root = bind_query(stmt, result.error);
            break;
        case NodeType::InsertStmt:
            result.root = bind_insert(stmt, result.error);
            break;
        case NodeType::UpdateStmt:
            result.root = bind_update(stmt, result.error);
            break;
        case NodeType::DeleteStmt:
            result.root = bind_delete(stmt, result.error);
            break;
        default:
            result.error = "statement kind not yet lowered (TODO)";
            return result;
    }
    result.ok = (result.root != nullptr);
    return result;
}

LogicalNodePtr Binder::bind_query(const ASTNode* query, std::string& error) {
    if (query == nullptr) {
        error = "null query";
        return nullptr;
    }
    if (query->node_type == NodeType::SelectStmt) {
        return bind_select(query, error);
    }
    if (is_setop_node(query->node_type)) {
        return bind_setop(query, error);
    }
    error = "unsupported query block kind (TODO)";
    return nullptr;
}

LogicalNodePtr Binder::bind_setop(const ASTNode* setop, std::string& error) {
    // A set-operation node has exactly two branch children (left, right); the
    // parser folds successive operators left-deep, so the left child may itself
    // be a nested set operation. This left-associativity is preserved here.
    const ASTNode* left_q = first_child(setop);
    const ASTNode* right_q = left_q != nullptr ? left_q->next_sibling : nullptr;
    if (left_q == nullptr || right_q == nullptr) {
        error = "set operation without two branches";
        return nullptr;
    }
    auto left = bind_query(left_q, error);
    if (!left) {
        return nullptr;
    }
    auto right = bind_query(right_q, error);
    if (!right) {
        return nullptr;
    }

    auto node = make_node(LogicalOp::SetOp);
    node->set_op = setop_kind(setop);
    // The reconciled output schema is the analyzer's projection for the set-op
    // node (arity checked, branch types unified, nullability OR-ed).
    if (const auto* proj = analyzer_.projection_of(setop)) {
        node->output.reserve(proj->size());
        for (const auto& c : *proj) {
            node->output.push_back(to_schema(c));
        }
    } else {
        error = "analyzer produced no projection for this set operation";
        return nullptr;
    }
    node->add_child(std::move(left));
    node->add_child(std::move(right));
    return node;
}

LogicalNodePtr Binder::bind_select(const ASTNode* select_stmt, std::string& error) {
    // --- FROM -> Scan / Join subtree (or a synthetic single row) ---
    LogicalNodePtr current;
    const ASTNode* from = find_child(select_stmt, NodeType::FromClause);
    if (from == nullptr) {
        // FROM-less SELECT (e.g. `SELECT 1 + 2`, `SELECT now()`): project over a
        // synthetic single-row, zero-column input (the standard "dual").
        auto values = make_node(LogicalOp::Values);
        values->value_rows.emplace_back();  // one empty row
        current = std::move(values);
    } else {
        current = bind_from(from, error);
        if (!current) {
            return nullptr;
        }
    }

    // --- WHERE -> Filter ---
    if (const ASTNode* where = find_child(select_stmt, NodeType::WhereClause)) {
        auto filter = make_node(LogicalOp::Filter);
        filter->predicate = first_child(where);  // the predicate expression
        filter->output = current->output;         // filter is schema-preserving
        filter->add_child(std::move(current));
        current = std::move(filter);
    }

    // --- GROUP BY -> Aggregate ---
    const ASTNode* group_by = find_child(select_stmt, NodeType::GroupByClause);
    const ASTNode* select_list = find_child(select_stmt, NodeType::SelectList);
    if (group_by != nullptr) {
        auto agg = make_node(LogicalOp::Aggregate);
        for (const ASTNode* key = first_child(group_by); key != nullptr;
             key = key->next_sibling) {
            agg->group_keys.push_back(key);
        }
        // Derive the aggregate output by walking the SELECT list in order,
        // classifying each item as a grouping key or an aggregate result and
        // reading its type / nullability back from the analyzer.
        if (select_list != nullptr) {
            for (const ASTNode* item = first_child(select_list); item != nullptr;
                 item = item->next_sibling) {
                ColumnSchema col;
                col.name = item_output_name(item);
                col.type = analyzer_.type_of(item);
                col.nullable = analyzer_.nullability_of(item) != 1;
                if (is_aggregate_call(item)) {
                    agg->aggregates.push_back(item);
                }
                agg->output.push_back(std::move(col));
            }
        }
        agg->add_child(std::move(current));
        current = std::move(agg);
    }

    // --- SELECT list -> Project (authoritative output schema) ---
    auto project = make_node(LogicalOp::Project);
    if (const auto* proj = analyzer_.projection_of(select_stmt)) {
        project->output.reserve(proj->size());
        for (const auto& c : *proj) {
            project->output.push_back(to_schema(c));
        }
    } else {
        error = "analyzer produced no projection for this SELECT";
        return nullptr;
    }
    if (select_list != nullptr) {
        for (const ASTNode* item = first_child(select_list); item != nullptr;
             item = item->next_sibling) {
            project->exprs.push_back(item);
        }
    }
    project->add_child(std::move(current));
    current = std::move(project);

    // --- ORDER BY -> Sort (real sort keys + directions) ---
    if (const ASTNode* order_by = find_child(select_stmt, NodeType::OrderByClause)) {
        auto sort = make_node(LogicalOp::Sort);
        // Each ORDER BY child is a sort expression; the parser records ASC/DESC
        // and NULLS placement in its semantic_flags (bit 7 = DESC, bit 5 = NULLS
        // ordering explicit, bit 4 = NULLS FIRST).
        for (const ASTNode* key = first_child(order_by); key != nullptr;
             key = key->next_sibling) {
            SortKey sk;
            sk.expr = key;
            sk.descending = (key->semantic_flags & (1u << 7)) != 0;
            sk.nulls_order_explicit = (key->semantic_flags & (1u << 5)) != 0;
            sk.nulls_first = (key->semantic_flags & (1u << 4)) != 0;
            sort->sort_keys.push_back(sk);
        }
        sort->output = current->output;  // sort is schema-preserving
        sort->add_child(std::move(current));
        current = std::move(sort);
    }

    // --- LIMIT / OFFSET -> Limit ---
    if (const ASTNode* limit = find_child(select_stmt, NodeType::LimitClause)) {
        auto lim = make_node(LogicalOp::Limit);
        const ASTNode* limit_op = first_child(limit);
        const ASTNode* offset_op = limit_op != nullptr ? limit_op->next_sibling : nullptr;
        std::int64_t v = 0;
        if (parse_int_literal(limit_op, v)) {
            lim->has_limit = true;
            lim->limit = v;
        }
        if (parse_int_literal(offset_op, v)) {
            lim->has_offset = true;
            lim->offset = v;
        }
        lim->output = current->output;  // limit is schema-preserving
        lim->add_child(std::move(current));
        current = std::move(lim);
    }

    return current;
}

// ---------------------------------------------------------------------------
// DML lowering. Each produces a dedicated logical node carrying the target
// table plus the relevant child plan. Deeper semantics (RETURNING projections,
// ON CONFLICT, multi-table UPDATE/DELETE, constraint checking) are left as
// clearly-marked TODOs; the analyzer already validates the surface shapes.
// ---------------------------------------------------------------------------

LogicalNodePtr Binder::bind_insert(const ASTNode* insert_stmt, std::string& error) {
    const ASTNode* table_ref = find_child(insert_stmt, NodeType::TableRef);
    if (table_ref == nullptr) {
        error = "INSERT without a target table";
        return nullptr;
    }
    auto node = make_node(LogicalOp::Insert);
    node->table_name = std::string{table_ref->primary_text};

    // Explicit target column list (empty => all columns in declaration order).
    if (const ASTNode* col_list = find_child(insert_stmt, NodeType::ColumnList)) {
        for (const ASTNode* c = first_child(col_list); c != nullptr; c = c->next_sibling) {
            node->target_columns.push_back(
                std::string{split_column_ref(c->primary_text).column});
        }
    }

    // Source of rows: a VALUES clause or a query (INSERT ... SELECT / set op).
    if (const ASTNode* values = find_child(insert_stmt, NodeType::ValuesClause)) {
        auto vnode = make_node(LogicalOp::Values);
        for (const ASTNode* row = first_child(values); row != nullptr;
             row = row->next_sibling) {
            std::vector<const ASTNode*> vals;
            for (const ASTNode* v = first_child(row); v != nullptr; v = v->next_sibling) {
                vals.push_back(v);
            }
            vnode->value_rows.push_back(std::move(vals));
        }
        node->add_child(std::move(vnode));
    } else {
        const ASTNode* source = find_child(insert_stmt, NodeType::SelectStmt);
        if (source == nullptr) {
            for (const ASTNode* c = first_child(insert_stmt); c != nullptr;
                 c = c->next_sibling) {
                if (is_setop_node(c->node_type)) {
                    source = c;
                    break;
                }
            }
        }
        if (source == nullptr) {
            error = "INSERT has neither VALUES nor a query source";
            return nullptr;
        }
        auto src = bind_query(source, error);
        if (!src) {
            return nullptr;
        }
        node->add_child(std::move(src));
    }
    // A bare INSERT projects nothing (RETURNING is not modeled yet). TODO.
    return node;
}

LogicalNodePtr Binder::bind_update(const ASTNode* update_stmt, std::string& error) {
    const ASTNode* table_ref = find_child(update_stmt, NodeType::TableRef);
    if (table_ref == nullptr) {
        error = "UPDATE without a target table";
        return nullptr;
    }
    // Child plan: a Scan of the target, wrapped in a Filter when there is a
    // WHERE clause (the set of rows the UPDATE rewrites).
    auto child = bind_table_ref(table_ref, error);
    if (!child) {
        return nullptr;
    }
    if (const ASTNode* where = find_child(update_stmt, NodeType::WhereClause)) {
        auto filter = make_node(LogicalOp::Filter);
        filter->predicate = first_child(where);
        filter->output = child->output;
        filter->add_child(std::move(child));
        child = std::move(filter);
    }

    auto node = make_node(LogicalOp::Update);
    node->table_name = std::string{table_ref->primary_text};
    // SET assignments: each a BinaryExpr (primary_text = target column, first
    // child = value expression). Kept borrowed; deeper checking is the
    // analyzer's job. TODO: model the post-update output columns.
    if (const ASTNode* set_clause = find_child(update_stmt, NodeType::SetClause)) {
        for (const ASTNode* asgn = first_child(set_clause); asgn != nullptr;
             asgn = asgn->next_sibling) {
            node->assignments.push_back(asgn);
        }
    }
    node->add_child(std::move(child));
    return node;
}

LogicalNodePtr Binder::bind_delete(const ASTNode* delete_stmt, std::string& error) {
    const ASTNode* table_ref = find_child(delete_stmt, NodeType::TableRef);
    if (table_ref == nullptr) {
        error = "DELETE without a target table";
        return nullptr;
    }
    auto child = bind_table_ref(table_ref, error);
    if (!child) {
        return nullptr;
    }
    if (const ASTNode* where = find_child(delete_stmt, NodeType::WhereClause)) {
        auto filter = make_node(LogicalOp::Filter);
        filter->predicate = first_child(where);
        filter->output = child->output;
        filter->add_child(std::move(child));
        child = std::move(filter);
    }

    auto node = make_node(LogicalOp::Delete);
    node->table_name = std::string{table_ref->primary_text};
    node->add_child(std::move(child));
    return node;
}

}  // namespace db25::plan
