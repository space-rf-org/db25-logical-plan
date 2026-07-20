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

LogicalNodePtr Binder::bind_join(LogicalNodePtr left, const ASTNode* join_node,
                                 std::string& error) {
    // A join node's children are the right-hand relation(s) plus the ON
    // predicate. Bind the first relation child as the right input; the first
    // non-relation, non-USING child is the ON condition.
    const ASTNode* right_ref = nullptr;
    const ASTNode* predicate = nullptr;
    for (const ASTNode* c = first_child(join_node); c != nullptr; c = c->next_sibling) {
        if (c->node_type == NodeType::TableRef) {
            if (right_ref == nullptr) {
                right_ref = c;
            }
        } else if (is_join_node(c->node_type)) {
            error = "nested join in a single join node not yet lowered (TODO)";
            return nullptr;
        } else if (c->node_type == NodeType::UsingClause) {
            error = "JOIN USING not yet lowered (TODO)";
            return nullptr;
        } else if (predicate == nullptr) {
            predicate = c;  // the ON expression
        }
    }
    if (right_ref == nullptr) {
        error = "join without a right-hand base table not yet lowered (TODO)";
        return nullptr;
    }

    auto right = bind_table_ref(right_ref, error);
    if (!right) {
        return nullptr;
    }

    auto join = make_node(LogicalOp::Join);
    join->join_type = join_type_of(join_node);
    join->predicate = predicate;

    // Build the concatenated output schema (left ++ right) with outer-join
    // nullability applied to the null-supplying side.
    const bool null_left =
        join->join_type == ast::JoinType::Right || join->join_type == ast::JoinType::Full;
    const bool null_right =
        join->join_type == ast::JoinType::Left || join->join_type == ast::JoinType::Full;

    Schema out;
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

LogicalNodePtr Binder::bind_from(const ASTNode* from_clause, std::string& error) {
    const ASTNode* item = first_child(from_clause);
    if (item == nullptr) {
        error = "empty FROM clause";
        return nullptr;
    }
    if (item->node_type != NodeType::TableRef) {
        error = "FROM item kind not yet lowered (TODO: derived tables / VALUES)";
        return nullptr;
    }
    LogicalNodePtr current = bind_table_ref(item, error);
    if (!current) {
        return nullptr;
    }
    for (item = item->next_sibling; item != nullptr; item = item->next_sibling) {
        if (is_join_node(item->node_type)) {
            current = bind_join(std::move(current), item, error);
            if (!current) {
                return nullptr;
            }
        } else if (item->node_type == NodeType::TableRef) {
            error = "comma / cross join of base tables not yet lowered (TODO)";
            return nullptr;
        }
        // Other node kinds at FROM level are ignored (defensive).
    }
    return current;
}

BindResult Binder::bind(const ASTNode* select_stmt) {
    BindResult result;
    if (select_stmt == nullptr) {
        result.error = "null statement";
        return result;
    }
    if (select_stmt->node_type != NodeType::SelectStmt) {
        // Set operations (UNION/...) and DML are out of scope for this slice.
        result.error =
            "only single SELECT statements are lowered today (TODO: set ops, DML)";
        return result;
    }

    // --- FROM -> Scan / Join subtree ---
    const ASTNode* from = find_child(select_stmt, NodeType::FromClause);
    if (from == nullptr) {
        result.error = "SELECT without FROM not yet lowered (TODO: constant / VALUES)";
        return result;
    }
    LogicalNodePtr current = bind_from(from, result.error);
    if (!current) {
        return result;
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
        result.error = "analyzer produced no projection for this SELECT";
        return result;
    }
    if (select_list != nullptr) {
        for (const ASTNode* item = first_child(select_list); item != nullptr;
             item = item->next_sibling) {
            project->exprs.push_back(item);
        }
    }
    project->add_child(std::move(current));
    current = std::move(project);

    // --- ORDER BY -> Sort ---
    if (const ASTNode* order_by = find_child(select_stmt, NodeType::OrderByClause)) {
        (void)order_by;
        auto sort = make_node(LogicalOp::Sort);
        sort->output = current->output;  // sort is schema-preserving
        sort->add_child(std::move(current));
        current = std::move(sort);
        // TODO: capture sort keys / directions from the ORDER BY children.
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

    result.root = std::move(current);
    result.ok = true;
    return result;
}

}  // namespace db25::plan
