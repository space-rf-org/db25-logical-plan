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
        case NodeType::IntersectStmt: return all ? ast::SetOp::IntersectAll : ast::SetOp::Intersect;
        case NodeType::ExceptStmt:    return all ? ast::SetOp::ExceptAll : ast::SetOp::Except;
        default:                      return ast::SetOp::Union;
    }
}

// Build a binary Join node over two already-bound inputs, producing the
// concatenated (left ++ right) output schema with outer-join nullability applied
// to the null-supplying side. Used for explicit joins without USING and for
// comma / CROSS joins. The node is created predicate-less; a caller with an ON
// condition lowers it (against the join's concatenated input schema) afterwards.
LogicalNodePtr make_join_node(LogicalNodePtr left, LogicalNodePtr right,
                              ast::JoinType jt) {
    auto join = std::make_unique<LogicalNode>(LogicalOp::Join);
    join->join_type = jt;
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

// A window-function call: a FunctionCall / FunctionExpr that carries a WindowSpec
// child (the OVER (...) specification). Declared here so aggregate detection can
// exclude it (SUM(..) OVER (...) is a window function, not a grouping aggregate).
bool is_window_call(const ASTNode* n);

// Walk an expression subtree collecting aggregate call nodes into `out`. Unlike
// the top-level `is_aggregate_call` check this finds aggregates nested inside a
// larger expression (e.g. `SUM(x) + 1`) and aggregates that appear only in
// HAVING / ORDER BY. It deliberately does NOT descend into a window call (an
// aggregate written as a window function is handled by the Window node, not by
// grouping) nor into an embedded Subquery (which owns its own aggregates), and it
// does not descend into an aggregate's own arguments (SQL forbids nesting one
// aggregate inside another).
void collect_aggregates(const ASTNode* n, std::vector<const ASTNode*>& out) {
    if (n == nullptr || n->node_type == NodeType::Subquery || is_window_call(n)) {
        return;
    }
    if (is_aggregate_call(n)) {
        out.push_back(n);
        return;
    }
    for (const ASTNode* c = first_child(n); c != nullptr; c = c->next_sibling) {
        collect_aggregates(c, out);
    }
}

// Walk an expression subtree collecting window-function call nodes into `out`.
// Like `collect_aggregates` for aggregates, this finds window calls nested inside
// a larger expression (e.g. `ROW_NUMBER() OVER (...) + 1`), not just a select
// item that IS a whole window call. On reaching a window call it records that
// node and stops - it does NOT descend into the call's own arguments (SQL forbids
// nesting a window function inside another) - and it does not descend into an
// embedded Subquery (which owns its own window functions).
void collect_windows(const ASTNode* n, std::vector<const ASTNode*>& out) {
    if (n == nullptr || n->node_type == NodeType::Subquery) {
        return;
    }
    if (is_window_call(n)) {
        out.push_back(n);
        return;
    }
    for (const ASTNode* c = first_child(n); c != nullptr; c = c->next_sibling) {
        collect_windows(c, out);
    }
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

// A window-function call: a FunctionCall / FunctionExpr that carries a
// WindowSpec child (the OVER (...) specification). The WindowSpec in turn holds
// the PARTITION BY / ORDER BY / frame sub-clauses.
bool is_window_call(const ASTNode* n) {
    if (n == nullptr ||
        (n->node_type != NodeType::FunctionCall &&
         n->node_type != NodeType::FunctionExpr)) {
        return false;
    }
    return find_child(n, NodeType::WindowSpec) != nullptr;
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

// Build an owned ColumnRef Expr that references slot `slot` of an input schema,
// carrying the referenced column's type, nullability (parser 2-bit: 1 not-null /
// 2 nullable) and provenance ids. The single place a positional projection leaf
// is minted, so passthrough columns and producer-map hits share one encoding.
ExprPtr make_column_ref(std::uint32_t slot, const ColumnSchema& c) {
    auto e = std::make_unique<Expr>(ExprKind::ColumnRef);
    e->input_index = slot;
    e->type = c.type;
    e->nullability = c.nullable ? std::uint8_t{2} : std::uint8_t{1};
    e->ref_table_id = c.table_id;
    e->ref_column_id = c.column_id;
    return e;
}

// Find a schema slot by output column name (the producer-map fallback for a
// precomputed aggregate / window output). Returns -1 when absent.
int slot_by_name(const Schema& s, std::string_view name) {
    for (std::size_t i = 0; i < s.size(); ++i) {
        if (s[i].name == name) {
            return static_cast<int>(i);
        }
    }
    return -1;
}

}  // namespace

ExprPtr Binder::lower_precomputed_aggregate(const ASTNode* call, const Schema& input) const {
    if (call == nullptr || !(is_aggregate_call(call) || is_window_call(call))) {
        return nullptr;
    }
    const int slot = slot_by_name(input, item_output_name(call));
    if (slot < 0) {
        return nullptr;
    }
    return make_column_ref(static_cast<std::uint32_t>(slot),
                           input[static_cast<std::size_t>(slot)]);
}

Schema Binder::scan_schema(const TableInfo& table, std::uint32_t table_id,
                           std::string_view alias) const {
    Schema schema;
    schema.reserve(table.columns.size());
    for (const auto& c : table.columns) {
        ColumnSchema col{c.name, c.type, c.nullable, table_id, c.column_id};
        col.alias = std::string{alias};
        schema.push_back(std::move(col));
    }
    return schema;
}

LogicalNodePtr Binder::bind_table_ref(const ASTNode* table_ref, std::string& error) {
    const std::string_view name = table_ref->primary_text;

    // A CTE reference resolves before the catalog (so `WITH x AS (...)` shadows a
    // base table `x`). Bind a FRESH copy of the CTE body - each reference is an
    // independent derived-table subplan - and label it with the reference's alias
    // (or the CTE name when unaliased) so qualified `name.col` refs resolve.
    // Search innermost-first so an inner WITH shadows an enclosing one.
    for (auto it = ctes_.rbegin(); it != ctes_.rend(); ++it) {
        if (it->first == name) {
            const ASTNode* def = it->second;
            auto body = bind_query(find_child(def, NodeType::SelectStmt), error);
            if (!body) {
                return nullptr;
            }
            // Optional column-list rename `WITH t(a, b)`: rename the subplan's
            // output columns positionally so a later `t.a` / bare `a` resolves.
            if (const ASTNode* col_list = find_child(def, NodeType::ColumnList)) {
                std::size_t i = 0;
                for (const ASTNode* cn = first_child(col_list);
                     cn != nullptr && i < body->output.size();
                     cn = cn->next_sibling, ++i) {
                    body->output[i].name =
                        std::string{split_column_ref(cn->primary_text).column};
                }
            }
            const std::string_view a = alias_of(table_ref);
            body->alias = a.empty() ? std::string{name} : std::string{a};
            // Stamp the reference name onto the output columns so `t.col` picks
            // this instance (and two references to one CTE stay distinguishable
            // in a self-join). See the derived-table path for the rationale.
            if (!body->alias.empty())
                for (auto& c : body->output) c.alias = body->alias;
            return body;
        }
    }

    const TableInfo* table = catalog_.find_table(name);
    if (table == nullptr) {
        error = "unresolved table '" + std::string{name} + "'";
        return nullptr;
    }
    auto scan = make_node(LogicalOp::Scan);
    scan->table_name = std::string{name};
    scan->alias = std::string{alias_of(table_ref)};
    // Qualified column references use the correlation name when one is given,
    // otherwise the table name (`emp.id`); stamp whichever applies so self-join
    // occurrences stay distinguishable.
    const std::string_view eff_alias = scan->alias.empty() ? name : scan->alias;
    scan->output = scan_schema(*table, table->table_id, eff_alias);
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
        // Stamp the correlation name onto every output column so a qualified
        // reference (`p.id`) can pick THIS relation's copy. Without it, two
        // derived tables over the same body share (table_id, column_id) with no
        // distinguishing alias, so find_slot_by_id() resolves both `p.id` and
        // `q.id` to the first match and a self-join predicate `p.id = q.id`
        // collapses to `#0 = #0` (a cross product). Mirrors scan_schema().
        if (!inner->alias.empty())
            for (auto& c : inner->output) c.alias = inner->alias;
        return inner;
    }
    // A parenthesized join group `( a JOIN b ... )` in table-reference position:
    // the parser represents it as a nested FromClause. Build its join subtree the
    // same way a top-level FROM does, preserving the group's own join
    // associativity, and return it as this relation's input.
    if (relation->node_type == NodeType::FromClause) {
        return bind_from(relation, error);
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
    // NATURAL joins carry no ON / USING clause; their join columns are every
    // column common to both inputs. The parser records NATURAL in the join
    // clause's primary_text ("NATURAL JOIN", "NATURAL LEFT JOIN", ...).
    const bool natural =
        upper(join_node->primary_text).find("NATURAL") != std::string::npos;

    if (using_clause == nullptr && !natural) {
        auto join = make_join_node(std::move(left), std::move(right), jt);
        if (predicate != nullptr) {
            // Lower the ON condition against the join's concatenated input
            // schema (left.output ++ right.output = join->output).
            join->predicate = lower_expr(predicate, join->output, error);
            if (!join->predicate) {
                return nullptr;
            }
        }
        return join;
    }

    // JOIN ... USING (cols) / NATURAL JOIN: the shared columns collapse to a
    // single merged output column. Keep the left copy and drop the right's
    // duplicate; the equality is materialized as the join predicate below.
    // USING names the columns explicitly; NATURAL uses every column common to
    // both inputs (by name, in left order, de-duplicated). A NATURAL join with
    // no common columns has an empty set - it degrades to a plain cross join,
    // exactly as SQL specifies.
    std::vector<std::string_view> merged;
    if (using_clause != nullptr) {
        for (const ASTNode* col = first_child(using_clause); col != nullptr;
             col = col->next_sibling) {
            merged.push_back(split_column_ref(col->primary_text).column);
        }
    } else {
        const auto count_by_name = [](const Schema& s, std::string_view name) {
            int n = 0;
            for (const auto& c : s) {
                if (c.name == name) ++n;
            }
            return n;
        };
        for (const auto& lc : left->output) {
            const int right_count = count_by_name(right->output, lc.name);
            if (right_count == 0) {
                continue;  // not a common column
            }
            bool already = false;
            for (const std::string_view m : merged) {
                if (m == lc.name) { already = true; break; }
            }
            if (already) {
                continue;
            }
            // A common column that occurs more than once on either side is
            // ambiguous - the equi-predicate would tie only the first slot and
            // leave the duplicate unconstrained, silently producing wrong rows.
            // SQL requires this to be an error.
            if (count_by_name(left->output, lc.name) > 1 || right_count > 1) {
                error = "common column '" + std::string{lc.name} +
                        "' in NATURAL JOIN is ambiguous";
                return nullptr;
            }
            merged.push_back(lc.name);
        }
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
    const bool null_left = jt == ast::JoinType::Right || jt == ast::JoinType::Full;
    const bool null_right = jt == ast::JoinType::Left || jt == ast::JoinType::Full;

    // A USING / NATURAL merged column is COALESCE(left.c, right.c). Keeping only
    // the left copy is value-correct exactly when the left side is never
    // null-supplied - INNER and LEFT joins. Under RIGHT / FULL the left copy is
    // NULL for rows with no left match, so a bare reference to the merged column
    // would wrongly read NULL: it must read the right copy (RIGHT) or the
    // COALESCE of both (FULL). For those we keep BOTH copies in the join frame
    // and add a Project that materializes the real COALESCE; INNER / LEFT keep
    // the compact left-copy output unchanged.
    const bool coalesce_merged =
        !merged.empty() &&
        (jt == ast::JoinType::Right || jt == ast::JoinType::Full);
    const auto left_width = static_cast<std::uint32_t>(left->output.size());

    Schema out;
    for (const auto& col : left->output) {
        ColumnSchema c = col;
        c.nullable = c.nullable || null_left;
        out.push_back(std::move(c));
    }
    for (const auto& col : right->output) {
        if (!coalesce_merged && is_merged(col.name)) {
            continue;  // INNER / LEFT: merged into the left copy
        }
        ColumnSchema c = col;
        c.nullable = c.nullable || null_right;
        out.push_back(std::move(c));
    }
    join->output = std::move(out);

    // Materialize the USING equality as the join predicate: for each shared
    // column, `left.col = right.col` over the pre-merge (left ++ right) frame.
    // Without this the join carries no condition and degrades to a cross product
    // (the output is merged, so it looked right while producing wrong rows). The
    // predicate indexes the full input frame; the merged output is narrower,
    // which the optimizer's non-full-concat guard already treats conservatively.
    ExprPtr pred;
    for (const std::string_view name : merged) {
        const int li = slot_by_name(left->output, name);
        const int ri = slot_by_name(right->output, name);
        if (li < 0 || ri < 0) {
            error = "USING column '" + std::string{name} +
                    "' is not present in both join inputs";
            return nullptr;
        }
        auto eq = std::make_unique<Expr>(ExprKind::BinaryOp);
        eq->bin_op = ast::BinaryOp::Equal;
        eq->type = ast::DataType::Boolean;
        eq->children.push_back(
            make_column_ref(static_cast<std::uint32_t>(li), left->output[li]));
        eq->children.push_back(make_column_ref(
            left_width + static_cast<std::uint32_t>(ri), right->output[ri]));
        if (!pred) {
            pred = std::move(eq);
        } else {
            auto conj = std::make_unique<Expr>(ExprKind::BinaryOp);
            conj->bin_op = ast::BinaryOp::And;
            conj->type = ast::DataType::Boolean;
            conj->children.push_back(std::move(pred));
            conj->children.push_back(std::move(eq));
            pred = std::move(conj);
        }
    }
    join->predicate = std::move(pred);

    if (!coalesce_merged) {
        join->add_child(std::move(left));
        join->add_child(std::move(right));
        return join;
    }

    // RIGHT / FULL USING/NATURAL: the join above emits the full left ++ right
    // frame; this Project collapses each merged pair to COALESCE(left.c, right.c)
    // and drops the duplicate right copy, reproducing the compact merged schema.
    // The merged column keeps the LEFT column's identity (table/column id, name)
    // so downstream references resolve exactly as they do for INNER / LEFT.
    auto project = make_node(LogicalOp::Project);
    Schema pout;
    std::vector<ExprPtr> pexprs;
    for (std::uint32_t i = 0; i < left_width; ++i) {
        const ColumnSchema& lc = join->output[i];  // null_left-adjusted
        if (!is_merged(lc.name)) {
            pexprs.push_back(make_column_ref(i, lc));
            pout.push_back(lc);
            continue;
        }
        const int ri = slot_by_name(right->output, lc.name);
        const ColumnSchema& rc =
            join->output[left_width + static_cast<std::uint32_t>(ri)];
        // Nullability of the merged key is driven by the side that is PRESENT in
        // a null-extended row, using the base (pre-join-null-supply) nullability:
        //   RIGHT: every emitted row has the right side, so it is the right key's
        //          base nullability (the left copy is only a NULL fill).
        //   FULL : either side may be the sole present one, so it is nullable if
        //          either base key is nullable.
        const bool merged_nullable =
            (jt == ast::JoinType::Full)
                ? (left->output[i].nullable ||
                   right->output[static_cast<std::size_t>(ri)].nullable)
                : right->output[static_cast<std::size_t>(ri)].nullable;
        auto coa = std::make_unique<Expr>(ExprKind::ScalarFunction);
        coa->func_name = "COALESCE";
        coa->type = lc.type;
        coa->nullability = merged_nullable ? std::uint8_t{2} : std::uint8_t{1};
        coa->children.push_back(make_column_ref(i, lc));
        coa->children.push_back(
            make_column_ref(left_width + static_cast<std::uint32_t>(ri), rc));
        ColumnSchema mc = left->output[i];  // left identity
        mc.nullable = merged_nullable;
        pexprs.push_back(std::move(coa));
        pout.push_back(std::move(mc));
    }
    for (std::uint32_t j = 0; j < static_cast<std::uint32_t>(right->output.size()); ++j) {
        const ColumnSchema& rc = join->output[left_width + j];
        if (is_merged(rc.name)) {
            continue;  // its coalesced value lives in the left section
        }
        pexprs.push_back(make_column_ref(left_width + j, rc));
        pout.push_back(rc);
    }
    project->output = std::move(pout);
    project->exprs = std::move(pexprs);

    join->add_child(std::move(left));
    join->add_child(std::move(right));
    project->add_child(std::move(join));
    return project;
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
                                     ast::JoinType::Cross);
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

    // --- Hoist a trailing ORDER BY / LIMIT off the last branch ------------
    // A trailing ORDER BY / LIMIT that follows a set operation scopes to the
    // WHOLE result. SQL forbids a set-op branch from carrying its own ORDER BY
    // (without parentheses), so any ORDER BY / LIMIT the grammar hangs on the
    // last branch belongs to the set operation - but the parser attaches it to
    // that last SelectStmt and bind_query bound it INSIDE the branch (a Sort
    // and/or Limit at the top of `right`). Peel those off, build the SetOp over
    // the branch core, and re-apply them ABOVE the SetOp (Sort directly above,
    // Limit above the Sort). The ORDER BY keys are re-lowered against the
    // reconciled set-op output so `ORDER BY <col>` binds to the set operation's
    // output column (not to a same-named base column of the last branch).
    //
    // Conservative: only the last branch, and only when it is a plain
    // SelectStmt whose bound form exposes a Sort / Limit at its very top. A
    // parenthesized subquery with its own interior ORDER BY binds as a derived
    // table and does not expose a top Sort / Limit here, so it is left alone.
    bool hoist_sort = false;
    bool hoist_limit = false;
    bool sl_has_limit = false, sl_has_offset = false;
    std::int64_t sl_limit = -1, sl_offset = 0;
    if (right_q->node_type == NodeType::SelectStmt) {
        // Peel the outermost Limit (Limit -> Sort -> core or Limit -> core).
        if (right->op == LogicalOp::Limit && right->child_count() == 1) {
            hoist_limit = true;
            sl_has_limit = right->has_limit;
            sl_limit = right->limit;
            sl_has_offset = right->has_offset;
            sl_offset = right->offset;
            right = std::move(right->children[0]);
        }
        // Peel the outermost Sort (now the top node, if present).
        if (right->op == LogicalOp::Sort && right->child_count() == 1) {
            hoist_sort = true;
            right = std::move(right->children[0]);
            // The branch's own Sort may have appended hidden sort-only columns
            // to the core Project; the set operation reconciles only the visible
            // columns, so drop the hidden ones to keep the branch's arity in
            // step with the set-op output. (Under DISTINCT no hidden columns are
            // ever added, so `right` is a plain Project here whenever there are
            // extra columns to drop.)
            const std::size_t n = node->output.size();
            if (right->op == LogicalOp::Project && right->output.size() > n) {
                right->output.resize(n);
                right->exprs.resize(n);
            }
        }
    }

    node->add_child(std::move(left));
    node->add_child(std::move(right));
    LogicalNodePtr result = std::move(node);

    // Re-apply the ORDER BY as a Sort above the SetOp, keyed on the reconciled
    // set-op output. Mirrors the ordinal / column / ASC-DESC / NULLS handling in
    // bind_select, minus the hidden-column path (an ORDER BY over a set op must
    // reference an output column).
    if (hoist_sort) {
        const ASTNode* order_by = find_child(right_q, NodeType::OrderByClause);
        if (order_by == nullptr) {
            error = "internal: hoisted set-op ORDER BY lost its clause";
            return nullptr;
        }
        auto sort = make_node(LogicalOp::Sort);
        const Schema& out = result->output;
        for (const ASTNode* key = first_child(order_by); key != nullptr;
             key = key->next_sibling) {
            SortKeyIR sk;
            sk.descending = (key->semantic_flags & (1u << 7)) != 0;
            sk.nulls_order_explicit = (key->semantic_flags & (1u << 5)) != 0;
            sk.nulls_first = (key->semantic_flags & (1u << 4)) != 0;

            std::int64_t ordinal = 0;
            if (key->node_type == NodeType::IntegerLiteral &&
                parse_int_literal(key, ordinal)) {
                if (ordinal < 1 ||
                    static_cast<std::size_t>(ordinal) > out.size()) {
                    error = "ORDER BY ordinal " + std::to_string(ordinal) +
                            " out of range";
                    return nullptr;
                }
                sk.expr = make_column_ref(static_cast<std::uint32_t>(ordinal - 1),
                                          out[static_cast<std::size_t>(ordinal - 1)]);
                sort->sort_keys.push_back(std::move(sk));
                continue;
            }

            // A trailing set-op ORDER BY resolves by the reconciled OUTPUT
            // column (SQL scopes it to the set operation, whose columns take
            // their names/positions from the first branch), NOT by the base
            // column the analyzer bound the key to inside the last branch. So a
            // bare `ORDER BY <name>` is matched by name against the set-op
            // output first; only if that misses do we fall back to lowering by
            // the analyzer's provenance (an expression, or a same-named column
            // whose ids happen to line up).
            if (key->node_type == NodeType::ColumnRef ||
                key->node_type == NodeType::Identifier) {
                const std::string_view name =
                    split_column_ref(key->primary_text).column;
                bool matched = false;
                for (std::size_t i = 0; i < out.size(); ++i) {
                    if (out[i].name == name) {
                        sk.expr = make_column_ref(static_cast<std::uint32_t>(i),
                                                  out[i]);
                        sort->sort_keys.push_back(std::move(sk));
                        matched = true;
                        break;
                    }
                }
                if (matched) {
                    continue;
                }
            }
            std::string local_error;
            auto e = lower_expr(key, out, local_error);
            if (!e) {
                error = "ORDER BY item must reference a set-operation output "
                        "column: " + local_error;
                return nullptr;
            }
            sk.expr = std::move(e);
            sort->sort_keys.push_back(std::move(sk));
        }
        sort->output = out;  // schema-preserving over the set-op output
        sort->add_child(std::move(result));
        result = std::move(sort);
    }

    // Re-apply the LIMIT above the Sort.
    if (hoist_limit) {
        auto lim = make_node(LogicalOp::Limit);
        lim->has_limit = sl_has_limit;
        lim->limit = sl_limit;
        lim->has_offset = sl_has_offset;
        lim->offset = sl_offset;
        lim->output = result->output;  // limit is schema-preserving
        lim->add_child(std::move(result));
        result = std::move(lim);
    }

    return result;
}

LogicalNodePtr Binder::bind_select(const ASTNode* select_stmt, std::string& error) {
    // This block's Aggregate frame is local; a scalar subquery in a select item
    // recurses into bind_select and would clobber `agg_frame_`. Save the
    // enclosing frame, run with none active (the aggregate payload below lowers
    // against pre-aggregation columns), and restore on every exit.
    struct FrameGuard {
        Binder* b;
        const AggregateFrame* prev;
        std::vector<std::pair<const ASTNode*, std::uint32_t>> prev_windows;
        ~FrameGuard() {
            b->agg_frame_ = prev;
            b->window_slots_ = std::move(prev_windows);
        }
    } frame_guard{this, agg_frame_, std::move(window_slots_)};
    agg_frame_ = nullptr;
    window_slots_.clear();

    // --- WITH: register this block's CTEs so a FROM reference can resolve them.
    // The bodies are bound lazily, once per reference, in bind_table_ref (so two
    // references to the same CTE get independent subplans). Registration is
    // scoped: restore the previous set on every exit so a nested block's CTEs do
    // not leak outward while enclosing CTEs stay visible inward.
    struct CteGuard {
        std::vector<std::pair<std::string, const ASTNode*>>* v;
        std::size_t mark;
        ~CteGuard() { v->resize(mark); }
    } cte_guard{&ctes_, ctes_.size()};
    if (const ASTNode* cte_clause = find_child(select_stmt, NodeType::CTEClause)) {
        for (const ASTNode* def = first_child(cte_clause); def != nullptr;
             def = def->next_sibling) {
            if (def->node_type != NodeType::CTEDefinition) {
                continue;
            }
            if (find_child(def, NodeType::SelectStmt) != nullptr) {
                ctes_.emplace_back(std::string{def->primary_text}, def);
            }
        }
    }

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
        const ASTNode* pred_ast = first_child(where);  // the predicate expression
        auto filter = make_node(LogicalOp::Filter);
        filter->output = current->output;   // filter is schema-preserving
        // Lower the predicate against the child's output (the filter's input).
        // Any IN / EXISTS / scalar subquery is folded inline into the owned
        // predicate expression (an ExprKind::Subquery owning its sub_plan), with
        // correlated references resolved against this input.
        filter->predicate = lower_expr(pred_ast, current->output, error);
        if (!filter->predicate) {
            return nullptr;
        }
        filter->add_child(std::move(current));
        current = std::move(filter);
    }

    // --- GROUP BY / aggregation -> Aggregate ---
    // An Aggregate node is emitted when the query groups (GROUP BY present) OR
    // when it uses any aggregate function without a GROUP BY - the "implicit
    // aggregation" case (`SELECT COUNT(*) FROM users`), which collapses the input
    // to a single group with EMPTY group keys. Aggregates are detected by walking
    // the SELECT list, the HAVING condition and the ORDER BY keys (not just the
    // top-level SELECT items), so aggregates nested in a larger expression
    // (`SUM(x)+1`) or appearing only in HAVING / ORDER BY are found too.
    const ASTNode* group_by = find_child(select_stmt, NodeType::GroupByClause);
    const ASTNode* select_list = find_child(select_stmt, NodeType::SelectList);
    const ASTNode* having = find_child(select_stmt, NodeType::HavingClause);
    const ASTNode* order_by = find_child(select_stmt, NodeType::OrderByClause);

    std::vector<const ASTNode*> aggregates;
    if (select_list != nullptr) {
        for (const ASTNode* item = first_child(select_list); item != nullptr;
             item = item->next_sibling) {
            collect_aggregates(item, aggregates);
        }
    }
    std::vector<const ASTNode*> having_aggs;
    if (having != nullptr) {
        collect_aggregates(first_child(having), having_aggs);
        aggregates.insert(aggregates.end(), having_aggs.begin(), having_aggs.end());
    }
    if (order_by != nullptr) {
        for (const ASTNode* key = first_child(order_by); key != nullptr;
             key = key->next_sibling) {
            collect_aggregates(key, aggregates);
        }
    }

    // The precomputed-column frame for the Project / HAVING / hidden ORDER BY
    // expressions above the Aggregate. Empty (and never enabled) when the query
    // does not aggregate; populated below in output order (group keys, then
    // aggregate results) so a producer's index equals its Aggregate output slot.
    AggregateFrame agg_frame;

    if (group_by != nullptr || !aggregates.empty()) {
        auto agg = make_node(LogicalOp::Aggregate);
        // Group keys and aggregate calls are lowered against the Aggregate's
        // input (its child's output), where their base-column references live.
        const Schema& agg_input = current->output;
        // The Aggregate output is the canonical shape an executor emits: one
        // column per group key (in GROUP BY order), then one column per aggregate
        // result, positional 1:1 with the group_keys / aggregates payloads. The
        // Project above reshapes this into the SELECT list (reordering, wrapping
        // `SUM(x)+1`, dropping keys) by resolving each item against `agg_frame`.
        //
        // Group keys: the GROUP BY expressions, or empty for implicit
        // aggregation. Keys are base-column references or expressions over the
        // input, which lower directly. (GROUP BY by output ordinal `GROUP BY 1`
        // or by select alias is rejected upstream by the analyzer, so it never
        // reaches a clean bind and is not resolved here.) A bare-column key
        // additionally carries its source (table_id, column_id) so an operator
        // above resolves it by id rather than only structurally.
        std::uint32_t slot = 0;
        for (const ASTNode* key = group_by != nullptr ? first_child(group_by) : nullptr;
             key != nullptr; key = key->next_sibling) {
            auto e = lower_expr(key, agg_input, error);
            if (!e) {
                return nullptr;
            }
            ColumnSchema col;
            col.name = item_output_name(key);
            col.type = analyzer_.type_of(key);
            col.nullable = analyzer_.nullability_of(key) != 1;
            if (key->node_type == NodeType::ColumnRef ||
                key->node_type == NodeType::Identifier) {
                col.table_id = key->context.analysis.table_id;
                col.column_id = key->context.analysis.column_id;
            }
            agg->output.push_back(std::move(col));
            agg->group_keys.push_back(std::move(e));
            agg_frame.producers.emplace_back(key, slot);
            ++slot;
        }
        // Aggregate results: one column per DISTINCT aggregate call collected
        // across SELECT + HAVING + ORDER BY. The same aggregate appearing in more
        // than one clause (`SELECT COUNT(*) ... HAVING COUNT(*)`) is a separate
        // AST node each time; dedup it to a single result column - a
        // structurally-equal producer already registered covers every occurrence,
        // since the frame routes each by structure to that one slot.
        for (const ASTNode* call : aggregates) {
            bool duplicate = false;
            for (const auto& [producer, existing] : agg_frame.producers) {
                if (same_producer_expr(call, producer)) {
                    duplicate = true;
                    break;
                }
            }
            if (duplicate) {
                continue;
            }
            auto e = lower_expr(call, agg_input, error);
            if (!e) {
                return nullptr;
            }
            ColumnSchema col;
            col.name = item_output_name(call);
            col.type = analyzer_.type_of(call);
            col.nullable = analyzer_.nullability_of(call) != 1;
            agg->output.push_back(std::move(col));
            agg->aggregates.push_back(std::move(e));
            agg_frame.producers.emplace_back(call, slot);
            ++slot;
        }
        agg->add_child(std::move(current));
        current = std::move(agg);

        // --- HAVING -> Filter (post-aggregation predicate, above the Aggregate) ---
        if (having != nullptr) {
            const ASTNode* pred_ast = first_child(having);  // the HAVING condition
            auto filter = make_node(LogicalOp::Filter);
            filter->output = current->output;   // schema-preserving
            // Lower against the aggregate's output (the HAVING filter's input)
            // with the frame active, so `HAVING SUM(x) > 10` resolves SUM(x) to
            // its precomputed column; any embedded subquery folds inline.
            agg_frame_ = &agg_frame;
            filter->predicate = lower_expr(pred_ast, current->output, error);
            agg_frame_ = nullptr;
            if (!filter->predicate) {
                return nullptr;
            }
            filter->add_child(std::move(current));
            current = std::move(filter);
        }
    }

    // --- Window functions -> Window (below Project) ---
    // Window functions are evaluated after WHERE / GROUP BY but before the final
    // projection. Collect the SELECT-list items that are window calls; if any,
    // insert a Window node that carries them and appends one output column per
    // function (its type / nullability read back from the analyzer) to the
    // input schema. The Project above then references those outputs.
    if (select_list != nullptr) {
        // Collect every window call reachable in the select list - not only a
        // select item that IS a whole window call, but also one nested inside a
        // larger expression (`ROW_NUMBER() OVER (...) + 1`). Each distinct call
        // gets its own Window output column; the Project above references it by
        // node identity (via window_slots_), so two same-named calls do not
        // collide on the "SUM" / "ROW_NUMBER" output name.
        std::vector<const ASTNode*> window_fns;
        for (const ASTNode* item = first_child(select_list); item != nullptr;
             item = item->next_sibling) {
            collect_windows(item, window_fns);
        }
        if (!window_fns.empty()) {
            auto window = make_node(LogicalOp::Window);
            // Window functions lower against the node's input (the child's
            // output, before the window result columns are appended), where
            // their arguments and PARTITION BY / ORDER BY references live.
            const Schema& win_input = current->output;
            window->output = current->output;  // input columns pass through
            const auto base_width = static_cast<std::uint32_t>(window->output.size());
            for (const ASTNode* fn : window_fns) {
                auto e = lower_expr(fn, win_input, error);
                if (!e) {
                    return nullptr;
                }
                // Record this call's exact output slot so the Project references
                // the right column - not the first same-named window output.
                window_slots_.emplace_back(
                    fn, base_width + static_cast<std::uint32_t>(
                                        window->window_functions.size()));
                window->window_functions.push_back(std::move(e));
                ColumnSchema col;
                col.name = item_output_name(fn);
                col.type = analyzer_.type_of(fn);
                col.nullable = analyzer_.nullability_of(fn) != 1;
                window->output.push_back(std::move(col));
            }
            window->add_child(std::move(current));
            current = std::move(window);
        }
    }

    // --- SELECT list -> Project (authoritative output schema) ---
    // A bare, unqualified `SELECT *` projects exactly the child's output columns.
    // Over a USING / NATURAL join the child output is the merged frame (the join
    // column coalesced to one), which the analyzer's projection does not model -
    // it lists the un-merged columns and so disagrees on arity with the star
    // expansion. Trust the child schema for that case (it is what `*` covers, and
    // equals the analyzer's projection for every non-merged input).
    // A Star node stores its qualifier in schema_name / catalog_name (its
    // primary_text is just "*"), so a qualified `t.*` must be excluded by those
    // fields - it is NOT a whole-child star and keeps using the analyzer's
    // projection (which correctly covers only t's columns; a qualified star over
    // a join still hits the not-yet-lowered arity guard rather than binding to
    // the full frame).
    const ASTNode* only_item =
        select_list != nullptr ? first_child(select_list) : nullptr;
    const bool bare_star =
        only_item != nullptr && only_item->next_sibling == nullptr &&
        only_item->node_type == NodeType::Star &&
        only_item->schema_name.empty() && only_item->catalog_name.empty();

    auto project = make_node(LogicalOp::Project);
    if (bare_star) {
        project->output = current->output;
    } else if (const auto* proj = analyzer_.projection_of(select_stmt)) {
        project->output.reserve(proj->size());
        for (const auto& c : *proj) {
            project->output.push_back(to_schema(c));
        }
    } else {
        error = "analyzer produced no projection for this SELECT";
        return nullptr;
    }
    if (select_list != nullptr) {
        // Lower the SELECT list into owned, typed projected expressions. Over an
        // Aggregate the frame resolves each item's group keys / aggregate calls
        // (including wrapped ones, `SUM(x)+1`) to precomputed columns. A scalar
        // subquery embedded in an item folds inline into that item's owned Expr
        // (an ExprKind::Subquery owning its sub_plan), with correlated references
        // resolved against the Project's input (the child's output).
        agg_frame_ = &agg_frame;
        const bool projected = lower_projection(select_list, current.get(),
                                                project->exprs, error);
        agg_frame_ = nullptr;
        if (!projected) {
            return nullptr;
        }
        // Invariant: exactly one projected expression per output column. A
        // divergence means star expansion disagreed with the analyzer's
        // projection; fail loudly rather than emit an inconsistent Project.
        if (project->exprs.size() != project->output.size()) {
            error = "projection arity (" + std::to_string(project->exprs.size()) +
                    ") does not match the analyzer's output (" +
                    std::to_string(project->output.size()) + ")";
            return nullptr;
        }
    }
    project->add_child(std::move(current));
    current = std::move(project);

    // --- SELECT DISTINCT -> Distinct (de-duplicate the projected rows) ---
    // The parser records DISTINCT as bit 0 (NodeFlags::Distinct) of the
    // SelectStmt's semantic_flags. Model it as a dedicated schema-preserving
    // Distinct node sitting directly above the Project, so ORDER BY / LIMIT apply
    // to the de-duplicated result.
    const bool distinct =
        (select_stmt->semantic_flags &
         static_cast<std::uint16_t>(ast::NodeFlags::Distinct)) != 0;
    if (distinct) {
        auto dnode = make_node(LogicalOp::Distinct);
        dnode->output = current->output;  // distinct is schema-preserving
        dnode->add_child(std::move(current));
        current = std::move(dnode);
    }

    // --- ORDER BY -> Sort (real sort keys + directions) ---
    if (order_by != nullptr) {
        auto sort = make_node(LogicalOp::Sort);
        LogicalNode* input_node = current.get();  // the Project or Distinct below
        const bool over_distinct = input_node->op == LogicalOp::Distinct;
        // The Sort's visible output is its input's current output (the projected,
        // possibly de-duplicated columns), captured before any hidden sort-only
        // columns are appended below.
        const Schema visible = input_node->output;
        // A non-DISTINCT query may ORDER BY an expression that is not a selected
        // output column (e.g. `SELECT id ... ORDER BY name`). Such a key is
        // computed as a HIDDEN sort-only column appended to the Project (lowered
        // against the Project's input); the Sort orders by it and then drops it
        // from its output. Under DISTINCT this is illegal - SQL requires ORDER BY
        // items to appear in the select list - so it is rejected rather than
        // adding a column below the Distinct (which would change de-duplication).
        LogicalNode* project = over_distinct ? nullptr : input_node;
        const Schema* proj_input =
            (project != nullptr && project->child_count() > 0)
                ? &project->child(0)->output
                : nullptr;

        // The parser records ASC/DESC and NULLS placement in each key's
        // semantic_flags (bit 7 = DESC, bit 5 = NULLS ordering explicit, bit 4 =
        // NULLS FIRST).
        for (const ASTNode* key = first_child(order_by); key != nullptr;
             key = key->next_sibling) {
            SortKeyIR sk;
            sk.descending = (key->semantic_flags & (1u << 7)) != 0;
            sk.nulls_order_explicit = (key->semantic_flags & (1u << 5)) != 0;
            sk.nulls_first = (key->semantic_flags & (1u << 4)) != 0;

            std::int64_t ordinal = 0;
            if (key->node_type == NodeType::IntegerLiteral &&
                parse_int_literal(key, ordinal)) {
                // ORDER BY <ordinal>: the N-th visible output column.
                if (ordinal < 1 ||
                    static_cast<std::size_t>(ordinal) > visible.size()) {
                    error = "ORDER BY ordinal " + std::to_string(ordinal) + " out of range";
                    return nullptr;
                }
                sk.expr = make_column_ref(static_cast<std::uint32_t>(ordinal - 1),
                                          visible[static_cast<std::size_t>(ordinal - 1)]);
                sort->sort_keys.push_back(std::move(sk));
                continue;
            }

            // Resolve against the input's current output (a selected column, an
            // output alias, or a prior hidden sort column already appended).
            std::string local_error;
            if (auto e = lower_expr(key, input_node->output, local_error)) {
                sk.expr = std::move(e);
                sort->sort_keys.push_back(std::move(sk));
                continue;
            }
            // Not a visible output column: append a hidden sort column (or reject
            // under DISTINCT).
            if (over_distinct || proj_input == nullptr) {
                error = "ORDER BY item must appear in the SELECT list (DISTINCT): " +
                        local_error;
                return nullptr;
            }
            // Lower against the Project's input (the Aggregate / HAVING-filter
            // output) with the frame active, so an ORDER-BY-only aggregate such
            // as `ORDER BY SUM(sal)` resolves to its precomputed column. The
            // visible attempt above deliberately runs without the frame - it
            // targets the Project output, a different (narrower) frame.
            agg_frame_ = &agg_frame;
            auto hidden = lower_expr(key, *proj_input, error);
            agg_frame_ = nullptr;
            if (!hidden) {
                return nullptr;
            }
            ColumnSchema hcol;
            hcol.name = item_output_name(key);
            hcol.type = hidden->type;
            hcol.nullable = hidden->nullability != 1;
            // Carry the source column's provenance (a plain base-column key) so a
            // repeated ORDER BY of the same column resolves against this hidden
            // slot by id next time instead of appending a duplicate.
            hcol.table_id = hidden->ref_table_id;
            hcol.column_id = hidden->ref_column_id;
            project->output.push_back(hcol);
            project->exprs.push_back(std::move(hidden));
            sk.expr = make_column_ref(
                static_cast<std::uint32_t>(project->output.size() - 1),
                project->output.back());
            sort->sort_keys.push_back(std::move(sk));
        }
        sort->output = visible;  // the Sort drops any hidden sort columns
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
        // VALUES rows are constant expressions with no column references, so
        // they lower against an empty input schema.
        const Schema no_input;
        for (const ASTNode* row = first_child(values); row != nullptr;
             row = row->next_sibling) {
            std::vector<ExprPtr> vals;
            for (const ASTNode* v = first_child(row); v != nullptr; v = v->next_sibling) {
                auto e = lower_expr(v, no_input, error);
                if (!e) {
                    return nullptr;
                }
                vals.push_back(std::move(e));
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
            // INSERT ... DEFAULT VALUES: a single all-defaults row. Represent it
            // as a one-empty-row Values source (the same synthetic single row a
            // FROM-less SELECT uses) rather than erroring as it did before.
            if (find_child(insert_stmt, NodeType::DefaultClause) != nullptr) {
                auto vnode = make_node(LogicalOp::Values);
                vnode->value_rows.emplace_back();  // one empty row
                node->add_child(std::move(vnode));
            } else {
                error = "INSERT has neither VALUES nor a query source";
                return nullptr;
            }
        } else {
            auto src = bind_query(source, error);
            if (!src) {
                return nullptr;
            }
            node->add_child(std::move(src));
        }
    }

    // ON CONFLICT: record the conflict target and the action so the plan
    // faithfully represents the upsert instead of dropping it (previously the
    // clause was parsed and silently discarded, lowering an upsert as a plain
    // INSERT). DO UPDATE's SET assignments lower against the target table's
    // schema and reuse `assignments`.
    if (const ASTNode* oc = find_child(insert_stmt, NodeType::OnConflictClause)) {
        for (const ASTNode* c = first_child(oc); c != nullptr; c = c->next_sibling) {
            if (c->node_type == NodeType::Identifier) {
                node->conflict_columns.push_back(
                    std::string{split_column_ref(c->primary_text).column});
            }
        }
        const TableInfo* target = catalog_.find_table(node->table_name);
        if ((oc->semantic_flags & 0x02) != 0) {  // DO UPDATE SET ...
            node->conflict_action = ConflictAction::DoUpdate;
            Schema tschema;
            if (target != nullptr) {
                tschema = scan_schema(*target, target->table_id, node->table_name);
            }
            if (const ASTNode* set_clause = find_child(oc, NodeType::SetClause)) {
                for (const ASTNode* asgn = first_child(set_clause); asgn != nullptr;
                     asgn = asgn->next_sibling) {
                    Assignment assignment;
                    const std::string_view col = split_column_ref(asgn->primary_text).column;
                    if (target != nullptr) {
                        if (const auto* ci = target->find_column(col)) {
                            assignment.target_column_id = ci->column_id;
                        }
                    }
                    assignment.value = lower_expr(first_child(asgn), tschema, error);
                    if (!assignment.value) {
                        return nullptr;
                    }
                    node->assignments.push_back(std::move(assignment));
                }
            }
        } else {  // DO NOTHING (0x01)
            node->conflict_action = ConflictAction::DoNothing;
        }
    }
    return wrap_returning(std::move(node), insert_stmt, error);
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
    // UPDATE ... FROM extra_relations: cross-join the extra relations under the
    // target so the WHERE predicate and SET values (lowered against child->output
    // below) can reference them. The WHERE supplies the join condition.
    if (const ASTNode* from = find_child(update_stmt, NodeType::FromClause)) {
        auto extra = bind_from(from, error);
        if (!extra) {
            return nullptr;
        }
        child = make_join_node(std::move(child), std::move(extra), ast::JoinType::Cross);
    }
    if (const ASTNode* where = find_child(update_stmt, NodeType::WhereClause)) {
        const ASTNode* pred_ast = first_child(where);
        auto filter = make_node(LogicalOp::Filter);
        filter->output = child->output;
        filter->predicate = lower_expr(pred_ast, child->output, error);
        if (!filter->predicate) {
            return nullptr;
        }
        filter->add_child(std::move(child));
        child = std::move(filter);
    }

    auto node = make_node(LogicalOp::Update);
    node->table_name = std::string{table_ref->primary_text};
    // SET assignments: each a BinaryExpr whose primary_text is the target column
    // and whose first child is the value expression. Lower to an owned
    // Assignment{target column id, value}; the value lowers against the rows
    // being updated (child->output), so `SET x = x + 1` resolves the read of x.
    const TableInfo* target = catalog_.find_table(node->table_name);
    if (const ASTNode* set_clause = find_child(update_stmt, NodeType::SetClause)) {
        for (const ASTNode* asgn = first_child(set_clause); asgn != nullptr;
             asgn = asgn->next_sibling) {
            Assignment assignment;
            const std::string_view col = split_column_ref(asgn->primary_text).column;
            if (target != nullptr) {
                if (const auto* ci = target->find_column(col)) {
                    assignment.target_column_id = ci->column_id;
                }
            }
            assignment.value = lower_expr(first_child(asgn), child->output, error);
            if (!assignment.value) {
                return nullptr;
            }
            node->assignments.push_back(std::move(assignment));
        }
    }
    node->add_child(std::move(child));
    return wrap_returning(std::move(node), update_stmt, error);
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
    // DELETE ... USING extra_relations: cross-join the USING relations under the
    // target so the WHERE predicate can join against them (bind_from builds a
    // cross-join chain over the clause's TableRef children).
    if (const ASTNode* using_clause = find_child(delete_stmt, NodeType::UsingClause)) {
        auto extra = bind_from(using_clause, error);
        if (!extra) {
            return nullptr;
        }
        child = make_join_node(std::move(child), std::move(extra), ast::JoinType::Cross);
    }
    if (const ASTNode* where = find_child(delete_stmt, NodeType::WhereClause)) {
        const ASTNode* pred_ast = first_child(where);
        auto filter = make_node(LogicalOp::Filter);
        filter->output = child->output;
        filter->predicate = lower_expr(pred_ast, child->output, error);
        if (!filter->predicate) {
            return nullptr;
        }
        filter->add_child(std::move(child));
        child = std::move(filter);
    }

    auto node = make_node(LogicalOp::Delete);
    node->table_name = std::string{table_ref->primary_text};
    node->add_child(std::move(child));
    return wrap_returning(std::move(node), delete_stmt, error);
}

// ---------------------------------------------------------------------------
// RETURNING (INSERT / UPDATE / DELETE ... RETURNING ...).
//
// The parser emits a ReturningClause whose children are the returned items
// (ColumnRef / Star / expressions). The analyzer does not type these items, so
// the output schema is resolved here against the target table's catalog columns
// (a Star expands to every column; a bare column reference picks up that
// column's type / nullability / ids; anything else is left Unknown-typed).
//
// NOTE: the build of the parser we consume drops the RETURNING clause for
// INSERT (it emits no ReturningClause node), so only UPDATE / DELETE RETURNING
// are represented end-to-end today. INSERT RETURNING is handled here too and
// will light up automatically once the parser preserves it. TODO(parser).
// ---------------------------------------------------------------------------
LogicalNodePtr Binder::wrap_returning(LogicalNodePtr dml, const ASTNode* stmt,
                                      std::string& error) {
    const ASTNode* returning = find_child(stmt, NodeType::ReturningClause);
    if (returning == nullptr) {
        return dml;  // no RETURNING: the DML node is the whole plan
    }
    const TableInfo* table = catalog_.find_table(dml->table_name);
    if (table == nullptr) {
        error = "RETURNING on unresolved table '" + dml->table_name + "'";
        return nullptr;
    }

    auto node = make_node(LogicalOp::Returning);
    node->table_name = dml->table_name;
    // The RETURNING items are evaluated over the target table's rows; resolve
    // them (and expand `*`) positionally against that table's schema so the
    // owned exprs stay 1:1 with `output`.
    const Schema target = scan_schema(*table, table->table_id, dml->table_name);
    for (const ASTNode* item = first_child(returning); item != nullptr;
         item = item->next_sibling) {
        if (item->node_type == NodeType::Star) {
            // RETURNING * -> every column of the target table, in order.
            for (std::size_t s = 0; s < target.size(); ++s) {
                node->output.push_back(target[s]);
                node->exprs.push_back(make_column_ref(static_cast<std::uint32_t>(s), target[s]));
            }
            continue;
        }
        ColumnSchema col;
        col.name = item_output_name(item);
        ExprPtr expr;
        if (item->node_type == NodeType::ColumnRef ||
            item->node_type == NodeType::Identifier) {
            const std::string_view cname = split_column_ref(item->primary_text).column;
            const int slot = slot_by_name(target, cname);
            if (slot >= 0) {
                col.type = target[slot].type;
                col.nullable = target[slot].nullable;
                col.table_id = target[slot].table_id;
                col.column_id = target[slot].column_id;
                expr = make_column_ref(static_cast<std::uint32_t>(slot), target[slot]);
            }
        }
        if (!expr) {
            // A non-column RETURNING item (an expression over the target row):
            // lower it as a fresh expression against the target schema.
            expr = lower_expr(item, target, error);
            if (!expr) {
                return nullptr;
            }
        }
        node->exprs.push_back(std::move(expr));
        node->output.push_back(std::move(col));
    }
    node->add_child(std::move(dml));
    return node;
}

// ---------------------------------------------------------------------------
// Projection lowering (SELECT list -> owned, typed expressions).
//
// One owned Expr per output column. A `*` expands to one positional ColumnRef
// per covered child column. Over an Aggregate, a group key or aggregate call
// (bare or wrapped, `SUM(x)+1`) resolves through the active frame (in lower_expr)
// to a ColumnRef into the precomputed output; a projected window item that a
// child Window already computed becomes a ColumnRef into that child column (the
// by-name producer map) rather than a re-evaluated expression tree.
// ---------------------------------------------------------------------------
ExprPtr Binder::lower_projection_item(const ASTNode* item, const Schema& input,
                                      std::string& error) {
    // A precomputed window output: reference the child column by its output name
    // instead of re-evaluating it (re-lowering would reach for arguments the
    // child no longer exposes). Aggregate calls are NOT matched by name here -
    // a call name is not unique (SUM(x) / SUM(y) share "SUM") - they resolve
    // structurally through the Aggregate frame inside lower_expr below.
    if (is_window_call(item)) {
        // Match this exact call to the slot the Window node computed for it (by
        // node identity), so two un-aliased same-named window calls resolve to
        // their own columns instead of both hitting the first "SUM".
        for (const auto& [node, slot] : window_slots_) {
            if (node == item) {
                return make_column_ref(slot, input[slot]);
            }
        }
        const int slot = slot_by_name(input, item_output_name(item));
        if (slot >= 0) {
            return make_column_ref(static_cast<std::uint32_t>(slot), input[slot]);
        }
        return lower_expr(item, input, error);
    }
    // A plain column passthrough: resolve by (table_id, column_id) first so
    // same-named columns from different inputs stay distinct (over an Aggregate
    // a group-key column also matches structurally through the frame), then fall
    // back to the output name for a producer whose ids were not carried through.
    if (item->node_type == NodeType::ColumnRef || item->node_type == NodeType::Identifier) {
        std::string local_error;
        if (auto e = lower_expr(item, input, local_error)) {
            return e;
        }
        const int slot = slot_by_name(input, item_output_name(item));
        if (slot >= 0) {
            return make_column_ref(static_cast<std::uint32_t>(slot), input[slot]);
        }
        error = std::move(local_error);
        return nullptr;
    }
    // Otherwise a fresh scalar expression over the child's output.
    return lower_expr(item, input, error);
}

bool Binder::lower_projection(const ASTNode* select_list, const LogicalNode* child,
                              std::vector<ExprPtr>& out, std::string& error) {
    const Schema& input = child->output;
    for (const ASTNode* item = first_child(select_list); item != nullptr;
         item = item->next_sibling) {
        if (item->node_type == NodeType::Star) {
            // Only an unqualified whole-child `*` is supported: expand to one
            // positional ColumnRef per child output column. A qualified `t.*`
            // covers a subset and needs table-scoped expansion (TODO); fail
            // loudly rather than emit a wrong-arity projection.
            const std::string_view qual = split_column_ref(item->primary_text).qualifier;
            if (!qual.empty()) {
                error = "qualified '" + std::string{qual} + ".*' projection not yet lowered";
                return false;
            }
            for (std::size_t s = 0; s < input.size(); ++s) {
                out.push_back(make_column_ref(static_cast<std::uint32_t>(s), input[s]));
            }
            continue;
        }
        auto e = lower_projection_item(item, input, error);
        if (!e) {
            return false;
        }
        out.push_back(std::move(e));
    }
    return true;
}

}  // namespace db25::plan
