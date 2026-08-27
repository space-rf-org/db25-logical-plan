// DB25 Logical Plan - Binder implementation
//
// See include/db25/plan/binder.hpp for the contract and pipeline shape.

#include "db25/plan/binder.hpp"

#include "db25/ast/ast_node.hpp"
#include "db25/ast/node_types.hpp"
#include "db25/plan/identifier.hpp"       // iequals: case-insensitive name matching
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

// Reconcile a VALUES column's type across two rows, matching the analyzer's
// coerce(UnionReconcile) rule (a multi-row VALUES is a UNION ALL of its rows, so
// each column's type folds across every row). Kept in lock-step with the
// analyzer's columns_from_values / promote_numeric; the cross-check test
// test_values_column_types_match_analyzer fails if the two ever diverge.
DataType reconcile_value_type(DataType a, DataType b) {
    if (a == b) {
        return a;
    }
    const auto is_wildcard = [](DataType t) {
        return t == DataType::Null || t == DataType::Unknown || t == DataType::Any;
    };
    if (is_wildcard(a)) return b;
    if (is_wildcard(b)) return a;
    const auto numeric_rank = [](DataType t) -> int {
        switch (t) {
            case DataType::TinyInt: return 1;
            case DataType::SmallInt: return 2;
            case DataType::Integer: return 3;
            case DataType::BigInt: return 4;
            case DataType::Decimal: return 5;
            case DataType::Real: return 6;
            case DataType::Double: return 7;
            default: return 0;  // not numeric
        }
    };
    if (numeric_rank(a) > 0 && numeric_rank(b) > 0) {
        return numeric_rank(a) >= numeric_rank(b) ? a : b;  // wider numeric wins
    }
    const auto is_string = [](DataType t) {
        return t == DataType::Char || t == DataType::VarChar || t == DataType::Text;
    };
    if (is_string(a) && is_string(b)) {
        return DataType::Text;  // char / varchar / text collapse to text
    }
    return DataType::Unknown;  // incompatible (the analyzer emits the diagnostic)
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

// True if `node`'s subtree contains a table reference named `name` (identifiers
// fold case). A `WITH RECURSIVE` CTE is only actually recursive if its recursive
// term references the CTE; this decides whether to lower to a RecursiveCTE node
// or expand the CTE inline. It is an over-approximation used only for that
// decision - the self-reference itself is resolved in bind_table_ref.
bool subtree_references_cte(const ASTNode* node, std::string_view name) {
    if (node == nullptr) {
        return false;
    }
    if (node->node_type == NodeType::TableRef &&
        iequals(node->primary_text, name)) {
        return true;
    }
    for (const ASTNode* c = first_child(node); c != nullptr;
         c = c->next_sibling) {
        if (subtree_references_cte(c, name)) {
            return true;
        }
    }
    return false;
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

// Aggregate-function recognizer. The name set MUST match the analyzer's
// kAggregateNames (and expr_lower.cpp's is_aggregate_name) exactly - the
// analyzer is the authority that validated the bare-column / GROUP BY discipline
// against this set, so any divergence lowers a real aggregate as a per-row
// scalar (silently wrong) or builds an Aggregate the analyzer never grouped for
// (a legal query fails to bind).
bool is_aggregate_call(const ASTNode* n) {
    if (n == nullptr) {
        return false;
    }
    if (n->node_type != NodeType::FunctionCall &&
        n->node_type != NodeType::FunctionExpr) {
        return false;
    }
    const std::string name = upper(n->primary_text);
    return
        // Core SQL aggregates.
        name == "COUNT" || name == "SUM" || name == "AVG" || name == "MIN" ||
        name == "MAX" ||
        // Statistical aggregates.
        name == "STDDEV" || name == "STDDEV_POP" || name == "STDDEV_SAMP" ||
        name == "VARIANCE" || name == "VAR_POP" || name == "VAR_SAMP" ||
        // Collection / boolean aggregates.
        name == "STRING_AGG" || name == "ARRAY_AGG" || name == "BOOL_AND" ||
        name == "BOOL_OR";
}

// A window-function call: a FunctionCall / FunctionExpr that carries a WindowSpec
// child (the OVER (...) specification). Declared here so aggregate detection can
// exclude it (SUM(..) OVER (...) is a window function, not a grouping aggregate).
bool is_window_call(const ASTNode* n);

// Walk an expression subtree collecting aggregate call nodes into `out`. Unlike
// the top-level `is_aggregate_call` check this finds aggregates nested inside a
// larger expression (e.g. `SUM(x) + 1`) and aggregates that appear only in
// HAVING / ORDER BY. It does not descend into an embedded Subquery (which owns
// its own aggregates), nor into an aggregate's own arguments (SQL forbids nesting
// one aggregate inside another).
//
// A window call is NOT itself a grouping aggregate (it is handled by the Window
// node), but grouping aggregates can appear INSIDE it and must still be gathered
// so the Aggregate node precomputes them:
//   - in its OVER clause: `RANK() OVER (ORDER BY SUM(sal))` / `... PARTITION BY MAX(x)`
//   - in its arguments:   `SUM(SUM(sal)) OVER (...)` (a window aggregate of a group aggregate)
// So on a window call we skip recording the call but DO descend into its children.
// (A plain window aggregate over raw columns - `SUM(sal) OVER (PARTITION BY dept)`
// - contributes nothing, since neither its arg `sal` nor `dept` is an aggregate.)
void collect_aggregates(const ASTNode* n, std::vector<const ASTNode*>& out) {
    if (n == nullptr || n->node_type == NodeType::Subquery) {
        return;
    }
    if (is_window_call(n)) {
        for (const ASTNode* c = first_child(n); c != nullptr; c = c->next_sibling) {
            collect_aggregates(c, out);
        }
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

// True if a LOWERED expression tree contains a raw Aggregate node - a freshly
// computed aggregate, as opposed to a ColumnRef routed to a precomputed
// Aggregate output slot. Above the Aggregate node (in a Project / Sort) an
// aggregate must always be the precomputed value; a raw one here would
// re-aggregate the already-grouped rows. Does not cross into an owned Subquery
// (its aggregates belong to its own plan).
bool contains_raw_aggregate(const ExprPtr& e) {
    if (!e) {
        return false;
    }
    if (e->kind == ExprKind::Aggregate) {
        return true;
    }
    if (e->kind == ExprKind::Subquery) {
        return false;
    }
    for (const auto& c : e->children) {
        if (contains_raw_aggregate(c)) {
            return true;
        }
    }
    return false;
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

// A GROUP BY key may name a SELECT-list output alias (a PostgreSQL extension the
// analyzer accepts): `SELECT dept AS d ... GROUP BY d` groups by dept. If `key`
// is an unqualified column reference that matches a projected item's output name,
// return that item - its expression is the real grouping target. Only consulted
// after the key fails to resolve as an input column, so input-column precedence
// (the analyzer's rule) is preserved.
const ASTNode* group_key_alias_target(const ASTNode* key, const ASTNode* select_list) {
    if (key == nullptr || select_list == nullptr) {
        return nullptr;
    }
    if (key->node_type != NodeType::ColumnRef && key->node_type != NodeType::Identifier) {
        return nullptr;
    }
    const auto qref = split_column_ref(key->primary_text);
    if (!qref.qualifier.empty()) {
        return nullptr;  // a qualified `t.c` is a base column, never an alias
    }
    for (const ASTNode* item = first_child(select_list); item != nullptr;
         item = item->next_sibling) {
        if (item->node_type == NodeType::Star) {
            continue;
        }
        if (iequals(item_output_name(item), qref.column)) {
            return item;
        }
    }
    return nullptr;
}

// Positional GROUP BY: `GROUP BY <n>` groups by the n-th (1-based) SELECT output
// column's expression - standard SQL (Postgres / MySQL / SQLite / DuckDB), which
// the analyzer accepts and validates. Return that SELECT item so its expression
// is lowered as the grouping key (mirroring group_key_alias_target); the integer
// literal itself must NOT be lowered as a constant single-group key. Out of range
// or a `*` before the ordinal -> nullptr (leave the existing handling).
const ASTNode* group_key_ordinal_target(const ASTNode* key, const ASTNode* select_list) {
    if (key == nullptr || select_list == nullptr ||
        key->node_type != NodeType::IntegerLiteral || key->primary_text.empty()) {
        return nullptr;
    }
    std::size_t ordinal = 0;
    for (const char c : key->primary_text) {
        if (c < '0' || c > '9') {
            return nullptr;  // not a plain non-negative integer (e.g. hex / sign)
        }
        ordinal = ordinal * 10 + static_cast<std::size_t>(c - '0');
    }
    if (ordinal < 1) {
        return nullptr;
    }
    std::size_t i = 1;
    for (const ASTNode* item = first_child(select_list); item != nullptr;
         item = item->next_sibling, ++i) {
        if (item->node_type == NodeType::Star) {
            return nullptr;  // ordinal into an unexpanded `*`: out of scope
        }
        if (i == ordinal) {
            return item;
        }
    }
    return nullptr;  // out of range
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
        if (iequals(s[i].name, name)) {  // computed columns resolve by name, case-insensitively
            return static_cast<int>(i);
        }
    }
    return -1;
}

}  // namespace

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
        if (iequals(it->name, name)) {  // CTE names are identifiers: fold case
            const ASTNode* def = it->def;
            // A reference to a recursive CTE whose RECURSIVE TERM is currently
            // being bound is the recursive self-reference: it reads the working
            // table (the previous iteration's rows), so bind a WorkingTableScan
            // carrying the CTE's columns rather than re-expanding the body.
            for (auto rit = recursive_working_.rbegin();
                 rit != recursive_working_.rend(); ++rit) {
                if (rit->def == def) {
                    auto ws = make_node(LogicalOp::WorkingTableScan);
                    ws->table_name = rit->name;
                    const std::string_view a = alias_of(table_ref);
                    ws->alias = a.empty() ? rit->name : std::string{a};
                    ws->output = rit->schema;  // the CTE columns (ids preserved)
                    // Stamp the reference name so a qualified `r.col` (and a
                    // self-join of the working table) stays distinguishable, just
                    // like a base-table Scan.
                    for (auto& c : ws->output) c.alias = ws->alias;
                    return ws;
                }
            }
            // Refuse to re-expand a CTE that is already being expanded higher up:
            // a reference to it inside its own body would recurse without bound
            // and overflow the stack. For a recursive CTE this is a self-reference
            // in the ANCHOR term (illegal SQL); for a plain CTE it is direct or
            // mutual recursion, which we do not support. Reject gracefully.
            for (const ASTNode* active : cte_expanding_) {
                if (active == def) {
                    error = it->recursive
                        ? "recursive CTE '" + std::string{name} +
                              "': self-reference is only allowed in the recursive term"
                        : "recursive CTE '" + std::string{name} +
                              "' is not supported";
                    return nullptr;
                }
            }
            // A `WITH RECURSIVE` CTE whose body is `<anchor> UNION [ALL] <term>`
            // and whose recursive term actually references the CTE lowers to a
            // RecursiveCTE fixpoint node. A recursive-keyword CTE that does not
            // self-reference (or is not a UNION) is an ordinary CTE: fall through
            // to plain inline expansion below.
            if (it->recursive) {
                const ASTNode* rbody = subquery_body(def);
                if (rbody != nullptr && is_setop_node(rbody->node_type)) {
                    const ASTNode* anchor = first_child(rbody);
                    const ASTNode* rterm = anchor ? anchor->next_sibling : nullptr;
                    if (rterm != nullptr && subtree_references_cte(rterm, name)) {
                        return bind_recursive_cte(*it, table_ref, error);
                    }
                }
            }
            // The CTE body is a SELECT or a set operation (UNION/INTERSECT/EXCEPT);
            // subquery_body handles both. find_child(SelectStmt) alone missed a
            // set-op body, so `WITH t AS (SELECT .. UNION SELECT ..)` failed to bind.
            cte_expanding_.push_back(def);
            auto body = bind_query(subquery_body(def), error);
            cte_expanding_.pop_back();
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

LogicalNodePtr Binder::bind_recursive_cte(CteEntry entry,
                                          const ASTNode* table_ref,
                                          std::string& error) {
    const ASTNode* def = entry.def;
    const ASTNode* body = subquery_body(def);  // an <anchor> UNION[ALL] <term> node
    const ASTNode* anchor = first_child(body);
    const ASTNode* rec_term = anchor != nullptr ? anchor->next_sibling : nullptr;
    if (anchor == nullptr || rec_term == nullptr) {
        error = "recursive CTE '" + entry.name +
                "' must be an anchor term UNION a recursive term";
        return nullptr;
    }
    // SQL / Postgres allow only UNION [ALL] to combine the terms of a recursive
    // CTE (INTERSECT / EXCEPT recursion is not defined). Reject the others.
    const ast::SetOp combine = setop_kind(body);
    if (combine != ast::SetOp::Union && combine != ast::SetOp::UnionAll) {
        error = "recursive CTE '" + entry.name +
                "' must combine its terms with UNION [ALL]";
        return nullptr;
    }

    // The CTE's columns are the analyzer's reconciled projection of the UNION
    // body (anchor types unified with the recursive term, arity checked,
    // nullability OR-ed). These columns carry the ids the analyzer stamped on
    // references to the CTE - in the recursive term (through the working table)
    // and in the outer query alike - so the same schema drives resolution in
    // both places unchanged.
    const auto* proj = analyzer_.projection_of(body);
    if (proj == nullptr) {
        error = "analyzer produced no projection for recursive CTE '" +
                entry.name + "'";
        return nullptr;
    }
    Schema cte_schema;
    cte_schema.reserve(proj->size());
    for (const auto& c : *proj) {
        cte_schema.push_back(to_schema(c));
    }
    // Optional `WITH r(a, b)` column-list rename: rename positionally so a bare
    // `a` / `r.a` (a computed CTE column the analyzer resolves by name) and the
    // dumped schema use the declared names.
    if (const ASTNode* col_list = find_child(def, NodeType::ColumnList)) {
        std::size_t i = 0;
        for (const ASTNode* cn = first_child(col_list);
             cn != nullptr && i < cte_schema.size();
             cn = cn->next_sibling, ++i) {
            cte_schema[i].name =
                std::string{split_column_ref(cn->primary_text).column};
        }
    }

    // Bind the anchor term. The CTE is marked as expanding (so a self-reference
    // in the ANCHOR is rejected - it is illegal there) but its working table is
    // NOT yet in scope: only the recursive term may read the working table.
    cte_expanding_.push_back(def);
    auto anchor_plan = bind_query(anchor, error);
    if (!anchor_plan) {
        cte_expanding_.pop_back();
        return nullptr;
    }

    // Bind the recursive term with the working table in scope, so its
    // self-reference resolves to a WorkingTableScan carrying the CTE columns.
    recursive_working_.push_back({def, cte_schema, entry.name});
    auto rec_plan = bind_query(rec_term, error);
    recursive_working_.pop_back();
    cte_expanding_.pop_back();
    if (!rec_plan) {
        return nullptr;
    }

    auto node = make_node(LogicalOp::RecursiveCTE);
    node->table_name = entry.name;
    node->set_op = combine;  // UNION (dedup across iterations) vs UNION ALL
    node->output = cte_schema;
    // Label this reference so the outer query's `name.col` (and a self-join of
    // the CTE) stay distinguishable, mirroring the non-recursive CTE path.
    const std::string_view a = alias_of(table_ref);
    node->alias = a.empty() ? entry.name : std::string{a};
    for (auto& c : node->output) {
        c.alias = node->alias;
    }
    node->add_child(std::move(anchor_plan));
    node->add_child(std::move(rec_plan));
    return node;
}

LogicalNodePtr Binder::bind_values_relation(const ASTNode* values_stmt,
                                            std::string& error) {
    // A VALUES list used as a derived table (Subquery -> ValuesStmt -> ValuesClause
    // -> one row per child). Lower each row's constant expressions into a Values
    // node (the same node kind INSERT ... VALUES uses) and give it an output
    // schema: one column per value position in the first row, typed from that row.
    // Columns are anonymous here; a column-alias list names them in bind_relation.
    const ASTNode* clause = find_child(values_stmt, NodeType::ValuesClause);
    if (clause == nullptr || first_child(clause) == nullptr) {
        error = "VALUES derived table has no rows";
        return nullptr;
    }
    auto vnode = make_node(LogicalOp::Values);
    const Schema no_input;  // VALUES expressions are constants
    for (const ASTNode* row = first_child(clause); row != nullptr;
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
    // Type each output column by reconciling across ALL rows, not just the first
    // (a multi-row VALUES is a UNION ALL of its rows). Typing from row 0 alone
    // disagreed with the analyzer, which already reconciles these column types
    // (columns_from_values): e.g. (VALUES (1),(2.5)) is Double not Integer, and
    // (VALUES (NULL),(2)) is Integer not Null. reconcile_value_type mirrors the
    // analyzer's UnionReconcile rule exactly (cross-checked by a test).
    const auto& first_row = vnode->value_rows.front();
    std::vector<DataType> col_types;
    col_types.reserve(first_row.size());
    for (const ExprPtr& e : first_row) {
        col_types.push_back(e->type);
    }
    for (std::size_t r = 1; r < vnode->value_rows.size(); ++r) {
        const auto& row = vnode->value_rows[r];
        for (std::size_t i = 0; i < col_types.size() && i < row.size(); ++i) {
            col_types[i] = reconcile_value_type(col_types[i], row[i]->type);
        }
    }
    for (const DataType t : col_types) {
        ColumnSchema c;
        c.type = t;
        c.nullable = true;
        vnode->output.push_back(std::move(c));
    }
    return vnode;
}

LogicalNodePtr Binder::bind_relation(const ASTNode* relation, std::string& error) {
    if (relation->node_type == NodeType::TableRef) {
        return bind_table_ref(relation, error);
    }
    if (is_derived_node(relation->node_type)) {
        // Derived table / subquery in FROM: bind the inner query block (a SELECT /
        // set operation, or a VALUES list) and use its plan as the Scan-equivalent
        // input. Its output schema is the derived projection; the alias labels the
        // relation.
        const ASTNode* body = subquery_body(relation);
        LogicalNodePtr inner;
        if (body != nullptr) {
            inner = bind_query(body, error);
        } else if (const ASTNode* values = find_child(relation, NodeType::ValuesStmt)) {
            inner = bind_values_relation(values, error);
        } else {
            error = "derived table without a query body";
            return nullptr;
        }
        if (!inner) {
            return nullptr;
        }
        // Optional column-alias list "(a, b)": rename the derived output columns
        // positionally so `s.a` / bare `a` resolves. A computed column (an
        // aggregate or expression) has synthetic (0, 0) ids, so it resolves BY
        // NAME - the alias must therefore be its output name, not just the
        // analyzer's binding name. Mirrors the CTE column-list rename.
        if (const ASTNode* col_list = find_child(relation, NodeType::ColumnList)) {
            std::size_t i = 0;
            for (const ASTNode* cn = first_child(col_list);
                 cn != nullptr && i < inner->output.size();
                 cn = cn->next_sibling, ++i) {
                inner->output[i].name =
                    std::string{split_column_ref(cn->primary_text).column};
            }
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
        // A `hidden` column is an internal per-side copy retained from an EARLIER
        // USING/NATURAL merge (so a qualified `u.c` still resolves after the merge);
        // it is not a user-visible relation column, so it is NOT a NATURAL common
        // column and must not inflate the duplicate/ambiguity count. Excluding it
        // keeps a chained `A NATURAL RIGHT JOIN B NATURAL RIGHT JOIN C` from seeing
        // the first merge's hidden copies as duplicate `id`s and falsely rejecting
        // the (legal) query as ambiguous.
        const auto count_by_name = [](const Schema& s, std::string_view name) {
            int n = 0;
            for (const auto& c : s) {
                if (!c.hidden && iequals(c.name, name)) ++n;
            }
            return n;
        };
        for (const auto& lc : left->output) {
            if (lc.hidden) {
                continue;  // internal per-side copy, not a common column
            }
            const int right_count = count_by_name(right->output, lc.name);
            if (right_count == 0) {
                continue;  // not a common column
            }
            bool already = false;
            for (const std::string_view m : merged) {
                if (iequals(m, lc.name)) { already = true; break; }
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
            if (iequals(m, name)) {
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
        ColumnSchema c = col;
        c.nullable = c.nullable || null_right;
        if (!coalesce_merged && is_merged(col.name)) {
            // INNER / LEFT: the merged column's value is the left copy (kept
            // above and shown by `SELECT *`). Keep the right copy too, but
            // HIDDEN: a qualified `right.c` must resolve to the RIGHT column
            // (NULL for a LEFT-join row with no right match) rather than to the
            // left/merged copy - which previously returned the wrong value, or,
            // for an INNER join with `WHERE right.c = ...`, failed to bind
            // because the right copy had been dropped entirely. It keeps its own
            // (table_id, column_id, alias) so the qualified reference finds it,
            // and is excluded from `*`. (RIGHT / FULL build a COALESCE Project
            // below that keeps BOTH sides as hidden copies for the same reason -
            // there the merged value is a distinct COALESCE column, not the left
            // copy, so both individual copies must be retained.)
            c.hidden = true;
        }
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
    // frame; this Project materializes each merged pair as a VISIBLE
    // COALESCE(left.c, right.c) column plus a HIDDEN copy of each individual side.
    // The visible column carries the left (table_id, column_id) + name (so an
    // unqualified `c` and `*` resolve to the coalesced value) with its alias
    // cleared; the hidden left/right copies keep their own identity and alias so a
    // qualified `u.c` / `o.c` resolves to that side's column - NULL for a row with
    // no match on the null-supplying side - rather than the coalesced value. This
    // mirrors the INNER / LEFT hidden right-copy, extended to both sides.
    auto project = make_node(LogicalOp::Project);
    Schema pout;
    std::vector<ExprPtr> pexprs;
    for (std::uint32_t i = 0; i < left_width; ++i) {
        const ColumnSchema& lc = join->output[i];  // null_left-adjusted
        // A hidden per-side copy from an EARLIER merge is not itself a merge key -
        // it passes through UNCHANGED (still hidden, keeping its qualified-ref
        // identity). Only a VISIBLE column is materialized as the COALESCE, so a
        // chained `... RIGHT JOIN o USING(id) RIGHT JOIN e USING(id)` emits exactly
        // ONE visible `id` instead of one per prior copy.
        if (lc.hidden || !is_merged(lc.name)) {
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
        // Visible merged column: COALESCE(left.c, right.c). It keeps the LEFT
        // column's (table_id, column_id) and name so an UNQUALIFIED `c` and
        // `SELECT *` resolve to it, but its alias is CLEARED: a qualified `u.c`
        // must NOT bind here (that would read the coalesced value), it must find
        // the hidden left copy below. Emitted before the hidden copies so the
        // unqualified first-match lands on it.
        ColumnSchema mc = left->output[i];  // left identity + name
        mc.alias.clear();
        mc.nullable = merged_nullable;
        mc.hidden = false;
        pexprs.push_back(std::move(coa));
        pout.push_back(std::move(mc));

        // Hidden LEFT copy: keeps the left identity AND left alias, so a qualified
        // reference to the null-supplying left side (`u.c` under RIGHT / FULL)
        // resolves to the left column itself - NULL for a row with no left match -
        // instead of the coalesced value. Excluded from `*`.
        ColumnSchema lh = join->output[i];  // null_left-adjusted, left alias
        lh.hidden = true;
        pexprs.push_back(make_column_ref(i, join->output[i]));
        pout.push_back(std::move(lh));

        // Hidden RIGHT copy: keeps the right identity AND right alias, so a
        // qualified `o.c` resolves to the right column (NULL for a FULL row with
        // no right match) rather than the merged column. Excluded from `*`. This
        // is the symmetric completion of the INNER / LEFT hidden right-copy: under
        // RIGHT / FULL BOTH individual copies are addressable, only the merged
        // COALESCE is shown by `*`.
        ColumnSchema rh = rc;  // null_right-adjusted, right alias
        rh.hidden = true;
        pexprs.push_back(
            make_column_ref(left_width + static_cast<std::uint32_t>(ri), rc));
        pout.push_back(std::move(rh));
    }
    for (std::uint32_t j = 0; j < static_cast<std::uint32_t>(right->output.size()); ++j) {
        const ColumnSchema& rc = join->output[left_width + j];
        // A VISIBLE right column whose name is merged has its value in the left
        // section (the COALESCE). A hidden right copy from an earlier merge is not
        // a merge key and passes through unchanged, so a qualified reference into
        // that side still resolves after this join.
        if (!rc.hidden && is_merged(rc.name)) {
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
    // Comma binds looser than JOIN. The FROM list is a sequence of
    // comma-separated table_references, and each table_reference may itself be a
    // chain of joins. `group` is the table_reference being built right now (an
    // explicit JOIN attaches to it as its left operand); `current` is the
    // CROSS-join of the table_references already completed. Folding a JOIN onto
    // the whole accumulated `current` instead would place a preceding comma
    // relation on the join's left operand, so a RIGHT/FULL join would wrongly
    // null-extend it: `A, B RIGHT JOIN C` is `A CROSS (B RIGHT JOIN C)`, NOT
    // `(A CROSS B) RIGHT JOIN C`. (Column order - left ++ right at every node -
    // is identical to the old fold, so slot indices are unchanged.)
    LogicalNodePtr group = bind_relation(item, error);
    if (!group) {
        return nullptr;
    }
    LogicalNodePtr current;  // completed table_references, CROSS-joined together
    for (item = item->next_sibling; item != nullptr; item = item->next_sibling) {
        if (is_join_node(item->node_type)) {
            // A JOIN extends the current table_reference (left-associative within
            // the group) - its left operand is `group`, not the whole FROM so far.
            group = bind_join(std::move(group), item, error);
            if (!group) {
                return nullptr;
            }
        } else if (item->node_type == NodeType::TableRef ||
                   is_derived_node(item->node_type)) {
            // A comma starts a new table_reference: the current group is complete,
            // so CROSS it into the accumulated result, then begin the new group.
            current = current ? make_join_node(std::move(current), std::move(group),
                                               ast::JoinType::Cross)
                              : std::move(group);
            group = bind_relation(item, error);
            if (!group) {
                return nullptr;
            }
        }
        // Other node kinds at FROM level are ignored (defensive).
    }
    // Fold the final (or only) table_reference into the accumulated cross-join.
    current = current ? make_join_node(std::move(current), std::move(group),
                                       ast::JoinType::Cross)
                      : std::move(group);
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
    // A `WITH` above a top-level set operation attaches its CTEClause as a child
    // of THIS node, and the CTE is in scope for every branch (`WITH t AS (...)
    // SELECT ... FROM t UNION SELECT ... FROM t`). Register it before binding the
    // branches, scoped like bind_select's, so a branch's FROM reference resolves.
    // Without this the branch bind failed (unknown table), and reading the branch
    // off first_child would instead pick the CTEClause itself.
    struct CteGuard {
        std::vector<CteEntry>* v;
        std::size_t mark;
        ~CteGuard() { v->resize(mark); }
    } cte_guard{&ctes_, ctes_.size()};
    register_block_ctes(setop);

    // A set-operation node has exactly two branch children (left, right); the
    // parser folds successive operators left-deep, so the left child may itself
    // be a nested set operation. This left-associativity is preserved here. The
    // branches are the SelectStmt / set-op children specifically - the node may
    // also carry a leading CTEClause and a trailing ORDER BY / LIMIT, so select
    // the branch children by kind rather than reading the first two children.
    const ASTNode* left_q = nullptr;
    const ASTNode* right_q = nullptr;
    for (const ASTNode* c = first_child(setop); c != nullptr; c = c->next_sibling) {
        if (c->node_type != NodeType::SelectStmt && !is_setop_node(c->node_type)) {
            continue;
        }
        if (left_q == nullptr) {
            left_q = c;
        } else if (right_q == nullptr) {
            right_q = c;
        }
    }
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
    LogicalNodePtr result = std::move(node);

    // --- Trailing ORDER BY / LIMIT scope to the WHOLE set operation --------
    // SQL forbids an unparenthesized set-op branch from carrying its own ORDER
    // BY / LIMIT, so a trailing ORDER BY / LIMIT belongs to the set operation.
    // The parser attaches those clauses as DIRECT CHILDREN of the set-op node
    // (UnionStmt / IntersectStmt / ExceptStmt); read them from there and build a
    // Sort (directly above the SetOp) and a Limit (above the Sort) over the
    // reconciled set-op output. The ORDER BY keys are lowered against that output
    // so `ORDER BY <col>` / `ORDER BY <n>` bind to the set operation's output
    // column, not to a same-named base column of a branch. A branch's OWN
    // parenthesized ORDER BY stays inside that branch (it binds as a derived
    // table) and is not touched here.
    bool sl_has_limit = false, sl_has_offset = false;
    std::int64_t sl_limit = -1, sl_offset = 0;
    if (const ASTNode* limit = find_child(setop, NodeType::LimitClause)) {
        const ASTNode* limit_op = first_child(limit);
        const ASTNode* offset_op = limit_op != nullptr ? limit_op->next_sibling : nullptr;
        std::int64_t v = 0;
        if (parse_int_literal(limit_op, v)) { sl_has_limit = true; sl_limit = v; }
        if (parse_int_literal(offset_op, v)) { sl_has_offset = true; sl_offset = v; }
    }
    const bool hoist_sort = find_child(setop, NodeType::OrderByClause) != nullptr;
    const bool hoist_limit = find_child(setop, NodeType::LimitClause) != nullptr;

    // Re-apply the ORDER BY as a Sort above the SetOp, keyed on the reconciled
    // set-op output. Mirrors the ordinal / column / ASC-DESC / NULLS handling in
    // bind_select, minus the hidden-column path (an ORDER BY over a set op must
    // reference an output column).
    if (hoist_sort) {
        const ASTNode* order_by = find_child(setop, NodeType::OrderByClause);
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

void Binder::register_block_ctes(const ASTNode* stmt) {
    const ASTNode* cte_clause = find_child(stmt, NodeType::CTEClause);
    if (cte_clause == nullptr) {
        return;
    }
    // `WITH RECURSIVE` (the parser sets NodeFlags::IsRecursive on the clause)
    // lets a CTE reference itself; such a CTE lowers to a RecursiveCTE node
    // instead of being inlined, and only then is a self-reference legal.
    const bool clause_recursive =
        cte_clause->has_flag(ast::NodeFlags::IsRecursive);
    for (const ASTNode* def = first_child(cte_clause); def != nullptr;
         def = def->next_sibling) {
        if (def->node_type != NodeType::CTEDefinition) {
            continue;
        }
        // Register a CTE with a SELECT or a set-operation body (subquery_body
        // handles both); a set-op body was previously skipped, so a reference
        // to it resolved to nothing.
        if (subquery_body(def) != nullptr) {
            ctes_.push_back({std::string{def->primary_text}, def, clause_recursive});
        }
    }
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
        std::vector<CteEntry>* v;
        std::size_t mark;
        ~CteGuard() { v->resize(mark); }
    } cte_guard{&ctes_, ctes_.size()};
    register_block_ctes(select_stmt);

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
        // input, which lower directly. `GROUP BY 1` (output ordinal) is rejected
        // upstream. A GROUP BY key may, however, name a SELECT output ALIAS
        // (`GROUP BY d` for `dept AS d`) - a PostgreSQL extension the analyzer
        // accepts: it does not resolve against the input, so lower the aliased
        // SELECT item's expression instead (see group_key_alias_target). A
        // bare-column key additionally carries its source (table_id, column_id)
        // so an operator above resolves it by id rather than only structurally.
        std::uint32_t slot = 0;
        for (const ASTNode* key = group_by != nullptr ? first_child(group_by) : nullptr;
             key != nullptr; key = key->next_sibling) {
            const ASTNode* lowered_from = key;
            ExprPtr e;
            // Positional GROUP BY: `GROUP BY <n>` groups by the n-th SELECT item's
            // expression (which the analyzer accepts / validates). Resolve it and
            // lower THAT item, not the integer literal - lowering the literal would
            // succeed as a constant single-group key, and the bare SELECT column it
            // stands for would then fail to resolve. Checked before lower_expr for
            // exactly that reason. The literal's own name ("n") / Integer type must
            // not be used for the key column, so take them from the resolved item.
            const ASTNode* ordinal_item = group_key_ordinal_target(key, select_list);
            if (ordinal_item != nullptr) {
                e = lower_expr(ordinal_item, agg_input, error);
                if (!e) {
                    return nullptr;
                }
                lowered_from = ordinal_item;
            } else {
                e = lower_expr(key, agg_input, error);
                if (!e) {
                    // Not an input column/expression: try a SELECT output alias.
                    // (Reaching here means the key did not resolve against the
                    // input, so input-column precedence is already honoured.)
                    if (const ASTNode* alias_item =
                            group_key_alias_target(key, select_list)) {
                        error.clear();
                        e = lower_expr(alias_item, agg_input, error);
                        lowered_from = alias_item;
                    }
                    if (!e) {
                        return nullptr;
                    }
                }
            }
            // A positional key's name/type come from the resolved item (the literal
            // is Integer and named "n"); a column / alias key already carries them.
            const ASTNode* name_src = (ordinal_item != nullptr) ? lowered_from : key;
            ColumnSchema col;
            col.name = item_output_name(name_src);
            col.type = analyzer_.type_of(name_src);
            col.nullable = analyzer_.nullability_of(name_src) != 1;
            if (lowered_from->node_type == NodeType::ColumnRef ||
                lowered_from->node_type == NodeType::Identifier) {
                col.table_id = lowered_from->context.analysis.table_id;
                col.column_id = lowered_from->context.analysis.column_id;
            }
            agg->output.push_back(std::move(col));
            agg->group_keys.push_back(std::move(e));
            // Register the producer(s) of this slot so a SELECT/HAVING/ORDER BY
            // reference routes here. Producers are matched STRUCTURALLY, so what
            // we register must be an expression whose recurrence above the
            // Aggregate genuinely denotes this group key:
            //   - column / expression key: register the key itself.
            //   - alias key (`GROUP BY d` for `x AS d`): also register the
            //     underlying expression, so a reference to either routes here.
            //   - positional key (`GROUP BY 1`): register ONLY the resolved
            //     n-th SELECT item, NEVER the integer-literal key. The literal
            //     is a positional selector, not the grouped value; registering
            //     it would rewrite every structurally-identical constant above
            //     the Aggregate (e.g. the `1` in `COUNT(*)+1`, a `2` in
            //     `HAVING sal > 2`) into a ColumnRef pointing at this slot.
            if (ordinal_item != nullptr) {
                agg_frame.producers.emplace_back(lowered_from, slot);
            } else {
                agg_frame.producers.emplace_back(key, slot);
                if (lowered_from != key) {
                    agg_frame.producers.emplace_back(lowered_from, slot);
                }
            }
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
            // Lower with the aggregate frame active, exactly as HAVING / the
            // Project do. A window clause over a grouped query may reference an
            // aggregate of the group (`RANK() OVER (ORDER BY SUM(sal))`,
            // `... PARTITION BY MAX(x)`): the window node sits above the
            // Aggregate, so that SUM(sal) must resolve to the precomputed
            // Aggregate output column, not re-lower the raw `sal` the
            // post-aggregation input no longer exposes. `agg_frame` is empty when
            // the query does not aggregate, so this is a no-op there.
            agg_frame_ = &agg_frame;
            bool window_ok = true;
            for (const ASTNode* fn : window_fns) {
                auto e = lower_expr(fn, win_input, error);
                if (!e) {
                    window_ok = false;
                    break;
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
            agg_frame_ = nullptr;
            if (!window_ok) {
                return nullptr;
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
        // `*` projects the child's visible columns - excluding any HIDDEN column
        // (the right-hand copy of a USING/NATURAL merged column, kept only for
        // qualified `right.c` resolution).
        for (const auto& c : current->output) {
            if (!c.hidden) {
                project->output.push_back(c);
            }
        }
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
        // Reconcile each projected column's declared nullability with the actual
        // bound plan. A projected ColumnRef's output column IS the child slot it
        // references, so its nullability must equal that slot's - the output
        // schema is otherwise seeded from the analyzer's projection annotation,
        // which is conservatively NULLABLE for a RIGHT / FULL USING (or NATURAL
        // RIGHT/FULL) merged key. That merged key is COALESCE(left, right) over a
        // preserved (non-null) side, which the binder's own COALESCE node has
        // already proven non-null; copying the analyzer's nullable annotation
        // left the top Project declaring the key nullable while its expr (and the
        // child COALESCE) typed it non-null - an internally inconsistent node.
        // The child slot is the ground truth for a pass-through column reference.
        for (std::size_t i = 0; i < project->exprs.size(); ++i) {
            const Expr* e = project->exprs[i].get();
            if (e != nullptr && e->kind == ExprKind::ColumnRef &&
                e->input_index < current->output.size()) {
                project->output[i].nullable =
                    current->output[e->input_index].nullable;
            }
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

            // A QUALIFIED column reference (`u.id`) in ORDER BY is an INPUT-column
            // reference, not an output-name match: it must resolve against the
            // Project's INPUT frame, where the per-side hidden copies of a USING /
            // NATURAL merged column carry their alias. Output columns carry no
            // alias, so resolving a qualified ref against the narrow Project output
            // would bind it to a same-(table_id,column_id) merged COALESCE column -
            // the wrong (non-null) value under a RIGHT / FULL join, where `u.id`
            // must order by the (nullable) left column. Reuse a projected output
            // column that already IS this input column; otherwise append a hidden
            // sort-only column resolved against the input frame.
            if (proj_input != nullptr && !over_distinct &&
                (key->node_type == NodeType::ColumnRef ||
                 key->node_type == NodeType::Identifier) &&
                !split_column_ref(key->primary_text).qualifier.empty()) {
                std::string qerr;
                agg_frame_ = &agg_frame;
                auto in_ref = lower_expr(key, *proj_input, qerr);
                agg_frame_ = nullptr;
                if (in_ref) {
                    int reuse = -1;
                    if (in_ref->kind == ExprKind::ColumnRef && project != nullptr) {
                        for (std::size_t k = 0; k < project->exprs.size(); ++k) {
                            const auto& pe = project->exprs[k];
                            if (pe && pe->kind == ExprKind::ColumnRef &&
                                pe->input_index == in_ref->input_index) {
                                reuse = static_cast<int>(k);
                                break;
                            }
                        }
                    }
                    if (reuse >= 0) {
                        sk.expr = make_column_ref(
                            static_cast<std::uint32_t>(reuse),
                            input_node->output[static_cast<std::size_t>(reuse)]);
                    } else {
                        ColumnSchema hcol;
                        hcol.name = item_output_name(key);
                        hcol.type = in_ref->type;
                        hcol.nullable = in_ref->nullability != 1;
                        hcol.table_id = in_ref->ref_table_id;
                        hcol.column_id = in_ref->ref_column_id;
                        project->output.push_back(hcol);
                        project->exprs.push_back(std::move(in_ref));
                        sk.expr = make_column_ref(
                            static_cast<std::uint32_t>(project->output.size() - 1),
                            project->output.back());
                    }
                    sort->sort_keys.push_back(std::move(sk));
                    continue;
                }
                // If the qualified ref did not resolve against the input frame,
                // fall through to the normal resolution below (which reports the
                // error consistently).
            }

            // Resolve against the input's current output (a selected column, an
            // output alias, or a prior hidden sort column already appended). A key
            // that lowers to a RAW aggregate is rejected here and routed to the
            // frame-active path below instead: an ORDER-BY aggregate not in the
            // SELECT list (e.g. `ORDER BY COUNT(*)`, `ORDER BY COUNT(dept)`) has no
            // unresolvable argument, so against the already-grouped Project output
            // it lowers to a fresh Aggregate over one-row-per-group (COUNT() == 1
            // for every group) instead of the precomputed value. `ORDER BY
            // SUM(sal)` already lands in the frame path by failing to resolve its
            // arg `sal` here; this makes the no-arg / selected-arg aggregates
            // behave the same, resolving to the Aggregate's output slot.
            std::string local_error;
            if (auto e = lower_expr(key, input_node->output, local_error)) {
                if (!contains_raw_aggregate(e)) {
                    sk.expr = std::move(e);
                    sort->sort_keys.push_back(std::move(sk));
                    continue;
                }
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
            // A Star stores its qualifier in schema_name as the dotted prefix
            // ("t" or "schema.table"); its primary_text is always "*", so the
            // qualifier must be read from schema_name - NOT from primary_text,
            // whose split is always unqualified.
            const std::string_view star_qual = item->schema_name;
            if (star_qual.empty()) {
                // Bare `*`: expand to one positional ColumnRef per visible child
                // output column (a hidden merged-right copy is not part of `*`).
                for (std::size_t s = 0; s < input.size(); ++s) {
                    if (input[s].hidden) {
                        continue;
                    }
                    out.push_back(make_column_ref(static_cast<std::uint32_t>(s), input[s]));
                }
                continue;
            }
            // Qualified `q.*`: expand only the child columns whose relation alias
            // matches the qualifier's table component (the last dotted part),
            // preserving child order so the expansion aligns with the analyzer's
            // projection for that star. This binds `SELECT u.* FROM a JOIN b`
            // to exactly u's columns instead of the whole join frame.
            //
            // Unlike a bare `*`, a qualified `q.*` DOES include q's copy of a
            // USING/NATURAL merged column even though that copy is HIDDEN: the
            // hidden bit only excludes the redundant merged-side copy from an
            // unqualified `*`, but `q.*` names the relation explicitly, so
            // Postgres expands it to ALL of q's columns (the join column
            // included). The hidden copy sits in q's natural column position in
            // the frame, so order still aligns with the analyzer's `q.*`.
            const std::string_view tbl = split_column_ref(star_qual).column;
            std::size_t matched = 0;
            for (std::size_t s = 0; s < input.size(); ++s) {
                if (!iequals(input[s].alias, tbl)) {
                    continue;
                }
                out.push_back(make_column_ref(static_cast<std::uint32_t>(s), input[s]));
                ++matched;
            }
            if (matched == 0) {
                error = "qualified '" + std::string{star_qual} +
                        ".*' matches no relation in the FROM clause";
                return false;
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
