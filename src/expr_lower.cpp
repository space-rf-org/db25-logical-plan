// DB25 Logical Plan - AST -> owned, typed Expr lowering
//
// Implements Binder::lower_expr (declared in binder.hpp). This is the single
// place that reads the analyzer + parse tree and emits an owned Expr:
//
//   * dispatch on node_type -> ExprKind;
//   * set type = analyzer_.type_of(n), nullability = analyzer_.nullability_of(n)
//     ONCE, on every node (kills the analyzer round-trip);
//   * resolve a ColumnRef to a flat `input_index` into `input` by matching the
//     analyzer's (table_id, column_id) against the already-computed input schema
//     (section 3.2), with a minimal producer-map (by-name) fallback for computed
//     columns whose ids are synthetic/zero;
//   * a base column that is NOT in `input` but resolves against an enclosing
//     input (`outer_inputs_`) becomes a first-class OuterRef{depth, input_index};
//   * an embedded subquery lowers inline into an owned `sub_plan` (bound via
//     bind_query) with its correlation flag from analyzer_.is_correlated.
//
// See the design memo section 4 and include/db25/plan/expr_ir.hpp.

#include "db25/plan/binder.hpp"
#include "db25/plan/expr_ir.hpp"

#include "db25/ast/ast_node.hpp"
#include "db25/ast/node_types.hpp"
#include "db25/semantic/ast_helpers.hpp"  // first_child / find_child / split_column_ref

#include <charconv>
#include <memory>
#include <string>
#include <string_view>

namespace db25::plan {

using db25::ast::ASTNode;
using db25::ast::BinaryOp;
using db25::ast::DataType;
using db25::ast::NodeType;
using db25::ast::UnaryOp;
using db25::semantic::find_child;
using db25::semantic::first_child;
using db25::semantic::split_column_ref;

namespace {

ExprPtr make_expr(ExprKind kind, const ASTNode* source) {
    auto e = std::make_unique<Expr>(kind);
    e->source = source;
    return e;
}

std::string to_upper(std::string_view s) {
    std::string out;
    out.reserve(s.size());
    for (const char ch : s) {
        out.push_back((ch >= 'a' && ch <= 'z') ? static_cast<char>(ch - 32) : ch);
    }
    return out;
}

// A predicate is negated (NOT EXISTS / NOT IN / NOT LIKE / NOT BETWEEN / IS NOT
// NULL). The parser marks NOT on the predicate node with semantic_flags bit 6
// (0x40); some shapes also spell "NOT" into the operator text. Accept either so
// the negation is never lost.
bool is_negated(const ASTNode* n) {
    return (n->semantic_flags & 0x40u) != 0 ||
           to_upper(n->primary_text).find("NOT") != std::string::npos;
}

// Find the flat slot of a base column (table_id, column_id) in a schema. When a
// `qualifier` is given (a column reference's alias), prefer the matching slot
// whose column carries that alias - this is what disambiguates a self-join,
// where every occurrence of the table shares the same (table_id, column_id).
// Falls back to the first (table_id, column_id) match otherwise, preserving the
// single-occurrence behaviour.
int find_slot_by_id(const Schema& s, std::uint32_t tid, std::uint32_t cid,
                    std::string_view qualifier = {}) {
    int first = -1;
    for (std::size_t i = 0; i < s.size(); ++i) {
        if (s[i].table_id == tid && s[i].column_id == cid) {
            if (first < 0) {
                first = static_cast<int>(i);
            }
            if (!qualifier.empty() && s[i].alias == qualifier) {
                return static_cast<int>(i);
            }
        }
    }
    return first;
}

// Minimal producer-map fallback: match a computed column (synthetic/zero ids)
// by its output name. The real producer map (design section 3.3) keys on the
// producing AST item; matching by name covers the unit-test cases (agg outputs,
// projected exprs) without the operator-side bookkeeping that later steps add.
int find_slot_by_name(const Schema& s, std::string_view name) {
    for (std::size_t i = 0; i < s.size(); ++i) {
        if (s[i].name == name) {
            return static_cast<int>(i);
        }
    }
    return -1;
}

// The standard SQL aggregate names the binder separates from scalar functions
// (mirrors binder.cpp's recognizer). A windowed call is handled separately.
bool is_aggregate_name(std::string_view upper) {
    return upper == "COUNT" || upper == "SUM" || upper == "AVG" || upper == "MIN" ||
           upper == "MAX" || upper == "TOTAL" || upper == "GROUP_CONCAT" ||
           upper == "STRING_AGG";
}

// Map a binary operator's text (the analyzer reads it straight from
// primary_text) to the parser BinaryOp enum. Returns false on an unrecognized
// operator so the caller can surface an error.
bool map_binary_op(std::string_view text, BinaryOp& out) {
    const std::string u = to_upper(text);
    if (text == "+") { out = BinaryOp::Add; return true; }
    if (text == "-") { out = BinaryOp::Subtract; return true; }
    if (text == "*") { out = BinaryOp::Multiply; return true; }
    if (text == "/") { out = BinaryOp::Divide; return true; }
    if (text == "%") { out = BinaryOp::Modulo; return true; }
    if (text == "=" || text == "==") { out = BinaryOp::Equal; return true; }
    if (text == "<>" || text == "!=") { out = BinaryOp::NotEqual; return true; }
    if (text == "<") { out = BinaryOp::LessThan; return true; }
    if (text == "<=") { out = BinaryOp::LessEqual; return true; }
    if (text == ">") { out = BinaryOp::GreaterThan; return true; }
    if (text == ">=") { out = BinaryOp::GreaterEqual; return true; }
    if (text == "||") { out = BinaryOp::Concat; return true; }
    if (text == "&") { out = BinaryOp::BitAnd; return true; }
    if (text == "|") { out = BinaryOp::BitOr; return true; }
    if (text == "^") { out = BinaryOp::BitXor; return true; }
    if (text == "<<") { out = BinaryOp::BitShiftLeft; return true; }
    if (text == ">>") { out = BinaryOp::BitShiftRight; return true; }
    if (u == "AND") { out = BinaryOp::And; return true; }
    if (u == "OR") { out = BinaryOp::Or; return true; }
    if (u == "LIKE") { out = BinaryOp::Like; return true; }
    if (u == "NOT LIKE") { out = BinaryOp::NotLike; return true; }
    if (u == "IS") { out = BinaryOp::Is; return true; }
    if (u == "IS NOT") { out = BinaryOp::IsNot; return true; }
    if (u == "IN") { out = BinaryOp::In; return true; }
    if (u == "NOT IN") { out = BinaryOp::NotIn; return true; }
    return false;
}

// Map a unary operator's text to the parser UnaryOp enum. EXISTS / NOT EXISTS
// are handled upstream (they lower to a Subquery Expr), not here.
bool map_unary_op(std::string_view text, UnaryOp& out) {
    const std::string u = to_upper(text);
    if (u == "NOT") { out = UnaryOp::Not; return true; }
    if (text == "-") { out = UnaryOp::Negate; return true; }
    if (text == "~") { out = UnaryOp::BitwiseNot; return true; }
    return false;
}

// Strip one pair of surrounding single quotes from a string-literal's text.
std::string_view unquote(std::string_view t) {
    if (t.size() >= 2 && t.front() == '\'' && t.back() == '\'') {
        return t.substr(1, t.size() - 2);
    }
    return t;
}

// The inner query block (SelectStmt or set-operation) of a subquery node.
const ASTNode* subquery_body(const ASTNode* node) {
    if (const ASTNode* sel = find_child(node, NodeType::SelectStmt)) {
        return sel;
    }
    for (const ASTNode* c = first_child(node); c != nullptr; c = c->next_sibling) {
        if (c->node_type == NodeType::UnionStmt ||
            c->node_type == NodeType::IntersectStmt ||
            c->node_type == NodeType::ExceptStmt) {
            return c;
        }
    }
    return nullptr;
}

// The Subquery / SubqueryExpr node beneath an operator (e.g. an EXISTS
// UnaryExpr, or the right side of IN). Returns null if there is none.
const ASTNode* find_subquery_child(const ASTNode* n) {
    for (const ASTNode* c = first_child(n); c != nullptr; c = c->next_sibling) {
        if (c->node_type == NodeType::Subquery || c->node_type == NodeType::SubqueryExpr) {
            return c;
        }
    }
    return nullptr;
}

}  // namespace

// Structural equality of two producer expressions (see the header). A column
// reference compares by resolved (table_id, column_id); every other node matches
// on node_type + operator text with structurally-equal children in order. This
// tells `SUM(x)` and `SUM(y)` apart (they differ in their column child), which
// by-name matching cannot. The `a == b` fast path covers the common case where a
// select item IS the collected producer node.
bool Binder::same_producer_expr(const ASTNode* a, const ASTNode* b) {
    if (a == b) {
        return true;
    }
    if (a == nullptr || b == nullptr || a->node_type != b->node_type) {
        return false;
    }
    if (a->node_type == NodeType::ColumnRef || a->node_type == NodeType::Identifier) {
        const std::uint32_t at = a->context.analysis.table_id;
        const std::uint32_t ac = a->context.analysis.column_id;
        if (!(at != 0 && ac != 0 && at == b->context.analysis.table_id &&
              ac == b->context.analysis.column_id)) {
            return false;
        }
        // Same base column. In a self-join the two occurrences share
        // (table_id, column_id) but carry different qualifiers (e1.x vs e2.x);
        // when BOTH are qualified and the qualifiers differ they are DISTINCT
        // producers, so `GROUP BY e1.x, e2.x` keeps two keys and the projection
        // maps e2.x to its own slot. An empty qualifier matches either (a
        // qualified vs unqualified reference to the same column is one producer).
        const std::string_view qa = split_column_ref(a->primary_text).qualifier;
        const std::string_view qb = split_column_ref(b->primary_text).qualifier;
        if (!qa.empty() && !qb.empty() && qa != qb) {
            return false;
        }
        return true;
    }
    // A DISTINCT / ALL modifier lives in semantic_flags, not in primary_text or
    // children, so `COUNT(DISTINCT x)` and `COUNT(x)` share the same text and
    // argument; compare those bits so the two are not treated as one producer
    // (which would drop a needed column and mis-map one of them).
    constexpr std::uint16_t kModifierMask =
        static_cast<std::uint16_t>(db25::ast::NodeFlags::Distinct) |
        static_cast<std::uint16_t>(db25::ast::NodeFlags::All);
    if ((a->semantic_flags & kModifierMask) != (b->semantic_flags & kModifierMask)) {
        return false;
    }
    if (a->primary_text != b->primary_text) {
        return false;
    }
    const ASTNode* ca = first_child(a);
    const ASTNode* cb = first_child(b);
    while (ca != nullptr && cb != nullptr) {
        if (!same_producer_expr(ca, cb)) {
            return false;
        }
        ca = ca->next_sibling;
        cb = cb->next_sibling;
    }
    return ca == nullptr && cb == nullptr;
}

int Binder::aggregate_frame_slot(const ASTNode* n) const {
    if (agg_frame_ == nullptr || n == nullptr) {
        return -1;
    }
    for (const auto& [producer, slot] : agg_frame_->producers) {
        if (same_producer_expr(n, producer)) {
            return static_cast<int>(slot);
        }
    }
    return -1;
}

ExprPtr Binder::lower_expr(const ASTNode* n, const Schema& input, std::string& error) {
    if (n == nullptr) {
        error = "cannot lower a null expression";
        return nullptr;
    }

    const DataType type = analyzer_.type_of(n);
    const auto nullability = static_cast<std::uint8_t>(analyzer_.nullability_of(n));

    // Aggregate frame: when lowering an expression directly above an Aggregate,
    // a subexpression that structurally matches a group key or aggregate call
    // resolves to a ColumnRef into the precomputed output (group_keys ++
    // aggregates) instead of being re-lowered against base columns the aggregate
    // no longer exposes. Checked before dispatch so a whole-item aggregate and an
    // aggregate wrapped in `... + 1` are both intercepted; the frame is only
    // active against the Aggregate output frame, where the slot is in range.
    if (const int slot = aggregate_frame_slot(n);
        slot >= 0 && static_cast<std::size_t>(slot) < input.size()) {
        auto e = make_expr(ExprKind::ColumnRef, n);
        e->type = type;
        e->nullability = nullability;
        e->input_index = static_cast<std::uint32_t>(slot);
        e->ref_table_id = input[static_cast<std::size_t>(slot)].table_id;
        e->ref_column_id = input[static_cast<std::size_t>(slot)].column_id;
        return e;
    }

    switch (n->node_type) {
        // ----- Column reference (ColumnRef or a bare-arg Identifier) -----
        case NodeType::ColumnRef:
        case NodeType::Identifier: {
            const std::uint32_t tid = n->context.analysis.table_id;
            const std::uint32_t cid = n->context.analysis.column_id;
            // The reference's qualifier (`m` in `m.id`) disambiguates a self-join,
            // where each occurrence shares (table_id, column_id).
            const std::string_view qual = split_column_ref(n->primary_text).qualifier;
            if (tid != 0 && cid != 0) {
                // Base / catalog column: resolve by id against the input schema.
                const int slot = find_slot_by_id(input, tid, cid, qual);
                if (slot >= 0) {
                    auto e = make_expr(ExprKind::ColumnRef, n);
                    e->type = type;
                    e->nullability = nullability;
                    e->input_index = static_cast<std::uint32_t>(slot);
                    e->ref_table_id = tid;
                    e->ref_column_id = cid;
                    return e;
                }
                // Not in this operator's input: a correlated outer reference.
                // Resolve against enclosing inputs (innermost = back()).
                for (std::size_t d = 1; d <= outer_inputs_.size(); ++d) {
                    const Schema& outer = *outer_inputs_[outer_inputs_.size() - d];
                    const int os = find_slot_by_id(outer, tid, cid, qual);
                    if (os >= 0) {
                        auto e = make_expr(ExprKind::OuterRef, n);
                        e->type = type;
                        e->nullability = nullability;
                        e->outer_depth = static_cast<std::uint32_t>(d);
                        e->input_index = static_cast<std::uint32_t>(os);
                        e->ref_table_id = tid;
                        e->ref_column_id = cid;
                        return e;
                    }
                }
                error = "column reference '" + std::string{n->primary_text} +
                        "' resolves to no input or enclosing slot";
                return nullptr;
            }
            // Computed column (synthetic/zero ids): producer-map (by-name) fallback.
            const std::string_view name = split_column_ref(n->primary_text).column;
            const int slot = find_slot_by_name(input, name);
            if (slot >= 0) {
                auto e = make_expr(ExprKind::ColumnRef, n);
                e->type = type;
                e->nullability = nullability;
                e->input_index = static_cast<std::uint32_t>(slot);
                return e;
            }
            error = "unresolved column reference '" + std::string{n->primary_text} + "'";
            return nullptr;
        }

        // ----- Literals -----
        case NodeType::IntegerLiteral: {
            auto e = make_expr(ExprKind::Literal, n);
            e->type = type;
            e->nullability = nullability;
            std::int64_t v = 0;
            const std::string_view t = n->primary_text;
            const auto [ptr, ec] = std::from_chars(t.data(), t.data() + t.size(), v);
            if (ec == std::errc{} && ptr == t.data() + t.size()) {
                e->value.value = v;
            } else {
                // The literal does not fit in int64 (e.g. 9223372036854775808).
                // Leaving value.value at its default (monostate == NULL) while the
                // type stays Integer silently turns every comparison against it
                // into UNKNOWN and drops rows. Promote it to double instead -
                // the numeric widening SQLite applies to oversized integer
                // literals - so the value is preserved and comparisons evaluate.
                double dv = 0.0;
                const auto [dptr, dec] =
                    std::from_chars(t.data(), t.data() + t.size(), dv);
                if (dec == std::errc{} && dptr == t.data() + t.size()) {
                    e->value.value = dv;
                    e->type = ast::DataType::Double;
                } else {
                    error = "integer literal '" + std::string{t} +
                            "' is not a valid number";
                    return nullptr;
                }
            }
            return e;
        }
        case NodeType::FloatLiteral: {
            auto e = make_expr(ExprKind::Literal, n);
            e->type = type;
            e->nullability = nullability;
            double v = 0.0;
            const std::string_view t = n->primary_text;
            const auto [ptr, ec] = std::from_chars(t.data(), t.data() + t.size(), v);
            if (ec == std::errc{} && ptr == t.data() + t.size()) {
                e->value.value = v;
            }
            return e;
        }
        case NodeType::BooleanLiteral: {
            auto e = make_expr(ExprKind::Literal, n);
            e->type = type;
            e->nullability = nullability;
            e->value.value = (to_upper(n->primary_text) == "TRUE");
            return e;
        }
        case NodeType::StringLiteral:
        case NodeType::DateTimeLiteral:
        case NodeType::IntervalLiteral: {
            auto e = make_expr(ExprKind::Literal, n);
            e->type = type;
            e->nullability = nullability;
            e->value.value = std::string{unquote(n->primary_text)};
            return e;
        }
        case NodeType::NullLiteral: {
            auto e = make_expr(ExprKind::Literal, n);
            e->type = type;
            e->nullability = nullability;  // NULL literal -> monostate (already set)
            return e;
        }

        // ----- Binary operator -----
        case NodeType::BinaryExpr: {
            const ASTNode* lhs = first_child(n);
            const ASTNode* rhs = lhs != nullptr ? lhs->next_sibling : nullptr;
            BinaryOp op{};
            if (!map_binary_op(n->primary_text, op)) {
                error = "unrecognized binary operator '" + std::string{n->primary_text} + "'";
                return nullptr;
            }
            auto e = make_expr(ExprKind::BinaryOp, n);
            e->type = type;
            e->nullability = nullability;
            e->bin_op = op;
            auto l = lower_expr(lhs, input, error);
            if (!l) return nullptr;
            auto r = lower_expr(rhs, input, error);
            if (!r) return nullptr;
            e->children.push_back(std::move(l));
            e->children.push_back(std::move(r));
            return e;
        }

        // ----- Unary operator (EXISTS / NOT EXISTS fold into a Subquery) -----
        case NodeType::UnaryExpr: {
            const std::string u = to_upper(n->primary_text);
            if (u == "EXISTS" || u == "NOT EXISTS") {
                const ASTNode* sq = find_subquery_child(n);
                if (sq == nullptr) {
                    error = "EXISTS without a subquery operand";
                    return nullptr;
                }
                return lower_subquery(sq, SubqueryKind::Exists, is_negated(n), nullptr,
                                      type, nullability, input, error);
            }
            UnaryOp op{};
            if (!map_unary_op(n->primary_text, op)) {
                error = "unrecognized unary operator '" + std::string{n->primary_text} + "'";
                return nullptr;
            }
            auto e = make_expr(ExprKind::UnaryOp, n);
            e->type = type;
            e->nullability = nullability;
            e->un_op = op;
            auto operand = lower_expr(first_child(n), input, error);
            if (!operand) return nullptr;
            e->children.push_back(std::move(operand));
            return e;
        }

        // ----- Function call: window / aggregate / scalar -----
        case NodeType::FunctionCall:
        case NodeType::FunctionExpr: {
            // An aggregate / window call surfacing above its Aggregate / Window
            // node (e.g. in HAVING or ORDER BY) reads the already-computed output
            // column by name rather than re-lowering the call, whose base-column
            // arguments are no longer in scope. Self-gating: only fires when the
            // input schema actually carries a same-named producer column.
            if (auto precomputed = lower_precomputed_aggregate(n, input)) {
                return precomputed;
            }
            const ASTNode* window_spec = find_child(n, NodeType::WindowSpec);
            const std::string uname = to_upper(n->primary_text);
            const ExprKind fk = window_spec != nullptr ? ExprKind::WindowFunction
                                : is_aggregate_name(uname) ? ExprKind::Aggregate
                                                           : ExprKind::ScalarFunction;
            auto e = make_expr(fk, n);
            e->type = type;
            e->nullability = nullability;
            e->func_name = uname;
            e->distinct = n->has_flag(ast::NodeFlags::Distinct);
            // EXTRACT(field FROM ts) / DATE_PART(field, ts): the leading field is
            // a date-part keyword (YEAR, MONTH, ...) the parser emits as an
            // Identifier. Lower it as a string literal, not a column reference -
            // otherwise it resolves to no input slot and bind fails.
            const bool datepart_head = (uname == "EXTRACT" || uname == "DATE_PART");
            bool first_arg = true;
            for (const ASTNode* arg = first_child(n); arg != nullptr; arg = arg->next_sibling) {
                if (arg->node_type == NodeType::WindowSpec) {
                    continue;  // the OVER clause, lowered below (not an argument)
                }
                if (arg->node_type == NodeType::Star) {
                    continue;  // COUNT(*): the star contributes no value expression
                }
                if (datepart_head && first_arg &&
                    (arg->node_type == NodeType::Identifier ||
                     arg->node_type == NodeType::ColumnRef)) {
                    first_arg = false;
                    auto kw = make_expr(ExprKind::Literal, arg);
                    kw->type = ast::DataType::Text;
                    kw->nullability = 1;
                    kw->value.value = to_upper(arg->primary_text);
                    e->children.push_back(std::move(kw));
                    continue;
                }
                first_arg = false;
                auto a = lower_expr(arg, input, error);
                if (!a) return nullptr;
                e->children.push_back(std::move(a));
            }
            if (window_spec != nullptr) {
                if (!lower_window_spec(window_spec, input, e->window, error)) {
                    return nullptr;
                }
            }
            return e;
        }

        // ----- CASE -----
        case NodeType::CaseExpr: {
            // Parser layout: WHEN branches are BinaryExpr "WHEN" nodes with two
            // children [condition, then-result]; a leading non-WHEN child (simple
            // CASE operand) and a trailing non-WHEN child (ELSE result) may appear.
            // We flatten to children = [when0, then0, ..., [else]].
            auto is_when = [](const ASTNode* c) {
                return c->node_type == NodeType::BinaryExpr &&
                       to_upper(c->primary_text) == "WHEN";
            };
            auto e = make_expr(ExprKind::Case, n);
            e->type = type;
            e->nullability = nullability;
            const ASTNode* first = first_child(n);
            const bool simple = first != nullptr && !is_when(first);
            for (const ASTNode* c = first; c != nullptr; c = c->next_sibling) {
                if (simple && c == first) {
                    auto operand = lower_expr(c, input, error);  // the CASE operand
                    if (!operand) return nullptr;
                    e->children.push_back(std::move(operand));
                    continue;
                }
                if (is_when(c)) {
                    const ASTNode* cond = first_child(c);
                    const ASTNode* then_res = cond != nullptr ? cond->next_sibling : nullptr;
                    auto lc = lower_expr(cond, input, error);
                    if (!lc) return nullptr;
                    auto lt = lower_expr(then_res, input, error);
                    if (!lt) return nullptr;
                    e->children.push_back(std::move(lc));
                    e->children.push_back(std::move(lt));
                } else {
                    auto le = lower_expr(c, input, error);  // trailing ELSE result
                    if (!le) return nullptr;
                    e->children.push_back(std::move(le));
                }
            }
            return e;
        }

        // ----- CAST(operand AS type) -----
        case NodeType::CastExpr: {
            const ASTNode* operand = first_child(n);
            auto e = make_expr(ExprKind::Cast, n);
            e->type = type;
            e->nullability = nullability;
            e->target_type = type;  // == the CAST's result type
            auto o = lower_expr(operand, input, error);
            if (!o) return nullptr;
            e->children.push_back(std::move(o));
            return e;
        }

        // ----- BETWEEN -----
        case NodeType::BetweenExpr: {
            const ASTNode* value = first_child(n);
            const ASTNode* low = value != nullptr ? value->next_sibling : nullptr;
            const ASTNode* high = low != nullptr ? low->next_sibling : nullptr;
            auto e = make_expr(ExprKind::Between, n);
            e->type = type;
            e->nullability = nullability;
            if (is_negated(n)) {
                e->expr_flags |= ExprFlagNegated;
            }
            for (const ASTNode* c : {value, low, high}) {
                auto lc = lower_expr(c, input, error);
                if (!lc) return nullptr;
                e->children.push_back(std::move(lc));
            }
            return e;
        }

        // ----- LIKE -----
        case NodeType::LikeExpr: {
            auto e = make_expr(ExprKind::Like, n);
            e->type = type;
            e->nullability = nullability;
            if (is_negated(n)) {
                e->expr_flags |= ExprFlagNegated;
            }
            for (const ASTNode* c = first_child(n); c != nullptr; c = c->next_sibling) {
                auto lc = lower_expr(c, input, error);
                if (!lc) return nullptr;
                e->children.push_back(std::move(lc));
            }
            return e;
        }

        // ----- IS [NOT] NULL -----
        case NodeType::IsNullExpr: {
            auto e = make_expr(ExprKind::IsNull, n);
            e->type = type;
            e->nullability = nullability;
            if (is_negated(n)) {
                e->expr_flags |= ExprFlagNegated;
            }
            auto o = lower_expr(first_child(n), input, error);
            if (!o) return nullptr;
            e->children.push_back(std::move(o));
            return e;
        }

        // ----- IN (list) / IN (subquery) -----
        case NodeType::InExpr: {
            const ASTNode* value = first_child(n);
            const ASTNode* right = value != nullptr ? value->next_sibling : nullptr;
            const bool negated = is_negated(n);
            if (right != nullptr && (right->node_type == NodeType::Subquery ||
                                     right->node_type == NodeType::SubqueryExpr)) {
                auto v = lower_expr(value, input, error);
                if (!v) return nullptr;
                return lower_subquery(right, SubqueryKind::In, negated, std::move(v), type,
                                      nullability, input, error);
            }
            auto e = make_expr(ExprKind::InList, n);
            e->type = type;
            e->nullability = nullability;
            if (negated) {
                e->expr_flags |= ExprFlagNegated;
            }
            auto v = lower_expr(value, input, error);
            if (!v) return nullptr;
            e->children.push_back(std::move(v));
            for (const ASTNode* c = right; c != nullptr; c = c->next_sibling) {
                auto lc = lower_expr(c, input, error);
                if (!lc) return nullptr;
                e->children.push_back(std::move(lc));
            }
            return e;
        }

        // ----- EXISTS wrapped directly / a scalar subquery -----
        case NodeType::ExistsExpr: {
            const ASTNode* sq = find_subquery_child(n);
            if (sq == nullptr) {
                error = "EXISTS without a subquery operand";
                return nullptr;
            }
            const bool negated = is_negated(n);
            return lower_subquery(sq, SubqueryKind::Exists, negated, nullptr, type,
                                  nullability, input, error);
        }
        case NodeType::Subquery:
        case NodeType::SubqueryExpr: {
            return lower_subquery(n, SubqueryKind::Scalar, false, nullptr, type, nullability,
                                  input, error);
        }

        // ----- Bind parameter -----
        case NodeType::Parameter: {
            auto e = make_expr(ExprKind::Parameter, n);
            e->type = type;         // Unknown/Any until a later parameter-binding step
            e->nullability = nullability;
            return e;
        }

        default:
            error = std::string{"expression form '"} + ast::node_type_to_string(n->node_type) +
                    "' is not yet lowerable";
            return nullptr;
    }
}

// ---------------------------------------------------------------------------
// Subquery: fold scalar / IN / EXISTS into an owned Subquery Expr whose
// `sub_plan` is the bound inner query block. `left` (IN only) is the already-
// lowered left operand and is kept as children[0]. The inner block is bound via
// bind_query with `input` pushed as an enclosing schema so any correlated
// reference the inner lowering encounters can resolve outward to an OuterRef.
// ---------------------------------------------------------------------------
ExprPtr Binder::lower_subquery(const ASTNode* subquery, SubqueryKind kind, bool negated,
                               ExprPtr left, DataType type, std::uint8_t nullability,
                               const Schema& input, std::string& error) {
    auto e = make_expr(ExprKind::Subquery, subquery);
    e->type = type;
    e->nullability = nullability;
    e->subquery_kind = kind;
    e->correlated = analyzer_.is_correlated(subquery);
    if (negated) {
        e->expr_flags |= ExprFlagNegated;
    }
    if (left) {
        e->children.push_back(std::move(left));
    }
    const ASTNode* body = subquery_body(subquery);
    if (body != nullptr) {
        outer_inputs_.push_back(&input);
        std::string local_error;
        e->sub_plan = bind_query(body, local_error);
        outer_inputs_.pop_back();
        if (!e->sub_plan) {
            error = "failed to lower subquery body: " + local_error;
            return nullptr;
        }
    }
    return e;
}

// ---------------------------------------------------------------------------
// Window spec: lower PARTITION BY expressions and ORDER BY keys against `input`.
// The frame is captured as best-effort text (not semantically consumed yet).
// ---------------------------------------------------------------------------
bool Binder::lower_window_spec(const ASTNode* window_spec, const Schema& input,
                               WindowSpecIR& out, std::string& error) {
    for (const ASTNode* clause = first_child(window_spec); clause != nullptr;
         clause = clause->next_sibling) {
        switch (clause->node_type) {
            case NodeType::PartitionBy:
            case NodeType::PartitionByClause: {
                for (const ASTNode* p = first_child(clause); p != nullptr; p = p->next_sibling) {
                    auto lp = lower_expr(p, input, error);
                    if (!lp) return false;
                    out.partition_by.push_back(std::move(lp));
                }
                break;
            }
            case NodeType::OrderByClause: {
                for (const ASTNode* k = first_child(clause); k != nullptr; k = k->next_sibling) {
                    SortKeyIR sk;
                    sk.descending = (k->semantic_flags & (1u << 7)) != 0;
                    sk.nulls_order_explicit = (k->semantic_flags & (1u << 5)) != 0;
                    sk.nulls_first = (k->semantic_flags & (1u << 4)) != 0;
                    sk.expr = lower_expr(k, input, error);
                    if (!sk.expr) return false;
                    out.order_by.push_back(std::move(sk));
                }
                break;
            }
            case NodeType::WindowFrame:
            case NodeType::FrameClause: {
                out.frame.present = true;
                out.frame.spec = std::string{clause->primary_text};
                break;
            }
            default:
                break;
        }
    }
    return true;
}

}  // namespace db25::plan
