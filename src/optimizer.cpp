// DB25 Logical Plan - Optimizer implementation
//
// See include/db25/plan/optimizer.hpp for the contract. Passes operate in place
// on the owned IR and must preserve observable results.

#include "db25/plan/optimizer.hpp"

#include "db25/plan/expr_ir.hpp"

#include <cstdint>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

namespace db25::plan {

namespace {

using ast::BinaryOp;
using ast::UnaryOp;

// ---- Literal value accessors ------------------------------------------------
// A folded operand is only ever a non-NULL numeric or boolean literal; these
// read the live variant arm (with integer -> double promotion for mixed
// arithmetic). std::string / monostate arms are never foldable and return false.

bool literal_i64(const LiteralValue& v, std::int64_t& out) {
    if (const auto* p = std::get_if<std::int64_t>(&v.value)) {
        out = *p;
        return true;
    }
    return false;
}

bool literal_f64(const LiteralValue& v, double& out) {
    if (const auto* d = std::get_if<double>(&v.value)) {
        out = *d;
        return true;
    }
    if (const auto* i = std::get_if<std::int64_t>(&v.value)) {
        out = static_cast<double>(*i);  // promote integer to double
        return true;
    }
    return false;
}

bool literal_bool(const LiteralValue& v, bool& out) {
    if (const auto* p = std::get_if<bool>(&v.value)) {
        out = *p;
        return true;
    }
    return false;
}

// ---- Constant folding of a single operator ----------------------------------

std::optional<LiteralValue> fold_binary(BinaryOp op, const LiteralValue& l,
                                        const LiteralValue& r) {
    // Conservative: only fold when BOTH operands are non-NULL literals, so we
    // never have to reason about SQL three-valued logic here.
    if (l.is_null() || r.is_null()) {
        return std::nullopt;
    }

    // Boolean connectives.
    if (op == BinaryOp::And || op == BinaryOp::Or) {
        bool lb = false;
        bool rb = false;
        if (literal_bool(l, lb) && literal_bool(r, rb)) {
            return LiteralValue{op == BinaryOp::And ? (lb && rb) : (lb || rb)};
        }
        return std::nullopt;
    }

    // Integer arithmetic / comparison (both operands integer). Arithmetic uses
    // checked builtins so a folded result never overflows (undefined) - on
    // overflow we simply leave the expression unfolded.
    std::int64_t li = 0;
    std::int64_t ri = 0;
    if (literal_i64(l, li) && literal_i64(r, ri)) {
        std::int64_t res = 0;
        switch (op) {
            case BinaryOp::Add:
                if (__builtin_add_overflow(li, ri, &res)) return std::nullopt;
                return LiteralValue{res};
            case BinaryOp::Subtract:
                if (__builtin_sub_overflow(li, ri, &res)) return std::nullopt;
                return LiteralValue{res};
            case BinaryOp::Multiply:
                if (__builtin_mul_overflow(li, ri, &res)) return std::nullopt;
                return LiteralValue{res};
            case BinaryOp::Divide:
                if (ri == 0) return std::nullopt;                 // preserve runtime error
                if (li == INT64_MIN && ri == -1) return std::nullopt;  // would overflow
                return LiteralValue{li / ri};
            case BinaryOp::Modulo:
                if (ri == 0) return std::nullopt;
                if (li == INT64_MIN && ri == -1) return std::nullopt;
                return LiteralValue{li % ri};
            case BinaryOp::Equal:        return LiteralValue{li == ri};
            case BinaryOp::NotEqual:     return LiteralValue{li != ri};
            case BinaryOp::LessThan:     return LiteralValue{li < ri};
            case BinaryOp::LessEqual:    return LiteralValue{li <= ri};
            case BinaryOp::GreaterThan:  return LiteralValue{li > ri};
            case BinaryOp::GreaterEqual: return LiteralValue{li >= ri};
            default:                     return std::nullopt;
        }
    }

    // Floating-point arithmetic / comparison (at least one operand is a double;
    // the other is promoted). Division by zero is left unfolded.
    double ld = 0.0;
    double rd = 0.0;
    if (literal_f64(l, ld) && literal_f64(r, rd)) {
        switch (op) {
            case BinaryOp::Add:          return LiteralValue{ld + rd};
            case BinaryOp::Subtract:     return LiteralValue{ld - rd};
            case BinaryOp::Multiply:     return LiteralValue{ld * rd};
            case BinaryOp::Divide:
                if (rd == 0.0) return std::nullopt;
                return LiteralValue{ld / rd};
            case BinaryOp::Equal:        return LiteralValue{ld == rd};
            case BinaryOp::NotEqual:     return LiteralValue{ld != rd};
            case BinaryOp::LessThan:     return LiteralValue{ld < rd};
            case BinaryOp::LessEqual:    return LiteralValue{ld <= rd};
            case BinaryOp::GreaterThan:  return LiteralValue{ld > rd};
            case BinaryOp::GreaterEqual: return LiteralValue{ld >= rd};
            default:                     return std::nullopt;
        }
    }

    return std::nullopt;
}

std::optional<LiteralValue> fold_unary(UnaryOp op, const LiteralValue& v) {
    if (v.is_null()) {
        return std::nullopt;
    }
    switch (op) {
        case UnaryOp::Negate: {
            std::int64_t i = 0;
            if (literal_i64(v, i)) {
                if (i == INT64_MIN) return std::nullopt;  // -INT64_MIN overflows
                return LiteralValue{-i};
            }
            double d = 0.0;
            if (std::holds_alternative<double>(v.value) && literal_f64(v, d)) {
                return LiteralValue{-d};
            }
            return std::nullopt;
        }
        case UnaryOp::Not: {
            bool b = false;
            if (literal_bool(v, b)) {
                return LiteralValue{!b};
            }
            return std::nullopt;
        }
        default:
            return std::nullopt;
    }
}

// Replace `e` with a folded literal that keeps the original expression's baked
// type (the analyzer already typed the whole sub-expression) and its diagnostics
// source pointer. The result is a non-NULL constant, hence not-null (nullability
// 1 in the parser 2-bit encoding).
ExprPtr make_folded_literal(LiteralValue value, const Expr& original) {
    auto lit = std::make_unique<Expr>(ExprKind::Literal);
    lit->type = original.type;
    lit->nullability = 1;
    lit->value = std::move(value);
    lit->source = original.source;
    return lit;
}

// A boolean-literal counterpart of make_folded_literal (for the AND / OR
// identities that reduce to a constant true / false).
ExprPtr make_bool_literal(bool v, const Expr& original) {
    LiteralValue value;
    value.value = v;
    return make_folded_literal(std::move(value), original);
}

// Read a boolean-literal expression's value; false for any non-boolean-literal.
bool literal_bool_expr(const Expr& e, bool& out) {
    if (e.kind == ExprKind::Literal) {
        if (const auto* p = std::get_if<bool>(&e.value.value)) {
            out = *p;
            return true;
        }
    }
    return false;
}

// Apply `fn` (an `ExprPtr&` transform) to every owned top-level expression
// payload of `node`. The single place the operator payloads are enumerated, so a
// pass never silently misses one (and a future payload is added here once).
template <typename Fn>
void for_each_payload_expr(LogicalNode* node, Fn&& fn) {
    fn(node->predicate);
    for (auto& e : node->exprs) fn(e);
    for (auto& e : node->group_keys) fn(e);
    for (auto& e : node->aggregates) fn(e);
    for (auto& e : node->window_functions) fn(e);
    for (auto& k : node->sort_keys) fn(k.expr);
    for (auto& row : node->value_rows) {
        for (auto& e : row) fn(e);
    }
    for (auto& a : node->assignments) fn(a.value);
}

// Fold constants within an owned expression tree (bottom-up), including the
// expressions of a window spec and the sub-plan of an embedded subquery.
void fold_expr(ExprPtr& e) {
    if (!e) {
        return;
    }
    for (auto& child : e->children) {
        fold_expr(child);
    }
    if (e->kind == ExprKind::WindowFunction) {
        for (auto& p : e->window.partition_by) {
            fold_expr(p);
        }
        for (auto& k : e->window.order_by) {
            fold_expr(k.expr);
        }
    }
    if (e->kind == ExprKind::Subquery && e->sub_plan) {
        fold_constants(e->sub_plan.get());
    }

    // With children folded, try to fold this node.
    if (e->kind == ExprKind::BinaryOp && e->children.size() == 2 &&
        e->children[0]->kind == ExprKind::Literal &&
        e->children[1]->kind == ExprKind::Literal) {
        if (auto v = fold_binary(e->bin_op, e->children[0]->value, e->children[1]->value)) {
            e = make_folded_literal(std::move(*v), *e);
        }
    } else if (e->kind == ExprKind::UnaryOp && e->children.size() == 1 &&
               e->children[0]->kind == ExprKind::Literal) {
        if (auto v = fold_unary(e->un_op, e->children[0]->value)) {
            e = make_folded_literal(std::move(*v), *e);
        }
    }
}

// Simplify boolean connectives within an owned expression tree (bottom-up),
// including window-spec expressions and embedded subquery sub-plans.
//
// The AND / OR identities are valid under SQL three-valued logic even when the
// surviving operand is NULL: `x AND false` is false and `x OR true` is true for
// x in {true, false, NULL}; `x AND true` and `x OR false` equal x in all three
// cases. Dropping the eliminated operand is sound because it cannot affect the
// result (short-circuit is not observable in a WHERE-style predicate).
void simplify_expr(ExprPtr& e) {
    if (!e) {
        return;
    }
    for (auto& child : e->children) {
        simplify_expr(child);
    }
    if (e->kind == ExprKind::WindowFunction) {
        for (auto& p : e->window.partition_by) {
            simplify_expr(p);
        }
        for (auto& k : e->window.order_by) {
            simplify_expr(k.expr);
        }
    }
    if (e->kind == ExprKind::Subquery && e->sub_plan) {
        simplify_booleans(e->sub_plan.get());
    }

    if (e->kind == ExprKind::BinaryOp && e->children.size() == 2 &&
        (e->bin_op == BinaryOp::And || e->bin_op == BinaryOp::Or)) {
        bool lv = false;
        bool rv = false;
        const bool l_is = literal_bool_expr(*e->children[0], lv);
        const bool r_is = literal_bool_expr(*e->children[1], rv);
        if (e->bin_op == BinaryOp::And) {
            if ((l_is && !lv) || (r_is && !rv)) {        // x AND false -> false
                e = make_bool_literal(false, *e);
            } else if (l_is && lv) {                     // true AND x -> x
                ExprPtr kept = std::move(e->children[1]);
                e = std::move(kept);
            } else if (r_is && rv) {                     // x AND true -> x
                ExprPtr kept = std::move(e->children[0]);
                e = std::move(kept);
            }
        } else {  // Or
            if ((l_is && lv) || (r_is && rv)) {          // x OR true -> true
                e = make_bool_literal(true, *e);
            } else if (l_is && !lv) {                    // false OR x -> x
                ExprPtr kept = std::move(e->children[1]);
                e = std::move(kept);
            } else if (r_is && !rv) {                    // x OR false -> x
                ExprPtr kept = std::move(e->children[0]);
                e = std::move(kept);
            }
        }
    } else if (e->kind == ExprKind::UnaryOp && e->un_op == UnaryOp::Not &&
               e->children.size() == 1 &&
               e->children[0]->kind == ExprKind::UnaryOp &&
               e->children[0]->un_op == UnaryOp::Not &&
               e->children[0]->children.size() == 1) {
        ExprPtr inner = std::move(e->children[0]->children[0]);  // NOT (NOT x) -> x
        e = std::move(inner);
    }
}

// ---- Predicate pushdown helpers ---------------------------------------------

// Flatten a predicate's top-level AND chain into individual conjuncts, taking
// ownership of `e`. `a AND b AND c` -> [a, b, c]; a non-AND -> [itself].
void collect_conjuncts(ExprPtr e, std::vector<ExprPtr>& out) {
    if (e && e->kind == ExprKind::BinaryOp && e->bin_op == BinaryOp::And &&
        e->children.size() == 2) {
        collect_conjuncts(std::move(e->children[0]), out);
        collect_conjuncts(std::move(e->children[1]), out);
    } else {
        out.push_back(std::move(e));
    }
}

// Re-AND a list of conjuncts into one predicate (left-deep), consuming `parts`.
// Returns null for an empty list.
ExprPtr combine_conjuncts(std::vector<ExprPtr>& parts) {
    if (parts.empty()) {
        return nullptr;
    }
    ExprPtr acc = std::move(parts[0]);
    for (std::size_t i = 1; i < parts.size(); ++i) {
        auto conj = std::make_unique<Expr>(ExprKind::BinaryOp);
        conj->bin_op = BinaryOp::And;
        conj->type = ast::DataType::Boolean;
        // AND is nullable if either operand is; not-null only if both are.
        const std::uint8_t ln = acc->nullability;
        const std::uint8_t rn = parts[i]->nullability;
        conj->nullability = (ln == 2 || rn == 2) ? 2 : ((ln == 1 && rn == 1) ? 1 : 0);
        conj->children.push_back(std::move(acc));
        conj->children.push_back(std::move(parts[i]));
        acc = std::move(conj);
    }
    return acc;
}

// Which join inputs a conjunct references, and whether it is safe to push.
struct RefInfo {
    bool refs_left = false;
    bool refs_right = false;
    bool any = false;       // references at least one join column
    bool pushable = true;   // false if it carries an OuterRef or a Subquery
};

// Classify the column references of `e` relative to a join whose left input has
// `left_width` columns (join output = left.output ++ right.output).
void scan_refs(const Expr& e, std::uint32_t left_width, RefInfo& info) {
    if (e.kind == ExprKind::ColumnRef) {
        info.any = true;
        if (e.input_index < left_width) {
            info.refs_left = true;
        } else {
            info.refs_right = true;
        }
    } else if (e.kind == ExprKind::OuterRef || e.kind == ExprKind::Subquery) {
        // A correlated reference or an embedded subquery must not be relocated.
        info.pushable = false;
        return;
    }
    for (const auto& c : e.children) {
        scan_refs(*c, left_width, info);
    }
}

// Shift every positional column slot in `e` down by `delta` (used when a
// right-only conjunct moves from the join output frame into the right input
// frame). Right-only pushable conjuncts contain no OuterRef / Subquery.
void remap_slots(Expr& e, std::uint32_t delta) {
    if (e.kind == ExprKind::ColumnRef) {
        e.input_index -= delta;
    }
    for (auto& c : e.children) {
        remap_slots(*c, delta);
    }
}

// Wrap `child` in a schema-preserving Filter carrying `pred`.
LogicalNodePtr make_filter(LogicalNodePtr child, ExprPtr pred) {
    auto filter = std::make_unique<LogicalNode>(LogicalOp::Filter);
    filter->output = child->output;
    filter->predicate = std::move(pred);
    filter->add_child(std::move(child));
    return filter;
}

// Recurse predicate pushdown into every embedded subquery sub-plan of `e`.
void push_down_in_expr(ExprPtr& e) {
    if (!e) {
        return;
    }
    if (e->kind == ExprKind::Subquery && e->sub_plan) {
        push_down_filters(e->sub_plan);
    }
    for (auto& c : e->children) {
        push_down_in_expr(c);
    }
    if (e->kind == ExprKind::WindowFunction) {
        for (auto& p : e->window.partition_by) push_down_in_expr(p);
        for (auto& k : e->window.order_by) push_down_in_expr(k.expr);
    }
}

// Split `filter_node`'s predicate and push each single-side conjunct into the
// corresponding input of the INNER / CROSS Join beneath it. `filter_node` is
// replaced by the bare Join if every conjunct is pushed.
void push_filter_into_join(LogicalNodePtr& filter_node) {
    if (!filter_node->predicate) {
        return;  // an unconditioned Filter has nothing to split (defensive).
    }
    LogicalNode* join = filter_node->child(0);
    const auto left_width = static_cast<std::uint32_t>(join->child(0)->output.size());
    // A right-only conjunct can only be re-based by subtracting left_width when
    // the join output is the plain concatenation left ++ right. A USING join
    // drops the merged right duplicates, compacting the right frame, so right
    // pushdown is disabled there (left pushdown stays valid - the left frame is
    // always the unmodified prefix).
    const bool full_concat =
        join->output.size() == left_width + join->child(1)->output.size();

    std::vector<ExprPtr> conjuncts;
    collect_conjuncts(std::move(filter_node->predicate), conjuncts);

    std::vector<ExprPtr> left_push;
    std::vector<ExprPtr> right_push;
    std::vector<ExprPtr> stay;
    for (auto& c : conjuncts) {
        RefInfo info;
        scan_refs(*c, left_width, info);
        if (info.pushable && info.any && info.refs_left && !info.refs_right) {
            left_push.push_back(std::move(c));
        } else if (info.pushable && info.any && info.refs_right && !info.refs_left &&
                   full_concat) {
            right_push.push_back(std::move(c));
        } else {
            stay.push_back(std::move(c));
        }
    }

    if (!left_push.empty()) {
        ExprPtr pred = combine_conjuncts(left_push);
        join->children[0] = make_filter(std::move(join->children[0]), std::move(pred));
    }
    if (!right_push.empty()) {
        for (auto& c : right_push) {
            remap_slots(*c, left_width);
        }
        ExprPtr pred = combine_conjuncts(right_push);
        join->children[1] = make_filter(std::move(join->children[1]), std::move(pred));
    }

    if (stay.empty()) {
        LogicalNodePtr kept = std::move(filter_node->children[0]);  // the Join
        filter_node = std::move(kept);
    } else {
        filter_node->predicate = combine_conjuncts(stay);
    }
}

}  // namespace

void fold_constants(LogicalNode* node) {
    if (node == nullptr) {
        return;
    }
    for_each_payload_expr(node, [](ExprPtr& e) { fold_expr(e); });
    for (auto& child : node->children) {
        fold_constants(child.get());
    }
}

void simplify_booleans(LogicalNode* node) {
    if (node == nullptr) {
        return;
    }
    for_each_payload_expr(node, [](ExprPtr& e) { simplify_expr(e); });
    for (auto& child : node->children) {
        simplify_booleans(child.get());
    }
}

void push_down_filters(LogicalNodePtr& node) {
    if (!node) {
        return;
    }
    // Bottom-up: settle children and embedded subquery sub-plans first.
    for (auto& child : node->children) {
        push_down_filters(child);
    }
    for_each_payload_expr(node.get(), [](ExprPtr& e) { push_down_in_expr(e); });

    // Merge a Filter directly over a Filter into one (conjoined) Filter.
    while (node->op == LogicalOp::Filter && node->child_count() == 1 &&
           node->child(0)->op == LogicalOp::Filter) {
        LogicalNode* inner = node->child(0);
        std::vector<ExprPtr> parts;
        collect_conjuncts(std::move(node->predicate), parts);
        collect_conjuncts(std::move(inner->predicate), parts);
        node->predicate = combine_conjuncts(parts);
        node->children[0] = std::move(inner->children[0]);
    }

    // Drop a Filter whose predicate simplified to constant TRUE.
    if (node->op == LogicalOp::Filter && node->child_count() == 1 && node->predicate &&
        node->predicate->kind == ExprKind::Literal) {
        const bool* b = std::get_if<bool>(&node->predicate->value.value);
        if (b != nullptr && *b) {
            LogicalNodePtr kept = std::move(node->children[0]);
            node = std::move(kept);
            return;
        }
    }

    // Push conjuncts below an INNER / CROSS Join.
    if (node->op == LogicalOp::Filter && node->child_count() == 1 &&
        node->child(0)->op == LogicalOp::Join &&
        (node->child(0)->join_type == ast::JoinType::Inner ||
         node->child(0)->join_type == ast::JoinType::Cross)) {
        push_filter_into_join(node);
    }
}

LogicalNodePtr optimize(LogicalNodePtr plan) {
    if (plan) {
        // Fold first so a folded `1 = 1` -> `true` feeds the boolean identities;
        // simplify next so a reduced predicate feeds pushdown; then push filters.
        fold_constants(plan.get());
        simplify_booleans(plan.get());
        push_down_filters(plan);
    }
    return plan;
}

}  // namespace db25::plan
