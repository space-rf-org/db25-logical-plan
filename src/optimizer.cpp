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

LogicalNodePtr optimize(LogicalNodePtr plan) {
    if (plan) {
        // Fold first so a folded `1 = 1` -> `true` feeds the boolean identities.
        fold_constants(plan.get());
        simplify_booleans(plan.get());
    }
    return plan;
}

}  // namespace db25::plan
