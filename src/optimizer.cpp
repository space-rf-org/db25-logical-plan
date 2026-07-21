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

}  // namespace

void fold_constants(LogicalNode* node) {
    if (node == nullptr) {
        return;
    }
    fold_expr(node->predicate);
    for (auto& e : node->exprs) fold_expr(e);
    for (auto& e : node->group_keys) fold_expr(e);
    for (auto& e : node->aggregates) fold_expr(e);
    for (auto& e : node->window_functions) fold_expr(e);
    for (auto& k : node->sort_keys) fold_expr(k.expr);
    for (auto& row : node->value_rows) {
        for (auto& e : row) fold_expr(e);
    }
    for (auto& a : node->assignments) fold_expr(a.value);
    for (auto& child : node->children) {
        fold_constants(child.get());
    }
}

LogicalNodePtr optimize(LogicalNodePtr plan) {
    if (plan) {
        fold_constants(plan.get());
    }
    return plan;
}

}  // namespace db25::plan
