// DB25 Logical Plan - Optimizer implementation
//
// See include/db25/plan/optimizer.hpp for the contract. Passes operate in place
// on the owned IR and must preserve observable results.

#include "db25/plan/optimizer.hpp"

#include "db25/plan/expr_ir.hpp"

#include <algorithm>
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

// ---- Column pruning helpers -------------------------------------------------

// Mark every input slot an expression reads into `used` (sized to the operator's
// input width) and flag an embedded subquery. OuterRef is intentionally ignored:
// it references an enclosing query block, not this operator's input. A subquery's
// own sub-plan is not descended (it is a separate block pruned on its own).
void collect_slots(const Expr& e, std::vector<bool>& used, bool& has_subquery) {
    if (e.kind == ExprKind::ColumnRef) {
        if (e.input_index < used.size()) {
            used[e.input_index] = true;
        }
    } else if (e.kind == ExprKind::Subquery) {
        has_subquery = true;
    }
    for (const auto& c : e.children) {
        collect_slots(*c, used, has_subquery);
    }
    if (e.kind == ExprKind::WindowFunction) {
        for (const auto& p : e.window.partition_by) collect_slots(*p, used, has_subquery);
        for (const auto& k : e.window.order_by) collect_slots(*k.expr, used, has_subquery);
    }
}

// Rewrite each positional column slot in `e` through `remap` (old index -> new
// index; a kept slot is always >= 0). OuterRef and subquery sub-plans are left
// untouched (they belong to other schemas).
void remap_expr_slots(Expr& e, const std::vector<int>& remap) {
    if (e.kind == ExprKind::ColumnRef && e.input_index < remap.size() &&
        remap[e.input_index] >= 0) {
        e.input_index = static_cast<std::uint32_t>(remap[e.input_index]);
    }
    for (auto& c : e.children) {
        remap_expr_slots(*c, remap);
    }
    if (e.kind == ExprKind::WindowFunction) {
        for (auto& p : e.window.partition_by) remap_expr_slots(*p, remap);
        for (auto& k : e.window.order_by) remap_expr_slots(*k.expr, remap);
    }
}

// old-index -> new-index remap that keeps the `required` slots in order.
std::vector<int> compact_required(const std::vector<bool>& required) {
    std::vector<int> remap(required.size(), -1);
    int next = 0;
    for (std::size_t i = 0; i < required.size(); ++i) {
        if (required[i]) {
            remap[i] = next++;
        }
    }
    return remap;
}

// Rewrite a schema to keep only the remapped columns, placing each surviving
// column at its new index.
void apply_output_remap(Schema& out, const std::vector<int>& remap) {
    int new_size = 0;
    for (int v : remap) {
        new_size = std::max(new_size, v + 1);
    }
    Schema pruned(static_cast<std::size_t>(new_size));
    for (std::size_t old = 0; old < remap.size() && old < out.size(); ++old) {
        if (remap[old] >= 0) {
            pruned[static_cast<std::size_t>(remap[old])] = std::move(out[old]);
        }
    }
    out = std::move(pruned);
}

// An identity remap over `n` slots (nothing dropped or moved).
std::vector<int> identity_remap(std::size_t n) {
    std::vector<int> remap(n);
    for (std::size_t i = 0; i < n; ++i) {
        remap[i] = static_cast<int>(i);
    }
    return remap;
}

// Recursively prune every embedded subquery sub-plan of an expression, as an
// independent query block (its correlated OuterRefs resolve against enclosing
// inputs, which are kept intact because a subquery-bearing operator is a pruning
// barrier). Forward-declared: it drives the public prune_columns.
void prune_subplans_in_expr(ExprPtr& e);

// Prune `node`'s columns so it produces only the slots flagged in `required`
// (sized to the node's current output), returning the old-index -> new-index
// remap the parent uses to rewrite its references. Recurses into children with
// their computed requirements. In place.
std::vector<int> prune(LogicalNodePtr& node, const std::vector<bool>& required) {
    const std::size_t out_w = node->output.size();

    switch (node->op) {
        case LogicalOp::Scan: {
            std::vector<int> remap = compact_required(required);
            apply_output_remap(node->output, remap);
            return remap;
        }

        case LogicalOp::Project: {
            LogicalNode* child = node->child(0);
            std::vector<bool> child_req(child->output.size(), false);
            bool has_subquery = false;
            for (std::size_t i = 0; i < node->exprs.size(); ++i) {
                if (i < required.size() && required[i] && node->exprs[i]) {
                    collect_slots(*node->exprs[i], child_req, has_subquery);
                }
            }
            if (has_subquery) {
                std::fill(child_req.begin(), child_req.end(), true);
            }
            const std::vector<int> child_remap = prune(node->children[0], child_req);

            std::vector<ExprPtr> new_exprs;
            Schema new_out;
            std::vector<int> out_remap(out_w, -1);
            int next = 0;
            for (std::size_t i = 0; i < out_w; ++i) {
                if (required[i]) {
                    if (node->exprs[i]) {
                        remap_expr_slots(*node->exprs[i], child_remap);
                    }
                    new_exprs.push_back(std::move(node->exprs[i]));
                    new_out.push_back(std::move(node->output[i]));
                    out_remap[i] = next++;
                }
            }
            node->exprs = std::move(new_exprs);
            node->output = std::move(new_out);
            return out_remap;
        }

        case LogicalOp::Filter:
        case LogicalOp::Limit: {
            // True passthrough: output == child output (same width). (Distinct is
            // NOT here - its row multiplicity depends on all its input columns.)
            LogicalNode* child = node->child(0);
            std::vector<bool> child_req = required;
            child_req.resize(child->output.size(), false);
            bool has_subquery = false;
            if (node->predicate) {
                collect_slots(*node->predicate, child_req, has_subquery);
            }
            if (has_subquery) {
                std::fill(child_req.begin(), child_req.end(), true);
            }
            const std::vector<int> child_remap = prune(node->children[0], child_req);
            if (node->predicate) {
                remap_expr_slots(*node->predicate, child_remap);
            }
            node->output = node->child(0)->output;  // adopt the pruned child schema
            return child_remap;
        }

        case LogicalOp::Sort:
        case LogicalOp::Distinct:
        case LogicalOp::Window: {
            // These operators' output layout depends positionally on their child,
            // so they require ALL of their child's columns and keep their own
            // output intact:
            //   * Sort may hide sort-only columns (output narrower than child);
            //   * Distinct's row multiplicity depends on every input column;
            //   * Window passes the child schema through and appends one column
            //     per window function.
            // The child (typically a Project) still prunes the scan beneath it by
            // what its own expressions read, so pruning value is preserved. With
            // the child kept intact, child_remap is the identity, so remapping the
            // node's own expressions below is a no-op.
            LogicalNode* child = node->child(0);
            std::vector<bool> child_req(child->output.size(), true);
            const std::vector<int> child_remap = prune(node->children[0], child_req);
            for (auto& k : node->sort_keys) {
                if (k.expr) remap_expr_slots(*k.expr, child_remap);
            }
            for (auto& e : node->window_functions) {
                if (e) remap_expr_slots(*e, child_remap);
            }
            return identity_remap(out_w);
        }

        case LogicalOp::Join: {
            LogicalNode* left = node->child(0);
            LogicalNode* right = node->child(1);
            const std::size_t lw = left->output.size();
            // Only a plain-concatenation join (output == left ++ right) has a
            // right frame whose input index is `output_slot - lw`. A USING /
            // NATURAL join drops the merged right duplicates, compacting the
            // right frame, so that arithmetic would mis-index; treat such a join
            // as a barrier (prune nothing here) rather than corrupt slots.
            if (node->output.size() != lw + right->output.size()) {
                return identity_remap(out_w);
            }
            std::vector<bool> lreq(lw, false);
            std::vector<bool> rreq(right->output.size(), false);
            for (std::size_t i = 0; i < out_w; ++i) {
                if (required[i]) {
                    (i < lw ? lreq[i] : rreq[i - lw]) = true;
                }
            }
            bool has_subquery = false;
            if (node->predicate) {
                std::vector<bool> pref(out_w, false);
                collect_slots(*node->predicate, pref, has_subquery);
                for (std::size_t i = 0; i < out_w; ++i) {
                    if (pref[i]) {
                        (i < lw ? lreq[i] : rreq[i - lw]) = true;
                    }
                }
            }
            if (has_subquery) {
                std::fill(lreq.begin(), lreq.end(), true);
                std::fill(rreq.begin(), rreq.end(), true);
            }
            const std::vector<int> lrm = prune(node->children[0], lreq);
            const std::vector<int> rrm = prune(node->children[1], rreq);
            const std::size_t new_lw = node->child(0)->output.size();

            std::vector<int> out_remap(out_w, -1);
            for (std::size_t i = 0; i < lw; ++i) {
                if (lrm[i] >= 0) {
                    out_remap[i] = lrm[i];
                }
            }
            for (std::size_t i = lw; i < out_w; ++i) {
                if (rrm[i - lw] >= 0) {
                    out_remap[i] = static_cast<int>(new_lw) + rrm[i - lw];
                }
            }
            if (node->predicate) {
                remap_expr_slots(*node->predicate, out_remap);
            }
            apply_output_remap(node->output, out_remap);
            return out_remap;
        }

        case LogicalOp::SemiJoin:
        case LogicalOp::AntiJoin: {
            // A semi / anti join's output is exactly its LEFT input's schema (the
            // right side contributes no columns, only the existence test). So the
            // output slots map 1:1 to the left input, and the right input is
            // needed ONLY for the columns its join condition references - typically
            // just the correlation key, which lets the whole rest of the right
            // relation be pruned away.
            LogicalNode* left = node->child(0);
            LogicalNode* right = node->child(1);
            const std::size_t lw = left->output.size();
            const std::size_t rw = right->output.size();
            if (node->output.size() != lw) {
                return identity_remap(out_w);  // defensive: unexpected shape
            }
            std::vector<bool> lreq(lw, false);
            std::vector<bool> rreq(rw, false);
            // Parent-required output columns are left columns at the same index.
            for (std::size_t i = 0; i < out_w; ++i) {
                if (required[i]) {
                    lreq[i] = true;
                }
            }
            // The join condition spans the left ++ right frame.
            bool has_subquery = false;
            if (node->predicate) {
                std::vector<bool> pref(lw + rw, false);
                collect_slots(*node->predicate, pref, has_subquery);
                for (std::size_t i = 0; i < lw; ++i) {
                    if (pref[i]) lreq[i] = true;
                }
                for (std::size_t j = 0; j < rw; ++j) {
                    if (pref[lw + j]) rreq[j] = true;
                }
            }
            if (has_subquery) {
                std::fill(lreq.begin(), lreq.end(), true);
                std::fill(rreq.begin(), rreq.end(), true);
            }
            const std::vector<int> lrm = prune(node->children[0], lreq);
            const std::vector<int> rrm = prune(node->children[1], rreq);
            const std::size_t new_lw = node->child(0)->output.size();

            // Remap the condition across the pruned left ++ right frame.
            if (node->predicate) {
                std::vector<int> pred_remap(lw + rw, -1);
                for (std::size_t i = 0; i < lw; ++i) {
                    pred_remap[i] = lrm[i];
                }
                for (std::size_t j = 0; j < rw; ++j) {
                    if (rrm[j] >= 0) {
                        pred_remap[lw + j] = static_cast<int>(new_lw) + rrm[j];
                    }
                }
                remap_expr_slots(*node->predicate, pred_remap);
            }
            // Output is the pruned left schema (same remap as the left input).
            std::vector<int> out_remap(out_w, -1);
            for (std::size_t i = 0; i < lw; ++i) {
                out_remap[i] = lrm[i];
            }
            apply_output_remap(node->output, out_remap);
            return out_remap;
        }

        case LogicalOp::Aggregate: {
            // The Aggregate output is a fresh, non-passthrough schema (group keys
            // + aggregate results), so keep it intact and prune the child by what
            // the grouping keys and aggregate calls read.
            LogicalNode* child = node->child(0);
            std::vector<bool> child_req(child->output.size(), false);
            bool has_subquery = false;
            for (auto& e : node->group_keys) if (e) collect_slots(*e, child_req, has_subquery);
            for (auto& e : node->aggregates) if (e) collect_slots(*e, child_req, has_subquery);
            if (has_subquery) {
                std::fill(child_req.begin(), child_req.end(), true);
            }
            const std::vector<int> child_remap = prune(node->children[0], child_req);
            for (auto& e : node->group_keys) if (e) remap_expr_slots(*e, child_remap);
            for (auto& e : node->aggregates) if (e) remap_expr_slots(*e, child_remap);
            return identity_remap(out_w);
        }

        default:
            // Conservative barrier (SetOp, Values, Insert / Update / Delete /
            // Returning): keep this node and its inputs intact. Column flow
            // through these operators is intricate (branch-arity matching, target
            // column mapping), so nothing below is pruned here.
            return identity_remap(out_w);
    }
}

void prune_all_subplans(LogicalNode* node);

// Prune every embedded subquery sub-plan reachable from an expression, each as
// its own query block.
void prune_subplans_in_expr(ExprPtr& e) {
    if (!e) {
        return;
    }
    if (e->kind == ExprKind::Subquery && e->sub_plan) {
        prune_columns(e->sub_plan);
    }
    for (auto& c : e->children) {
        prune_subplans_in_expr(c);
    }
    if (e->kind == ExprKind::WindowFunction) {
        for (auto& p : e->window.partition_by) prune_subplans_in_expr(p);
        for (auto& k : e->window.order_by) prune_subplans_in_expr(k.expr);
    }
}

// Walk the plan tree and prune each embedded subquery sub-plan independently.
void prune_all_subplans(LogicalNode* node) {
    if (node == nullptr) {
        return;
    }
    for_each_payload_expr(node, [](ExprPtr& e) { prune_subplans_in_expr(e); });
    for (auto& child : node->children) {
        prune_all_subplans(child.get());
    }
}

// ---- EXISTS decorrelation helpers -------------------------------------------

// True if an expression tree contains any correlated OuterRef (descends into a
// nested subquery's sub-plan too, so "no OuterRef anywhere below" is a strict
// safety check).
bool subtree_has_outer_ref(const LogicalNode* node);

bool expr_has_outer_ref(const Expr& e) {
    if (e.kind == ExprKind::OuterRef) {
        return true;
    }
    if (e.kind == ExprKind::Subquery && e.sub_plan && subtree_has_outer_ref(e.sub_plan.get())) {
        return true;
    }
    for (const auto& c : e.children) {
        if (expr_has_outer_ref(*c)) return true;
    }
    if (e.kind == ExprKind::WindowFunction) {
        for (const auto& p : e.window.partition_by) if (expr_has_outer_ref(*p)) return true;
        for (const auto& k : e.window.order_by) if (expr_has_outer_ref(*k.expr)) return true;
    }
    return false;
}

// True if `e` embeds any represented Subquery (at any depth in its operand
// tree). Used to keep the IN rewrite off expressions whose frame remap would
// have to reach into a nested sub-plan.
bool expr_has_subquery(const Expr& e) {
    if (e.kind == ExprKind::Subquery) {
        return true;
    }
    for (const auto& c : e.children) {
        if (expr_has_subquery(*c)) return true;
    }
    if (e.kind == ExprKind::WindowFunction) {
        for (const auto& p : e.window.partition_by) if (expr_has_subquery(*p)) return true;
        for (const auto& k : e.window.order_by) if (expr_has_subquery(*k.expr)) return true;
    }
    return false;
}

bool subtree_has_outer_ref(const LogicalNode* node) {
    if (node == nullptr) {
        return false;
    }
    auto check = [](const ExprPtr& e) { return e && expr_has_outer_ref(*e); };
    if (check(node->predicate)) return true;
    for (const auto& e : node->exprs) if (check(e)) return true;
    for (const auto& e : node->group_keys) if (check(e)) return true;
    for (const auto& e : node->aggregates) if (check(e)) return true;
    for (const auto& e : node->window_functions) if (check(e)) return true;
    for (const auto& k : node->sort_keys) if (check(k.expr)) return true;
    for (const auto& row : node->value_rows) for (const auto& e : row) if (check(e)) return true;
    for (const auto& a : node->assignments) if (check(a.value)) return true;
    for (const auto& c : node->children) if (subtree_has_outer_ref(c.get())) return true;
    return false;
}

// A correlation conjunct is safe to hoist into a join condition only if every
// OuterRef it carries is at depth 1 (references the immediately enclosing input)
// and it embeds no subquery.
bool can_rewrite_correlation(const Expr& e) {
    if (e.kind == ExprKind::OuterRef) {
        return e.outer_depth == 1;
    }
    if (e.kind == ExprKind::Subquery) {
        return false;
    }
    for (const auto& c : e.children) {
        if (!can_rewrite_correlation(*c)) return false;
    }
    return true;
}

// Rewrite a hoisted correlation conjunct into the semi-join's left ++ right
// frame: an OuterRef at depth 1 (a left column at input_index i) becomes a plain
// left ColumnRef #i; an inner ColumnRef #j (into the right relation) shifts to
// #(j + left_width). OuterRef and ColumnRef are leaves, so converting them in
// place without recursing is unambiguous.
void rewrite_correlation(Expr& e, std::uint32_t left_width) {
    switch (e.kind) {
        case ExprKind::OuterRef:
            e.kind = ExprKind::ColumnRef;  // now a left column at the same index
            e.outer_depth = 0;
            return;
        case ExprKind::ColumnRef:
            e.input_index += left_width;   // shift into the right frame
            return;
        default:
            for (auto& c : e.children) {
                rewrite_correlation(*c, left_width);
            }
            return;
    }
}

// Every top-level AND conjunct that carries a correlation (an OuterRef) must be
// hoistable into a join condition (all its OuterRefs depth 1, no embedded
// subquery). A conjunct without an OuterRef is a local filter and imposes no
// constraint. Read-only: used as a pre-transform gate.
bool correlation_hoistable(const Expr& e) {
    if (e.kind == ExprKind::BinaryOp && e.bin_op == BinaryOp::And &&
        e.children.size() == 2) {
        return correlation_hoistable(*e.children[0]) &&
               correlation_hoistable(*e.children[1]);
    }
    if (expr_has_outer_ref(e)) {
        return can_rewrite_correlation(e);
    }
    return true;
}

// If `filter_node` is a Filter whose entire predicate is a [NOT] EXISTS subquery
// of a handled shape, replace it with a Semi / Anti join. Otherwise leaves it
// unchanged (the subquery stays represented). Correlation is decided by the
// ACTUAL presence of OuterRefs in the subquery body, not the analyzer's
// immediate-level `correlated` flag (which misses skip-level correlation, where
// the only OuterRef lives in a deeper-nested subquery).
void try_decorrelate_exists_filter(LogicalNodePtr& filter_node) {
    Expr* subq = filter_node->predicate.get();
    if (!subq->sub_plan) {
        return;
    }
    const bool is_anti = subq->negated();

    // Peek past a leading Project (a semi/anti join ignores the projected value,
    // so a correlated projection inside EXISTS is irrelevant and discarded).
    LogicalNode* body = subq->sub_plan.get();
    if (body->op == LogicalOp::Project && body->child_count() == 1) {
        body = body->child(0);
    }

    // ---- Gate (no mutation) ----
    const bool correlated = subtree_has_outer_ref(body);
    if (correlated) {
        // Only `Project -> Filter(correlation [AND local]) -> relation`, with all
        // correlation confined to that one top Filter, every correlation conjunct
        // depth-1 and subquery-free, is handled. Anything else stays a subquery.
        if (body->op != LogicalOp::Filter || !body->predicate || body->child_count() != 1) {
            return;
        }
        if (subtree_has_outer_ref(body->child(0))) {
            return;  // correlation reaches below the top Filter.
        }
        if (!correlation_hoistable(*body->predicate)) {
            return;  // a correlation conjunct is not hoistable (deep ref / subquery).
        }
    }
    // else: body is provably OuterRef-free -> a genuine uncorrelated EXISTS.

    // ---- Commit (gate passed, no further bail) ----
    const auto left_width =
        static_cast<std::uint32_t>(filter_node->child(0)->output.size());
    LogicalNodePtr sub = std::move(subq->sub_plan);
    if (sub->op == LogicalOp::Project && sub->child_count() == 1) {
        sub = std::move(sub->children[0]);
    }

    LogicalNodePtr right;
    ExprPtr join_cond;
    if (correlated) {
        std::vector<ExprPtr> conjuncts;
        collect_conjuncts(std::move(sub->predicate), conjuncts);
        std::vector<ExprPtr> correlation;
        std::vector<ExprPtr> local;
        for (auto& c : conjuncts) {
            (expr_has_outer_ref(*c) ? correlation : local).push_back(std::move(c));
        }
        for (auto& c : correlation) {
            rewrite_correlation(*c, left_width);
        }
        join_cond = combine_conjuncts(correlation);
        if (local.empty()) {
            right = std::move(sub->children[0]);  // drop the now-empty Filter
        } else {
            sub->predicate = combine_conjuncts(local);  // reuse as the local Filter
            right = std::move(sub);
        }
    } else {
        right = std::move(sub);  // conditionless: the OuterRef-free relation as-is
    }

    LogicalNodePtr left = std::move(filter_node->children[0]);
    auto join = std::make_unique<LogicalNode>(is_anti ? LogicalOp::AntiJoin
                                                      : LogicalOp::SemiJoin);
    join->output = left->output;  // semi / anti join produces only the left schema
    join->predicate = std::move(join_cond);
    join->add_child(std::move(left));
    join->add_child(std::move(right));
    filter_node = std::move(join);
}

// True only if `op` is provably NOT NULL. A ColumnRef is judged by its column's
// schema nullability (the authoritative source); any other expression falls back
// to its baked 2-bit nullability (1 == not-null). Conservative: an "unknown"
// nullability answers false.
bool operand_not_null(const Expr& op, const Schema& left_schema) {
    if (op.kind == ExprKind::ColumnRef && op.input_index < left_schema.size()) {
        return !left_schema[op.input_index].nullable;
    }
    return op.nullability == 1;
}

// If `filter_node` is a Filter whose entire predicate is a `x [NOT] IN (subquery)`
// of a handled shape, replace it with a Semi / Anti join whose condition is the
// IN equality `x = <the subquery's projected column>` conjoined with any hoisted
// correlation. Otherwise leaves it unchanged (the subquery stays represented).
//
// Positive IN is rewritten to a SemiJoin unconditionally: in a Filter, a row is
// kept only when the predicate is TRUE, so the SQL distinction between IN being
// FALSE and being UNKNOWN (an unmatched value, a NULL on either side) collapses -
// both drop the row, exactly as an equi-SemiJoin does.
//
// NOT IN is rewritten to an AntiJoin ONLY when both the probe value and the
// subquery's projected column are provably NOT NULL. With a NULL anywhere, SQL
// NOT IN yields UNKNOWN (never TRUE) rather than the AntiJoin's "no match -> keep",
// so a nullable side is left as a represented subquery.
void try_decorrelate_in_filter(LogicalNodePtr& filter_node) {
    Expr* subq = filter_node->predicate.get();
    if (!subq->sub_plan || subq->children.empty()) {
        return;  // need both the inner plan and the probe value (children[0]).
    }
    // Only `Project(1 column) -> [Filter] -> relation` is handled. A row-valued
    // IN (multiple projected columns) or a set operation is left as a subquery.
    LogicalNode* proj = subq->sub_plan.get();
    if (proj->op != LogicalOp::Project || proj->child_count() != 1 ||
        proj->exprs.size() != 1 || !proj->exprs[0]) {
        return;
    }
    const Expr* projected = proj->exprs[0].get();
    if (expr_has_outer_ref(*projected) || expr_has_subquery(*projected)) {
        return;  // the projected value must map cleanly into the right frame.
    }

    const bool is_anti = subq->negated();
    LogicalNode* below = proj->child(0);

    // ---- Gate (no mutation) ----
    const bool correlated = subtree_has_outer_ref(proj);
    if (correlated) {
        // Correlation must live entirely in a single top Filter of hoistable
        // depth-1 comparisons (mirrors the EXISTS contract).
        if (below->op != LogicalOp::Filter || !below->predicate ||
            below->child_count() != 1) {
            return;
        }
        if (subtree_has_outer_ref(below->child(0))) {
            return;  // correlation reaches below the top Filter.
        }
        if (!correlation_hoistable(*below->predicate)) {
            return;  // a correlation conjunct is not hoistable (deep ref / subquery).
        }
    }
    if (is_anti) {
        // AntiJoin is only NOT-IN-equivalent when neither side can be NULL.
        if (!operand_not_null(*subq->children[0], filter_node->child(0)->output) ||
            proj->output.empty() || proj->output[0].nullable) {
            return;
        }
    }

    // ---- Commit (gate passed, no further bail) ----
    const auto left_width =
        static_cast<std::uint32_t>(filter_node->child(0)->output.size());

    LogicalNodePtr proj_owned = std::move(subq->sub_plan);
    ExprPtr probe = std::move(subq->children[0]);          // left frame, no remap
    ExprPtr projected_owned = std::move(proj_owned->exprs[0]);
    rewrite_correlation(*projected_owned, left_width);      // shift into the right frame

    auto in_eq = std::make_unique<Expr>(ExprKind::BinaryOp);
    in_eq->bin_op = BinaryOp::Equal;
    in_eq->type = ast::DataType::Boolean;
    in_eq->children.push_back(std::move(probe));
    in_eq->children.push_back(std::move(projected_owned));

    std::vector<ExprPtr> join_conjuncts;
    join_conjuncts.push_back(std::move(in_eq));

    LogicalNodePtr below_owned = std::move(proj_owned->children[0]);
    LogicalNodePtr right;
    if (below_owned->op == LogicalOp::Filter && below_owned->predicate &&
        below_owned->child_count() == 1) {
        std::vector<ExprPtr> conjuncts;
        collect_conjuncts(std::move(below_owned->predicate), conjuncts);
        std::vector<ExprPtr> local;
        for (auto& c : conjuncts) {
            if (expr_has_outer_ref(*c)) {
                rewrite_correlation(*c, left_width);
                join_conjuncts.push_back(std::move(c));
            } else {
                local.push_back(std::move(c));
            }
        }
        if (local.empty()) {
            right = std::move(below_owned->children[0]);  // drop the now-empty Filter
        } else {
            below_owned->predicate = combine_conjuncts(local);
            right = std::move(below_owned);
        }
    } else {
        right = std::move(below_owned);
    }

    LogicalNodePtr left = std::move(filter_node->children[0]);
    auto join = std::make_unique<LogicalNode>(is_anti ? LogicalOp::AntiJoin
                                                      : LogicalOp::SemiJoin);
    join->output = left->output;  // semi / anti join produces only the left schema
    join->predicate = combine_conjuncts(join_conjuncts);
    join->add_child(std::move(left));
    join->add_child(std::move(right));
    filter_node = std::move(join);
}

// Build a positional ColumnRef into the current operator frame.
ExprPtr make_column_ref(std::uint32_t index, ast::DataType type, std::uint8_t nullability) {
    auto e = std::make_unique<Expr>(ExprKind::ColumnRef);
    e->input_index = index;
    e->type = type;
    e->nullability = nullability;
    return e;
}

// An aggregate whose value over the EMPTY set is NULL, so a LEFT JOIN's
// non-match NULL reproduces the scalar subquery's result exactly. COUNT is
// deliberately excluded: it yields 0 (not NULL) over the empty set, which a bare
// LEFT JOIN cannot reproduce, so a COUNT scalar subquery is left represented.
bool aggregate_null_over_empty(const std::string& fn) {
    return fn == "SUM" || fn == "MIN" || fn == "MAX" || fn == "AVG";
}

// A single correlation conjunct is hoistable into a group-by / equi-join only if
// it is `<bare depth-1 OuterRef> = <outer-ref-free inner expr>` (either operand
// order). The inner side becomes a GROUP BY key; the outer side becomes the
// join's left key.
bool valid_equi_correlation(const Expr& c) {
    if (c.kind != ExprKind::BinaryOp || c.bin_op != BinaryOp::Equal ||
        c.children.size() != 2) {
        return false;
    }
    const Expr* a = c.children[0].get();
    const Expr* b = c.children[1].get();
    const Expr* outer = (a->kind == ExprKind::OuterRef) ? a
                       : (b->kind == ExprKind::OuterRef) ? b : nullptr;
    const Expr* innr = (a->kind == ExprKind::OuterRef) ? b
                      : (b->kind == ExprKind::OuterRef) ? a : nullptr;
    if (!outer || outer->outer_depth != 1) {
        return false;  // correlation not a bare depth-1 outer reference
    }
    return !expr_has_outer_ref(*innr);  // the other side must be pure inner
}

// Read-only: verify every correlated top-level AND conjunct of `pred` is a valid
// equi-correlation, counting them. A conjunct with no outer ref is a local
// filter and is unconstrained.
bool inspect_scalar_correlation(const Expr* pred, int& corr_count) {
    if (pred->kind == ExprKind::BinaryOp && pred->bin_op == BinaryOp::And &&
        pred->children.size() == 2) {
        return inspect_scalar_correlation(pred->children[0].get(), corr_count) &&
               inspect_scalar_correlation(pred->children[1].get(), corr_count);
    }
    if (expr_has_outer_ref(*pred)) {
        if (!valid_equi_correlation(*pred)) return false;
        ++corr_count;
    }
    return true;
}

// If `s` is a correlated aggregate scalar subquery of the handled shape, build a
// decorrelating LEFT JOIN under `proj` (left = proj's current child, right = the
// inner relation grouped by the correlation keys with the aggregate computed per
// group) and return the ColumnRef that replaces `s` in the projection. Returns
// null (no mutation) for any shape outside the contract, which is left as a
// represented subquery. Handled shape:
//   Project(one pass-through ColumnRef #0)
//     Aggregate group=() aggs=(one NULL-over-empty, outer-ref-free aggregate)
//       Filter(equi-correlation [AND local], every correlation a bare depth-1
//              OuterRef = inner expr, nothing correlated below the Filter)
//         relation
//
// The left child's columns keep their positions (they are the join's left
// input), so the projection's other expressions need no remap; only the new
// aggregate column is appended, at index W + n.
ExprPtr try_build_scalar_join(Expr* s, LogicalNode* proj) {
    if (!s->sub_plan) {
        return nullptr;
    }
    // Project must be a bare pass-through of the single aggregate column (#0).
    LogicalNode* inner_proj = s->sub_plan.get();
    if (inner_proj->op != LogicalOp::Project || inner_proj->child_count() != 1 ||
        inner_proj->exprs.size() != 1 || !inner_proj->exprs[0] ||
        inner_proj->exprs[0]->kind != ExprKind::ColumnRef ||
        inner_proj->exprs[0]->input_index != 0) {
        return nullptr;
    }
    LogicalNode* agg = inner_proj->child(0);
    if (agg->op != LogicalOp::Aggregate || !agg->group_keys.empty() ||
        agg->aggregates.size() != 1 || !agg->aggregates[0] || agg->child_count() != 1 ||
        agg->output.empty()) {
        return nullptr;
    }
    const Expr* agg_call = agg->aggregates[0].get();
    if (agg_call->kind != ExprKind::Aggregate ||
        !aggregate_null_over_empty(agg_call->func_name) || expr_has_outer_ref(*agg_call)) {
        return nullptr;
    }
    // Correlation must live entirely in a single Filter directly under the Aggregate.
    LogicalNode* filt = agg->child(0);
    if (filt->op != LogicalOp::Filter || !filt->predicate || filt->child_count() != 1) {
        return nullptr;
    }
    if (subtree_has_outer_ref(filt->child(0))) {
        return nullptr;  // correlation reaches below the correlation Filter.
    }
    int corr_count = 0;
    if (!inspect_scalar_correlation(filt->predicate.get(), corr_count) || corr_count == 0) {
        return nullptr;  // a correlation conjunct is not a hoistable equi-correlation.
    }

    // ---- Gate passed; commit (no further bail) ----
    const auto W = static_cast<std::uint32_t>(proj->children[0]->output.size());

    LogicalNodePtr inner_proj_owned = std::move(s->sub_plan);
    LogicalNodePtr agg_owned = std::move(inner_proj_owned->children[0]);
    LogicalNodePtr filt_owned = std::move(agg_owned->children[0]);
    LogicalNodePtr relation = std::move(filt_owned->children[0]);

    std::vector<ExprPtr> conjuncts;
    collect_conjuncts(std::move(filt_owned->predicate), conjuncts);
    std::vector<ExprPtr> group_keys;  // inner exprs, in the relation frame
    std::vector<ExprPtr> left_keys;   // outer columns, parallel to group_keys
    std::vector<ExprPtr> local_conj;
    for (auto& c : conjuncts) {
        if (!expr_has_outer_ref(*c)) {
            local_conj.push_back(std::move(c));
            continue;
        }
        const bool a_outer = c->children[0]->kind == ExprKind::OuterRef;
        ExprPtr outer = std::move(c->children[a_outer ? 0 : 1]);
        ExprPtr innr = std::move(c->children[a_outer ? 1 : 0]);
        left_keys.push_back(make_column_ref(outer->input_index, outer->type, outer->nullability));
        group_keys.push_back(std::move(innr));
    }
    const auto n = static_cast<std::uint32_t>(group_keys.size());

    // Grouped-inner Aggregate: group by the correlation keys, keep the aggregate.
    auto grouped = std::make_unique<LogicalNode>(LogicalOp::Aggregate);
    Schema g_out;
    for (const auto& gk : group_keys) {
        ColumnSchema cs;
        cs.type = gk->type;
        cs.nullable = gk->nullability != 1;
        g_out.push_back(cs);
    }
    g_out.push_back(agg_owned->output[0]);  // the aggregate column schema
    grouped->group_keys = std::move(group_keys);
    grouped->aggregates.push_back(std::move(agg_owned->aggregates[0]));
    grouped->output = std::move(g_out);
    if (local_conj.empty()) {
        grouped->add_child(std::move(relation));
    } else {
        auto lf = std::make_unique<LogicalNode>(LogicalOp::Filter);
        lf->output = relation->output;
        lf->predicate = combine_conjuncts(local_conj);
        lf->add_child(std::move(relation));
        grouped->add_child(std::move(lf));
    }

    // Join condition: left_key[i] = right group key at #(W + i).
    std::vector<ExprPtr> on;
    for (std::uint32_t i = 0; i < n; ++i) {
        auto rk = make_column_ref(W + i, grouped->output[i].type,
                                  grouped->output[i].nullable ? 2 : 1);
        auto eq = std::make_unique<Expr>(ExprKind::BinaryOp);
        eq->bin_op = BinaryOp::Equal;
        eq->type = ast::DataType::Boolean;
        eq->children.push_back(std::move(left_keys[i]));
        eq->children.push_back(std::move(rk));
        on.push_back(std::move(eq));
    }

    // LEFT JOIN: left keeps its column positions; the grouped right is appended
    // and its columns are nullable (a non-matching outer row gets NULLs).
    auto join = std::make_unique<LogicalNode>(LogicalOp::Join);
    join->join_type = ast::JoinType::Left;
    LogicalNodePtr left = std::move(proj->children[0]);
    join->output = left->output;
    for (const auto& col : grouped->output) {
        ColumnSchema c = col;
        c.nullable = true;
        join->output.push_back(c);
    }
    join->predicate = combine_conjuncts(on);
    join->add_child(std::move(left));
    join->add_child(std::move(grouped));
    proj->children[0] = std::move(join);

    // The aggregate value is the last appended column (#W + n); a non-match makes
    // it NULL, so the replacement column is nullable.
    return make_column_ref(W + n, s->type, 2);
}

// Rewrite the first handled correlated scalar subquery found anywhere within `e`
// (mutating `e` and wrapping `proj`'s child). Returns whether it rewrote one, so
// the caller can loop to catch several in one projected expression.
bool rewrite_scalar_subqueries(ExprPtr& e, LogicalNode* proj) {
    if (!e) {
        return false;
    }
    if (e->kind == ExprKind::Subquery && e->subquery_kind == SubqueryKind::Scalar &&
        e->sub_plan) {
        if (auto repl = try_build_scalar_join(e.get(), proj)) {
            e = std::move(repl);
            return true;
        }
        return false;
    }
    for (auto& c : e->children) {
        if (rewrite_scalar_subqueries(c, proj)) return true;
    }
    if (e->kind == ExprKind::WindowFunction) {
        for (auto& p : e->window.partition_by) if (rewrite_scalar_subqueries(p, proj)) return true;
        for (auto& k : e->window.order_by) if (rewrite_scalar_subqueries(k.expr, proj)) return true;
    }
    return false;
}

// Decorrelate correlated aggregate scalar subqueries in a Project's expressions.
void try_decorrelate_scalar_in_project(LogicalNode* proj) {
    if (proj->op != LogicalOp::Project || proj->child_count() != 1) {
        return;
    }
    for (auto& e : proj->exprs) {
        while (rewrite_scalar_subqueries(e, proj)) {
            // keep going: a single expression may hold several scalar subqueries.
        }
    }
}

void decorrelate_node(LogicalNodePtr& node);

// Recurse decorrelation into every embedded subquery sub-plan of an expression.
void decorrelate_in_expr(ExprPtr& e) {
    if (!e) {
        return;
    }
    if (e->kind == ExprKind::Subquery && e->sub_plan) {
        decorrelate_node(e->sub_plan);
    }
    for (auto& c : e->children) {
        decorrelate_in_expr(c);
    }
    if (e->kind == ExprKind::WindowFunction) {
        for (auto& p : e->window.partition_by) decorrelate_in_expr(p);
        for (auto& k : e->window.order_by) decorrelate_in_expr(k.expr);
    }
}

void decorrelate_node(LogicalNodePtr& node) {
    if (!node) {
        return;
    }
    for (auto& child : node->children) {
        decorrelate_node(child);
    }
    for_each_payload_expr(node.get(), [](ExprPtr& e) { decorrelate_in_expr(e); });

    if (node->op == LogicalOp::Project) {
        try_decorrelate_scalar_in_project(node.get());
    }

    if (node->op == LogicalOp::Filter && node->child_count() == 1 && node->predicate &&
        node->predicate->kind == ExprKind::Subquery) {
        if (node->predicate->subquery_kind == SubqueryKind::Exists) {
            try_decorrelate_exists_filter(node);
        } else if (node->predicate->subquery_kind == SubqueryKind::In) {
            try_decorrelate_in_filter(node);
        }
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
        // A conjunct pushed onto a join input that is ITSELF a join settles there
        // in this single bottom-up pass (that input was already visited). Re-run
        // pushdown on the join's inputs so the pushed filter cascades all the way
        // to a fixpoint - without this, optimize() is not idempotent (a second run
        // pushes the filter further). Each push moves filters strictly downward, so
        // the recursion terminates.
        LogicalNode* joined = (node->op == LogicalOp::Join) ? node.get() : node->child(0);
        if (joined != nullptr && joined->op == LogicalOp::Join) {
            for (auto& input : joined->children) {
                push_down_filters(input);
            }
        }
    }

    // Push a whole Filter below a Semi / Anti join into its LEFT input. The join's
    // output is exactly the left schema, so every conjunct references only left
    // columns (at the same indices) - no split or remap is needed, and moving the
    // filter is valid for both polarities: a semi/anti join only decides which
    // LEFT rows survive, so selecting on left columns before vs. after the join
    // yields the same rows. Recurse so the moved filter can push further.
    if (node->op == LogicalOp::Filter && node->child_count() == 1 && node->predicate &&
        (node->child(0)->op == LogicalOp::SemiJoin ||
         node->child(0)->op == LogicalOp::AntiJoin)) {
        LogicalNodePtr join = std::move(node->children[0]);
        join->children[0] =
            make_filter(std::move(join->children[0]), std::move(node->predicate));
        node = std::move(join);
        push_down_filters(node->children[0]);
    }
}

void prune_columns(LogicalNodePtr& node) {
    if (!node) {
        return;
    }
    // The root's full output is the query result, so nothing there is dropped.
    std::vector<bool> keep_all(node->output.size(), true);
    prune(node, keep_all);
    // Prune embedded subquery sub-plans as independent blocks.
    prune_all_subplans(node.get());
}

void decorrelate_exists(LogicalNodePtr& node) {
    decorrelate_node(node);
}

LogicalNodePtr optimize(LogicalNodePtr plan) {
    if (plan) {
        // Decorrelate first, so the later passes optimize the resulting joins;
        // fold so a folded `1 = 1` -> `true` feeds the boolean identities;
        // simplify next so a reduced predicate feeds pushdown; push filters so
        // they narrow inputs before pruning; then drop unreferenced columns.
        decorrelate_exists(plan);
        fold_constants(plan.get());
        simplify_booleans(plan.get());
        push_down_filters(plan);
        prune_columns(plan);
    }
    return plan;
}

}  // namespace db25::plan
