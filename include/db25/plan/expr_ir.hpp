// DB25 Logical Plan - Owned, typed expression IR (Expr)
//
// This is the expression-layer vocabulary for the logical plan: an owned,
// typed expression node whose column leaves are *positional* (a flat ordinal
// into the owning operator's input schema, DuckDB `BoundReferenceExpression` /
// Calcite `RexInputRef` style). It is the target of `Binder::lower_expr`
// (see expr_lower.cpp), which reads the analyzer once and bakes type,
// nullability and slots into each node so the plan no longer round-trips to the
// analyzer nor borrows the parser arena for its semantics.
//
// Representation is a single tagged struct `Expr` discriminated by `ExprKind`,
// mirroring the `LogicalNode` idiom (one heap node per expr, owned via
// `unique_ptr`, switch-based visitors, no vtables / RTTI - clean under
// -fno-exceptions). See docs design memo "Owned, Typed Expression IR" for the
// full rationale and the locked decisions this file implements:
//   * `unique_ptr` per node;
//   * tagged struct + `ExprKind`;
//   * a `Subquery` Expr owns its `sub_plan` inline;
//   * correlated outer refs are a first-class `OuterRef{depth, input_index}`;
//   * parameters carry `Unknown`/`Any` + `param_index`;
//   * flat `input_index` (a Join's input schema is child0.output ++ child1.output);
//   * `switch(kind)` visitor + checked `as_*()` accessors.
//
// STATUS: purely additive vocabulary + lowering (migration steps 1-2). No
// operator payload is migrated yet; nothing here is used by the operator-
// building binder code, so the existing plan tests are unaffected.

#pragma once

#include "db25/plan/logical_plan.hpp"  // LogicalNode, LogicalNodePtr, SubqueryKind, Schema

#include "db25/ast/ast_node.hpp"
#include "db25/ast/node_types.hpp"

#include <cassert>
#include <cstdint>
#include <memory>
#include <string>
#include <variant>
#include <vector>

namespace db25::plan {

using ast::DataType;

// The expression kinds this IR can represent. `Subquery` folds scalar / IN /
// EXISTS (discriminated by `subquery_kind`); `OuterRef` is the first-class
// correlated outer-column reference (Calcite `RexCorrelVariable` style), kept
// distinct from `ColumnRef` so a future decorrelation pass has an explicit
// handle on correlation.
enum class ExprKind : std::uint8_t {
    ColumnRef,       // positional reference into the input schema (input_index)
    Literal,         // typed constant (LiteralValue)
    BinaryOp,        // {lhs, rhs}, bin_op
    UnaryOp,         // {operand}, un_op
    ScalarFunction,  // args..., func_name
    Aggregate,       // args..., func_name, distinct
    WindowFunction,  // args..., func_name, window (WindowSpecIR)
    Case,            // {when0, then0, ..., [else]}
    Cast,            // {operand}, target_type
    Between,         // {value, low, high}
    Like,            // {input, pattern[, escape]}
    IsNull,          // {operand}
    InList,          // {value, elem0, elem1, ...}
    Subquery,        // owns sub_plan; subquery_kind + correlated
    Parameter,       // ? / $n, param_index
    OuterRef,        // correlated outer reference: {outer_depth, input_index}
};

[[nodiscard]] const char* expr_kind_to_string(ExprKind kind) noexcept;

// NOT-flavor bits carried in Expr::expr_flags (NOT LIKE, IS NOT NULL, NOT IN,
// NOT EXISTS). A single "negated" bit suffices for the shapes we admit today.
enum ExprFlags : std::uint16_t {
    ExprFlagNegated = 0x0001,  // NOT LIKE / IS NOT NULL / NOT IN / NOT EXISTS
};

struct Expr;
using ExprPtr = std::unique_ptr<Expr>;

// A typed SQL literal value. The variant arms are the literal domains we admit;
// the owning Expr's `type` says which arm is live (an Interval literal is stored
// in the string arm with `type == DataType::Interval`). `monostate` is the NULL
// / unset literal. -fno-exceptions-clean (no throwing accessors are used).
struct LiteralValue {
    std::variant<std::monostate, std::int64_t, double, std::string, bool> value;

    [[nodiscard]] bool is_null() const noexcept {
        return std::holds_alternative<std::monostate>(value);
    }
};

// SortKeyIR (one owned ORDER BY key) is defined in logical_plan.hpp so it can be
// shared by the Sort operator payload and the window OVER clause below.

// A window frame specification (ROWS/RANGE ... ). Kept as best-effort text for
// now; the frame is not semantically consumed at this layer yet.
struct FrameIR {
    bool present = false;
    std::string spec;  // raw frame text, e.g. "ROWS BETWEEN ... "
};

// An owned lowering of the AST WindowSpec (the OVER (...) clause).
struct WindowSpecIR {
    std::vector<ExprPtr> partition_by;
    std::vector<SortKeyIR> order_by;
    FrameIR frame;
};

// Assignment (one owned UPDATE SET assignment) is defined in logical_plan.hpp
// alongside the other operator-payload helper structs it lives in.

// A single owned, typed expression node. `kind` selects which payload fields
// are meaningful (union-by-convention, the same discipline LogicalNode uses).
// `type` and `nullability` are carried on EVERY node.
struct Expr {
    ExprKind kind;
    DataType type = DataType::Unknown;
    std::uint8_t nullability = 0;       // parser 2-bit: 0 unknown / 1 not-null / 2 nullable
    std::vector<ExprPtr> children;      // operands (kind fixes arity/meaning)

    // Diagnostics-only back-pointer into the parse tree. NEVER dereferenced for
    // semantics (type / nullability / slots are all baked in); null on a cached
    // or serialized plan. See the design memo section 5.
    const ast::ASTNode* source = nullptr;

    // --- ColumnRef / OuterRef ---
    std::uint32_t input_index = 0;     // flat ordinal into the operator's input schema
    std::uint32_t ref_table_id = 0;    // provenance echo (diagnostics / re-resolve)
    std::uint32_t ref_column_id = 0;
    std::uint32_t outer_depth = 0;     // OuterRef only: 1 = immediately enclosing block

    // --- Literal ---
    LiteralValue value;

    // --- BinaryOp / UnaryOp ---
    ast::BinaryOp bin_op{};
    ast::UnaryOp un_op{};

    // --- ScalarFunction / Aggregate / WindowFunction ---
    std::string func_name;             // canonical (upper-cased) name
    bool distinct = false;             // Aggregate DISTINCT
    WindowSpecIR window;               // WindowFunction only

    // --- Cast ---
    DataType target_type = DataType::Unknown;  // == `type`, kept explicit

    // --- NOT-flavor bits (Like / IsNull / InList / Subquery) ---
    std::uint16_t expr_flags = 0;

    // --- Subquery ---
    SubqueryKind subquery_kind = SubqueryKind::Scalar;
    bool correlated = false;
    LogicalNodePtr sub_plan;           // OWNED bound inner plan

    // --- Parameter ---
    std::uint32_t param_index = 0;     // 1-based $n / positional ?

    explicit Expr(ExprKind k) : kind(k) {}

    [[nodiscard]] bool negated() const noexcept {
        return (expr_flags & ExprFlagNegated) != 0;
    }

    // ----- Checked accessors -----
    // Tagged-struct payload access is by-convention; these accessors assert the
    // node's kind (in debug builds) so mis-typed access is caught early, then
    // return the node so callers read the payload fields directly, e.g.
    // `e.as_column().input_index`. Under NDEBUG the assert compiles out.
    [[nodiscard]] Expr& as_column() noexcept { assert(kind == ExprKind::ColumnRef); return *this; }
    [[nodiscard]] const Expr& as_column() const noexcept { assert(kind == ExprKind::ColumnRef); return *this; }

    [[nodiscard]] Expr& as_outer_ref() noexcept { assert(kind == ExprKind::OuterRef); return *this; }
    [[nodiscard]] const Expr& as_outer_ref() const noexcept { assert(kind == ExprKind::OuterRef); return *this; }

    [[nodiscard]] Expr& as_literal() noexcept { assert(kind == ExprKind::Literal); return *this; }
    [[nodiscard]] const Expr& as_literal() const noexcept { assert(kind == ExprKind::Literal); return *this; }

    [[nodiscard]] Expr& as_binary() noexcept { assert(kind == ExprKind::BinaryOp); return *this; }
    [[nodiscard]] const Expr& as_binary() const noexcept { assert(kind == ExprKind::BinaryOp); return *this; }

    [[nodiscard]] Expr& as_unary() noexcept { assert(kind == ExprKind::UnaryOp); return *this; }
    [[nodiscard]] const Expr& as_unary() const noexcept { assert(kind == ExprKind::UnaryOp); return *this; }

    [[nodiscard]] Expr& as_function() noexcept {
        assert(kind == ExprKind::ScalarFunction || kind == ExprKind::Aggregate ||
               kind == ExprKind::WindowFunction);
        return *this;
    }
    [[nodiscard]] const Expr& as_function() const noexcept {
        assert(kind == ExprKind::ScalarFunction || kind == ExprKind::Aggregate ||
               kind == ExprKind::WindowFunction);
        return *this;
    }

    [[nodiscard]] Expr& as_cast() noexcept { assert(kind == ExprKind::Cast); return *this; }
    [[nodiscard]] const Expr& as_cast() const noexcept { assert(kind == ExprKind::Cast); return *this; }

    [[nodiscard]] Expr& as_subquery() noexcept { assert(kind == ExprKind::Subquery); return *this; }
    [[nodiscard]] const Expr& as_subquery() const noexcept { assert(kind == ExprKind::Subquery); return *this; }

    [[nodiscard]] Expr& as_parameter() noexcept { assert(kind == ExprKind::Parameter); return *this; }
    [[nodiscard]] const Expr& as_parameter() const noexcept { assert(kind == ExprKind::Parameter); return *this; }
};

// Pretty-print an expression as positional/typed IR (e.g. "(#2:Double > 100:Integer)")
// for debugging and test diagnostics.
[[nodiscard]] std::string dump_expr(const Expr& e);

}  // namespace db25::plan
