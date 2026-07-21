// DB25 Logical Plan - Relational-algebra logical operator IR
//
// This is the next layer above the DB25 semantic analyzer: it lowers a
// parsed + analyzed SELECT AST into a tree of relational-algebra logical
// operators. The IR is intentionally small and execution-agnostic - it is the
// shared contract that a future optimizer / physical planner consumes.
//
// Design notes:
//   * Ownership is via std::unique_ptr children (a plain owning tree). No arena,
//     because logical plans are small and short-lived compared to the AST.
//   * Every node carries an explicit output schema (the columns it produces),
//     mirroring db25::semantic::ResolvedColumn so the shapes line up 1:1 with
//     what Analyzer::projection_of() reports.
//   * Expression payloads are being migrated, one operator at a time, from
//     *borrowed* AST pointers to the owned, typed Expr IR (see expr_ir.hpp).
//     Migrated payloads (currently: Filter / Join predicates) own their
//     expression trees outright and carry baked type / nullability / positional
//     column slots, so they no longer depend on the parser arena. Not-yet-
//     migrated payloads (projected expressions, group keys, aggregates, ...)
//     remain borrowed pointers into the parser-owned AST, which must therefore
//     still outlive the LogicalNode tree, exactly as the Analyzer requires.
//
// The build matches the rest of the stack: C++23, -fno-exceptions.

#pragma once

#include "db25/ast/ast_node.hpp"
#include "db25/ast/node_types.hpp"

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace db25::plan {

using ast::DataType;

// The owned, typed expression IR node (defined in expr_ir.hpp). Forward-declared
// here so migrated operator payloads can own Expr trees by `unique_ptr` without
// this header depending on the full expression vocabulary. LogicalNode's
// destructor is defined out-of-line (logical_plan.cpp, where Expr is complete).
struct Expr;
using ExprPtr = std::unique_ptr<Expr>;

// The relational-algebra operators this IR can represent. A LogicalNode's `op`
// selects which of the op-specific payload fields below are meaningful.
enum class LogicalOp : std::uint8_t {
    Scan,       // base-table access
    Filter,     // WHERE / HAVING predicate
    Project,    // SELECT list -> named output columns
    Join,       // binary join (INNER / OUTER / CROSS; USING columns merged)
    Aggregate,  // GROUP BY + aggregate functions
    Window,     // window functions (RANK/ROW_NUMBER/SUM(..) OVER (...)); sits
                // below Project, appends one output column per window function
    Distinct,   // SELECT DISTINCT: de-duplicate the child's rows (sits directly
                // above Project; schema-preserving)
    Sort,       // ORDER BY (with sort keys + directions)
    Limit,      // LIMIT / OFFSET
    SetOp,      // UNION [ALL] / INTERSECT / EXCEPT
    Values,     // VALUES (row), (row), ... (also the synthetic single row of a
                // FROM-less SELECT)
    Insert,     // INSERT INTO target <- child (Values / query source)
    Update,     // UPDATE target SET ... [WHERE] over a Scan / Filter child
    Delete,     // DELETE FROM target [WHERE] over a Scan / Filter child
    Returning,  // RETURNING projection on top of an Insert / Update / Delete
};

[[nodiscard]] const char* logical_op_to_string(LogicalOp op) noexcept;

// One output column of a logical operator. Field-for-field compatible with
// db25::semantic::ResolvedColumn, which is where most of these values originate.
struct ColumnSchema {
    std::string name;
    DataType type = DataType::Unknown;
    bool nullable = true;
    std::uint32_t table_id = 0;
    std::uint32_t column_id = 0;
};

using Schema = std::vector<ColumnSchema>;

// One ORDER BY key on a Sort node: a borrowed sort expression plus its
// direction and (optional) NULLS placement, decoded from the parser's flags.
struct SortKey {
    const ast::ASTNode* expr = nullptr;  // borrowed ORDER BY expression
    bool descending = false;             // ASC (false) / DESC (true)
    bool nulls_order_explicit = false;   // whether NULLS FIRST/LAST was written
    bool nulls_first = false;            // meaningful when nulls_order_explicit
};

struct LogicalNode;  // forward declaration for SubPlan

// How a subquery is used in the expression that owns it.
enum class SubqueryKind : std::uint8_t {
    Scalar,  // a scalar subquery: (SELECT ...) yielding a single value
    In,      // expr IN (SELECT ...)
    Exists,  // [NOT] EXISTS (SELECT ...)
};

// A subquery embedded in an expression (a SELECT-list item or a WHERE
// predicate), faithfully represented rather than dropped. `plan` is the bound
// inner query block; `expr` borrows the AST Subquery node it came from; and
// `correlated` records Analyzer::is_correlated for that subquery. Decorrelation
// of correlated subqueries is deliberately left to a later optimizer pass (TODO)
// - the binder only represents the subquery and its correlation status here.
struct SubPlan {
    const ast::ASTNode* expr = nullptr;         // borrowed Subquery AST node
    SubqueryKind kind = SubqueryKind::Scalar;   // how it is used
    bool correlated = false;                    // Analyzer::is_correlated(expr)
    std::unique_ptr<LogicalNode> plan;          // bound inner query sub-plan
};

// A node in the logical plan tree. Payload fields are grouped by the operator
// that uses them; a node only populates the fields relevant to its `op`.
struct LogicalNode {
    LogicalOp op;
    std::vector<std::unique_ptr<LogicalNode>> children;

    // The columns this operator produces, in order.
    Schema output;

    // --- Scan payload ---
    std::string table_name;  // base relation name
    std::string alias;       // correlation name, empty if none

    // --- Filter / Join payload ---
    // Owned, typed predicate expression (WHERE / HAVING condition, or a join's
    // ON condition), lowered against this node's input schema so its column
    // leaves are positional. Null for a CROSS join, a USING join, or an
    // unconditioned filter.
    ExprPtr predicate;

    // --- Join payload ---
    ast::JoinType join_type = ast::JoinType::Inner;

    // --- Project / Returning payload ---
    // Owned, typed projected expressions, one per output column (a `*` is
    // expanded to one positional ColumnRef per covered column, so `exprs` and
    // `output` are 1:1). For a Project over an Aggregate / Window child, an
    // item that names a precomputed group/aggregate/window output lowers to a
    // ColumnRef into that child column rather than a re-evaluated expression.
    std::vector<ExprPtr> exprs;

    // --- Aggregate payload ---
    // Owned, typed grouping keys and aggregate calls, each lowered against the
    // Aggregate's input (its child's output) schema. An aggregate call lowers to
    // an ExprKind::Aggregate node whose children are the (already positional)
    // argument expressions.
    std::vector<ExprPtr> group_keys;   // GROUP BY expressions
    std::vector<ExprPtr> aggregates;   // aggregate call expressions

    // --- Window payload ---
    // Owned, typed window-function expressions (each an ExprKind::WindowFunction
    // carrying its lowered arguments and an owned WindowSpecIR for the PARTITION
    // BY / ORDER BY / frame), lowered against this node's input schema. The
    // node's output is its child's schema with one appended column per window
    // function, in this order.
    std::vector<ExprPtr> window_functions;

    // --- Subquery payload (any node that owns expression subqueries) ---
    // Sub-plans for subqueries embedded in this node's expressions: scalar
    // subqueries in a Project's SELECT list, or IN / EXISTS subqueries in a
    // Filter's predicate.
    std::vector<SubPlan> subplans;

    // --- Sort payload ---
    std::vector<SortKey> sort_keys;   // ORDER BY keys, in order

    // --- Values payload ---
    // Each row is a list of borrowed value expressions. A FROM-less SELECT is
    // lowered over a single empty row (one row, zero columns).
    std::vector<std::vector<const ast::ASTNode*>> value_rows;

    // --- Limit payload ---
    bool has_limit = false;
    bool has_offset = false;
    std::int64_t limit = -1;   // meaningful when has_limit
    std::int64_t offset = 0;   // meaningful when has_offset

    // --- SetOp payload ---
    ast::SetOp set_op = ast::SetOp::Union;

    // --- DML payload (Insert / Update / Delete) ---
    // The target relation name is carried in `table_name`. For INSERT,
    // `target_columns` is the explicit target column list (empty = all columns
    // in declaration order). For UPDATE, `assignments` holds the borrowed SET
    // assignment nodes (each a BinaryExpr whose primary_text is the target
    // column and whose first child is the value expression).
    std::vector<std::string> target_columns;
    std::vector<const ast::ASTNode*> assignments;

    explicit LogicalNode(LogicalOp o) : op(o) {}

    // Out-of-line (defined in logical_plan.cpp) because `predicate` is an owning
    // unique_ptr to the forward-declared Expr; the destructor must be emitted
    // where Expr is a complete type. Moves are consequently not implicitly
    // declared, which is fine: LogicalNode is only ever held by unique_ptr.
    ~LogicalNode();

    [[nodiscard]] LogicalNode* child(std::size_t i) const {
        return i < children.size() ? children[i].get() : nullptr;
    }
    [[nodiscard]] std::size_t child_count() const noexcept { return children.size(); }

    void add_child(std::unique_ptr<LogicalNode> c) {
        children.push_back(std::move(c));
    }
};

using LogicalNodePtr = std::unique_ptr<LogicalNode>;

// Pretty-print a logical plan tree for debugging / test diagnostics.
[[nodiscard]] std::string dump_plan(const LogicalNode* root);

}  // namespace db25::plan
