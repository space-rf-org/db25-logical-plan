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
//   * Expression payloads (predicates, projected expressions, group keys,
//     aggregates) are *borrowed* pointers into the parser-owned AST. The Parser
//     that produced the AST must therefore outlive the LogicalNode tree, exactly
//     as the Analyzer already requires.
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

// The relational-algebra operators this IR can represent. A LogicalNode's `op`
// selects which of the op-specific payload fields below are meaningful.
enum class LogicalOp : std::uint8_t {
    Scan,       // base-table access
    Filter,     // WHERE / HAVING predicate
    Project,    // SELECT list -> named output columns
    Join,       // binary join (INNER today; others scaffolded)
    Aggregate,  // GROUP BY + aggregate functions
    Sort,       // ORDER BY
    Limit,      // LIMIT / OFFSET
    SetOp,      // UNION / INTERSECT / EXCEPT (scaffold)
    Values,     // VALUES (row), (row), ... (scaffold)
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
    // Borrowed predicate expression subtree (WHERE condition, or a join's ON
    // condition). nullptr for a CROSS join or an unconditioned filter.
    const ast::ASTNode* predicate = nullptr;

    // --- Join payload ---
    ast::JoinType join_type = ast::JoinType::Inner;

    // --- Project payload ---
    // Borrowed SELECT-list expression nodes, parallel to `output`. A `Star`
    // item expands to several output columns, so exprs and output are only
    // 1:1 when no star was expanded (see is_star below).
    std::vector<const ast::ASTNode*> exprs;

    // --- Aggregate payload ---
    std::vector<const ast::ASTNode*> group_keys;   // GROUP BY expressions
    std::vector<const ast::ASTNode*> aggregates;   // aggregate call nodes

    // --- Limit payload ---
    bool has_limit = false;
    bool has_offset = false;
    std::int64_t limit = -1;   // meaningful when has_limit
    std::int64_t offset = 0;   // meaningful when has_offset

    // --- SetOp payload ---
    ast::SetOp set_op = ast::SetOp::Union;

    explicit LogicalNode(LogicalOp o) : op(o) {}

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
