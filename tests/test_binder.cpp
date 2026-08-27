// DB25 Logical Plan - Binder tests
//
// Self-contained harness (no gtest, so no network fetch and a clean
// -fno-exceptions build). Parses -> analyzes -> binds a handful of SELECT
// queries and asserts the logical tree shape and the Project output schema.

#include "db25/plan/binder.hpp"
#include "db25/plan/logical_plan.hpp"

#include "db25/parser/parser.hpp"
#include "db25/semantic/analyzer.hpp"
#include "db25/semantic/catalog.hpp"

#include <cstdint>
#include <functional>
#include <cstdio>
#include <string>
#include <string_view>
#include <variant>

using db25::ast::DataType;
using db25::ast::SetOp;
using db25::plan::Binder;
using db25::plan::BindResult;
using db25::plan::ColumnSchema;
using db25::plan::ExprKind;
using db25::plan::LogicalNode;
using db25::plan::LogicalOp;
using db25::plan::SubqueryKind;
using db25::semantic::Analyzer;
using db25::semantic::InMemoryCatalog;

namespace {

int g_checks = 0;
int g_failures = 0;

void check(bool cond, const std::string& what) {
    ++g_checks;
    if (!cond) {
        ++g_failures;
        std::printf("  FAIL: %s\n", what.c_str());
    }
}

InMemoryCatalog make_catalog() {
    InMemoryCatalog cat;
    cat.add_table("users", {
        {"id", DataType::Integer, false},
        {"name", DataType::VarChar, true},
    });
    cat.add_table("orders", {
        {"id", DataType::Integer, false},
        {"user_id", DataType::Integer, true},
        {"total", DataType::Double, true},
    });
    cat.add_table("emp", {
        {"id", DataType::Integer, false},
        {"dept", DataType::VarChar, true},
        {"sal", DataType::Double, true},
    });
    // All columns nullable: INSERT ... DEFAULT VALUES is well-formed here (no
    // NOT-NULL-without-default column to violate).
    cat.add_table("nn", {
        {"a", DataType::Integer, true},
        {"b", DataType::VarChar, true},
    });
    return cat;
}

// Bind a query and hand the plan to `body`. The Parser lives for the duration
// of the callback because the plan borrows AST-owned text.
template <typename F>
void with_plan(const InMemoryCatalog& cat, std::string_view sql, F&& body) {
    db25::parser::Parser parser;
    auto parsed = parser.parse(sql);
    check(parsed.has_value(), std::string{"parse: "} + std::string{sql});
    if (!parsed) {
        return;
    }
    Analyzer analyzer(cat);
    analyzer.analyze(parsed.value());
    check(!analyzer.has_errors(), std::string{"analyze clean: "} + std::string{sql});

    Binder binder(analyzer, cat);
    BindResult res = binder.bind(parsed.value());
    if (!res.ok) {
        check(false, std::string{"bind: "} + std::string{sql} + " -> " + res.error);
        return;
    }
    std::forward<F>(body)(res.root.get());
}

void expect_col(const ColumnSchema& c, std::string_view name, DataType type,
                bool nullable, const std::string& ctx) {
    check(c.name == name, ctx + ": name '" + c.name + "' == '" + std::string{name} + "'");
    check(c.type == type, ctx + ": type of '" + c.name + "'");
    check(c.nullable == nullable, ctx + ": nullability of '" + c.name + "'");
}

const LogicalNode* only_child(const LogicalNode* n) {
    return (n != nullptr && n->child_count() == 1) ? n->child(0) : nullptr;
}

// Assert a projected expression is a positional ColumnRef into slot `slot`.
void expect_col_ref(const db25::plan::ExprPtr& e, std::uint32_t slot,
                    const std::string& ctx) {
    check(e && e->kind == ExprKind::ColumnRef, ctx + ": is a ColumnRef");
    check(e && e->kind == ExprKind::ColumnRef && e->input_index == slot,
          ctx + ": input_index == " + std::to_string(slot));
}

// Assert an expression is an owned ExprKind::Subquery of the given kind and
// correlation, owning a bound inner Project sub-plan.
void expect_subquery(const db25::plan::Expr* e, SubqueryKind kind, bool correlated,
                     const std::string& ctx) {
    check(e && e->kind == ExprKind::Subquery, ctx + ": is a Subquery expr");
    if (e != nullptr && e->kind == ExprKind::Subquery) {
        check(e->subquery_kind == kind, ctx + ": subquery kind");
        check(e->correlated == correlated, ctx + ": correlation");
        check(e->sub_plan && e->sub_plan->op == LogicalOp::Project,
              ctx + ": sub_plan is a bound Project");
    }
}

// -------------------------------------------------------------------------

// Double-quoted (delimited) identifiers must resolve as ordinary columns end
// to end: the tokenizer delivers them as Identifier tokens with the bare inner
// text, so `"id"` binds to the same column as `id`. Previously `"id"` lexed as
// a string literal and could never be a column reference.
void test_delimited_identifiers(const InMemoryCatalog& cat) {
    std::printf("[test] delimited (double-quoted) identifiers\n");

    with_plan(cat, "SELECT \"id\", \"name\" FROM users", [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        check(root->output.size() == 2, "project has 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "id", DataType::Integer, false, "proj[0]");
            expect_col(root->output[1], "name", DataType::VarChar, true, "proj[1]");
        }
        // Both items lower to positional column refs into the users scan.
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "proj expr[0]");
            expect_col_ref(root->exprs[1], 1, "proj expr[1]");
        }
    });

    // A delimited identifier is usable in the WHERE clause too.
    with_plan(cat, "SELECT \"id\" FROM users WHERE \"id\" = 1", [](const LogicalNode* root) {
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        check(filter && filter->predicate &&
                  filter->predicate->kind == ExprKind::BinaryOp,
              "WHERE predicate is a BinaryOp");
        if (filter && filter->predicate &&
            filter->predicate->children.size() == 2) {
            check(filter->predicate->children[0]->kind == ExprKind::ColumnRef &&
                      filter->predicate->children[0]->input_index == 0,
                  "lhs is column ref #0 (id)");
        }
    });
}

// A single-quoted string literal must lower to its actual value, with each
// doubled '' collapsed to one '. `'it''s'` is the value `it's`, not `it''s` -
// the latter is a wrong-answer bug for any string containing an apostrophe.
void test_string_escape_unquote(const InMemoryCatalog& cat) {
    std::printf("[test] string literal '' escape collapses to one quote\n");

    auto check_literal = [&](const char* sql, const std::string& expected,
                             const std::string& ctx) {
        with_plan(cat, sql, [&](const LogicalNode* root) {
            const LogicalNode* proj =
                (root->op == LogicalOp::Project) ? root : only_child(root);
            check(proj && proj->op == LogicalOp::Project, ctx + ": has Project");
            if (!proj || proj->exprs.empty()) return;
            const auto& e = proj->exprs[0];
            check(e && e->kind == ExprKind::Literal, ctx + ": item is a literal");
            const auto* s = e ? std::get_if<std::string>(&e->value.value) : nullptr;
            check(s != nullptr, ctx + ": literal holds a string");
            check(s && *s == expected,
                  ctx + ": value '" + (s ? *s : std::string{"<none>"}) +
                      "' == '" + expected + "'");
        });
    };

    check_literal("SELECT 'it''s' FROM users", "it's", "it''s");
    check_literal("SELECT 'O''Brien' FROM users", "O'Brien", "O''Brien");
    check_literal("SELECT 'plain' FROM users", "plain", "plain");
    // Two adjacent escapes collapse independently.
    check_literal("SELECT 'a''''b' FROM users", "a''b", "a''''b");
}

// A CAST's type modifier - DECIMAL(precision, scale) or VARCHAR(length) - must
// survive into the plan. The parser captures the modifier text but the binder
// used to drop it, silently widening DECIMAL(10,2) to a bare DECIMAL. The Cast
// Expr now carries precision/scale (numeric) or length (char/varchar).
void test_cast_modifiers(const InMemoryCatalog& cat) {
    std::printf("[test] CAST type modifiers (precision/scale/length)\n");

    auto cast_of = [&](const LogicalNode* root) -> const db25::plan::Expr* {
        const LogicalNode* proj =
            (root->op == LogicalOp::Project) ? root : only_child(root);
        if (!proj || proj->op != LogicalOp::Project || proj->exprs.empty()) {
            return nullptr;
        }
        return proj->exprs[0].get();
    };

    with_plan(cat, "SELECT CAST(id AS DECIMAL(10,2)) FROM users",
              [&](const LogicalNode* root) {
        const db25::plan::Expr* e = cast_of(root);
        check(e && e->kind == ExprKind::Cast, "DECIMAL(10,2): is a Cast");
        check(e && e->target_type == DataType::Decimal, "DECIMAL(10,2): target Decimal");
        check(e && e->type_precision == 10, "DECIMAL(10,2): precision == 10");
        check(e && e->type_scale == 2, "DECIMAL(10,2): scale == 2");
    });

    with_plan(cat, "SELECT CAST(id AS DECIMAL(8)) FROM users",
              [&](const LogicalNode* root) {
        const db25::plan::Expr* e = cast_of(root);
        check(e && e->type_precision == 8, "DECIMAL(8): precision == 8");
        check(e && e->type_scale == 0, "DECIMAL(8): scale defaults to 0");
    });

    with_plan(cat, "SELECT CAST(name AS VARCHAR(5)) FROM users",
              [&](const LogicalNode* root) {
        const db25::plan::Expr* e = cast_of(root);
        check(e && e->target_type == DataType::VarChar, "VARCHAR(5): target VarChar");
        check(e && e->type_length == 5, "VARCHAR(5): length == 5");
    });

    // A bare type carries no modifier - fields stay 0 so sized vs unsized differ.
    with_plan(cat, "SELECT CAST(id AS BIGINT) FROM users",
              [&](const LogicalNode* root) {
        const db25::plan::Expr* e = cast_of(root);
        check(e && e->kind == ExprKind::Cast, "BIGINT: is a Cast");
        check(e && e->type_precision == 0 && e->type_scale == 0 &&
                  e->type_length == 0,
              "BIGINT: no modifier, all zero");
    });
}

// ARRAY[elem, ...] must lower instead of hard-failing at the binder. It is
// represented as a ScalarFunction named "ARRAY" (the same shape ROW(...) takes)
// whose type is DataType::Array and whose children are the lowered elements.
void test_array_constructor(const InMemoryCatalog& cat) {
    std::printf("[test] ARRAY[...] constructor lowering\n");

    auto item0 = [&](const LogicalNode* root) -> const db25::plan::Expr* {
        const LogicalNode* proj =
            (root->op == LogicalOp::Project) ? root : only_child(root);
        if (!proj || proj->op != LogicalOp::Project || proj->exprs.empty()) {
            return nullptr;
        }
        return proj->exprs[0].get();
    };

    with_plan(cat, "SELECT ARRAY[1, 2, 3] FROM users", [&](const LogicalNode* root) {
        const db25::plan::Expr* e = item0(root);
        check(e && e->kind == ExprKind::ScalarFunction, "ARRAY: is a ScalarFunction");
        check(e && e->func_name == "ARRAY", "ARRAY: func_name is ARRAY");
        check(e && e->type == DataType::Array, "ARRAY: typed Array");
        check(e && e->children.size() == 3, "ARRAY: 3 elements");
        if (e && e->children.size() == 3) {
            check(e->children[0]->kind == ExprKind::Literal, "ARRAY: elem 0 is a literal");
        }
    });

    // Elements can be column references (they resolve against the scan).
    with_plan(cat, "SELECT ARRAY[id, id] FROM users", [&](const LogicalNode* root) {
        const db25::plan::Expr* e = item0(root);
        check(e && e->kind == ExprKind::ScalarFunction && e->func_name == "ARRAY",
              "ARRAY[id,id]: ScalarFunction ARRAY");
        check(e && e->children.size() == 2 &&
                  e->children[0]->kind == ExprKind::ColumnRef,
              "ARRAY[id,id]: elements are column refs");
    });
}

// <value> COLLATE <name> must lower end to end (it used to drop the column and
// fail to analyze). It is a ScalarFunction "COLLATE" whose first child is the
// value and whose second child is a string literal naming the collation; the
// node keeps the operand's type.
void test_collate(const InMemoryCatalog& cat) {
    std::printf("[test] COLLATE annotation lowering\n");

    with_plan(cat, "SELECT name COLLATE \"C\" FROM users", [](const LogicalNode* root) {
        const LogicalNode* proj =
            (root->op == LogicalOp::Project) ? root : only_child(root);
        check(proj && proj->op == LogicalOp::Project && !proj->exprs.empty(),
              "COLLATE: has Project item");
        if (!proj || proj->exprs.empty()) return;
        const auto& e = proj->exprs[0];
        check(e && e->kind == ExprKind::ScalarFunction, "COLLATE: is a ScalarFunction");
        check(e && e->func_name == "COLLATE", "COLLATE: func_name is COLLATE");
        // name is VarChar in this catalog; the annotation preserves the type.
        check(e && e->type == DataType::VarChar, "COLLATE: keeps operand type (VarChar)");
        check(e && e->children.size() == 2, "COLLATE: value + collation-name children");
        if (e && e->children.size() == 2) {
            check(e->children[0]->kind == ExprKind::ColumnRef, "COLLATE: child0 is the column");
            const auto* c = std::get_if<std::string>(&e->children[1]->value.value);
            check(c && *c == "C", "COLLATE: child1 names the collation");
        }
    });

    // COLLATE in a predicate binds tighter than '=' and does not lose the column.
    with_plan(cat, "SELECT id FROM users WHERE name COLLATE \"C\" = 'a'",
              [](const LogicalNode* root) {
        const LogicalNode* proj =
            (root->op == LogicalOp::Project) ? root : only_child(root);
        const LogicalNode* filter = proj ? only_child(proj) : nullptr;
        check(filter && filter->op == LogicalOp::Filter && filter->predicate,
              "COLLATE in WHERE: Filter with predicate");
        if (filter && filter->predicate &&
            filter->predicate->children.size() == 2) {
            check(filter->predicate->children[0]->kind == ExprKind::ScalarFunction &&
                      filter->predicate->children[0]->func_name == "COLLATE",
                  "COLLATE in WHERE: lhs is the COLLATE annotation");
        }
    });
}

void test_scan_filter_project_limit(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, name FROM users WHERE id = 1 LIMIT 10\n");
    with_plan(cat, "SELECT id, name FROM users WHERE id = 1 LIMIT 10",
              [](const LogicalNode* root) {
        // Limit -> Project -> Filter -> Scan
        check(root->op == LogicalOp::Limit, "root is Limit");
        check(root->has_limit && root->limit == 10, "limit == 10");
        check(!root->has_offset, "no offset");

        const LogicalNode* project = only_child(root);
        check(project && project->op == LogicalOp::Project, "child is Project");

        const LogicalNode* filter = only_child(project);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        check(filter && filter->predicate != nullptr, "filter has predicate");
        if (filter && filter->predicate) {
            // WHERE id = 1 lowers to an owned, typed BinaryOp with a positional
            // column leaf (id is slot #0 of the users scan) and an int literal.
            const auto& p = *filter->predicate;
            check(p.kind == ExprKind::BinaryOp, "predicate is a BinaryOp");
            check(p.bin_op == db25::ast::BinaryOp::Equal, "predicate operator is '='");
            check(p.type == DataType::Boolean, "predicate typed Boolean");
            check(p.children.size() == 2, "predicate has 2 operands");
            if (p.children.size() == 2) {
                check(p.children[0]->kind == ExprKind::ColumnRef &&
                          p.children[0]->input_index == 0,
                      "lhs is column ref #0 (id)");
                check(p.children[1]->kind == ExprKind::Literal, "rhs is a literal");
            }
        }

        const LogicalNode* scan = only_child(filter);
        check(scan && scan->op == LogicalOp::Scan, "leaf is Scan");
        check(scan && scan->table_name == "users", "scan of users");

        check(project && project->output.size() == 2, "project has 2 cols");
        if (project && project->output.size() == 2) {
            expect_col(project->output[0], "id", DataType::Integer, false, "proj[0]");
            expect_col(project->output[1], "name", DataType::VarChar, true, "proj[1]");
        }
        // SELECT id, name lowers to two positional column refs (#0, #1).
        check(project && project->exprs.size() == 2, "project has 2 exprs");
        if (project && project->exprs.size() == 2) {
            expect_col_ref(project->exprs[0], 0, "proj expr[0]");
            expect_col_ref(project->exprs[1], 1, "proj expr[1]");
        }
    });
}

// The WHERE predicate's right-hand-side literal of `SELECT id FROM users WHERE
// <col> = <literal>`, or null if the shape is not the expected Filter/BinaryOp.
const db25::plan::Expr* where_rhs_literal(const LogicalNode* root) {
    // root is the Project (no LIMIT in these queries); its child is the Filter.
    const LogicalNode* project =
        (root && root->op == LogicalOp::Project) ? root : only_child(root);
    if (!project || project->op != LogicalOp::Project) return nullptr;
    const LogicalNode* filter = only_child(project);
    if (!filter || filter->op != LogicalOp::Filter || !filter->predicate) return nullptr;
    const auto& p = *filter->predicate;
    if (p.kind != ExprKind::BinaryOp || p.children.size() != 2) return nullptr;
    return p.children[1].get();
}

// Hex (0x..) / binary (0b..) integer literals and leading-dot floats must lower
// to their actual numeric VALUE. Before the tokenizer/parser fix `0xFF` lexed as
// `0` followed by an alias, so this silently bound the value 0 - a wrong-answer
// bug, which is why the value (not just the node kind) is asserted here.
void test_hex_binary_literals(const InMemoryCatalog& cat) {
    std::printf("[test] hex / binary / leading-dot numeric literals\n");

    with_plan(cat, "SELECT id FROM users WHERE id = 0xFF", [](const LogicalNode* root) {
        const db25::plan::Expr* lit = where_rhs_literal(root);
        check(lit && lit->kind == ExprKind::Literal, "0xFF: rhs is a literal");
        const auto* v = lit ? std::get_if<std::int64_t>(&lit->value.value) : nullptr;
        check(v != nullptr, "0xFF: literal holds an int64");
        check(v && *v == 255, "0xFF lowers to 255");
    });

    with_plan(cat, "SELECT id FROM users WHERE id = 0xBEEF", [](const LogicalNode* root) {
        // Regression: the hex digits contain 'E'/'e', which the naive float
        // heuristic mistook for an exponent marker.
        const db25::plan::Expr* lit = where_rhs_literal(root);
        const auto* v = lit ? std::get_if<std::int64_t>(&lit->value.value) : nullptr;
        check(v && *v == 0xBEEF, "0xBEEF lowers to 48879");
    });

    with_plan(cat, "SELECT id FROM users WHERE id = 0b1010", [](const LogicalNode* root) {
        const db25::plan::Expr* lit = where_rhs_literal(root);
        const auto* v = lit ? std::get_if<std::int64_t>(&lit->value.value) : nullptr;
        check(v && *v == 10, "0b1010 lowers to 10");
    });

    with_plan(cat, "SELECT id FROM orders WHERE total = .5", [](const LogicalNode* root) {
        const db25::plan::Expr* lit = where_rhs_literal(root);
        check(lit && lit->kind == ExprKind::Literal, ".5: rhs is a literal");
        const auto* v = lit ? std::get_if<double>(&lit->value.value) : nullptr;
        check(v != nullptr, ".5: literal holds a double");
        check(v && *v == 0.5, ".5 lowers to 0.5");
    });
}

// An integer literal whose magnitude exceeds int64 is typed Decimal (exact SQL
// numeric) by the analyzer. The binder must lower it preserving that value and
// type. Regression: it cast the magnitude to double - corrupting the value past
// 2^53 (e.g. 9223372036854775809 -> 9223372036854775808) and overwriting the
// schema's Decimal type with Double, which also made a VALUES column reconcile
// Double instead of the analyzer's Decimal.
void test_oversized_integer_literal_stays_exact_decimal(const InMemoryCatalog& cat) {
    std::printf("[test] integer literal > int64 lowers to an exact Decimal\n");

    auto proj_literal = [&](const char* sql, const std::string& ctx,
                            auto&& inspect) {
        with_plan(cat, sql, [&](const LogicalNode* root) {
            const LogicalNode* proj =
                (root->op == LogicalOp::Project) ? root : only_child(root);
            check(proj && proj->op == LogicalOp::Project && !proj->exprs.empty(),
                  ctx + ": has Project");
            if (!proj || proj->exprs.empty()) return;
            const auto& e = proj->exprs[0];
            check(e && e->kind == ExprKind::Literal, ctx + ": item is a literal");
            if (e && e->kind == ExprKind::Literal) inspect(*e);
        });
    };

    // > int64: exact text carried in the string arm, type Decimal (NOT a lossy
    // Double). The value string must be byte-exact.
    proj_literal("SELECT 9223372036854775809", "9223372036854775809",
                 [](const db25::plan::Expr& e) {
        check(e.type == DataType::Decimal, "9223372036854775809: type Decimal");
        const auto* s = std::get_if<std::string>(&e.value.value);
        check(s != nullptr, "9223372036854775809: exact text in string arm");
        check(s && *s == "9223372036854775809", "9223372036854775809: value exact");
    });
    proj_literal("SELECT 18446744073709551615", "18446744073709551615",
                 [](const db25::plan::Expr& e) {
        check(e.type == DataType::Decimal, "u64max: type Decimal");
        const auto* s = std::get_if<std::string>(&e.value.value);
        check(s && *s == "18446744073709551615", "u64max: value exact");
    });

    // Fits int64: unchanged - int64 arm, BigInt type.
    proj_literal("SELECT 9223372036854775807", "int64max",
                 [](const db25::plan::Expr& e) {
        const auto* v = std::get_if<std::int64_t>(&e.value.value);
        check(v && *v == 9223372036854775807LL, "int64max: exact int64");
    });

    // The VALUES column type reconciles to Decimal (matching the analyzer), not
    // Double: (Integer, Decimal) -> Decimal.
    with_plan(cat, "SELECT * FROM (VALUES (1),(9223372036854775808)) AS t(x)",
              [](const LogicalNode* root) {
        check(root->output.size() == 1, "VALUES: one output column");
        if (!root->output.empty()) {
            check(root->output[0].type == DataType::Decimal,
                  "VALUES (1),(2^63) reconciles to Decimal, not Double");
        }
    });
}

void test_limit_offset(const InMemoryCatalog& cat) {
    std::printf("[test] ... LIMIT 10 OFFSET 5\n");
    with_plan(cat, "SELECT id, name FROM users WHERE id = 1 LIMIT 10 OFFSET 5",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Limit, "root is Limit");
        check(root->has_limit && root->limit == 10, "limit == 10");
        check(root->has_offset && root->offset == 5, "offset == 5");
    });
}

void test_inner_join(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.id, o.total FROM users u INNER JOIN orders o ON ...\n");
    with_plan(cat,
              "SELECT u.id, o.total FROM users u INNER JOIN orders o ON u.id = o.user_id",
              [](const LogicalNode* root) {
        // Project -> Join -> [Scan users, Scan orders]
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "child is Join");
        check(join && join->join_type == db25::ast::JoinType::Inner, "inner join");
        check(join && join->predicate != nullptr, "join has ON predicate");
        if (join && join->predicate) {
            // ON u.id = o.user_id lowers over the concatenated input schema
            // [users.id #0, users.name #1, orders.id #2, orders.user_id #3,
            //  orders.total #4], so both sides are positional column refs.
            const auto& p = *join->predicate;
            check(p.kind == ExprKind::BinaryOp &&
                      p.bin_op == db25::ast::BinaryOp::Equal,
                  "ON predicate is '='");
            check(p.children.size() == 2, "ON predicate has 2 operands");
            if (p.children.size() == 2) {
                check(p.children[0]->kind == ExprKind::ColumnRef &&
                          p.children[0]->input_index == 0,
                      "lhs is column ref #0 (u.id)");
                check(p.children[1]->kind == ExprKind::ColumnRef &&
                          p.children[1]->input_index == 3,
                      "rhs is column ref #3 (o.user_id)");
            }
        }
        check(join && join->child_count() == 2, "join has 2 inputs");
        if (join && join->child_count() == 2) {
            check(join->child(0)->op == LogicalOp::Scan &&
                  join->child(0)->table_name == "users", "left scan users");
            check(join->child(1)->op == LogicalOp::Scan &&
                  join->child(1)->table_name == "orders", "right scan orders");
            // Join output schema is the concatenation of both scans (5 cols).
            check(join->output.size() == 5, "join output = 5 cols");
        }
        check(root->output.size() == 2, "project has 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "id", DataType::Integer, false, "proj[0]");
            expect_col(root->output[1], "total", DataType::Double, true, "proj[1]");
        }
    });
}

// Self-join: two aliases of the SAME base table share (table_id, column_id), so
// column references must be disambiguated by their qualifier (alias). Before the
// fix, `m.sal` resolved into the LEFT scan (first (table_id, column_id) match).
void test_self_join_alias_resolution(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT e.dept, m.sal FROM emp e JOIN emp m ON e.id = m.id\n");
    with_plan(cat,
              "SELECT e.dept, m.sal FROM emp e JOIN emp m ON e.id = m.id",
              [](const LogicalNode* root) {
        // Frame = e[id#0,dept#1,sal#2] ++ m[id#3,dept#4,sal#5].
        check(root->op == LogicalOp::Project && root->exprs.size() == 2, "root Project of 2");
        if (root->exprs.size() == 2) {
            check(root->exprs[0]->kind == ExprKind::ColumnRef &&
                      root->exprs[0]->input_index == 1,
                  "e.dept -> #1 (left occurrence)");
            check(root->exprs[1]->kind == ExprKind::ColumnRef &&
                      root->exprs[1]->input_index == 5,
                  "m.sal -> #5 (RIGHT occurrence, not the left alias)");
        }
        const LogicalNode* join = only_child(root);
        check(join && join->predicate && join->predicate->children.size() == 2,
              "join has an ON predicate");
        if (join && join->predicate && join->predicate->children.size() == 2) {
            check(join->predicate->children[0]->input_index == 0 &&
                      join->predicate->children[1]->input_index == 3,
                  "ON e.id (#0) = m.id (#3), not #0 = #0");
        }
    });
}

// Two derived tables exposing identically-named COMPUTED columns (synthetic zero
// ids) must be disambiguated by the qualifier, exactly like the self-join above.
// Regression: the by-name computed-column path ignored the qualifier, so every
// `v2.*` bound to v1's first same-named copy -- the join ON collapsed to
// `#0 = #0` (a tautology / cross product) and `SELECT v2.dept` read v1.dept.
void test_derived_table_join_qualifier_resolution(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT v2.dept FROM (VALUES ...) v1(id,dept) JOIN (VALUES ...) v2(id,dept) ON v1.id = v2.id\n");
    with_plan(cat,
              "SELECT v2.dept FROM (VALUES (1, 'a')) v1(id, dept) "
              "JOIN (VALUES (2, 'c')) v2(id, dept) ON v1.id = v2.id",
              [](const LogicalNode* root) {
        // Frame = v1[id#0,dept#1] ++ v2[id#2,dept#3].
        check(root->op == LogicalOp::Project && root->exprs.size() == 1, "root Project of 1");
        if (root->exprs.size() == 1) {
            check(root->exprs[0]->kind == ExprKind::ColumnRef &&
                      root->exprs[0]->input_index == 3,
                  "v2.dept -> #3 (v2's copy, not v1's #1)");
        }
        const LogicalNode* join = only_child(root);
        check(join && join->predicate && join->predicate->children.size() == 2,
              "join has an ON predicate");
        if (join && join->predicate && join->predicate->children.size() == 2) {
            check(join->predicate->children[0]->input_index == 0 &&
                      join->predicate->children[1]->input_index == 2,
                  "ON v1.id (#0) = v2.id (#2), not #0 = #0");
        }
    });
}

// The same class through expression-aliased derived tables (SELECT id+K AS k):
// `b.k` must resolve to b's computed column, not a's.
void test_derived_expr_alias_join_qualifier_resolution(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT b.k FROM (SELECT id+1 AS k FROM users) a JOIN (SELECT id+10 AS k FROM orders) b ON a.k = b.k\n");
    with_plan(cat,
              "SELECT b.k FROM (SELECT id + 1 AS k FROM users) a "
              "JOIN (SELECT id + 10 AS k FROM orders) b ON a.k = b.k",
              [](const LogicalNode* root) {
        // Frame = a[k#0] ++ b[k#1].
        check(root->op == LogicalOp::Project && root->exprs.size() == 1, "root Project of 1");
        if (root->exprs.size() == 1) {
            check(root->exprs[0]->kind == ExprKind::ColumnRef &&
                      root->exprs[0]->input_index == 1,
                  "b.k -> #1 (b's copy, not a's #0)");
        }
        const LogicalNode* join = only_child(root);
        check(join && join->predicate && join->predicate->children.size() == 2,
              "join has an ON predicate");
        if (join && join->predicate && join->predicate->children.size() == 2) {
            check(join->predicate->children[0]->input_index == 0 &&
                      join->predicate->children[1]->input_index == 1,
                  "ON a.k (#0) = b.k (#1), not #0 = #0");
        }
    });
}

// A table-name qualifier (no explicit alias) still resolves against the single
// occurrence - the fix must not regress the common unaliased case.
void test_table_name_qualifier(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT emp.dept FROM emp WHERE emp.sal > 10\n");
    with_plan(cat, "SELECT emp.dept FROM emp WHERE emp.sal > 10",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->exprs.size() == 1, "root Project of 1");
        if (root->exprs.size() == 1) {
            check(root->exprs[0]->kind == ExprKind::ColumnRef &&
                      root->exprs[0]->input_index == 1,
                  "emp.dept -> #1");
        }
    });
}

void test_group_by(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT dept, COUNT(*) FROM emp GROUP BY dept\n");
    with_plan(cat, "SELECT dept, COUNT(*) FROM emp GROUP BY dept",
              [](const LogicalNode* root) {
        // Project -> Aggregate -> Scan
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "child is Aggregate");
        check(agg && agg->group_keys.size() == 1, "1 group key");
        check(agg && agg->aggregates.size() == 1, "1 aggregate");
        // GROUP BY dept lowers to a positional key (dept is slot #1 of emp);
        // COUNT(*) lowers to an owned Aggregate expression.
        if (agg && agg->group_keys.size() == 1) {
            expect_col_ref(agg->group_keys[0], 1, "group key (dept)");
        }
        if (agg && agg->aggregates.size() == 1) {
            check(agg->aggregates[0]->kind == ExprKind::Aggregate, "aggregate is Aggregate expr");
            check(agg->aggregates[0]->func_name == "COUNT", "aggregate func is COUNT");
        }
        const LogicalNode* scan = only_child(agg);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "emp",
              "leaf scan emp");
        check(root->output.size() == 2, "project has 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "dept", DataType::VarChar, true, "proj[0]");
            // COUNT(*) -> BigInt, not null.
            expect_col(root->output[1], "COUNT", DataType::BigInt, false, "proj[1]");
        }
        // Over an Aggregate child the projection is positional into its output:
        // the group key (#0) and the aggregate (#1) are both column refs, not
        // re-evaluated calls.
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "agg proj expr[0] (dept)");
            expect_col_ref(root->exprs[1], 1, "agg proj expr[1] (COUNT)");
        }
    });
}

// Ordered aggregate: string_agg(dept, ',' ORDER BY sal DESC). The ORDER BY is
// lowered into the Aggregate expr's agg_order_by (a positional key into the
// aggregate's input), NOT as a value argument, and the DESC flag rides along.
void test_ordered_aggregate(const InMemoryCatalog& cat) {
    std::printf("[test] string_agg(dept, ',' ORDER BY sal DESC)\n");
    with_plan(cat, "SELECT string_agg(dept, ',' ORDER BY sal DESC) FROM emp",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "child is Aggregate");
        check(agg && agg->aggregates.size() == 1, "1 aggregate");
        if (agg && agg->aggregates.size() == 1) {
            const auto& a = agg->aggregates[0];
            check(a->kind == ExprKind::Aggregate, "aggregate is Aggregate expr");
            check(a->func_name == "STRING_AGG", "func is STRING_AGG");
            // Two value arguments (dept, ','); the ORDER BY is NOT a third arg.
            check(a->children.size() == 2, "two value args (ORDER BY is not an arg)");
            // Exactly one ordered-aggregate key: sal (emp slot #2), DESC.
            check(a->agg_order_by.size() == 1, "1 ORDER BY key");
            if (a->agg_order_by.size() == 1) {
                expect_col_ref(a->agg_order_by[0].expr, 2, "ORDER BY key -> sal (#2)");
                check(a->agg_order_by[0].descending, "ORDER BY key is DESC");
            }
        }
    });
}

// Two ordered aggregates that share func + args + sort-key COLUMN but differ in
// direction (ASC vs DESC) or NULLS ordering are DISTINCT producers - they build
// oppositely-ordered results. The binder must keep both (2 aggregates, projection
// column i -> slot i), not dedup them into one (which silently returned one
// ordering for both). Two IDENTICAL ordered aggregates must still dedup to one.
void test_ordered_aggregate_dedup(const InMemoryCatalog& cat) {
    std::printf("[test] array_agg(x ORDER BY y ASC) vs (... DESC) stay distinct\n");

    with_plan(cat,
              "SELECT array_agg(sal ORDER BY sal ASC), array_agg(sal ORDER BY sal DESC) FROM emp",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "asc/desc: child is Aggregate");
        check(agg && agg->aggregates.size() == 2,
              "ASC and DESC are two distinct aggregates");
        // The projection maps col 0 -> slot 0 and col 1 -> slot 1 (not both to 0).
        check(root->exprs.size() == 2, "two projected columns");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "proj[0] -> agg slot 0 (ASC)");
            expect_col_ref(root->exprs[1], 1, "proj[1] -> agg slot 1 (DESC)");
        }
    });

    // NULLS FIRST vs the default likewise splits.
    with_plan(cat,
              "SELECT array_agg(sal ORDER BY sal), array_agg(sal ORDER BY sal NULLS FIRST) FROM emp",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->aggregates.size() == 2, "NULLS ordering splits producers");
    });

    // Two IDENTICAL ordered aggregates still collapse to one (no over-splitting).
    with_plan(cat,
              "SELECT array_agg(sal ORDER BY sal), array_agg(sal ORDER BY sal) FROM emp",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->aggregates.size() == 1,
              "identical ordered aggregates dedup to one");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "identical proj[0] -> slot 0");
            expect_col_ref(root->exprs[1], 0, "identical proj[1] -> slot 0");
        }
    });
}

// The binder's aggregate-name set must match the analyzer's exactly. ARRAY_AGG,
// STDDEV*, VARIANCE/VAR_*, BOOL_AND/OR are aggregates the analyzer recognizes;
// the binder previously omitted them, lowering them as per-row scalars (no
// Aggregate node - silently wrong) or failing to bind a legal GROUP BY.
void test_aggregate_name_parity(const InMemoryCatalog& cat) {
    std::printf("[test] binder aggregate-name set matches the analyzer\n");

    // array_agg with no GROUP BY -> Aggregate(group=()) collapsing to one row,
    // NOT a per-row ScalarFunction in the Project.
    with_plan(cat, "SELECT array_agg(sal) FROM emp", [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "array_agg: root is Project");
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate,
              "array_agg builds an Aggregate node (not a per-row scalar)");
        check(agg && agg->group_keys.empty(), "no GROUP BY -> empty group");
        check(agg && agg->aggregates.size() == 1 &&
                  agg->aggregates[0]->kind == ExprKind::Aggregate &&
                  agg->aggregates[0]->func_name == "ARRAY_AGG",
              "the aggregate is ARRAY_AGG");
    });

    // A grouped stddev binds (previously bind-failed: bare `sal` looked up
    // against the group-by output because stddev was not recognized).
    with_plan(cat, "SELECT dept, stddev(sal) FROM emp GROUP BY dept",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "stddev GROUP BY: Aggregate");
        check(agg && agg->aggregates.size() == 1 &&
                  agg->aggregates[0]->func_name == "STDDEV",
              "the aggregate is STDDEV");
    });

    // The ordered-aggregate flagship now actually aggregates (ARRAY_AGG was the
    // headline example of the ordered-aggregate work yet was not recognized).
    with_plan(cat, "SELECT array_agg(sal ORDER BY id) FROM emp",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "ordered array_agg: Aggregate");
        check(agg && agg->aggregates.size() == 1 &&
                  agg->aggregates[0]->agg_order_by.size() == 1,
              "ordered array_agg carries its ORDER BY key on the Aggregate expr");
    });
}

// A GROUP BY key may name a SELECT-list output alias (PostgreSQL extension the
// analyzer accepts): the binder must group by the aliased expression, not fail
// to resolve the alias as a base column. Regression: `... GROUP BY d` for
// `dept AS d` bound-failed with "unresolved column reference 'd'".
void test_group_by_output_alias(const InMemoryCatalog& cat) {
    std::printf("[test] GROUP BY <select output alias>\n");

    // Single-column alias: groups by dept (slot #1 of emp); the projection's
    // `d` resolves to the group-key slot #0.
    with_plan(cat, "SELECT dept AS d, COUNT(*) FROM emp GROUP BY d",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "alias: root is Project");
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "alias: child is Aggregate");
        check(agg && agg->group_keys.size() == 1, "alias: 1 group key");
        if (agg && agg->group_keys.size() == 1) {
            expect_col_ref(agg->group_keys[0], 1, "alias: group key is dept (#1)");
        }
        check(root->exprs.size() == 2, "alias: project has 2 exprs");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "alias: proj d -> group-key slot #0");
        }
        if (root->output.size() == 2) {
            check(root->output[0].name == "d", "alias: output col named 'd'");
        }
    });

    // Compound-expression alias: `GROUP BY s` groups by `sal + 1`.
    with_plan(cat, "SELECT sal + 1 AS s FROM emp GROUP BY s",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "expr-alias: child is Aggregate");
        check(agg && agg->group_keys.size() == 1 &&
                  agg->group_keys[0]->kind == ExprKind::BinaryOp,
              "expr-alias: group key is the sal+1 expression");
    });
}

// Positional GROUP BY: `GROUP BY <n>` groups by the n-th SELECT output column's
// expression - standard SQL the analyzer accepts and validates. Regression: the
// binder lowered the integer literal as a CONSTANT single-group key (its comment
// wrongly assumed ordinals were "rejected upstream"), so the referenced bare
// column then failed to resolve and a legal, analyzer-blessed query failed to
// bind. The plan must be identical to spelling the column out.
void test_group_by_positional(const InMemoryCatalog& cat) {
    std::printf("[test] GROUP BY <ordinal>\n");

    // `GROUP BY 1` == `GROUP BY dept`: Aggregate group=(dept #1), COUNT agg.
    with_plan(cat, "SELECT dept, COUNT(*) FROM emp GROUP BY 1",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "ord: root is Project");
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "ord: child is Aggregate");
        check(agg && agg->group_keys.size() == 1, "ord: 1 group key");
        if (agg && agg->group_keys.size() == 1) {
            expect_col_ref(agg->group_keys[0], 1, "ord: group key is dept (#1)");
        }
        check(agg && agg->aggregates.size() == 1, "ord: 1 aggregate (COUNT)");
        // The bare `dept` in the SELECT resolves to the group-key slot #0.
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "ord: proj dept -> group-key slot #0");
        }
        if (!agg->output.empty()) {
            check(agg->output[0].name == "dept", "ord: key column named 'dept'");
            check(agg->output[0].type == DataType::VarChar,
                  "ord: key column typed VarChar (from the item, not the literal)");
        }
    });

    // `GROUP BY 1` with an aggregate also present binds and groups by dept.
    with_plan(cat, "SELECT dept, SUM(sal) FROM emp GROUP BY 1",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "ord+agg: child is Aggregate");
        check(agg && agg->group_keys.size() == 1 && agg->aggregates.size() == 1,
              "ord+agg: 1 key + 1 aggregate");
        if (agg && agg->group_keys.size() == 1) {
            expect_col_ref(agg->group_keys[0], 1, "ord+agg: group key is dept (#1)");
        }
    });

    // Regression: the ordinal literal is a positional SELECTOR, not the grouped
    // value. It must NOT be registered as an aggregate-frame producer - if it
    // were, every structurally-equal integer constant above the Aggregate would
    // be rewritten into the group slot. Here the `1` in `COUNT(*)+1` must stay a
    // Literal, exactly as it does for the named-key form `GROUP BY dept`.
    with_plan(cat, "SELECT dept, COUNT(*)+1 FROM emp GROUP BY 1",
              [](const LogicalNode* root) {
        check(root->exprs.size() == 2, "lit: project has 2 exprs");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "lit: dept -> group-key slot #0");
            const auto& add = root->exprs[1];
            check(add && add->kind == ExprKind::BinaryOp && add->children.size() == 2,
                  "lit: second item is COUNT(*)+1 (BinaryOp)");
            if (add && add->kind == ExprKind::BinaryOp && add->children.size() == 2) {
                expect_col_ref(add->children[0], 1, "lit: COUNT(*) -> agg slot #1");
                check(add->children[1] && add->children[1]->kind == ExprKind::Literal,
                      "lit: the literal 1 stays a Literal, not a ColumnRef into the group slot");
            }
        }
    });

    // Regression: HAVING constant on a two-key positional grouping. `GROUP BY 1, 2`
    // registers dept (slot #0) and sal (slot #1); the `2` in `HAVING sal > 2` is
    // structurally equal to the ordinal `2` key but must remain a Literal, not be
    // rewritten into the sal slot (#1).
    with_plan(cat, "SELECT dept, sal, COUNT(*) FROM emp GROUP BY 1, 2 HAVING sal > 2",
              [](const LogicalNode* root) {
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "having: child is Filter");
        if (filter && filter->predicate) {
            const auto& p = filter->predicate;
            check(p->kind == ExprKind::BinaryOp && p->children.size() == 2,
                  "having: predicate is sal > 2 (BinaryOp)");
            if (p->kind == ExprKind::BinaryOp && p->children.size() == 2) {
                expect_col_ref(p->children[0], 1, "having: sal -> group-key slot #1");
                check(p->children[1] && p->children[1]->kind == ExprKind::Literal,
                      "having: the literal 2 stays a Literal, not a ColumnRef into the sal slot");
            }
        }
    });
}

// The Aggregate output is group_keys ++ aggregates, independent of SELECT order.
// `SELECT COUNT(*), dept` puts the aggregate first in the select list but the
// Aggregate output is still [dept (key), COUNT (agg)]; the Project reorders it
// back, mapping select item #0 (COUNT) to output slot #1 and #1 (dept) to #0.
// The old select-list-shaped model declared the output in select order, which an
// executor emitting keys++aggs would have mis-mapped (columns swapped).
void test_group_by_select_reordered(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT COUNT(*), dept FROM emp GROUP BY dept  (agg before key)\n");
    with_plan(cat, "SELECT COUNT(*), dept FROM emp GROUP BY dept",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "child is Aggregate");
        check(agg && agg->output.size() == 2, "aggregate output is [dept, COUNT]");
        if (agg && agg->output.size() == 2) {
            // Canonical order: group key first, aggregate result second.
            check(agg->output[0].name == "dept", "output #0 is the group key dept");
            check(agg->output[1].name == "COUNT", "output #1 is the aggregate COUNT");
        }
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            // Select order is (COUNT, dept); the Project maps it onto the
            // keys++aggs output: COUNT -> slot #1, dept -> slot #0.
            expect_col_ref(root->exprs[0], 1, "proj expr[0] COUNT -> agg slot #1");
            expect_col_ref(root->exprs[1], 0, "proj expr[1] dept -> agg slot #0");
        }
    });
}

// Two aggregates that share a function name but differ in argument
// (`SUM(sal)` vs `SUM(id)`) get DISTINCT output columns, and each select item
// resolves to its own column. By-name matching would alias both to the first
// "SUM"; structural matching keeps them apart.
void test_group_by_same_name_aggregates(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT SUM(sal), SUM(id) FROM emp GROUP BY dept  (name collision)\n");
    with_plan(cat, "SELECT SUM(sal), SUM(id) FROM emp GROUP BY dept",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "child is Aggregate");
        // [dept (key), SUM(sal), SUM(id)] - the two SUMs are separate columns.
        check(agg && agg->output.size() == 3, "aggregate output is [dept, SUM, SUM]");
        check(agg && agg->aggregates.size() == 2, "two distinct aggregates");
        if (agg && agg->aggregates.size() == 2) {
            // SUM(sal): arg sal is emp slot #2; SUM(id): arg id is emp slot #0.
            expect_col_ref(agg->aggregates[0]->children[0], 2, "SUM(sal) arg -> #2");
            expect_col_ref(agg->aggregates[1]->children[0], 0, "SUM(id) arg -> #0");
        }
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            // Each select SUM maps to ITS OWN aggregate column, not the first.
            expect_col_ref(root->exprs[0], 1, "SUM(sal) -> agg slot #1");
            expect_col_ref(root->exprs[1], 2, "SUM(id) -> agg slot #2 (not aliased to #1)");
        }
    });
}

// Self-join GROUP BY on the same base column: e1.dept and e2.dept share
// (table_id, column_id) but are distinct group keys. The projection must map
// each select item to its OWN key slot via the qualifier - previously both
// resolved to the first key (Project #0,#0 instead of #0,#1).
void test_self_join_group_key_distinct_slots(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT e1.dept, e2.dept FROM emp e1 JOIN emp e2 ... GROUP BY e1.dept, e2.dept\n");
    with_plan(cat,
              "SELECT e1.dept, e2.dept FROM emp e1 JOIN emp e2 ON e1.id = e2.id "
              "GROUP BY e1.dept, e2.dept",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "child is Aggregate");
        check(agg && agg->group_keys.size() == 2, "two distinct group keys");
        check(root->exprs.size() == 2, "two projected columns");
        if (root->exprs.size() == 2) {
            check(root->exprs[0]->kind == ExprKind::ColumnRef &&
                      root->exprs[1]->kind == ExprKind::ColumnRef,
                  "both project columns reference the aggregate output");
            check(root->exprs[0]->input_index != root->exprs[1]->input_index,
                  "e1.dept / e2.dept map to DISTINCT key slots");
        }
    });
}

// COUNT(DISTINCT x) and COUNT(x) share their name AND argument - the DISTINCT
// modifier lives only in semantic_flags - so they must still be kept as two
// separate aggregate columns and not deduped into one.
void test_group_by_distinct_vs_plain(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT COUNT(DISTINCT sal), COUNT(sal) FROM emp GROUP BY dept\n");
    with_plan(cat, "SELECT COUNT(DISTINCT sal), COUNT(sal) FROM emp GROUP BY dept",
              [](const LogicalNode* root) {
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "child is Aggregate");
        // [dept (key), COUNT(DISTINCT sal), COUNT(sal)] - NOT deduped.
        check(agg && agg->output.size() == 3,
              "DISTINCT and plain COUNT are separate columns");
        check(agg && agg->aggregates.size() == 2, "two distinct aggregates");
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 1, "COUNT(DISTINCT sal) -> agg slot #1");
            expect_col_ref(root->exprs[1], 2, "COUNT(sal) -> agg slot #2 (not merged)");
        }
    });
}

// -------------------------------------------------------------------------
// Implicit aggregation: an aggregate with no GROUP BY collapses the input to a
// single group (Aggregate with EMPTY group keys) below the Project.

void test_implicit_aggregate_count(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT COUNT(*) FROM users  (implicit aggregation)\n");
    with_plan(cat, "SELECT COUNT(*) FROM users", [](const LogicalNode* root) {
        // Project -> Aggregate(0 keys) -> Scan
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "child is Aggregate");
        check(agg && agg->group_keys.empty(), "no group keys (implicit)");
        check(agg && agg->aggregates.size() == 1, "1 aggregate (COUNT)");
        if (agg && agg->aggregates.size() == 1) {
            check(agg->aggregates[0]->kind == ExprKind::Aggregate, "aggregate is Aggregate expr");
            check(agg->aggregates[0]->func_name == "COUNT", "aggregate func is COUNT");
        }
        const LogicalNode* scan = only_child(agg);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "users",
              "leaf scan users");
        check(root->output.size() == 1, "project has 1 col");
        if (root->output.size() == 1) {
            // COUNT(*) -> BigInt, not null.
            expect_col(root->output[0], "COUNT", DataType::BigInt, false, "proj[0]");
        }
    });
}

void test_implicit_aggregate_nested(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT SUM(sal)+1 FROM emp  (aggregate nested in expr)\n");
    with_plan(cat, "SELECT SUM(sal)+1 FROM emp", [](const LogicalNode* root) {
        // Project -> Aggregate(0 keys, detects the nested SUM) -> Scan
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "child is Aggregate");
        check(agg && agg->group_keys.empty(), "no group keys (implicit)");
        // The SUM is nested inside `SUM(sal) + 1`; detection must still find it.
        check(agg && agg->aggregates.size() == 1, "1 aggregate (nested SUM)");
        // The SUM aggregate's argument lowers to a positional ref (sal is #2 of
        // emp), proving aggregate arguments resolve against the Aggregate input.
        if (agg && agg->aggregates.size() == 1) {
            const auto& a = *agg->aggregates[0];
            check(a.kind == ExprKind::Aggregate && a.func_name == "SUM", "aggregate is SUM");
            check(a.children.size() == 1, "SUM has 1 argument");
            if (a.children.size() == 1) {
                expect_col_ref(a.children[0], 2, "SUM arg (sal -> #2)");
            }
        }
        const LogicalNode* scan = only_child(agg);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "emp",
              "leaf scan emp");
        check(root->output.size() == 1, "project has 1 col");
        // The Aggregate output is the canonical [SUM] (one aggregate result),
        // and the Project reshapes it back into `SUM(sal) + 1` - the `+ 1`
        // wrapper is preserved (the old select-list-shaped model dropped it,
        // collapsing the item to a bare ColumnRef).
        check(agg && agg->output.size() == 1, "aggregate output is [SUM]");
        check(root->exprs.size() == 1, "project has 1 expr");
        if (root->exprs.size() == 1) {
            const auto& p = *root->exprs[0];
            check(p.kind == ExprKind::BinaryOp && p.bin_op == db25::ast::BinaryOp::Add,
                  "project keeps SUM(sal)+1 as an Add (the +1 is not dropped)");
            if (p.kind == ExprKind::BinaryOp && p.children.size() == 2) {
                expect_col_ref(p.children[0], 0, "Add lhs is the precomputed SUM (#0)");
                check(p.children[1]->kind == ExprKind::Literal, "Add rhs is a literal");
            }
        }
    });
}

// -------------------------------------------------------------------------
// HAVING: a post-aggregation Filter sitting above the Aggregate.

void test_having(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING COUNT(*) > 5\n");
    with_plan(cat,
              "SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING COUNT(*) > 5",
              [](const LogicalNode* root) {
        // Project -> Filter (HAVING) -> Aggregate -> Scan
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter (HAVING)");
        check(filter && filter->predicate != nullptr, "HAVING has predicate");
        const LogicalNode* agg = only_child(filter);
        check(agg && agg->op == LogicalOp::Aggregate, "filter child is Aggregate");
        check(agg && agg->group_keys.size() == 1, "1 group key");
        const LogicalNode* scan = only_child(agg);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "emp",
              "leaf scan emp");
        // The HAVING Filter is schema-preserving over the Aggregate.
        check(filter && filter->output.size() == 2, "filter preserves 2 cols");
        check(root->output.size() == 2, "project has 2 cols");
    });
}

// HAVING that references an aggregate expression (not just COUNT(*)): the
// aggregate is matched to the Aggregate's already-computed output column and
// lowered to a ColumnRef, rather than being re-lowered (which would reach for
// base columns no longer in scope above the aggregation).
void test_having_aggregate_in_select(const InMemoryCatalog& cat) {
    std::printf("[test] ... GROUP BY dept HAVING SUM(sal) > 1000  (SUM also selected)\n");
    with_plan(cat,
              "SELECT dept, SUM(sal) FROM emp GROUP BY dept HAVING SUM(sal) > 1000",
              [](const LogicalNode* root) {
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is the HAVING Filter");
        check(filter && filter->predicate &&
                  filter->predicate->kind == ExprKind::BinaryOp &&
                  filter->predicate->children.size() == 2,
              "HAVING predicate is a comparison");
        // The SUM(sal) operand resolved to a ColumnRef into the Aggregate output
        // (the precomputed SUM column), NOT a re-lowered Aggregate expression.
        if (filter && filter->predicate && filter->predicate->children.size() == 2) {
            check(filter->predicate->children[0]->kind == ExprKind::ColumnRef,
                  "SUM(sal) in HAVING is a ColumnRef to the precomputed aggregate");
        }
        const LogicalNode* agg = filter ? only_child(filter) : nullptr;
        check(agg && agg->op == LogicalOp::Aggregate, "Filter over Aggregate");
        // Canonical output [dept (key), SUM (agg)]: the HAVING SUM(sal) and the
        // SELECT SUM(sal) dedup to that one aggregate column (both resolve to it
        // structurally), so the output stays at 2 columns.
        check(agg && agg->output.size() == 2, "aggregate output is [dept, SUM]");
        check(root->output.size() == 2, "query result is (dept, SUM)");
    });
}

// HAVING may reference an aggregate that is NOT in the SELECT list. It is a
// first-class aggregate result column (collected from HAVING into the payload);
// the Project simply does not select it, so it is absent from the query result.
void test_having_aggregate_not_selected(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT dept FROM emp GROUP BY dept HAVING MIN(sal) > 5  (MIN not selected)\n");
    with_plan(cat, "SELECT dept FROM emp GROUP BY dept HAVING MIN(sal) > 5",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->output.size() == 1,
              "query result is just (dept)");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is the HAVING Filter");
        if (filter && filter->predicate && filter->predicate->children.size() == 2) {
            check(filter->predicate->children[0]->kind == ExprKind::ColumnRef,
                  "MIN(sal) in HAVING resolved to a ColumnRef into the aggregate output");
        }
        const LogicalNode* agg = filter ? only_child(filter) : nullptr;
        // Canonical output [dept (key), MIN (agg)]; the Project emits only dept.
        check(agg && agg->op == LogicalOp::Aggregate && agg->output.size() == 2,
              "aggregate output is [dept, MIN]");
    });
}

// A selected aggregate hidden behind an alias is still referenceable by its call
// form in HAVING: the aggregate output column is named by the call (not the
// SELECT alias), so HAVING resolves structurally regardless of the alias.
void test_having_aggregate_aliased(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT dept, SUM(sal) AS total ... HAVING SUM(sal) > 1000  (aliased)\n");
    with_plan(cat,
              "SELECT dept, SUM(sal) AS total FROM emp GROUP BY dept HAVING SUM(sal) > 1000",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->output.size() == 2,
              "query result is (dept, total)");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is the HAVING Filter");
        if (filter && filter->predicate && filter->predicate->children.size() == 2) {
            check(filter->predicate->children[0]->kind == ExprKind::ColumnRef,
                  "HAVING SUM(sal) resolved to a ColumnRef despite the SELECT alias");
        }
    });
}

// ORDER BY an aggregate that is NOT selected. It is collected into the Aggregate
// payload (a first-class result column); the Sort resolves the key against the
// Aggregate output via the frame, appending a hidden Project column that carries
// the precomputed aggregate. (Under the old model the ORDER-BY-only aggregate got
// no output column, so this key had nothing to resolve to.)
void test_order_by_aggregate_not_selected(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT dept FROM emp GROUP BY dept ORDER BY SUM(sal)\n");
    with_plan(cat, "SELECT dept FROM emp GROUP BY dept ORDER BY SUM(sal)",
              [](const LogicalNode* root) {
        // Sort -> Project(dept + hidden SUM) -> Aggregate[dept, SUM] -> Scan
        check(root->op == LogicalOp::Sort, "root is Sort");
        check(root->sort_keys.size() == 1, "one sort key");
        const LogicalNode* project = only_child(root);
        check(project && project->op == LogicalOp::Project, "sort child is Project");
        // dept (visible) + a hidden SUM column appended for the sort key.
        check(project && project->output.size() == 2, "project has dept + hidden SUM");
        if (project && project->exprs.size() == 2) {
            // The hidden column is the precomputed SUM: a ColumnRef into the
            // Aggregate output slot #1 (dept is key #0, SUM is agg #1).
            expect_col_ref(project->exprs[1], 1, "hidden sort col -> agg SUM slot #1");
        }
        const LogicalNode* agg = project ? only_child(project) : nullptr;
        check(agg && agg->op == LogicalOp::Aggregate && agg->output.size() == 2,
              "aggregate output is [dept, SUM]");
    });

    // Regression: a no-argument aggregate (COUNT(*)) - or one whose argument is
    // resolvable against the grouped Project output (COUNT(dept)) - must ALSO
    // route to its precomputed Aggregate slot, not be re-lowered as a fresh
    // Aggregate over the one-row-per-group Project output (which would make
    // COUNT() == 1 for every row - a meaningless sort). Unlike SUM(sal) it has no
    // unresolvable argument, so it does not fail the visible-output attempt on its
    // own; the raw-aggregate guard is what diverts it to the frame path.
    std::printf("[test] SELECT dept FROM emp GROUP BY dept ORDER BY COUNT(*)\n");
    with_plan(cat, "SELECT dept FROM emp GROUP BY dept ORDER BY COUNT(*)",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Sort, "count: root is Sort");
        check(root->sort_keys.size() == 1, "count: one sort key");
        if (root->sort_keys.size() == 1) {
            // The sort key is a ColumnRef into the hidden COUNT column - NOT a raw
            // ExprKind::Aggregate re-computed above the Aggregate node.
            const auto& k = root->sort_keys[0].expr;
            check(k && k->kind == ExprKind::ColumnRef,
                  "count: sort key is a ColumnRef (precomputed), not a raw aggregate");
        }
        const LogicalNode* project = only_child(root);
        check(project && project->op == LogicalOp::Project, "count: sort child is Project");
        // dept (visible) + a hidden COUNT column = ColumnRef into agg slot #1.
        check(project && project->output.size() == 2,
              "count: project has dept + hidden COUNT");
        if (project && project->exprs.size() == 2) {
            expect_col_ref(project->exprs[1], 1, "count: hidden sort col -> agg COUNT slot #1");
        }
        // The Sort drops the hidden column: its visible output is just dept.
        check(root->output.size() == 1, "count: sort visible output is just dept");
    });
}

// A statement-level ORDER BY whose key is an aggregate ALSO selected must dedup
// to the ONE aggregate producer even when the ORDER BY carries a direction (DESC)
// or NULLS ordering. Those bits belong to the Sort node, not the aggregate's
// identity - the ordered-aggregate ordering guard (scoped to an aggregate's OWN
// argument-list ORDER BY) must not split a statement ORDER BY aggregate from its
// SELECT twin, or a redundant second aggregate column is emitted.
void test_order_by_selected_aggregate_direction_dedups(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT dept, sum(sal) ... ORDER BY sum(sal) DESC (dedups)\n");
    for (const char* sql : {
            "SELECT dept, sum(sal) FROM emp GROUP BY dept ORDER BY sum(sal) DESC",
            "SELECT dept, sum(sal) FROM emp GROUP BY dept ORDER BY sum(sal) ASC NULLS FIRST",
            "SELECT dept, count(*) FROM emp GROUP BY dept ORDER BY count(*) DESC"}) {
        with_plan(cat, sql, [](const LogicalNode* root) {
            // Sort -> Project -> Aggregate -> Scan.
            check(root->op == LogicalOp::Sort, "root is Sort");
            const LogicalNode* project = only_child(root);
            const LogicalNode* agg = project ? only_child(project) : nullptr;
            check(agg && agg->op == LogicalOp::Aggregate, "has an Aggregate");
            check(agg && agg->aggregates.size() == 1,
                  "ORDER BY <agg> DESC dedups to the SELECT aggregate (one producer)");
        });
    }
}

// -------------------------------------------------------------------------
// SELECT DISTINCT: a Distinct node directly above the Project.

void test_distinct(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT DISTINCT dept FROM emp\n");
    with_plan(cat, "SELECT DISTINCT dept FROM emp", [](const LogicalNode* root) {
        // Distinct -> Project -> Scan
        check(root->op == LogicalOp::Distinct, "root is Distinct");
        const LogicalNode* project = only_child(root);
        check(project && project->op == LogicalOp::Project, "child is Project");
        const LogicalNode* scan = only_child(project);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "emp",
              "leaf scan emp");
        // Distinct is schema-preserving: same output as its Project child.
        check(root->output.size() == 1, "distinct preserves 1 col");
        if (root->output.size() == 1) {
            expect_col(root->output[0], "dept", DataType::VarChar, true, "distinct[0]");
        }
    });
}

void test_select_star(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT * FROM users\n");
    with_plan(cat, "SELECT * FROM users", [](const LogicalNode* root) {
        // Project -> Scan
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* scan = only_child(root);
        check(scan && scan->op == LogicalOp::Scan, "leaf is Scan");
        check(root->output.size() == 2, "star expands to 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "id", DataType::Integer, false, "proj[0]");
            expect_col(root->output[1], "name", DataType::VarChar, true, "proj[1]");
            // Star expansion carries catalog ids through the analyzer.
            check(root->output[0].table_id != 0, "star col carries table_id");
            check(root->output[0].column_id == 1, "id column_id == 1");
        }
        // `*` expands to one positional column ref per covered column (#0, #1).
        check(root->exprs.size() == 2, "star lowers to 2 column-ref exprs");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "star expr[0]");
            expect_col_ref(root->exprs[1], 1, "star expr[1]");
        }
    });
}

// -------------------------------------------------------------------------
// ORDER BY: real sort keys + directions on the Sort node.

void test_order_by(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, name FROM users ORDER BY name DESC, id ASC\n");
    with_plan(cat, "SELECT id, name FROM users ORDER BY name DESC, id ASC",
              [](const LogicalNode* root) {
        // Sort -> Project -> Scan
        check(root->op == LogicalOp::Sort, "root is Sort");
        check(root->sort_keys.size() == 2, "sort has 2 keys");
        if (root->sort_keys.size() == 2) {
            // Both keys are selected columns -> positional refs into the output
            // (name #1 DESC, id #0 ASC), no hidden sort column needed.
            check(root->sort_keys[0].descending, "key[0] DESC (name)");
            expect_col_ref(root->sort_keys[0].expr, 1, "key[0] -> name #1");
            check(!root->sort_keys[1].descending, "key[1] ASC (id)");
            expect_col_ref(root->sort_keys[1].expr, 0, "key[1] -> id #0");
        }
        // Sort is schema-preserving here: same output as its Project child.
        check(root->output.size() == 2, "sort preserves 2 cols");
        const LogicalNode* project = only_child(root);
        check(project && project->op == LogicalOp::Project, "child is Project");
        check(project && project->exprs.size() == 2, "no hidden sort column added");
    });
}

void test_order_by_nulls(const InMemoryCatalog& cat) {
    std::printf("[test] ... ORDER BY name DESC NULLS FIRST\n");
    with_plan(cat, "SELECT id FROM users ORDER BY name DESC NULLS FIRST",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Sort, "root is Sort");
        check(root->sort_keys.size() == 1, "1 sort key");
        if (root->sort_keys.size() == 1) {
            check(root->sort_keys[0].descending, "DESC");
            check(root->sort_keys[0].nulls_order_explicit, "NULLS explicit");
            check(root->sort_keys[0].nulls_first, "NULLS FIRST");
        }
        // ORDER BY a NON-selected column (name): the Project is extended with a
        // hidden sort column [id, name], the sort key references it at #1, and
        // the Sort drops it so the visible output is just [id].
        check(root->output.size() == 1, "sort output is visible [id] only");
        if (root->sort_keys.size() == 1) {
            expect_col_ref(root->sort_keys[0].expr, 1, "sort key -> hidden name #1");
        }
        const LogicalNode* project = only_child(root);
        check(project && project->op == LogicalOp::Project, "child is Project");
        check(project && project->output.size() == 2, "Project extended to [id, name]");
        check(project && project->exprs.size() == 2, "Project has hidden sort expr");
        if (project && project->output.size() == 2) {
            expect_col(project->output[1], "name", DataType::VarChar, true, "hidden col");
            expect_col_ref(project->exprs[1], 1, "hidden expr -> scan name #1");
        }
    });
}

// ORDER BY by output ordinal (`ORDER BY 1`) references the N-th visible column.
void test_order_by_ordinal(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, name FROM users ORDER BY 2 DESC\n");
    with_plan(cat, "SELECT id, name FROM users ORDER BY 2 DESC",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Sort, "root is Sort");
        check(root->sort_keys.size() == 1, "1 sort key");
        if (root->sort_keys.size() == 1) {
            check(root->sort_keys[0].descending, "DESC");
            // ORDER BY 2 -> the 2nd output column (name), a ref to #1.
            expect_col_ref(root->sort_keys[0].expr, 1, "ordinal 2 -> name #1");
        }
    });
}

// A non-selected column repeated in ORDER BY reuses a single hidden sort column
// (the hidden column carries the source column's provenance ids, so the second
// key resolves against it rather than appending a duplicate).
void test_order_by_repeated_hidden_dedup(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users ORDER BY name, name\n");
    with_plan(cat, "SELECT id FROM users ORDER BY name, name",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Sort, "root is Sort");
        check(root->sort_keys.size() == 2, "2 sort keys");
        const LogicalNode* project = only_child(root);
        // One hidden column added, not two: Project is [id, name] (2 cols).
        check(project && project->output.size() == 2, "single hidden column reused");
        if (root->sort_keys.size() == 2) {
            expect_col_ref(root->sort_keys[0].expr, 1, "key[0] -> hidden name #1");
            expect_col_ref(root->sort_keys[1].expr, 1, "key[1] -> same hidden #1");
        }
    });
}

// SELECT DISTINCT ... ORDER BY <non-selected column> is illegal: the sort item
// must appear in the select list, so the bind fails cleanly (no hidden column
// is added below the Distinct, which would change de-duplication).
void test_order_by_distinct_nonoutput_rejected(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT DISTINCT id FROM users ORDER BY name (rejected)\n");
    db25::parser::Parser parser;
    auto parsed = parser.parse("SELECT DISTINCT id FROM users ORDER BY name");
    check(parsed.has_value(), "parse DISTINCT+ORDER BY");
    if (!parsed) {
        return;
    }
    Analyzer analyzer(cat);
    analyzer.analyze(parsed.value());
    Binder binder(analyzer, cat);
    BindResult res = binder.bind(parsed.value());
    check(!res.ok, "bind rejects ORDER BY of a non-selected column under DISTINCT");
}

// -------------------------------------------------------------------------
// SELECT without FROM: Project over a synthetic single-row Values input.

void test_select_no_from_const(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT 1 + 2 AS s\n");
    with_plan(cat, "SELECT 1 + 2 AS s", [](const LogicalNode* root) {
        // Project -> Values(one empty row)
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* values = only_child(root);
        check(values && values->op == LogicalOp::Values, "child is Values");
        check(values && values->value_rows.size() == 1, "one synthetic row");
        check(values && values->value_rows.size() == 1 && values->value_rows[0].empty(),
              "synthetic row has zero columns");
        // The projected `1 + 2` computes over the empty Values row.
        check(root->exprs.size() == 1 && root->exprs[0] &&
                  root->exprs[0]->kind == ExprKind::BinaryOp,
              "projection is the 1+2 BinaryOp");
        check(root->output.size() == 1, "one output col");
        if (root->output.size() == 1) {
            expect_col(root->output[0], "s", DataType::Integer, false, "const");
        }
    });
}

void test_select_no_from_func(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT now()\n");
    with_plan(cat, "SELECT now()", [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* values = only_child(root);
        check(values && values->op == LogicalOp::Values, "child is Values");
        check(root->output.size() == 1, "one output col");
    });
}

// -------------------------------------------------------------------------
// Comma / CROSS joins, and JOIN ... USING.

void test_comma_join(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.id FROM users u, orders o\n");
    with_plan(cat, "SELECT u.id, o.total FROM users u, orders o",
              [](const LogicalNode* root) {
        // Project -> Join(CROSS) -> [Scan users, Scan orders]
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "child is Join");
        check(join && join->join_type == db25::ast::JoinType::Cross, "CROSS join");
        check(join && join->predicate == nullptr, "no predicate");
        check(join && join->child_count() == 2, "join has 2 inputs");
        check(join && join->output.size() == 5, "cross output = 5 cols");
    });
}

// Comma binds looser than JOIN: `emp, users u RIGHT JOIN orders o` is
// `emp CROSS (users RIGHT JOIN orders)`, so the RIGHT join null-supplies only
// `users` (its own left operand) - NOT the comma-joined `emp`. Regression: the
// FROM list was folded left-associatively into `(emp CROSS users) RIGHT JOIN
// orders`, whose whole left input (including emp) was null-extended, so a NOT
// NULL column of the comma table came out nullable.
void test_comma_then_outer_join_nullability(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT emp.id FROM emp, users u RIGHT JOIN orders o ON ...\n");
    with_plan(cat,
              "SELECT emp.id, u.name FROM emp, users u "
              "RIGHT JOIN orders o ON u.id = o.user_id",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        // Tree shape: Project -> Join(CROSS) -> [Scan emp, Join(RIGHT)].
        const LogicalNode* cross = only_child(root);
        check(cross && cross->op == LogicalOp::Join &&
                  cross->join_type == db25::ast::JoinType::Cross,
              "child is a CROSS join (comma binds looser than JOIN)");
        if (cross && cross->child_count() == 2) {
            check(cross->child(0)->op == LogicalOp::Scan &&
                      cross->child(0)->table_name == "emp",
                  "CROSS left is the bare comma relation emp");
            check(cross->child(1)->op == LogicalOp::Join &&
                      cross->child(1)->join_type == db25::ast::JoinType::Right,
                  "CROSS right is the (users RIGHT JOIN orders) group");
        }
        // emp.id is comma-joined, NOT on the RIGHT join's null-supplying side, so
        // it keeps its base NOT NULL. u.name is on the null-supplied left of the
        // RIGHT join, so it is nullable.
        check(root->output.size() == 2, "project has 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "id", DataType::Integer, false,
                       "comma emp.id stays NOT NULL");
            expect_col(root->output[1], "name", DataType::VarChar, true,
                       "RIGHT-join left u.name is nullable");
        }
    });

    // FULL variant: the comma relation still keeps NOT NULL; both sides of the
    // FULL join are null-supplied.
    with_plan(cat,
              "SELECT emp.id FROM emp, users u "
              "FULL JOIN orders o ON u.id = o.user_id",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "full: root is Project");
        if (!root->output.empty()) {
            expect_col(root->output[0], "id", DataType::Integer, false,
                       "full: comma emp.id stays NOT NULL");
        }
    });
}

void test_cross_join(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.id FROM users u CROSS JOIN orders o\n");
    with_plan(cat, "SELECT u.id FROM users u CROSS JOIN orders o",
              [](const LogicalNode* root) {
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "child is Join");
        check(join && join->join_type == db25::ast::JoinType::Cross, "CROSS join");
        check(join && join->output.size() == 5, "cross output = 5 cols");
    });
}

void test_join_using(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users u JOIN orders o USING (id)\n");
    with_plan(cat, "SELECT u.name, o.total FROM users u JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        // Project -> Join -> [Scan users, Scan orders]
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "child is Join");
        // USING(id): the frame is the full concat - 2 (users) + 3 (orders) = 5.
        // The merged `id` is the left copy (visible); the right `id` copy is kept
        // HIDDEN (excluded from `*`) so a qualified `orders.id` still resolves.
        check(join && join->output.size() == 5, "USING keeps full frame -> 5 cols");
        if (join && join->output.size() == 5) {
            int visible_id = 0, hidden_id = 0;
            for (const auto& c : join->output) {
                if (c.name == "id") (c.hidden ? ++hidden_id : ++visible_id);
            }
            check(visible_id == 1, "exactly one visible (merged) id column");
            check(hidden_id == 1, "the right id copy is kept hidden");
        }
        // The USING equality must be materialized as the join predicate over the
        // pre-merge (left ++ right) frame: users.id (slot 0) = orders.id
        // (slot 2 = left_width 2 + 0). Without it the join is a silent cross
        // product that merely *looks* right because the output schema is merged.
        check(join && join->predicate != nullptr, "USING carries an equi-predicate");
        if (join && join->predicate) {
            const auto& p = *join->predicate;
            check(p.kind == ExprKind::BinaryOp &&
                      p.bin_op == db25::ast::BinaryOp::Equal,
                  "USING predicate is an '=' BinaryOp");
            if (p.kind == ExprKind::BinaryOp && p.children.size() == 2) {
                check(p.children[0]->kind == ExprKind::ColumnRef &&
                          p.children[0]->input_index == 0,
                      "lhs is left.id (slot 0)");
                check(p.children[1]->kind == ExprKind::ColumnRef &&
                          p.children[1]->input_index == 2,
                      "rhs is right.id (slot 2 = left_width + 0)");
            }
        }
    });
}

// NATURAL JOIN is USING over the columns common to both inputs. users and
// orders share exactly `id`, so `users u NATURAL JOIN orders o` must produce the
// identical merged frame and equi-predicate as `... USING (id)`.
void test_natural_join(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.name, o.total FROM users u NATURAL JOIN orders o\n");
    with_plan(cat, "SELECT u.name, o.total FROM users u NATURAL JOIN orders o",
              [](const LogicalNode* root) {
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "child is Join");
        // Common column id: full frame 2 (users) + 3 (orders) = 5, the right id
        // copy kept hidden (one visible merged id, one hidden right copy).
        check(join && join->output.size() == 5, "NATURAL keeps full frame -> 5 cols");
        if (join && join->output.size() == 5) {
            int visible_id = 0, hidden_id = 0;
            for (const auto& c : join->output) {
                if (c.name == "id") (c.hidden ? ++hidden_id : ++visible_id);
            }
            check(visible_id == 1, "exactly one visible (merged) id column");
            check(hidden_id == 1, "the right id copy is kept hidden");
        }
        // Equi-predicate over the pre-merge frame: users.id (#0) = orders.id (#2).
        check(join && join->predicate != nullptr, "NATURAL carries an equi-predicate");
        if (join && join->predicate) {
            const auto& p = *join->predicate;
            check(p.kind == ExprKind::BinaryOp &&
                      p.bin_op == db25::ast::BinaryOp::Equal,
                  "NATURAL predicate is an '=' BinaryOp");
            if (p.kind == ExprKind::BinaryOp && p.children.size() == 2) {
                check(p.children[0]->kind == ExprKind::ColumnRef &&
                          p.children[0]->input_index == 0,
                      "lhs is users.id (slot 0)");
                check(p.children[1]->kind == ExprKind::ColumnRef &&
                          p.children[1]->input_index == 2,
                      "rhs is orders.id (slot 2 = left_width + 0)");
            }
        }
    });
}

// NATURAL over inputs with NO common column degrades to a plain cross join
// (empty common-column set), exactly as SQL specifies. users and emp share no
// column names in this catalog... but they both have `id`; use a subquery alias
// that renames columns so there is genuinely no overlap.
void test_natural_join_no_common_is_cross(const InMemoryCatalog& cat) {
    std::printf("[test] users u NATURAL JOIN (SELECT total AS amt FROM orders) t\n");
    with_plan(cat,
              "SELECT u.name FROM users u NATURAL JOIN (SELECT total AS amt FROM orders) t",
              [](const LogicalNode* root) {
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "child is Join");
        // No shared column -> nothing merged, no predicate: a cross product.
        check(join && join->output.size() == 3, "no merge -> users(2) ++ t(1) = 3 cols");
        check(join && join->predicate == nullptr, "no common column -> cross join");
    });
}

// NATURAL LEFT JOIN routes the outer-join kind through the same merge path:
// Left join type, merged frame, equi-predicate, right side null-extended.
void test_natural_left_join(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.name, o.total FROM users u NATURAL LEFT JOIN orders o\n");
    with_plan(cat, "SELECT u.name, o.total FROM users u NATURAL LEFT JOIN orders o",
              [](const LogicalNode* root) {
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "child is Join");
        check(join && join->join_type == db25::ast::JoinType::Left, "NATURAL LEFT -> Left");
        check(join && join->output.size() == 5, "full frame (hidden right id) -> 5 cols");
        check(join && join->predicate != nullptr, "carries the equi-predicate");
    });
}

// RIGHT / FULL JOIN ... USING / NATURAL: the merged column is COALESCE(left,
// right), NOT the bare left copy. Under a RIGHT join the left copy is NULL for
// every right row with no left match, so keeping it would make a bare reference
// to the join key read NULL (verified end-to-end: SQLite and DuckDB return the
// key values, DB25 previously returned all-NULL). The binder must wrap the join
// in a Project that emits COALESCE(left.id, right.id) over the full frame, with
// the merged column keeping the LEFT column's identity.
void expect_coalesce_merge(const LogicalNode* root, db25::ast::JoinType jt,
                           const std::string& ctx) {
    // Project(outer SELECT) -> Project(COALESCE merge) -> Join(jt) -> [scans].
    const LogicalNode* merge = only_child(root);
    check(merge && merge->op == LogicalOp::Project, ctx + ": merge is a Project");
    if (!merge || merge->op != LogicalOp::Project) return;
    // users(id,name) + orders(id,user_id,total), merged on id. The merged id is a
    // VISIBLE COALESCE column PLUS a HIDDEN copy of each side (so a qualified
    // u.id / o.id resolves to that side's own column, NULL on the null-supplying
    // side): id(coalesce), id(left,hidden), id(right,hidden), name, user_id,
    // total = 6 cols. `SELECT *` still shows id once (the two copies are hidden).
    check(merge->output.size() == 6,
          ctx + ": merged frame -> 6 cols (COALESCE + 2 hidden per-side copies)");
    int visible_id = 0, hidden_id = 0;
    for (const auto& c : merge->output) {
        if (c.name == "id") (c.hidden ? ++hidden_id : ++visible_id);
    }
    check(visible_id == 1 && hidden_id == 2,
          ctx + ": one visible COALESCE id + two hidden per-side copies");
    // Both users.id and orders.id are NOT NULL, so COALESCE(id,id) is NOT NULL,
    // even under RIGHT / FULL where each side is otherwise null-supplied. It is
    // the visible column at slot 0; the two hidden copies follow it.
    check(!merge->output.empty() && merge->output[0].name == "id" &&
              !merge->output[0].hidden && !merge->output[0].nullable,
          ctx + ": merged id is the visible NOT-NULL column at slot 0");
    check(merge->output.size() >= 3 && merge->output[1].name == "id" &&
              merge->output[1].hidden && merge->output[2].name == "id" &&
              merge->output[2].hidden,
          ctx + ": slots 1,2 are the hidden per-side id copies");
    // expr[0] materializes COALESCE(left.id #0, right.id #2) over the full frame.
    check(!merge->exprs.empty() &&
              merge->exprs[0]->kind == ExprKind::ScalarFunction &&
              merge->exprs[0]->func_name == "COALESCE",
          ctx + ": merged id is a COALESCE call");
    if (!merge->exprs.empty() && merge->exprs[0]->kind == ExprKind::ScalarFunction &&
        merge->exprs[0]->children.size() == 2) {
        const auto& coa = *merge->exprs[0];
        check(coa.children[0]->kind == ExprKind::ColumnRef &&
                  coa.children[0]->input_index == 0,
              ctx + ": COALESCE arg0 is left.id (slot 0)");
        check(coa.children[1]->kind == ExprKind::ColumnRef &&
                  coa.children[1]->input_index == 2,
              ctx + ": COALESCE arg1 is right.id (slot 2 = left_width + 0)");
    }
    // The join underneath keeps BOTH id copies (full left ++ right frame = 5).
    const LogicalNode* join = only_child(merge);
    check(join && join->op == LogicalOp::Join, ctx + ": child is Join");
    check(join && join->join_type == jt, ctx + ": join type preserved");
    check(join && join->output.size() == 5, ctx + ": join keeps full frame (5)");
    check(join && join->predicate != nullptr, ctx + ": carries the equi-predicate");
}

void test_right_join_using_coalesces(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users u RIGHT JOIN orders o USING (id)\n");
    with_plan(cat, "SELECT id FROM users u RIGHT JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        expect_coalesce_merge(root, db25::ast::JoinType::Right, "RIGHT USING");
    });
}

void test_full_join_using_coalesces(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users u FULL JOIN orders o USING (id)\n");
    with_plan(cat, "SELECT id FROM users u FULL JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        expect_coalesce_merge(root, db25::ast::JoinType::Full, "FULL USING");
    });
}

void test_natural_right_join_coalesces(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users u NATURAL RIGHT JOIN orders o\n");
    with_plan(cat, "SELECT id FROM users u NATURAL RIGHT JOIN orders o",
              [](const LogicalNode* root) {
        expect_coalesce_merge(root, db25::ast::JoinType::Right, "NATURAL RIGHT");
    });
}

// INNER / LEFT keep the merged value in the left copy (no COALESCE Project): the
// left side is never null-supplied there, so the left copy already IS the merged
// value. The right copy is retained but HIDDEN (for qualified `right.c`).
void test_left_join_using_keeps_left_copy(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users u LEFT JOIN orders o USING (id)\n");
    with_plan(cat, "SELECT id FROM users u LEFT JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "LEFT USING: child is Join (no merge Project)");
        check(join && join->join_type == db25::ast::JoinType::Left, "LEFT preserved");
        // Full frame (users 2 + orders 3 = 5) with the right id copy hidden.
        check(join && join->output.size() == 5, "LEFT USING: full frame -> 5 cols");
        int hidden_id = 0, visible_id = 0;
        for (const auto& c : join->output) {
            if (c.name == "id") (c.hidden ? ++hidden_id : ++visible_id);
        }
        check(visible_id == 1 && hidden_id == 1,
              "one visible merged id + one hidden right id");
    });
}

// A QUALIFIED reference to a USING/NATURAL merged column's null-supplying side
// must resolve to THAT side's own column (NULL for an unmatched outer-join row),
// not to the left/merged copy. Regression: the right copy was dropped, so `o.id`
// on a LEFT join read the left value, and `WHERE o.id = ...` on an INNER join
// failed to bind entirely.
void test_using_qualified_null_side(const InMemoryCatalog& cat) {
    std::printf("[test] qualified null-supplying-side ref of a USING merged column\n");

    // LEFT JOIN: `o.id` resolves to the RIGHT (orders) id copy - a distinct slot
    // from `u.id`, and nullable (NULL for a left row with no right match).
    with_plan(cat, "SELECT u.id, o.id FROM users u LEFT JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->exprs.size() == 2,
              "left-null-side: project of 2");
        if (root->exprs.size() == 2) {
            check(root->exprs[0]->kind == ExprKind::ColumnRef &&
                      root->exprs[1]->kind == ExprKind::ColumnRef &&
                      root->exprs[0]->input_index != root->exprs[1]->input_index,
                  "u.id and o.id resolve to DIFFERENT slots (right copy not dropped)");
        }
        if (root->output.size() == 2) {
            check(!root->output[0].nullable, "u.id is NOT NULL (left preserved)");
            check(root->output[1].nullable, "o.id is nullable (null-supplying side)");
        }
    });

    // INNER JOIN: `WHERE o.id = 5` must BIND (the right id copy is present).
    {
        db25::parser::Parser parser;
        auto parsed = parser.parse(
            "SELECT u.id FROM users u JOIN orders o USING (id) WHERE o.id = 5");
        check(parsed.has_value(), "parse inner where-o.id");
        if (parsed) {
            Analyzer analyzer(cat);
            analyzer.analyze(parsed.value());
            Binder binder(analyzer, cat);
            BindResult res = binder.bind(parsed.value());
            check(res.ok, "inner USING: WHERE on the right merged copy binds");
        }
    }

    // `SELECT *` still shows the merged column exactly once (hidden copy excluded).
    with_plan(cat, "SELECT * FROM users u JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        int id_count = 0;
        for (const auto& c : root->output) if (c.name == "id") ++id_count;
        check(id_count == 1, "star: merged id shown exactly once");
    });
}

// The symmetric RIGHT / FULL case: a USING/NATURAL merged column is a COALESCE,
// and BOTH the left and right individual copies are kept HIDDEN so a qualified
// u.id / o.id resolves to that side's own column (NULL on the null-supplying
// side), while a bare `id` and `SELECT *` see the coalesced value. Regression:
// both copies were collapsed into the single COALESCE column, so u.id and o.id
// both read COALESCE(u.id, o.id) - the wrong (non-NULL) value for a non-matching
// outer-join row.
void test_right_full_using_qualified_sides(const InMemoryCatalog& cat) {
    std::printf("[test] RIGHT/FULL USING: qualified u.id / o.id resolve to per-side copies\n");

    // RIGHT: u.id is the null-supplying (left) side -> nullable; o.id is the
    // present (right) side -> NOT NULL; the two are DISTINCT slots, and neither is
    // the bare COALESCE.
    with_plan(cat, "SELECT id, u.id, o.id FROM users u RIGHT JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->exprs.size() == 3,
              "right-sides: project of 3");
        if (root->exprs.size() == 3) {
            const auto i0 = root->exprs[0]->input_index;  // bare id -> COALESCE
            const auto i1 = root->exprs[1]->input_index;  // u.id -> left copy
            const auto i2 = root->exprs[2]->input_index;  // o.id -> right copy
            check(root->exprs[0]->kind == ExprKind::ColumnRef &&
                      root->exprs[1]->kind == ExprKind::ColumnRef &&
                      root->exprs[2]->kind == ExprKind::ColumnRef,
                  "all three lower to ColumnRefs");
            check(i0 != i1 && i0 != i2 && i1 != i2,
                  "bare id, u.id, o.id resolve to THREE distinct slots");
        }
        if (root->output.size() == 3) {
            // Per-side nullability (the meaningful F4 correctness): u.id is the
            // null-supplying left side -> nullable; o.id is the present right
            // side -> NOT NULL. (output[0] is the bare merged id, whose outer
            // nullability is the analyzer's call, not asserted here.)
            check(root->output[1].nullable, "u.id nullable (left null-supplied under RIGHT)");
            check(!root->output[2].nullable, "o.id NOT NULL (right side present)");
        }
    });

    // FULL: both sides are null-supplying, so u.id and o.id are both nullable and
    // still distinct slots.
    with_plan(cat, "SELECT users.id, orders.id FROM users FULL JOIN orders USING (id)",
              [](const LogicalNode* root) {
        check(root->exprs.size() == 2, "full-sides: project of 2");
        if (root->exprs.size() == 2 && root->output.size() == 2) {
            check(root->exprs[0]->input_index != root->exprs[1]->input_index,
                  "users.id and orders.id resolve to DIFFERENT slots");
            check(root->output[0].nullable && root->output[1].nullable,
                  "both sides nullable under FULL");
        }
    });

    // `SELECT *` over a RIGHT USING join shows the merged id exactly once (both
    // hidden copies excluded).
    with_plan(cat, "SELECT * FROM users u RIGHT JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        int id_count = 0;
        for (const auto& c : root->output) if (c.name == "id") ++id_count;
        check(id_count == 1, "right star: merged id shown exactly once");
    });
}

// The merged USING/NATURAL key of a RIGHT / NATURAL-RIGHT join is
// COALESCE(left, right) over a preserved (non-null) right side, so it is NON-NULL.
// The top Project's output schema (seeded from the analyzer's conservatively-
// nullable projection annotation) must agree with the ColumnRef expr and the
// child COALESCE, which both type it non-null - not declare it nullable.
void test_right_using_merged_key_output_notnull(const InMemoryCatalog& cat) {
    std::printf("[test] RIGHT/NATURAL-RIGHT USING merged key: output schema is NOT NULL\n");
    // users(id NOT NULL,...), orders(id NOT NULL,...): the merged id is non-null.
    with_plan(cat, "SELECT id FROM users u RIGHT JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->output.size() == 1,
              "right: project of 1");
        if (!root->output.empty()) {
            check(!root->output[0].nullable,
                  "right: merged id output schema is NOT NULL (matches COALESCE)");
        }
        // The projected expr references the child's non-null COALESCE slot.
        if (!root->exprs.empty() && root->exprs[0]->kind == ExprKind::ColumnRef) {
            const LogicalNode* child = only_child(root);
            const auto idx = root->exprs[0]->input_index;
            check(child && idx < child->output.size() && !child->output[idx].nullable,
                  "right: child slot for merged id is non-null (expr/schema agree)");
        }
    });
    // LEFT / INNER were already non-null; assert they still are (no regression).
    with_plan(cat, "SELECT id FROM users u LEFT JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        check(!root->output.empty() && !root->output[0].nullable,
              "left: merged id still NOT NULL");
    });
    with_plan(cat, "SELECT id FROM users u JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        check(!root->output.empty() && !root->output[0].nullable,
              "inner: merged id still NOT NULL");
    });
}

// A NATURAL join whose common column is ambiguous on one side (here `id` occurs
// in both users and emp on the left) must be REJECTED, not silently tie only the
// first slot and leave the duplicate unconstrained (which returns wrong rows).
// A parenthesized join group in FROM, `( a JOIN b ) JOIN c`, binds to a nested
// join: the group is the left input of the outer join (previously the parser
// dropped the whole FROM clause and this failed to bind).
void test_parenthesized_join_group(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.id FROM (users u JOIN orders o ON ...) JOIN emp e ON ...\n");
    with_plan(cat,
              "SELECT u.id FROM (users u JOIN orders o ON o.user_id = u.id) "
              "JOIN emp e ON e.id = u.id",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* outer = only_child(root);
        check(outer && outer->op == LogicalOp::Join, "child is the outer Join");
        if (outer && outer->child_count() == 2) {
            // Left input is the parenthesized group: Join(users, orders).
            check(outer->child(0)->op == LogicalOp::Join,
                  "group binds to a nested Join (the outer join's left input)");
            check(outer->child(1)->op == LogicalOp::Scan,
                  "outer join's right input is Scan emp");
        }
    });
}

void test_natural_join_ambiguous_rejected(const InMemoryCatalog& cat) {
    std::printf("[test] users u CROSS JOIN emp e NATURAL JOIN orders o (ambiguous id, rejected)\n");
    db25::parser::Parser parser;
    auto parsed = parser.parse(
        "SELECT u.name FROM users u CROSS JOIN emp e NATURAL JOIN orders o");
    check(parsed.has_value(), "parse ambiguous NATURAL");
    if (!parsed) {
        return;
    }
    Analyzer analyzer(cat);
    analyzer.analyze(parsed.value());
    Binder binder(analyzer, cat);
    BindResult res = binder.bind(parsed.value());
    check(!res.ok, "bind rejects a NATURAL join with an ambiguous common column");
}

void test_join_using_multi(const InMemoryCatalog& cat) {
    std::printf("[test] users u1 JOIN users u2 USING (id, name)\n");
    with_plan(cat, "SELECT u1.id FROM users u1 JOIN users u2 USING (id, name)",
              [](const LogicalNode* root) {
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "child is Join");
        // Both columns merge: the full frame is left (id, name) ++ right (id,
        // name) = 4, with BOTH right copies hidden (each merged column shows the
        // left copy; the right copies stay for qualified `u2.id` / `u2.name`).
        check(join && join->output.size() == 4, "both cols merge -> 4 cols (2 hidden)");
        {
            int hidden = 0;
            for (const auto& c : join->output) if (c.hidden) ++hidden;
            check(hidden == 2, "both right copies kept hidden");
        }
        // Two USING columns AND-chain into a conjunction of two equalities over
        // the pre-merge frame: (u1.id=u2.id) AND (u1.name=u2.name), with the
        // right side at left_width (2) + its own slot.
        check(join && join->predicate != nullptr, "multi-USING carries a predicate");
        if (join && join->predicate) {
            const auto& p = *join->predicate;
            check(p.kind == ExprKind::BinaryOp &&
                      p.bin_op == db25::ast::BinaryOp::And,
                  "top predicate is AND of two equalities");
            if (p.kind == ExprKind::BinaryOp && p.bin_op == db25::ast::BinaryOp::And &&
                p.children.size() == 2) {
                const auto& lhs = *p.children[0];  // id equality
                const auto& rhs = *p.children[1];  // name equality
                check(lhs.kind == ExprKind::BinaryOp &&
                          lhs.bin_op == db25::ast::BinaryOp::Equal &&
                          lhs.children[0]->input_index == 0 &&
                          lhs.children[1]->input_index == 2,
                      "id equality: 0 = 2");
                check(rhs.kind == ExprKind::BinaryOp &&
                          rhs.bin_op == db25::ast::BinaryOp::Equal &&
                          rhs.children[0]->input_index == 1 &&
                          rhs.children[1]->input_index == 3,
                      "name equality: 1 = 3");
            }
        }
    });
}

// `SELECT *` over a USING join projects the MERGED frame: the coalesced join
// column once, then the remaining columns. The analyzer's projection lists the
// un-merged columns (it does not model USING coalescing), so the binder trusts
// the child's merged output schema here - otherwise the arity check rejected it.
void test_select_star_over_using(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT * FROM users u JOIN orders o USING (id)\n");
    with_plan(cat, "SELECT * FROM users u JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        // users(id,name) ++ orders(id,user_id,total) with id merged -> 4 columns.
        check(root->output.size() == 4, "star over USING -> 4 merged cols");
        if (root->output.size() == 4) {
            check(root->output[0].name == "id", "col0 is the merged id");
            check(root->output[1].name == "name", "col1 users.name");
            check(root->output[2].name == "user_id", "col2 orders.user_id");
            check(root->output[3].name == "total", "col3 orders.total");
            int id_count = 0;
            for (const auto& c : root->output) if (c.name == "id") ++id_count;
            check(id_count == 1, "id appears exactly once (coalesced)");
        }
        check(root->exprs.size() == 4, "one column-ref per merged column");
    });
}

// A QUALIFIED `t.*` over a join is NOT a whole-child star: it must resolve to
// ONLY t's columns, not the whole join frame. The qualifier lives in the Star
// node's schema_name (its primary_text is always "*"), so table-scoped
// expansion matches each child column's relation alias against the qualifier.
void test_qualified_star_over_join_expands(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.* FROM users u JOIN orders o -> only u's cols\n");
    // Plain ON join: the child frame is [u.id, u.name, o.id, o.user_id,
    // o.total]; `u.*` must project exactly u's two columns (slots 0, 1).
    with_plan(cat, "SELECT u.* FROM users u INNER JOIN orders o ON u.id = o.user_id",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "qualified star: root is Project");
        check(root->output.size() == 2, "qualified star expands to u's 2 cols");
        check(root->exprs.size() == 2, "qualified star lowers to 2 column-ref exprs");
        if (root->output.size() == 2) {
            check(root->output[0].name == "id", "qualified star col[0] is u.id");
            check(root->output[1].name == "name", "qualified star col[1] is u.name");
        }
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "qualified star expr[0] -> slot 0");
            expect_col_ref(root->exprs[1], 1, "qualified star expr[1] -> slot 1");
        }
    });

    // A qualifier that names no relation in the FROM clause fails cleanly
    // rather than silently projecting nothing or the whole frame.
    db25::parser::Parser parser;
    auto parsed = parser.parse("SELECT bogus.* FROM users u INNER JOIN orders o ON u.id = o.user_id");
    check(parsed.has_value(), "parse qualified star with unknown qualifier");
    if (parsed) {
        Analyzer analyzer(cat);
        analyzer.analyze(parsed.value());
        Binder binder(analyzer, cat);
        BindResult res = binder.bind(parsed.value());
        check(!res.ok, "bind rejects q.* whose q matches no relation");
    }
}

// -------------------------------------------------------------------------
// Derived tables / subqueries in FROM.

// A CTE reference binds as a derived table: `WITH t AS (query) ... FROM t`
// resolves `t` to a fresh copy of the CTE body (previously the binder had no CTE
// handling and reported `unresolved table 't'`).
void test_cte(const InMemoryCatalog& cat) {
    std::printf("[test] common table expressions (WITH)\n");

    // Single reference: FROM t lowers to the CTE body's plan, aliased 't'.
    with_plan(cat, "WITH t AS (SELECT id, name FROM users) SELECT name FROM t",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "single: root is Project");
        const LogicalNode* body = only_child(root);
        check(body && body->op == LogicalOp::Project, "single: CTE body is a Project");
        check(body && body->alias == "t", "single: CTE reference aliased 't'");
        const LogicalNode* scan = only_child(body);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "users",
              "single: CTE body scans users");
        check(root->output.size() == 1, "single: one output col");
        if (root->output.size() == 1)
            expect_col(root->output[0], "name", DataType::VarChar, true, "cte-single");
    });

    // Two CTEs joined: both names resolve; the plan carries a Join.
    with_plan(cat,
              "WITH a AS (SELECT id FROM users), b AS (SELECT user_id FROM orders) "
              "SELECT a.id FROM a JOIN b ON a.id = b.user_id",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "multi: root is Project");
        bool has_join = false;
        std::function<void(const LogicalNode*)> walk = [&](const LogicalNode* n) {
            if (n == nullptr) return;
            if (n->op == LogicalOp::Join) has_join = true;
            for (std::size_t i = 0; i < n->child_count(); ++i) walk(n->child(i));
        };
        walk(root);
        check(has_join, "multi: two CTEs joined -> plan has a Join");
    });

    // A later CTE references an earlier one (b reads from a).
    with_plan(cat,
              "WITH a AS (SELECT id FROM users), b AS (SELECT id FROM a) SELECT id FROM b",
              [](const LogicalNode* root) {
        check(root != nullptr && root->op == LogicalOp::Project,
              "chained: b-over-a binds to a Project");
    });

    // A CTE shadows a same-named base table: FROM users resolves to the CTE, so
    // the output is the CTE's single column, not the users table's two.
    with_plan(cat, "WITH users AS (SELECT user_id FROM orders) SELECT user_id FROM users",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "shadow: root is Project");
        const LogicalNode* body = only_child(root);
        const LogicalNode* scan = body ? only_child(body) : nullptr;
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "orders",
              "shadow: CTE named 'users' shadows the base table (scans orders)");
    });

    // Column-list rename `WITH t(a, b)`: the renamed names resolve; `a` selects
    // the CTE body's first column (users.id).
    with_plan(cat, "WITH t(a, b) AS (SELECT id, name FROM users) SELECT a FROM t",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "col-list: root is Project");
        check(root->output.size() == 1 && root->output[0].name == "a",
              "col-list: renamed column 'a' resolves");
    });

    // A CTE whose body is a set operation binds end to end: the reference lowers
    // to the UNION subplan (previously the set-op body was not registered, so `t`
    // resolved to nothing and the bind failed with 'unresolved table').
    with_plan(cat,
              "WITH t AS (SELECT id FROM users UNION SELECT user_id FROM orders) "
              "SELECT id FROM t",
              [](const LogicalNode* root) {
        check(root != nullptr && root->op == LogicalOp::Project,
              "setop-cte: root is Project");
        bool has_setop = false;
        std::function<void(const LogicalNode*)> walk = [&](const LogicalNode* n) {
            if (n == nullptr) return;
            if (n->op == LogicalOp::SetOp) has_setop = true;
            for (std::size_t i = 0; i < n->child_count(); ++i) walk(n->child(i));
        };
        walk(root);
        check(has_setop, "setop-cte: the CTE body lowered to a SetOp");
    });

    // A self-reference that is NOT under `WITH RECURSIVE` - or a mutual cycle -
    // must be rejected gracefully, not crash: re-expanding the body would recurse
    // without bound and overflow the stack. (A genuine `WITH RECURSIVE` is bound
    // to a RecursiveCTE node instead; see test_recursive_cte.)
    {
        db25::parser::Parser parser;
        auto reject = [&](const char* sql, const char* what) {
            auto parsed = parser.parse(sql);
            check(parsed.has_value(), std::string{"parse: "} + sql);
            if (!parsed) return;
            Analyzer analyzer(cat);
            analyzer.analyze(parsed.value());
            Binder binder(analyzer, cat);
            BindResult res = binder.bind(parsed.value());
            check(!res.ok, what);  // rejected, and (the point) did not crash
        };
        // Plain (non-RECURSIVE) self-reference: not allowed to re-expand.
        reject("WITH r AS (SELECT id FROM r) SELECT id FROM r",
               "non-recursive self-reference rejected, no stack overflow");
        // Mutual recursion is not supported (neither is under RECURSIVE anyway).
        reject("WITH a AS (SELECT id FROM b), b AS (SELECT id FROM a) SELECT id FROM a",
               "recursive: mutual a<->b reference rejected");
        // A self-reference in the ANCHOR term is illegal even under RECURSIVE.
        reject("WITH RECURSIVE r(n) AS (SELECT n FROM r UNION ALL SELECT 1) SELECT n FROM r",
               "recursive: self-reference in the anchor term rejected");
    }

    // Guard: a CTE referenced twice in a self-join is TWO sequential (non-nested)
    // expansions, not a cycle - it must still bind.
    with_plan(cat,
              "WITH t AS (SELECT id FROM users) "
              "SELECT t1.id FROM t t1 JOIN t t2 ON t1.id = t2.id",
              [](const LogicalNode* root) {
        check(root != nullptr && root->op == LogicalOp::Project,
              "cte-self-join: binds (two references are not a recursive cycle)");
    });
}

// WITH RECURSIVE: the CTE lowers to a RecursiveCTE fixpoint node - anchor term
// (child 0) and recursive term (child 1) - and the recursive term's
// self-reference resolves to a WorkingTableScan carrying the CTE's columns.
// There is no executor: this REPRESENTS the recursion (Postgres-compatible base;
// DuckDB USING KEY is a separate follow-up).
void test_recursive_cte(const InMemoryCatalog& cat) {
    // Find the first node of a given op in the tree (pre-order).
    std::function<const LogicalNode*(const LogicalNode*, LogicalOp)> find_op =
        [&](const LogicalNode* n, LogicalOp op) -> const LogicalNode* {
        if (n == nullptr) return nullptr;
        if (n->op == op) return n;
        for (std::size_t i = 0; i < n->child_count(); ++i)
            if (const LogicalNode* f = find_op(n->child(i), op)) return f;
        return nullptr;
    };
    std::function<int(const LogicalNode*, LogicalOp)> count_op =
        [&](const LogicalNode* n, LogicalOp op) -> int {
        if (n == nullptr) return 0;
        int c = (n->op == op) ? 1 : 0;
        for (std::size_t i = 0; i < n->child_count(); ++i)
            c += count_op(n->child(i), op);
        return c;
    };

    // Canonical counter: WITH RECURSIVE t(n) AS (SELECT 1 UNION ALL SELECT n+1
    // FROM t WHERE n<10). The n column types Integer from the anchor.
    with_plan(cat,
              "WITH RECURSIVE t(n) AS "
              "(SELECT 1 UNION ALL SELECT n + 1 FROM t WHERE n < 10) SELECT n FROM t",
              [&](const LogicalNode* root) {
        const LogicalNode* rec = find_op(root, LogicalOp::RecursiveCTE);
        check(rec != nullptr, "recursive-cte: a RecursiveCTE node is produced");
        if (rec == nullptr) return;
        check(rec->set_op == SetOp::UnionAll, "recursive-cte: UNION ALL recorded");
        check(rec->table_name == "t", "recursive-cte: CTE name on the node");
        check(rec->child_count() == 2, "recursive-cte: anchor + recursive-term children");
        check(rec->output.size() == 1 && rec->output[0].name == "n" &&
                  rec->output[0].type == DataType::Integer,
              "recursive-cte: output is [n:Integer] from the anchor via the alias");
        // The recursive term (child 1) reads the working table.
        const LogicalNode* wt =
            rec->child_count() == 2 ? find_op(rec->child(1), LogicalOp::WorkingTableScan)
                                    : nullptr;
        check(wt != nullptr, "recursive-cte: recursive term reads a WorkingTableScan");
        if (wt != nullptr) {
            check(wt->table_name == "t", "recursive-cte: working table carries the CTE name");
            check(wt->output.size() == 1 && wt->output[0].name == "n",
                  "recursive-cte: working table exposes the CTE columns");
        }
        // The anchor term (child 0) does NOT read a working table.
        if (rec->child_count() == 2)
            check(find_op(rec->child(0), LogicalOp::WorkingTableScan) == nullptr,
                  "recursive-cte: anchor term has no working-table read");
    });

    // A base-table JOIN in the recursive term: the self-reference `anc a` joins
    // against `emp e`. `a.id` and `e.id` share emp's base id and are disambiguated
    // by qualifier - the working table binds like any other relation.
    with_plan(cat,
              "WITH RECURSIVE anc(id, mgr) AS ("
              "  SELECT id, user_id FROM orders WHERE user_id IS NULL "
              "  UNION ALL "
              "  SELECT o.id, o.user_id FROM orders o JOIN anc a ON o.user_id = a.id) "
              "SELECT id FROM anc",
              [&](const LogicalNode* root) {
        const LogicalNode* rec = find_op(root, LogicalOp::RecursiveCTE);
        check(rec != nullptr, "recursive-join: RecursiveCTE produced");
        if (rec == nullptr) return;
        check(rec->output.size() == 2, "recursive-join: two output columns");
        const LogicalNode* wt = find_op(rec->child(1), LogicalOp::WorkingTableScan);
        check(wt != nullptr, "recursive-join: recursive term reads working table");
        check(find_op(rec->child(1), LogicalOp::Join) != nullptr,
              "recursive-join: recursive term contains the JOIN");
    });

    // UNION (distinct) form records Union, not UnionAll.
    with_plan(cat,
              "WITH RECURSIVE t(n) AS "
              "(SELECT 1 UNION SELECT n + 1 FROM t WHERE n < 5) SELECT n FROM t",
              [&](const LogicalNode* root) {
        const LogicalNode* rec = find_op(root, LogicalOp::RecursiveCTE);
        check(rec != nullptr && rec->set_op == SetOp::Union,
              "recursive-cte: UNION (distinct) recorded");
    });

    // A recursive-keyword CTE whose body does NOT self-reference is an ordinary
    // CTE: it inlines, with no RecursiveCTE node.
    with_plan(cat,
              "WITH RECURSIVE t AS (SELECT id FROM users) SELECT id FROM t",
              [&](const LogicalNode* root) {
        check(find_op(root, LogicalOp::RecursiveCTE) == nullptr,
              "recursive-keyword non-recursive body: inlined, no RecursiveCTE node");
    });

    // The CTE referenced twice: each reference is an independent RecursiveCTE
    // subplan (mirrors the non-recursive self-join expansion).
    with_plan(cat,
              "WITH RECURSIVE t(n) AS "
              "(SELECT 1 UNION ALL SELECT n + 1 FROM t WHERE n < 10) "
              "SELECT a.n FROM t a JOIN t b ON a.n = b.n",
              [&](const LogicalNode* root) {
        check(count_op(root, LogicalOp::RecursiveCTE) == 2,
              "recursive-cte self-join: two independent RecursiveCTE subplans");
    });
}

// A pathologically deep expression tree (a long a+a+...+a chain) must be
// rejected gracefully, never overflow a recursive walk in analyze / lower_expr.
// The parser now caps a flat operator chain at its max_depth (the producer-owned
// AST-depth contract, matching the set-op cap), so such a chain is rejected AT
// PARSE - the primary, reachable defense, which keeps the deep tree from ever
// reaching a downstream walker. The binder additionally retains its own
// lower_expr depth guard (kMaxLowerDepth) as defense-in-depth. This runs under
// the ASan/UBSan CI job, which is what caught the old stack overflow.
void test_deep_expression_no_overflow(const InMemoryCatalog& cat) {
    std::printf("[test] deeply-nested expression rejected without stack overflow\n");
    // ~4000 additive levels: comfortably past the parser's depth bound and past
    // the depth that overflowed the stack before the guards (~2500).
    std::string sql = "SELECT 1";
    for (int i = 0; i < 4000; ++i) {
        sql += " + 1";
    }
    sql += " FROM users";

    db25::parser::Parser parser;
    auto parsed = parser.parse(sql);
    // Rejected up front by the parser's chain cap, so no downstream walker
    // (analyze / lower_expr) ever recurses into an unbounded tree.
    check(!parsed.has_value(), "deep additive chain rejected at parse, no overflow");

    // Control: a normal-depth expression of the same shape still binds.
    with_plan(cat, "SELECT 1 + 1 + 1 + 1 + 1 FROM users",
              [](const LogicalNode* root) {
        check(root != nullptr && root->op == LogicalOp::Project,
              "shallow additive chain still binds");
    });
}

// A self-join of two derived tables (or two references to one CTE) over the same
// body must keep the two sides' columns distinguishable: the ON predicate has to
// resolve `p.id` and `q.id` to DIFFERENT flat slots. Both instances share
// (table_id, column_id), so the reference alias is the only discriminator; the
// binder now stamps it onto each derived/CTE output column. Regression guard for
// the predicate collapsing to `#0 = #0` (a cross product).
void test_derived_self_join(const InMemoryCatalog& cat) {
    std::printf("[test] self-join of two derived tables over the same body\n");

    auto check_distinct_join_pred = [](const LogicalNode* root, const std::string& ctx) {
        const LogicalNode* join = nullptr;
        std::function<void(const LogicalNode*)> walk = [&](const LogicalNode* n) {
            if (n == nullptr) return;
            if (n->op == LogicalOp::Join && join == nullptr) join = n;
            for (std::size_t i = 0; i < n->child_count(); ++i) walk(n->child(i));
        };
        walk(root);
        check(join != nullptr, ctx + ": plan has a Join");
        const db25::plan::Expr* p = join ? join->predicate.get() : nullptr;
        check(p && p->kind == ExprKind::BinaryOp && p->children.size() == 2,
              ctx + ": ON is a binary comparison");
        if (p && p->kind == ExprKind::BinaryOp && p->children.size() == 2) {
            const auto* l = p->children[0].get();
            const auto* r = p->children[1].get();
            check(l && r && l->kind == ExprKind::ColumnRef && r->kind == ExprKind::ColumnRef,
                  ctx + ": both sides are column refs");
            if (l && r && l->kind == ExprKind::ColumnRef && r->kind == ExprKind::ColumnRef)
                check(l->input_index != r->input_index,
                      ctx + ": the two sides resolve to DIFFERENT slots (not #0 = #0)");
        }
    };

    with_plan(cat,
              "SELECT p.id FROM (SELECT id FROM users) p JOIN (SELECT id FROM users) q "
              "ON p.id = q.id",
              [&](const LogicalNode* root) { check_distinct_join_pred(root, "derived"); });

    with_plan(cat,
              "WITH t AS (SELECT id FROM users) SELECT x.id FROM t x JOIN t y ON x.id = y.id",
              [&](const LogicalNode* root) { check_distinct_join_pred(root, "cte"); });
}

// INSERT ... ON CONFLICT must be represented on the Insert node, not silently
// dropped (previously the clause parsed and the binder ignored it, so an upsert
// lowered identically to a plain INSERT).
void test_on_conflict(const InMemoryCatalog& cat) {
    std::printf("[test] INSERT ... ON CONFLICT\n");

    with_plan(cat, "INSERT INTO users (id, name) VALUES (10, 'x') ON CONFLICT (id) DO NOTHING",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Insert, "do-nothing: root is Insert");
        check(root->conflict_action == db25::plan::ConflictAction::DoNothing,
              "do-nothing: action recorded");
        check(root->conflict_columns.size() == 1 &&
              (root->conflict_columns.empty() || root->conflict_columns[0] == "id"),
              "do-nothing: conflict target is (id)");
    });

    with_plan(cat,
              "INSERT INTO users (id, name) VALUES (10, 'x') "
              "ON CONFLICT (id) DO UPDATE SET name = 'y'",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Insert, "do-update: root is Insert");
        check(root->conflict_action == db25::plan::ConflictAction::DoUpdate,
              "do-update: action recorded");
        check(root->assignments.size() == 1, "do-update: one SET assignment lowered");
    });

    with_plan(cat, "INSERT INTO users (id, name) VALUES (10, 'x')",
              [](const LogicalNode* root) {
        check(root->conflict_action == db25::plan::ConflictAction::None,
              "plain INSERT: no conflict action");
    });
}

// Multi-relation DML and DEFAULT VALUES: each used to fail (UPDATE...FROM /
// DELETE...USING at analyze with 'unresolved column'; DEFAULT VALUES at bind).
void test_dml_extensions(const InMemoryCatalog& cat) {
    std::printf("[test] UPDATE...FROM / DELETE...USING / DEFAULT VALUES\n");

    auto has_join = [](const LogicalNode* root) {
        bool found = false;
        std::function<void(const LogicalNode*)> walk = [&](const LogicalNode* n) {
            if (n == nullptr) return;
            if (n->op == LogicalOp::Join) found = true;
            for (std::size_t i = 0; i < n->child_count(); ++i) walk(n->child(i));
        };
        walk(root);
        return found;
    };

    // UPDATE ... FROM: the extra relation resolves and the plan carries a join.
    with_plan(cat,
              "UPDATE users SET id = o.user_id FROM orders o WHERE users.id = o.user_id",
              [&](const LogicalNode* root) {
        check(root->op == LogicalOp::Update, "update-from: root is Update");
        check(has_join(root), "update-from: extra relation joined under target");
    });

    // DELETE ... USING: same.
    with_plan(cat, "DELETE FROM users USING orders o WHERE users.id = o.user_id",
              [&](const LogicalNode* root) {
        check(root->op == LogicalOp::Delete, "delete-using: root is Delete");
        check(has_join(root), "delete-using: USING relation joined under target");
    });

    // INSERT ... DEFAULT VALUES: a one-empty-row Values source, no error. Uses
    // `nn` (all columns nullable); DEFAULT VALUES into a table with a NOT NULL
    // column that has no default is now correctly a NotNullViolation.
    with_plan(cat, "INSERT INTO nn DEFAULT VALUES", [](const LogicalNode* root) {
        check(root->op == LogicalOp::Insert, "default-values: root is Insert");
        const LogicalNode* src = only_child(root);
        check(src && src->op == LogicalOp::Values, "default-values: Values source");
    });
}

void test_derived_table(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT x FROM (SELECT id AS x FROM users) t\n");
    with_plan(cat, "SELECT x FROM (SELECT id AS x FROM users) t",
              [](const LogicalNode* root) {
        // Project -> (inner Project -> Scan users)
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* inner = only_child(root);
        check(inner && inner->op == LogicalOp::Project, "derived input is Project");
        check(inner && inner->alias == "t", "derived alias 't'");
        const LogicalNode* scan = only_child(inner);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "users",
              "inner scan users");
        check(root->output.size() == 1, "one output col");
        if (root->output.size() == 1) {
            // id is NOT NULL in the catalog; the alias renames it to x.
            expect_col(root->output[0], "x", DataType::Integer, false, "derived");
        }
    });
}

// -------------------------------------------------------------------------
// Set operations.

void test_union(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users UNION SELECT id FROM orders\n");
    with_plan(cat, "SELECT id FROM users UNION SELECT id FROM orders",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::SetOp, "root is SetOp");
        check(root->set_op == SetOp::Union, "UNION (distinct)");
        check(root->child_count() == 2, "two branches");
        if (root->child_count() == 2) {
            check(root->child(0)->op == LogicalOp::Project, "left branch Project");
            check(root->child(1)->op == LogicalOp::Project, "right branch Project");
        }
        check(root->output.size() == 1, "reconciled to 1 col");
        if (root->output.size() == 1) {
            check(root->output[0].type == DataType::Integer, "reconciled type Integer");
        }
    });
}

// A `WITH` above a top-level set operation: the CTE is in scope for every
// branch (Postgres). The parser attaches the CTEClause to the set-op node, so
// bind_setop must register the CTE before binding branches AND select the two
// branch children by kind (not read the first two children, which would pick
// up the CTEClause). Before the fix the branch bind failed - the analyzer now
// accepts these (its own C3 fix), so the binder gap became reachable.
void test_cte_above_setop(const InMemoryCatalog& cat) {
    std::printf("[test] WITH above a set operation (CTE in scope for both arms)\n");

    // CTE referenced in BOTH branches.
    with_plan(cat,
              "WITH t AS (SELECT id FROM users) "
              "SELECT id FROM t UNION SELECT id FROM t",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::SetOp, "root is SetOp");
        check(root->set_op == SetOp::Union, "UNION (distinct)");
        check(root->child_count() == 2, "two branches");
        if (root->child_count() == 2) {
            check(root->child(0)->op == LogicalOp::Project, "left branch Project");
            check(root->child(1)->op == LogicalOp::Project, "right branch Project");
        }
        check(root->output.size() == 1 && root->output[0].type == DataType::Integer,
              "reconciled to 1 Integer col");
    });

    // CTE referenced in one arm only, the other reads a base table (UNION ALL).
    with_plan(cat,
              "WITH t AS (SELECT id FROM users) "
              "SELECT id FROM t UNION ALL SELECT id FROM users",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::SetOp, "root is SetOp");
        check(root->set_op == SetOp::UnionAll, "UNION ALL");
        check(root->child_count() == 2, "two branches");
    });

    // A trailing ORDER BY / LIMIT scopes to the whole set operation and must
    // still be found when a leading CTEClause precedes the branches.
    with_plan(cat,
              "WITH t AS (SELECT id FROM users) "
              "SELECT id FROM t UNION SELECT id FROM t ORDER BY id LIMIT 5",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Limit, "root is Limit over the set op");
        const LogicalNode* sort = only_child(root);
        check(sort && sort->op == LogicalOp::Sort, "Limit over a Sort");
        const LogicalNode* setop = sort ? only_child(sort) : nullptr;
        check(setop && setop->op == LogicalOp::SetOp, "Sort over the SetOp");
    });
}

void test_union_all(const InMemoryCatalog& cat) {
    std::printf("[test] ... UNION ALL ...\n");
    with_plan(cat, "SELECT id FROM users UNION ALL SELECT id FROM orders",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::SetOp, "root is SetOp");
        check(root->set_op == SetOp::UnionAll, "UNION ALL");
    });
}

void test_intersect_except(const InMemoryCatalog& cat) {
    std::printf("[test] INTERSECT / EXCEPT\n");
    with_plan(cat, "SELECT id FROM users INTERSECT SELECT id FROM orders",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::SetOp, "root is SetOp");
        check(root->set_op == SetOp::Intersect, "INTERSECT");
    });
    with_plan(cat, "SELECT id FROM users EXCEPT SELECT id FROM orders",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::SetOp, "root is SetOp");
        check(root->set_op == SetOp::Except, "EXCEPT");
    });
}

void test_union_chain(const InMemoryCatalog& cat) {
    std::printf("[test] a UNION b UNION c  (left-associative)\n");
    with_plan(cat,
              "SELECT id FROM users UNION SELECT id FROM orders "
              "UNION SELECT id FROM emp",
              [](const LogicalNode* root) {
        // Left-associative: (users UNION orders) UNION emp.
        check(root->op == LogicalOp::SetOp, "root is SetOp");
        check(root->child_count() == 2, "two branches");
        if (root->child_count() == 2) {
            check(root->child(0)->op == LogicalOp::SetOp, "left child is nested SetOp");
            check(root->child(1)->op == LogicalOp::Project, "right child is Project");
        }
    });
}

void test_setop_trailing_order_by_limit_hoisted(const InMemoryCatalog& cat) {
    std::printf("[test] ... UNION ... ORDER BY id LIMIT 5  (hoisted above SetOp)\n");
    // A trailing ORDER BY / LIMIT that follows a set operation scopes to the
    // whole result. The parser hangs it on the last branch; the binder must
    // hoist the Sort and Limit ABOVE the SetOp (Limit -> Sort -> SetOp), NOT
    // leave them wrapping just the right branch.
    with_plan(cat,
              "SELECT id FROM users UNION SELECT user_id FROM orders "
              "ORDER BY id LIMIT 5",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Limit, "root is Limit (above the SetOp)");
        check(root->has_limit && root->limit == 5, "limit == 5");

        const LogicalNode* sort = only_child(root);
        check(sort && sort->op == LogicalOp::Sort, "Limit's child is Sort");
        check(sort && sort->sort_keys.size() == 1, "one sort key");
        if (sort && sort->sort_keys.size() == 1) {
            // The key resolves to the reconciled set-op output column #0, not to
            // a hidden base column of the last branch.
            const auto& e = sort->sort_keys[0].expr;
            check(e && e->kind == ExprKind::ColumnRef && e->input_index == 0,
                  "sort key is set-op output col #0");
        }

        const LogicalNode* setop = only_child(sort);
        check(setop && setop->op == LogicalOp::SetOp,
              "Sort's child is the SetOp (Sort/Limit are ABOVE it)");
        check(setop && setop->set_op == SetOp::Union, "UNION");
        check(setop && setop->child_count() == 2, "SetOp has two branches");
        if (setop && setop->child_count() == 2) {
            // Both branches are plain single-column Projects: the hidden
            // sort-only column the last branch grew for `ORDER BY id` is dropped
            // so the branch matches the reconciled arity.
            check(setop->child(0)->op == LogicalOp::Project, "left branch Project");
            check(setop->child(1)->op == LogicalOp::Project, "right branch Project");
            check(setop->child(1)->output.size() == 1,
                  "right branch has no hidden sort column");
        }
    });
}

void test_setop_no_order_by_unchanged(const InMemoryCatalog& cat) {
    std::printf("[test] A UNION B  (no ORDER BY: SetOp root, no Sort/Limit)\n");
    // Control: a set op with no trailing ORDER BY / LIMIT is untouched.
    with_plan(cat, "SELECT id FROM users UNION SELECT user_id FROM orders",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::SetOp, "root is SetOp (nothing hoisted)");
        check(root->set_op == SetOp::Union, "UNION");
    });
}

void test_setop_trailing_order_by_only(const InMemoryCatalog& cat) {
    std::printf("[test] A UNION B ORDER BY 1  (no LIMIT: only the Sort hoists)\n");
    with_plan(cat,
              "SELECT id FROM users UNION SELECT user_id FROM orders ORDER BY 1",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Sort, "root is Sort (above the SetOp)");
        const LogicalNode* setop = only_child(root);
        check(setop && setop->op == LogicalOp::SetOp, "Sort's child is the SetOp");
        check(setop && setop->set_op == SetOp::Union, "UNION");
    });
}

// -------------------------------------------------------------------------
// DML: INSERT / UPDATE / DELETE.

void test_insert_values(const InMemoryCatalog& cat) {
    std::printf("[test] INSERT INTO users (id, name) VALUES (1,'a'),(2,'b')\n");
    with_plan(cat, "INSERT INTO users (id, name) VALUES (1, 'a'), (2, 'b')",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Insert, "root is Insert");
        check(root->table_name == "users", "target users");
        check(root->target_columns.size() == 2, "2 target columns");
        if (root->target_columns.size() == 2) {
            check(root->target_columns[0] == "id", "target[0] id");
            check(root->target_columns[1] == "name", "target[1] name");
        }
        const LogicalNode* src = only_child(root);
        check(src && src->op == LogicalOp::Values, "source is Values");
        check(src && src->value_rows.size() == 2, "2 value rows");
        if (src && src->value_rows.size() == 2) {
            check(src->value_rows[0].size() == 2, "row 0 has 2 values");
            // Each VALUES entry lowers to an owned typed literal.
            if (src->value_rows[0].size() == 2) {
                check(src->value_rows[0][0] && src->value_rows[0][0]->kind == ExprKind::Literal,
                      "row0 col0 is a Literal");
                check(src->value_rows[0][1] && src->value_rows[0][1]->kind == ExprKind::Literal,
                      "row0 col1 is a Literal");
            }
        }
    });
}

void test_insert_select(const InMemoryCatalog& cat) {
    std::printf("[test] INSERT INTO users SELECT id, name FROM users\n");
    with_plan(cat, "INSERT INTO users SELECT id, name FROM users",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Insert, "root is Insert");
        check(root->table_name == "users", "target users");
        const LogicalNode* src = only_child(root);
        check(src && src->op == LogicalOp::Project, "source is a query (Project)");
    });
}

void test_update(const InMemoryCatalog& cat) {
    std::printf("[test] UPDATE users SET name = 'x' WHERE id = 1\n");
    with_plan(cat, "UPDATE users SET name = 'x' WHERE id = 1",
              [](const LogicalNode* root) {
        // Update -> Filter -> Scan
        check(root->op == LogicalOp::Update, "root is Update");
        check(root->table_name == "users", "target users");
        check(root->assignments.size() == 1, "1 SET assignment");
        if (root->assignments.size() == 1) {
            // SET name = 'x' -> target column id 2 (users.name), owned literal value.
            check(root->assignments[0].target_column_id == 2, "assigns column id 2 (name)");
            check(root->assignments[0].value &&
                      root->assignments[0].value->kind == ExprKind::Literal,
                  "assignment value is a Literal");
        }
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        check(filter && filter->predicate != nullptr, "filter has predicate");
        const LogicalNode* scan = only_child(filter);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "users",
              "leaf scan users");
    });
}

void test_update_no_where(const InMemoryCatalog& cat) {
    std::printf("[test] UPDATE users SET name = 'x'\n");
    with_plan(cat, "UPDATE users SET name = 'x'", [](const LogicalNode* root) {
        check(root->op == LogicalOp::Update, "root is Update");
        const LogicalNode* scan = only_child(root);
        check(scan && scan->op == LogicalOp::Scan, "child is Scan (no Filter)");
    });
}

void test_delete(const InMemoryCatalog& cat) {
    std::printf("[test] DELETE FROM users WHERE id = 1\n");
    with_plan(cat, "DELETE FROM users WHERE id = 1", [](const LogicalNode* root) {
        // Delete -> Filter -> Scan
        check(root->op == LogicalOp::Delete, "root is Delete");
        check(root->table_name == "users", "target users");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        const LogicalNode* scan = only_child(filter);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "users",
              "leaf scan users");
    });
}

// -------------------------------------------------------------------------
// RETURNING: a Returning projection on top of the DML node, its output schema
// resolved from the target table's catalog columns.

void test_update_returning(const InMemoryCatalog& cat) {
    std::printf("[test] UPDATE users SET name='x' WHERE id=1 RETURNING id, name\n");
    with_plan(cat, "UPDATE users SET name = 'x' WHERE id = 1 RETURNING id, name",
              [](const LogicalNode* root) {
        // Returning -> Update -> Filter -> Scan
        check(root->op == LogicalOp::Returning, "root is Returning");
        check(root->table_name == "users", "returning of users");
        check(root->output.size() == 2, "returning 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "id", DataType::Integer, false, "ret[0]");
            expect_col(root->output[1], "name", DataType::VarChar, true, "ret[1]");
        }
        const LogicalNode* upd = only_child(root);
        check(upd && upd->op == LogicalOp::Update, "child is Update");
        const LogicalNode* filter = only_child(upd);
        check(filter && filter->op == LogicalOp::Filter, "update child is Filter");
        const LogicalNode* scan = only_child(filter);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "users",
              "leaf scan users");
    });
}

void test_delete_returning(const InMemoryCatalog& cat) {
    std::printf("[test] DELETE FROM orders WHERE id=1 RETURNING id, total\n");
    with_plan(cat, "DELETE FROM orders WHERE id = 1 RETURNING id, total",
              [](const LogicalNode* root) {
        // Returning -> Delete -> Filter -> Scan
        check(root->op == LogicalOp::Returning, "root is Returning");
        check(root->table_name == "orders", "returning of orders");
        check(root->output.size() == 2, "returning 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "id", DataType::Integer, false, "ret[0]");
            expect_col(root->output[1], "total", DataType::Double, true, "ret[1]");
        }
        const LogicalNode* del = only_child(root);
        check(del && del->op == LogicalOp::Delete, "child is Delete");
    });
}

void test_delete_returning_star(const InMemoryCatalog& cat) {
    std::printf("[test] DELETE FROM users RETURNING *\n");
    with_plan(cat, "DELETE FROM users RETURNING *", [](const LogicalNode* root) {
        check(root->op == LogicalOp::Returning, "root is Returning");
        // RETURNING * expands to every column of users.
        check(root->output.size() == 2, "returning * -> 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "id", DataType::Integer, false, "ret*[0]");
            expect_col(root->output[1], "name", DataType::VarChar, true, "ret*[1]");
            check(root->output[0].column_id == 1, "star col carries column_id");
        }
        // RETURNING * lowers to owned positional column refs over the target row.
        check(root->exprs.size() == 2, "returning * -> 2 exprs");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "ret* expr[0]");
            expect_col_ref(root->exprs[1], 1, "ret* expr[1]");
        }
        const LogicalNode* del = only_child(root);
        check(del && del->op == LogicalOp::Delete, "child is Delete");
        const LogicalNode* scan = only_child(del);
        check(scan && scan->op == LogicalOp::Scan, "delete child is Scan (no WHERE)");
    });
}

// -------------------------------------------------------------------------
// Window functions: a Window node below the Project, carrying the window-call
// specs and appending one output column per function.

void test_window_rank(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, RANK() OVER (PARTITION BY name ORDER BY id) FROM users\n");
    with_plan(cat, "SELECT id, RANK() OVER (PARTITION BY name ORDER BY id) FROM users",
              [](const LogicalNode* root) {
        // Project -> Window -> Scan
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* window = only_child(root);
        check(window && window->op == LogicalOp::Window, "child is Window");
        check(window && window->window_functions.size() == 1, "1 window function");
        // The window call lowers to an owned WindowFunction whose OVER clause is
        // an owned WindowSpecIR with positional PARTITION BY (name #1) and
        // ORDER BY (id #0) keys over the input schema [id #0, name #1].
        if (window && window->window_functions.size() == 1) {
            const auto& w = *window->window_functions[0];
            check(w.kind == ExprKind::WindowFunction, "is a WindowFunction expr");
            check(w.func_name == "RANK", "window func is RANK");
            check(w.window.partition_by.size() == 1, "1 PARTITION BY key");
            if (w.window.partition_by.size() == 1) {
                expect_col_ref(w.window.partition_by[0], 1, "PARTITION BY name #1");
            }
            check(w.window.order_by.size() == 1, "1 ORDER BY key");
            if (w.window.order_by.size() == 1) {
                expect_col_ref(w.window.order_by[0].expr, 0, "ORDER BY id #0");
            }
        }
        // Window output = input columns (id, name) + the RANK result.
        check(window && window->output.size() == 3, "window output = 3 cols");
        if (window && window->output.size() == 3) {
            expect_col(window->output[2], "RANK", DataType::BigInt, false, "win[2]");
        }
        const LogicalNode* scan = only_child(window);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "users",
              "leaf scan users");
        check(root->output.size() == 2, "project 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "id", DataType::Integer, false, "proj[0]");
            expect_col(root->output[1], "RANK", DataType::BigInt, false, "proj[1]");
        }
        // The window function is precomputed by the Window child (output slot
        // #2); the projection references it by name rather than re-evaluating.
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "win proj expr[0] (id)");
            expect_col_ref(root->exprs[1], 2, "win proj expr[1] (RANK -> #2)");
        }
    });
}

void test_window_row_number(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, ROW_NUMBER() OVER (ORDER BY id) AS rn FROM users\n");
    with_plan(cat, "SELECT id, ROW_NUMBER() OVER (ORDER BY id) AS rn FROM users",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* window = only_child(root);
        check(window && window->op == LogicalOp::Window, "child is Window");
        check(window && window->window_functions.size() == 1, "1 window function");
        check(root->output.size() == 2, "project 2 cols");
        if (root->output.size() == 2) {
            // The alias renames the window output to rn.
            expect_col(root->output[1], "rn", DataType::BigInt, false, "proj[1]");
        }
    });
}

void test_window_sum(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT dept, SUM(sal) OVER (PARTITION BY dept) FROM emp\n");
    with_plan(cat, "SELECT dept, SUM(sal) OVER (PARTITION BY dept) FROM emp",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* window = only_child(root);
        check(window && window->op == LogicalOp::Window, "child is Window");
        check(window && window->window_functions.size() == 1, "1 window function");
        // SUM(sal) OVER (PARTITION BY dept): the aggregate argument (sal #2) and
        // the PARTITION BY key (dept #1) are positional refs over emp
        // [id #0, dept #1, sal #2].
        if (window && window->window_functions.size() == 1) {
            const auto& w = *window->window_functions[0];
            check(w.kind == ExprKind::WindowFunction && w.func_name == "SUM",
                  "window func is SUM");
            check(w.children.size() == 1, "SUM has 1 argument");
            if (w.children.size() == 1) {
                expect_col_ref(w.children[0], 2, "SUM arg (sal #2)");
            }
            check(w.window.partition_by.size() == 1, "1 PARTITION BY key");
            if (w.window.partition_by.size() == 1) {
                expect_col_ref(w.window.partition_by[0], 1, "PARTITION BY dept #1");
            }
        }
        check(root->output.size() == 2, "project 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[1], "SUM", DataType::Double, true, "proj[1]");
        }
    });
}

// Two un-aliased window calls of the SAME function must resolve to DISTINCT
// output columns. Both produce an output column named "SUM", so a by-name lookup
// pointed the projection at the first one for both (SUM(sal) OVER, SUM(id) OVER
// would both read SUM(sal)); the projection must map each call to the slot the
// Window node computed for it, by node identity.
void test_window_same_name_distinct_slots(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT SUM(sal) OVER w, SUM(id) OVER w FROM emp\n");
    with_plan(cat,
              "SELECT SUM(sal) OVER (PARTITION BY dept), "
              "SUM(id) OVER (PARTITION BY dept) FROM emp",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* window = only_child(root);
        check(window && window->op == LogicalOp::Window, "child is Window");
        check(window && window->window_functions.size() == 2,
              "two window functions computed");
        check(root->exprs.size() == 2, "two projected columns");
        if (root->exprs.size() == 2) {
            check(root->exprs[0]->kind == ExprKind::ColumnRef &&
                      root->exprs[1]->kind == ExprKind::ColumnRef,
                  "both projected columns reference the window output");
            check(root->exprs[0]->input_index != root->exprs[1]->input_index,
                  "the two same-named window calls resolve to DISTINCT slots");
        }
    });
}

// A window clause over a GROUPED query may reference an aggregate of the group.
// The Window node sits above the Aggregate, so an aggregate in the window's
// ORDER BY / PARTITION BY (`RANK() OVER (ORDER BY SUM(sal))`) must resolve to
// the precomputed Aggregate output column - not re-lower the raw `sal` the
// post-aggregation input no longer exposes. Regression: the window-function
// lowering loop ran with the aggregate frame inactive (unlike HAVING and the
// Project), so this legal query failed to bind ("column reference 'sal'
// resolves to no input or enclosing slot").
void test_window_over_aggregate(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT dept, SUM(sal), RANK() OVER (ORDER BY SUM(sal)) "
                "FROM emp GROUP BY dept\n");
    with_plan(cat,
              "SELECT dept, SUM(sal), RANK() OVER (ORDER BY SUM(sal)) "
              "FROM emp GROUP BY dept",
              [](const LogicalNode* root) {
        // Project <- Window <- Aggregate <- Scan emp.
        check(root->op == LogicalOp::Project, "root is Project");
        check(root->output.size() == 3, "project 3 cols (dept, SUM(sal), RANK)");
        const LogicalNode* window = only_child(root);
        check(window && window->op == LogicalOp::Window, "child is Window");
        check(window && window->window_functions.size() == 1, "1 window function");
        if (window && window->window_functions.size() == 1) {
            const auto& w = *window->window_functions[0];
            check(w.kind == ExprKind::WindowFunction && w.func_name == "RANK",
                  "window func is RANK");
            // The ORDER BY key is SUM(sal), which lives in the Aggregate output at
            // slot #1 (after the group key dept #0) - a positional ref, NOT a
            // re-lowered raw column.
            check(w.window.order_by.size() == 1, "1 ORDER BY key");
            if (w.window.order_by.size() == 1) {
                expect_col_ref(w.window.order_by[0].expr, 1,
                               "window ORDER BY SUM(sal) -> agg output #1");
            }
        }
        // Window output = [dept #0, SUM(sal) #1, RANK #2].
        check(window && window->output.size() == 3, "window output = 3 cols");
        const LogicalNode* agg = only_child(window);
        check(agg && agg->op == LogicalOp::Aggregate, "window child is Aggregate");
        check(agg && agg->group_keys.size() == 1, "1 group key (dept)");
        check(agg && agg->aggregates.size() == 1, "1 aggregate (SUM(sal))");
        const LogicalNode* scan = only_child(agg);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "emp",
              "leaf scan emp");
    });
}

// A grouping aggregate that appears ONLY inside a window function's OVER clause
// (PARTITION BY / ORDER BY) must still be precomputed by the Aggregate node.
// Regression: collect_aggregates early-returned on any window call, so it never
// saw SUM(sal) inside OVER (ORDER BY SUM(sal)). With GROUP BY the aggregate was
// absent from the frame and the window ORDER BY re-lowered raw `sal` -> bind
// failed; with no GROUP BY the aggregates set stayed empty so NO Aggregate node
// was built and the Window ran over the raw Scan (wrong cardinality + result).
void test_window_over_clause_only_aggregate(const InMemoryCatalog& cat) {
    // (A) With GROUP BY: the OVER-clause aggregate must precompute and the window
    // ORDER BY key resolve to it. dept is the sole group key (#0), SUM(sal) the
    // sole aggregate (#1).
    std::printf("[test] SELECT dept, RANK() OVER (ORDER BY SUM(sal)) FROM emp GROUP BY dept\n");
    with_plan(cat, "SELECT dept, RANK() OVER (ORDER BY SUM(sal)) FROM emp GROUP BY dept",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "A: root is Project");
        const LogicalNode* window = only_child(root);
        check(window && window->op == LogicalOp::Window, "A: child is Window");
        if (window && window->window_functions.size() == 1) {
            const auto& w = *window->window_functions[0];
            check(w.window.order_by.size() == 1 &&
                      w.window.order_by[0].expr->kind == ExprKind::ColumnRef &&
                      w.window.order_by[0].expr->input_index == 1,
                  "A: window ORDER BY SUM(sal) -> agg output #1");
        }
        const LogicalNode* agg = window ? only_child(window) : nullptr;
        check(agg && agg->op == LogicalOp::Aggregate, "A: window child is Aggregate");
        check(agg && agg->group_keys.size() == 1, "A: 1 group key (dept)");
        check(agg && agg->aggregates.size() == 1, "A: 1 aggregate (SUM(sal))");
    });

    // (B) No GROUP BY: the OVER-clause aggregate forces implicit single-group
    // aggregation - an Aggregate with ZERO keys and one aggregate must exist, so
    // the query yields exactly one row (RANK over a single row). The bug produced
    // a Window directly over the Scan (one row per emp row).
    std::printf("[test] SELECT RANK() OVER (ORDER BY SUM(sal)) FROM emp (implicit group)\n");
    with_plan(cat, "SELECT RANK() OVER (ORDER BY SUM(sal)) FROM emp",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "B: root is Project");
        const LogicalNode* window = only_child(root);
        check(window && window->op == LogicalOp::Window, "B: child is Window");
        const LogicalNode* agg = window ? only_child(window) : nullptr;
        check(agg && agg->op == LogicalOp::Aggregate,
              "B: an Aggregate node exists (implicit single group)");
        check(agg && agg->group_keys.empty(), "B: zero group keys");
        check(agg && agg->aggregates.size() == 1, "B: one aggregate (SUM(sal))");
        const LogicalNode* scan = agg ? only_child(agg) : nullptr;
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "emp",
              "B: Aggregate over Scan emp (not Window over raw Scan)");
    });

    // (C) PARTITION BY aggregate, with GROUP BY: same requirement via the
    // PARTITION BY key.
    std::printf("[test] SELECT dept, RANK() OVER (PARTITION BY MAX(sal)) FROM emp GROUP BY dept\n");
    with_plan(cat, "SELECT dept, RANK() OVER (PARTITION BY MAX(sal)) FROM emp GROUP BY dept",
              [](const LogicalNode* root) {
        const LogicalNode* window = only_child(root);
        const LogicalNode* agg = window ? only_child(window) : nullptr;
        check(agg && agg->op == LogicalOp::Aggregate, "C: window child is Aggregate");
        check(agg && agg->aggregates.size() == 1, "C: MAX(sal) precomputed");
    });

    // (D) A plain window aggregate over raw columns must NOT trigger grouping:
    // SUM(sal) OVER (PARTITION BY dept) has no grouping aggregate, so no Aggregate
    // node (its child is the Scan). Guards against over-collecting.
    std::printf("[test] SELECT dept, SUM(sal) OVER (PARTITION BY dept) FROM emp (no grouping)\n");
    with_plan(cat, "SELECT dept, SUM(sal) OVER (PARTITION BY dept) FROM emp",
              [](const LogicalNode* root) {
        const LogicalNode* window = only_child(root);
        check(window && window->op == LogicalOp::Window, "D: child is Window");
        const LogicalNode* below = window ? only_child(window) : nullptr;
        check(below && below->op == LogicalOp::Scan,
              "D: Window directly over Scan (no spurious Aggregate)");
    });
}

// A window function NESTED inside a larger expression must STILL be evaluated by
// a Window node below the Project; the Project references the window's output
// column and re-applies the wrapper (`... + 1`). Previously the window call was
// re-lowered inline as a fresh WindowFunction in the Project with no Window node
// - the window result was silently recomputed in the projection.
void test_window_nested_in_expr(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, ROW_NUMBER() OVER (ORDER BY id) + 1 FROM users\n");
    with_plan(cat, "SELECT id, ROW_NUMBER() OVER (ORDER BY id) + 1 FROM users",
              [](const LogicalNode* root) {
        // Project -> Window -> Scan (the Window is NOT skipped for a wrapped call).
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* window = only_child(root);
        check(window && window->op == LogicalOp::Window, "child is Window");
        check(window && window->window_functions.size() == 1, "1 window function");
        if (window && window->window_functions.size() == 1) {
            const auto& w = *window->window_functions[0];
            check(w.kind == ExprKind::WindowFunction && w.func_name == "ROW_NUMBER",
                  "window func is ROW_NUMBER");
        }
        // Window output = input columns (id, name) + the ROW_NUMBER result at #2.
        check(window && window->output.size() == 3, "window output = 3 cols");
        if (window && window->output.size() == 3) {
            expect_col(window->output[2], "ROW_NUMBER", DataType::BigInt, false, "win[2]");
        }
        const LogicalNode* scan = only_child(window);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "users",
              "leaf scan users");
        // The projection keeps `ROW_NUMBER() OVER(...) + 1` as an Add whose left
        // child is a ColumnRef into the Window output slot (#2) - NOT a re-lowered
        // WindowFunction - and whose right child is the literal 1.
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            expect_col_ref(root->exprs[0], 0, "proj expr[0] (id #0)");
            const auto& p = *root->exprs[1];
            check(p.kind == ExprKind::BinaryOp && p.bin_op == db25::ast::BinaryOp::Add,
                  "proj expr[1] is an Add (the +1 wrapper is preserved)");
            if (p.kind == ExprKind::BinaryOp && p.children.size() == 2) {
                check(p.children[0]->kind == ExprKind::ColumnRef,
                      "Add lhs is a ColumnRef into the window output (not a "
                      "re-lowered WindowFunction)");
                expect_col_ref(p.children[0], 2, "Add lhs references window slot #2");
                check(p.children[1]->kind == ExprKind::Literal, "Add rhs is a literal");
            }
        }
    });
}

// -------------------------------------------------------------------------
// Subqueries in expressions: owned inline by an ExprKind::Subquery node (which
// holds the bound inner plan), tagged by kind and correlation. No separate
// borrowed subquery payload exists on a LogicalNode.

void test_scalar_subquery(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, (SELECT MAX(total) FROM orders) FROM users\n");
    with_plan(cat, "SELECT id, (SELECT MAX(total) FROM orders) FROM users",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        // The scalar subquery is the second projected expression.
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            expect_subquery(root->exprs[1].get(), SubqueryKind::Scalar, false,
                            "scalar select-list subquery");
        }
    });
}

void test_scalar_subquery_correlated(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, (SELECT MAX(total) FROM orders o WHERE o.user_id = users.id) FROM users\n");
    with_plan(cat,
              "SELECT id, (SELECT MAX(total) FROM orders o WHERE o.user_id = users.id) "
              "FROM users",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            expect_subquery(root->exprs[1].get(), SubqueryKind::Scalar, true,
                            "correlated scalar subquery");
        }
    });
}

void test_in_subquery(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users WHERE id IN (SELECT user_id FROM orders)\n");
    with_plan(cat, "SELECT id FROM users WHERE id IN (SELECT user_id FROM orders)",
              [](const LogicalNode* root) {
        // Project -> Filter (predicate is the owned IN Subquery) -> Scan
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        expect_subquery(filter ? filter->predicate.get() : nullptr, SubqueryKind::In,
                        false, "IN predicate subquery");
        // The IN subquery keeps the left operand (id) as its first child.
        if (filter && filter->predicate &&
            filter->predicate->kind == ExprKind::Subquery) {
            check(filter->predicate->children.size() == 1, "IN keeps left operand");
            if (filter->predicate->children.size() == 1) {
                expect_col_ref(filter->predicate->children[0], 0, "IN left operand (id #0)");
            }
        }
    });
}

// NOT EXISTS must carry the negation: the parser marks NOT with semantic_flags
// bit 6 (not in the operator text), so the lowered Subquery is negated.
void test_not_exists_negated(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users WHERE NOT EXISTS (SELECT 1 FROM orders ...)\n");
    with_plan(cat,
              "SELECT id FROM users WHERE NOT EXISTS "
              "(SELECT 1 FROM orders WHERE orders.user_id = users.id)",
              [](const LogicalNode* root) {
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        if (filter && filter->predicate &&
            filter->predicate->kind == ExprKind::Subquery) {
            check(filter->predicate->subquery_kind == SubqueryKind::Exists, "EXISTS kind");
            check(filter->predicate->negated(), "NOT EXISTS sets the negated flag");
        } else {
            check(false, "predicate is a Subquery");
        }
    });
}

// A scalar subquery that is a whole SELECT item over an Aggregate child must
// still be lowered into an owned Subquery (not swallowed by the positional
// aggregate-passthrough rule, which would drop its plan).
void test_scalar_subquery_over_aggregate(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT COUNT(*), (SELECT MAX(total) FROM orders) FROM users\n");
    with_plan(cat, "SELECT COUNT(*), (SELECT MAX(total) FROM orders) FROM users",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* agg = only_child(root);
        check(agg && agg->op == LogicalOp::Aggregate, "child is Aggregate");
        check(root->exprs.size() == 2, "project has 2 exprs");
        if (root->exprs.size() == 2) {
            // COUNT(*) is the precomputed aggregate output (#0); the scalar
            // subquery is lowered fresh with its inner plan owned inline.
            expect_col_ref(root->exprs[0], 0, "COUNT -> #0");
            expect_subquery(root->exprs[1].get(), SubqueryKind::Scalar, false,
                            "scalar subquery over aggregate");
        }
    });
}

void test_exists_subquery(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users WHERE EXISTS (SELECT 1 FROM orders WHERE ...)\n");
    with_plan(cat,
              "SELECT id FROM users WHERE EXISTS "
              "(SELECT 1 FROM orders WHERE orders.user_id = users.id)",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        expect_subquery(filter ? filter->predicate.get() : nullptr, SubqueryKind::Exists,
                        true, "correlated EXISTS predicate subquery");
    });
}

// Does the expression subtree contain a correlated OuterRef? (Does not cross a
// nested Subquery boundary - that inner block has its own outer scope.)
bool expr_has_outer_ref(const db25::plan::Expr* e) {
    if (e == nullptr) {
        return false;
    }
    if (e->kind == ExprKind::OuterRef) {
        return true;
    }
    for (const auto& c : e->children) {
        if (expr_has_outer_ref(c.get())) {
            return true;
        }
    }
    return false;
}

// Does any expression in this plan node (or its children) hold an OuterRef?
bool plan_has_outer_ref(const LogicalNode* n) {
    if (n == nullptr) {
        return false;
    }
    if (n->predicate && expr_has_outer_ref(n->predicate.get())) {
        return true;
    }
    for (const auto& ex : n->exprs) {
        if (expr_has_outer_ref(ex.get())) {
            return true;
        }
    }
    for (int i = 0; i < n->child_count(); ++i) {
        if (plan_has_outer_ref(n->child(i))) {
            return true;
        }
    }
    return false;
}

// A correlated subquery whose inner FROM reads the SAME base table as the
// correlated outer column must still resolve the outer column as an OuterRef.
// Regression: the qualified outer ref `e.dept` was silently bound to the inner
// scan's same-(table_id,column_id) slot (`e2.dept`), producing the tautology
// `e2.dept = e2.dept` with no OuterRef - which the optimizer then mis-
// decorrelated. The qualifier `e` names no relation in the inner scan, so it
// must fall through to the enclosing input.
void test_self_correlated_subquery(const InMemoryCatalog& cat) {
    std::printf("[test] correlated EXISTS whose inner FROM reuses the outer's base table\n");
    with_plan(cat,
              "SELECT e.id FROM emp e WHERE EXISTS "
              "(SELECT 1 FROM emp e2 WHERE e2.dept = e.dept)",
              [](const LogicalNode* root) {
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        const db25::plan::Expr* sub = filter ? filter->predicate.get() : nullptr;
        expect_subquery(sub, SubqueryKind::Exists, true,
                        "self-correlated EXISTS predicate subquery");
        // The outer column `e.dept` must survive as an OuterRef in the inner plan,
        // not be swallowed into the inner `e2.dept` slot.
        check(sub && sub->kind == ExprKind::Subquery && sub->sub_plan &&
                  plan_has_outer_ref(sub->sub_plan.get()),
              "inner plan carries an OuterRef (outer column not swallowed)");
    });
}

// A correlated subquery may reference an outer COMPUTED column (a derived-table
// alias like `sal + 1 AS x`, which has no catalog id). The computed-column
// resolution path must fall back to the enclosing inputs by name - exactly as
// the base-column path already does by id - and emit an OuterRef. Before the
// fix, the by-name branch resolved only against the current input and then
// errored, so this analyzer-accepted, legal query failed to bind.
void test_correlated_outer_computed_column(const InMemoryCatalog& cat) {
    std::printf("[test] correlated EXISTS referencing an outer computed (aliased) column\n");
    with_plan(cat,
              "SELECT t.id FROM (SELECT id, sal + 1 AS x FROM emp) t "
              "WHERE EXISTS (SELECT 1 FROM emp e WHERE e.sal > x)",
              [](const LogicalNode* root) {
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        const db25::plan::Expr* sub = filter ? filter->predicate.get() : nullptr;
        expect_subquery(sub, SubqueryKind::Exists, true,
                        "EXISTS predicate subquery");
        // The outer computed column `x` survives as an OuterRef in the inner plan.
        check(sub && sub->kind == ExprKind::Subquery && sub->sub_plan &&
                  plan_has_outer_ref(sub->sub_plan.get()),
              "inner plan carries an OuterRef to the outer computed column 'x'");
    });
    // The scalar-subquery form (qualified `t.x`) likewise binds.
    with_plan(cat,
              "SELECT t.id, (SELECT COUNT(*) FROM emp e WHERE e.sal > t.x) "
              "FROM (SELECT id, sal + 1 AS x FROM emp) t",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "scalar-subquery form binds");
    });
}

}  // namespace

void test_derived_table_column_alias(const InMemoryCatalog& cat) {
    std::printf("[test] derived table with a column-alias list AS s(d, hi)\n");
    // The alias list renames the derived output columns; `s.hi` names an aliased
    // COMPUTED column (MAX), which resolves by name - so the plan must carry the
    // alias as the derived column's output name.
    with_plan(cat,
              "SELECT s.hi FROM (SELECT dept, MAX(sal) FROM emp GROUP BY dept) AS s(d, hi)",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        check(root->output.size() == 1, "one output column");
        if (!root->output.empty())
            check(root->output[0].name == "hi", "output column named by alias 'hi'");
        const LogicalNode* derived = only_child(root);
        check(derived && derived->op == LogicalOp::Project, "derived table is a Project");
        if (derived && derived->output.size() == 2) {
            check(derived->output[0].name == "d", "derived col 0 renamed to 'd'");
            check(derived->output[1].name == "hi", "derived col 1 renamed to 'hi'");
        }
    });
}

void test_values_derived_table(const InMemoryCatalog& cat) {
    std::printf("[test] VALUES derived table AS v(id, label)\n");
    with_plan(cat,
              "SELECT v.label FROM (VALUES (1, 'eng'), (2, 'sales')) AS v(id, label) "
              "WHERE v.id = 1",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        check(root->output.size() == 1 && root->output[0].name == "label",
              "projects the aliased column 'label'");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter (WHERE v.id = 1)");
        const LogicalNode* values = filter ? only_child(filter) : nullptr;
        check(values && values->op == LogicalOp::Values, "leaf is a Values node");
        if (values) {
            check(values->value_rows.size() == 2, "two value rows");
            check(values->output.size() == 2, "two output columns");
            if (values->output.size() == 2) {
                check(values->output[0].name == "id", "col 0 named by alias 'id'");
                check(values->output[1].name == "label", "col 1 named by alias 'label'");
                check(values->output[0].type == DataType::Integer, "col 0 typed Integer");
            }
        }
    });
}

// GUARDRAIL MATRIX: USING / NATURAL join column merging. This neighborhood was
// touched by three separate audit passes (bare-ref coalescing, the INNER/LEFT
// hidden right-copy, the RIGHT/FULL per-side hidden copies), each closing one
// adjacent cell. This table pins the WHOLE matrix - every join type x merge
// syntax x reference form - so a future change that regresses any single cell
// (a dropped copy, a wrong slot, a wrong null flag) fails loudly here.
void test_using_natural_join_matrix(const InMemoryCatalog& cat) {
    std::printf("[test] USING/NATURAL join matrix (join type x merge syntax x ref form)\n");
    // users(id,name) and orders(id,user_id,total) share only `id`, so USING(id)
    // and NATURAL merge the same single column. Per-side nullability of a
    // qualified key ref follows which side is null-supplied by the join.
    struct JT { const char* kw; bool u_nullable; bool o_nullable; };
    const JT jts[] = {
        {"INNER JOIN", false, false},
        {"LEFT JOIN",  false, true},   // right null-supplied
        {"RIGHT JOIN", true,  false},  // left null-supplied
        {"FULL JOIN",  true,  true},   // both
    };
    const auto count_visible = [](const LogicalNode* root, const char* nm) {
        int v = 0;
        for (const auto& c : root->output) if (c.name == nm && !c.hidden) ++v;
        return v;
    };
    for (const JT& j : jts) {
        for (int natural = 0; natural < 2; ++natural) {
            const std::string join =
                std::string("users u ") +
                (natural ? std::string("NATURAL ") + j.kw : std::string(j.kw)) +
                " orders o" + (natural ? "" : " USING (id)");
            const std::string ctx = join;

            // bare `id` -> exactly one visible merged column.
            with_plan(cat, "SELECT id FROM " + join, [&](const LogicalNode* root) {
                check(count_visible(root, "id") == 1, "matrix bare id once: " + ctx);
            });
            // SELECT * -> merged id shown once (hidden per-side copies excluded).
            with_plan(cat, "SELECT * FROM " + join, [&](const LogicalNode* root) {
                check(count_visible(root, "id") == 1, "matrix star id once: " + ctx);
            });
            // u.id / o.id -> DISTINCT slots with the correct per-side nullability.
            const bool un = j.u_nullable, on = j.o_nullable;
            with_plan(cat, "SELECT u.id, o.id FROM " + join,
                      [&, un, on](const LogicalNode* root) {
                if (root->exprs.size() == 2 && root->output.size() == 2) {
                    check(root->exprs[0]->input_index != root->exprs[1]->input_index,
                          "matrix u.id/o.id distinct slots: " + ctx);
                    check(root->output[0].nullable == un, "matrix u.id nullability: " + ctx);
                    check(root->output[1].nullable == on, "matrix o.id nullability: " + ctx);
                } else {
                    check(false, "matrix u.id/o.id shape: " + ctx);
                }
            });
            // A qualified null-supplying-side ref in WHERE must still bind (the
            // per-side copy is addressable). with_plan asserts bind success.
            with_plan(cat, "SELECT u.id FROM " + join + " WHERE o.id = 5",
                      [](const LogicalNode*) {});
        }
    }
    // Multi-column merge: a users self-join on USING (id, name) merges BOTH
    // columns; `SELECT *` shows each exactly once and qualified refs to both
    // sides bind.
    for (const char* kw : {"INNER JOIN", "LEFT JOIN", "RIGHT JOIN", "FULL JOIN"}) {
        const std::string join = std::string("users a ") + kw + " users b USING (id, name)";
        with_plan(cat, "SELECT * FROM " + join, [&](const LogicalNode* root) {
            check(count_visible(root, "id") == 1 && count_visible(root, "name") == 1,
                  std::string("matrix multi-col id/name once: ") + kw);
        });
        with_plan(cat, "SELECT a.id, b.id, a.name, b.name FROM " + join,
                  [](const LogicalNode*) {});  // qualified both sides binds
    }
}

// GUARDRAIL: the binder's Values-node output column types must equal the types
// the analyzer assigns to the same columns (a multi-row VALUES is a UNION ALL of
// rows; both layers reconcile across all rows). Typing the Values node from the
// first row only made the two layers DISAGREE. Here `SELECT * FROM (VALUES...) t`
// lowers the derived columns straight through, so the top Project's output types
// come from the analyzer while the Values node's come from the binder's own
// reconciliation - they must match position-for-position. This cross-check fails
// if reconcile_value_type ever drifts from the analyzer's UnionReconcile rule.
void test_values_column_types_match_analyzer(const InMemoryCatalog& cat) {
    std::printf("[test] binder VALUES column types match the analyzer (no divergence)\n");
    const char* sqls[] = {
        "SELECT * FROM (VALUES (1),(2),(3)) t(a)",
        "SELECT * FROM (VALUES (1),(2.5)) t(a)",
        "SELECT * FROM (VALUES (2.5),(1)) t(a)",
        "SELECT * FROM (VALUES (1),(2.0),(3)) t(a)",
        "SELECT * FROM (VALUES (NULL),(1)) t(a)",
        "SELECT * FROM (VALUES (1),(NULL)) t(a)",
        "SELECT * FROM (VALUES (NULL, 1),(2, 2.5)) t(a,b)",
        "SELECT * FROM (VALUES (1,'x'),(2,'y')) t(a,b)",
        "SELECT * FROM (VALUES ('a'),('bb')) t(a)",
    };
    // Recursively find the (single) Values node in the bound plan.
    struct F {
        static const LogicalNode* find(const LogicalNode* n) {
            if (!n) return nullptr;
            if (n->op == LogicalOp::Values) return n;
            for (std::size_t i = 0; i < n->child_count(); ++i)
                if (const LogicalNode* v = find(n->child(i))) return v;
            return nullptr;
        }
    };
    for (const char* sql : sqls) {
        with_plan(cat, sql, [&](const LogicalNode* root) {
            const LogicalNode* values = F::find(root);
            check(values != nullptr, std::string{"found Values node: "} + sql);
            // `SELECT *` carries every derived column straight to the root Project,
            // whose types are the analyzer's; compare them to the Values node's.
            if (values && root->output.size() == values->output.size()) {
                for (std::size_t i = 0; i < root->output.size(); ++i) {
                    check(root->output[i].type == values->output[i].type,
                          std::string{"col "} + std::to_string(i) +
                              " type agrees analyzer<->binder: " + sql);
                }
            } else {
                check(false, std::string{"arity match: "} + sql);
            }
        });
    }
}

// A qualified ORDER BY reference to the null-supplying side of a RIGHT/FULL
// USING/NATURAL join must order by THAT side's own (nullable) column, not the
// merged COALESCE output. Regression: the ORDER BY key resolved against the
// narrow SELECT Project output, where the merged column retains the left
// (table_id,column_id) but carries no alias, so `u.id` bound to the merged slot
// (a not-null value) even when the output column was renamed. The qualified key
// now resolves against the input frame (with the per-side hidden copies).
void test_order_by_qualified_null_side_right_join(const InMemoryCatalog& cat) {
    std::printf("[test] ORDER BY u.id on a RIGHT USING join orders by the left copy\n");
    // Bare `id` is projected (the merged COALESCE, slot 0). ORDER BY u.id must NOT
    // reuse slot 0; it must order by a distinct, NULLABLE column (the left copy).
    with_plan(cat, "SELECT id FROM users u RIGHT JOIN orders o USING (id) ORDER BY u.id",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Sort && !root->sort_keys.empty(),
              "root is a Sort with a key");
        const LogicalNode* proj = only_child(root);
        if (!root->sort_keys.empty() && proj != nullptr) {
            const auto& k = root->sort_keys[0].expr;
            check(k && k->kind == ExprKind::ColumnRef, "sort key is a ColumnRef");
            if (k && k->kind == ExprKind::ColumnRef) {
                const std::size_t slot = k->input_index;
                // The projected merged id is slot 0 and NOT NULL; the sort key must
                // point at a different, nullable column (the hidden left copy).
                check(slot != 0, "ORDER BY u.id does NOT reuse the merged id (slot 0)");
                check(slot < proj->output.size() && proj->output[slot].nullable,
                      "ORDER BY u.id orders by a nullable (left-side) column");
            }
        }
    });

    // Renaming the output must not change this (proves it is not an output-name
    // match): still a distinct nullable sort column, not the renamed merged slot.
    with_plan(cat, "SELECT id AS xyz FROM users u RIGHT JOIN orders o USING (id) ORDER BY u.id",
              [](const LogicalNode* root) {
        if (!root->sort_keys.empty()) {
            const auto& k = root->sort_keys[0].expr;
            check(k && k->kind == ExprKind::ColumnRef && k->input_index != 0,
                  "renamed output: ORDER BY u.id still not the merged slot 0");
        }
    });

    // Control: a plain qualified ORDER BY that IS the projected column reuses the
    // output slot (no wasteful hidden column, no regression).
    with_plan(cat, "SELECT o.total FROM orders o ORDER BY o.total",
              [](const LogicalNode* root) {
        const LogicalNode* proj = only_child(root);
        check(!root->sort_keys.empty() && root->sort_keys[0].expr &&
                  root->sort_keys[0].expr->input_index == 0,
              "ORDER BY o.total reuses projected slot 0");
        check(proj && proj->output.size() == 1,
              "no extra hidden sort column appended");
    });
}

// A USING / NATURAL merge whose result is itself an input of a SECOND USING /
// NATURAL join on the same column must still produce exactly ONE visible merged
// column. The first merge leaves HIDDEN per-side copies of the key; the second
// join must exclude them from merge-key emission (else RIGHT / FULL emit the key
// once PER copy - three visible `id`s) and from NATURAL common-column discovery
// (else the extra copies read as duplicates and the legal query is rejected
// "ambiguous"). Regression from the hidden-per-side-copy design.
void test_chained_using_natural_single_merged_column(const InMemoryCatalog& cat) {
    std::printf("[test] chained USING / NATURAL keeps one merged column\n");
    const char* queries[] = {
        "SELECT * FROM users u RIGHT JOIN orders o USING(id) RIGHT JOIN emp e USING(id)",
        "SELECT * FROM users u FULL JOIN orders o USING(id) FULL JOIN emp e USING(id)",
        "SELECT * FROM users u NATURAL RIGHT JOIN orders o NATURAL RIGHT JOIN emp e",
    };
    for (const char* sql : queries) {
        // with_plan asserts the bind SUCCEEDS (the NATURAL chain previously failed
        // "ambiguous") before invoking the body.
        with_plan(cat, sql, [&](const LogicalNode* root) {
            // users(id,name) ++ orders(id,user_id,total) ++ emp(id,dept,sal) with
            // id merged across the whole chain -> exactly [id, name, user_id,
            // total, dept, sal]: six visible columns, one `id`.
            int id_count = 0;
            int visible = 0;
            for (const auto& c : root->output) {
                if (!c.hidden) {
                    ++visible;
                    if (c.name == "id") {
                        ++id_count;
                    }
                }
            }
            check(id_count == 1, std::string{"exactly one visible merged id: "} + sql);
            check(visible == 6, std::string{"six visible output columns: "} + sql);
        });
    }
}

// An aggregate whose SELECT-list output ALIAS equals a base-column name in the
// FROM relation must still COMPUTE the aggregate - the alias must never redirect
// the aggregate to a same-named base column of its input. Regression: the
// by-output-name precomputed-aggregate shortcut mis-fired during aggregate
// construction (where the input is the scan/join), lowering `MAX(sal) AS id` to
// a ColumnRef to emp.id instead of MAX(sal). The correct precomputed resolution
// is by STRUCTURAL identity against the active aggregate frame, which is inactive
// during construction.
void test_aggregate_alias_collides_with_base_column(const InMemoryCatalog& cat) {
    std::printf("[test] aggregate output alias colliding with a base column name\n");
    struct Case { const char* sql; std::size_t n_aggs; const char* func0; };
    const Case cases[] = {
        {"SELECT MAX(sal) AS id FROM emp", 1, "MAX"},                 // alias = base col
        {"SELECT SUM(sal) AS sal FROM emp GROUP BY dept", 1, "SUM"},   // alias = agg'd col
        {"SELECT SUM(sal) AS dept FROM emp GROUP BY dept", 1, "SUM"},  // alias = group key
        {"SELECT AVG(sal) AS dept, COUNT(*) AS id FROM emp GROUP BY dept", 2, "AVG"},
    };
    for (const Case& c : cases) {
        with_plan(cat, c.sql, [&](const LogicalNode* root) {
            const LogicalNode* agg = only_child(root);
            check(agg && agg->op == LogicalOp::Aggregate,
                  std::string{"child is Aggregate: "} + c.sql);
            if (!agg || agg->op != LogicalOp::Aggregate) return;
            check(agg->aggregates.size() == c.n_aggs,
                  std::string{"aggregate count: "} + c.sql);
            // Every aggregate slot must be a real Aggregate expr - NOT a ColumnRef
            // that the colliding alias redirected to a base column.
            bool all_agg = true;
            for (const auto& a : agg->aggregates) {
                if (!a || a->kind != ExprKind::Aggregate) all_agg = false;
            }
            check(all_agg,
                  std::string{"every aggregate lowers to an Aggregate expr (not a "
                              "base-column ref): "} + c.sql);
            if (!agg->aggregates.empty() && agg->aggregates[0]) {
                check(agg->aggregates[0]->func_name == c.func0,
                      std::string{"first aggregate func is "} + c.func0 + ": " + c.sql);
            }
        });
    }
}

// A quantified comparison `x <cmp> ALL|ANY|SOME (subquery)` is typed Boolean by
// the analyzer, but the binder does not yet lower it. It must be rejected with a
// SPECIFIC "not yet supported" message, not the generic "unrecognized binary
// operator" (which wrongly implies a malformed / typo'd operator).
void test_quantified_comparison_rejected_clearly(const InMemoryCatalog& cat) {
    std::printf("[test] quantified comparison rejected with a specific message\n");
    const char* forms[] = {
        "SELECT id FROM emp WHERE sal > ALL (SELECT sal FROM emp)",
        "SELECT id FROM emp WHERE sal > ANY (SELECT sal FROM emp)",
        "SELECT id FROM emp WHERE sal = SOME (SELECT sal FROM emp)",
    };
    for (const char* sql : forms) {
        db25::parser::Parser parser;
        auto parsed = parser.parse(sql);
        check(parsed.has_value(), std::string{"parse: "} + sql);
        if (!parsed) continue;
        Analyzer analyzer(cat);
        analyzer.analyze(parsed.value());
        Binder binder(analyzer, cat);
        BindResult res = binder.bind(parsed.value());
        check(!res.ok, std::string{"quantified comparison must not bind: "} + sql);
        check(res.error.find("quantified comparison") != std::string::npos,
              std::string{"error names the unsupported feature, not a generic "
                          "'unrecognized binary operator': "} + res.error);
    }
}

int main() {
    const InMemoryCatalog cat = make_catalog();
    test_chained_using_natural_single_merged_column(cat);
    test_aggregate_alias_collides_with_base_column(cat);
    test_quantified_comparison_rejected_clearly(cat);

    test_scan_filter_project_limit(cat);
    test_derived_table_column_alias(cat);
    test_values_derived_table(cat);
    test_hex_binary_literals(cat);
    test_oversized_integer_literal_stays_exact_decimal(cat);
    test_delimited_identifiers(cat);
    test_string_escape_unquote(cat);
    test_cast_modifiers(cat);
    test_array_constructor(cat);
    test_collate(cat);
    test_limit_offset(cat);
    test_inner_join(cat);
    test_self_join_alias_resolution(cat);
    test_derived_table_join_qualifier_resolution(cat);
    test_derived_expr_alias_join_qualifier_resolution(cat);
    test_table_name_qualifier(cat);
    test_group_by(cat);
    test_ordered_aggregate(cat);
    test_ordered_aggregate_dedup(cat);
    test_aggregate_name_parity(cat);
    test_group_by_output_alias(cat);
    test_group_by_positional(cat);
    test_group_by_select_reordered(cat);
    test_group_by_same_name_aggregates(cat);
    test_self_join_group_key_distinct_slots(cat);
    test_group_by_distinct_vs_plain(cat);
    test_implicit_aggregate_count(cat);
    test_implicit_aggregate_nested(cat);
    test_having(cat);
    test_having_aggregate_in_select(cat);
    test_having_aggregate_not_selected(cat);
    test_having_aggregate_aliased(cat);
    test_order_by_aggregate_not_selected(cat);
    test_order_by_selected_aggregate_direction_dedups(cat);
    test_distinct(cat);
    test_select_star(cat);
    test_order_by(cat);
    test_order_by_nulls(cat);
    test_order_by_ordinal(cat);
    test_order_by_repeated_hidden_dedup(cat);
    test_order_by_distinct_nonoutput_rejected(cat);
    test_select_no_from_const(cat);
    test_select_no_from_func(cat);
    test_comma_join(cat);
    test_comma_then_outer_join_nullability(cat);
    test_cross_join(cat);
    test_join_using(cat);
    test_natural_join(cat);
    test_natural_left_join(cat);
    test_natural_join_no_common_is_cross(cat);
    test_natural_join_ambiguous_rejected(cat);
    test_parenthesized_join_group(cat);
    test_right_join_using_coalesces(cat);
    test_full_join_using_coalesces(cat);
    test_natural_right_join_coalesces(cat);
    test_left_join_using_keeps_left_copy(cat);
    test_using_qualified_null_side(cat);
    test_right_full_using_qualified_sides(cat);
    test_right_using_merged_key_output_notnull(cat);
    test_using_natural_join_matrix(cat);
    test_values_column_types_match_analyzer(cat);
    test_order_by_qualified_null_side_right_join(cat);
    test_join_using_multi(cat);
    test_select_star_over_using(cat);
    test_qualified_star_over_join_expands(cat);
    test_derived_table(cat);
    test_derived_self_join(cat);
    test_cte(cat);
    test_recursive_cte(cat);
    test_deep_expression_no_overflow(cat);
    test_union(cat);
    test_cte_above_setop(cat);
    test_union_all(cat);
    test_intersect_except(cat);
    test_union_chain(cat);
    test_setop_trailing_order_by_limit_hoisted(cat);
    test_setop_no_order_by_unchanged(cat);
    test_setop_trailing_order_by_only(cat);
    test_insert_values(cat);
    test_on_conflict(cat);
    test_dml_extensions(cat);
    test_insert_select(cat);
    test_update(cat);
    test_update_no_where(cat);
    test_delete(cat);

    test_update_returning(cat);
    test_delete_returning(cat);
    test_delete_returning_star(cat);

    test_window_rank(cat);
    test_window_row_number(cat);
    test_window_over_aggregate(cat);
    test_window_over_clause_only_aggregate(cat);
    test_window_sum(cat);
    test_window_same_name_distinct_slots(cat);
    test_window_nested_in_expr(cat);

    test_scalar_subquery(cat);
    test_scalar_subquery_correlated(cat);
    test_in_subquery(cat);
    test_exists_subquery(cat);
    test_self_correlated_subquery(cat);
    test_correlated_outer_computed_column(cat);
    test_not_exists_negated(cat);
    test_scalar_subquery_over_aggregate(cat);

    std::printf("\n%d checks, %d failures\n", g_checks, g_failures);
    if (g_failures == 0) {
        std::printf("ALL TESTS PASSED\n");
        return 0;
    }
    std::printf("TESTS FAILED\n");
    return 1;
}
