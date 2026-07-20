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

#include <cstdio>
#include <string>
#include <string_view>

using db25::ast::DataType;
using db25::plan::Binder;
using db25::plan::BindResult;
using db25::plan::ColumnSchema;
using db25::plan::LogicalNode;
using db25::plan::LogicalOp;
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

// -------------------------------------------------------------------------

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

        const LogicalNode* scan = only_child(filter);
        check(scan && scan->op == LogicalOp::Scan, "leaf is Scan");
        check(scan && scan->table_name == "users", "scan of users");

        check(project && project->output.size() == 2, "project has 2 cols");
        if (project && project->output.size() == 2) {
            expect_col(project->output[0], "id", DataType::Integer, false, "proj[0]");
            expect_col(project->output[1], "name", DataType::VarChar, true, "proj[1]");
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
        const LogicalNode* scan = only_child(agg);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "emp",
              "leaf scan emp");
        check(root->output.size() == 2, "project has 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[0], "dept", DataType::VarChar, true, "proj[0]");
            // COUNT(*) -> BigInt, not null.
            expect_col(root->output[1], "COUNT", DataType::BigInt, false, "proj[1]");
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
    });
}

}  // namespace

int main() {
    const InMemoryCatalog cat = make_catalog();

    test_scan_filter_project_limit(cat);
    test_limit_offset(cat);
    test_inner_join(cat);
    test_group_by(cat);
    test_select_star(cat);

    std::printf("\n%d checks, %d failures\n", g_checks, g_failures);
    if (g_failures == 0) {
        std::printf("ALL TESTS PASSED\n");
        return 0;
    }
    std::printf("TESTS FAILED\n");
    return 1;
}
