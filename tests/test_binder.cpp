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
using db25::ast::SetOp;
using db25::plan::Binder;
using db25::plan::BindResult;
using db25::plan::ColumnSchema;
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
        const LogicalNode* scan = only_child(agg);
        check(scan && scan->op == LogicalOp::Scan && scan->table_name == "emp",
              "leaf scan emp");
        check(root->output.size() == 1, "project has 1 col");
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
            check(root->sort_keys[0].descending, "key[0] DESC (name)");
            check(root->sort_keys[0].expr != nullptr, "key[0] has expr");
            check(!root->sort_keys[1].descending, "key[1] ASC (id)");
        }
        // Sort is schema-preserving: same output as its Project child.
        check(root->output.size() == 2, "sort preserves 2 cols");
        const LogicalNode* project = only_child(root);
        check(project && project->op == LogicalOp::Project, "child is Project");
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
    });
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
        // USING(id) merges the two id columns: 2 (users) + 3 (orders) - 1 = 4.
        check(join && join->output.size() == 4, "USING merges id -> 4 cols");
        if (join && join->output.size() == 4) {
            // Exactly one "id" column survives.
            int id_count = 0;
            for (const auto& c : join->output) {
                if (c.name == "id") ++id_count;
            }
            check(id_count == 1, "single merged id column");
        }
    });
}

// -------------------------------------------------------------------------
// Derived tables / subqueries in FROM.

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
        check(root->output.size() == 2, "project 2 cols");
        if (root->output.size() == 2) {
            expect_col(root->output[1], "SUM", DataType::Double, true, "proj[1]");
        }
    });
}

// -------------------------------------------------------------------------
// Subqueries in expressions: represented as SubPlans (not decorrelated),
// tagged by kind and correlation.

void test_scalar_subquery(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, (SELECT MAX(total) FROM orders) FROM users\n");
    with_plan(cat, "SELECT id, (SELECT MAX(total) FROM orders) FROM users",
              [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        check(root->subplans.size() == 1, "project has 1 subplan");
        if (root->subplans.size() == 1) {
            const auto& sp = root->subplans[0];
            check(sp.kind == SubqueryKind::Scalar, "scalar subquery");
            check(!sp.correlated, "uncorrelated");
            check(sp.plan && sp.plan->op == LogicalOp::Project, "subplan is a Project");
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
        check(root->subplans.size() == 1, "project has 1 subplan");
        if (root->subplans.size() == 1) {
            const auto& sp = root->subplans[0];
            check(sp.kind == SubqueryKind::Scalar, "scalar subquery");
            check(sp.correlated, "correlated");
        }
    });
}

void test_in_subquery(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users WHERE id IN (SELECT user_id FROM orders)\n");
    with_plan(cat, "SELECT id FROM users WHERE id IN (SELECT user_id FROM orders)",
              [](const LogicalNode* root) {
        // Project -> Filter(with IN subplan) -> Scan
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        check(filter && filter->subplans.size() == 1, "filter has 1 subplan");
        if (filter && filter->subplans.size() == 1) {
            const auto& sp = filter->subplans[0];
            check(sp.kind == SubqueryKind::In, "IN subquery");
            check(!sp.correlated, "uncorrelated");
            check(sp.plan && sp.plan->op == LogicalOp::Project, "subplan is a Project");
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
        check(filter && filter->subplans.size() == 1, "filter has 1 subplan");
        if (filter && filter->subplans.size() == 1) {
            const auto& sp = filter->subplans[0];
            check(sp.kind == SubqueryKind::Exists, "EXISTS subquery");
            check(sp.correlated, "correlated");
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
    test_implicit_aggregate_count(cat);
    test_implicit_aggregate_nested(cat);
    test_having(cat);
    test_distinct(cat);
    test_select_star(cat);
    test_order_by(cat);
    test_order_by_nulls(cat);
    test_select_no_from_const(cat);
    test_select_no_from_func(cat);
    test_comma_join(cat);
    test_cross_join(cat);
    test_join_using(cat);
    test_derived_table(cat);
    test_union(cat);
    test_union_all(cat);
    test_intersect_except(cat);
    test_union_chain(cat);
    test_insert_values(cat);
    test_insert_select(cat);
    test_update(cat);
    test_update_no_where(cat);
    test_delete(cat);

    test_update_returning(cat);
    test_delete_returning(cat);
    test_delete_returning_star(cat);

    test_window_rank(cat);
    test_window_row_number(cat);
    test_window_sum(cat);

    test_scalar_subquery(cat);
    test_scalar_subquery_correlated(cat);
    test_in_subquery(cat);
    test_exists_subquery(cat);

    std::printf("\n%d checks, %d failures\n", g_checks, g_failures);
    if (g_failures == 0) {
        std::printf("ALL TESTS PASSED\n");
        return 0;
    }
    std::printf("TESTS FAILED\n");
    return 1;
}
