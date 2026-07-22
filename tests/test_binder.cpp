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
        // Common column id merges: 2 (users) + 3 (orders) - 1 = 4.
        check(join && join->output.size() == 4, "NATURAL merges id -> 4 cols");
        if (join && join->output.size() == 4) {
            int id_count = 0;
            for (const auto& c : join->output) {
                if (c.name == "id") ++id_count;
            }
            check(id_count == 1, "single merged id column");
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
        check(join && join->output.size() == 4, "merged frame -> 4 cols");
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
    // users(id,name) + orders(id,user_id,total), merged on id -> 4 output cols
    // (id, name, user_id, total); exactly one id, and it is expr[0].
    check(merge->output.size() == 4, ctx + ": merged frame -> 4 cols");
    int id_count = 0;
    for (const auto& c : merge->output) if (c.name == "id") ++id_count;
    check(id_count == 1, ctx + ": single merged id column");
    // Both users.id and orders.id are NOT NULL, so COALESCE(id,id) is NOT NULL,
    // even under RIGHT / FULL where each side is otherwise null-supplied.
    check(!merge->output.empty() && merge->output[0].name == "id" &&
              !merge->output[0].nullable,
          ctx + ": merged id is NOT NULL (both sides not-null)");
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

// INNER / LEFT keep the compact left-copy output (no COALESCE Project): the left
// side is never null-supplied there, so the left copy already IS the merged value.
void test_left_join_using_keeps_left_copy(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users u LEFT JOIN orders o USING (id)\n");
    with_plan(cat, "SELECT id FROM users u LEFT JOIN orders o USING (id)",
              [](const LogicalNode* root) {
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "LEFT USING: child is Join (no merge Project)");
        check(join && join->join_type == db25::ast::JoinType::Left, "LEFT preserved");
        check(join && join->output.size() == 4, "LEFT USING: compact merged frame -> 4 cols");
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
        // Both columns merge, so the right frame contributes nothing:
        // output = left (id, name) = 2 cols.
        check(join && join->output.size() == 2, "both cols merge -> 2 cols");
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
// only t's columns. That table-scoped expansion is not yet lowered, so the bind
// must fail CLEANLY rather than silently project the whole join frame. Guards
// the bare-star fast path against swallowing a qualified star (whose qualifier
// lives in the Star node's schema_name, not its primary_text "*").
void test_qualified_star_over_join_rejected(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.* FROM users u JOIN orders o USING (id) (rejected)\n");
    db25::parser::Parser parser;
    auto parsed = parser.parse("SELECT u.* FROM users u JOIN orders o USING (id)");
    check(parsed.has_value(), "parse qualified star over join");
    if (!parsed) {
        return;
    }
    Analyzer analyzer(cat);
    analyzer.analyze(parsed.value());
    Binder binder(analyzer, cat);
    BindResult res = binder.bind(parsed.value());
    check(!res.ok, "bind rejects qualified t.* over a join (not silently full frame)");
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

}  // namespace

int main() {
    const InMemoryCatalog cat = make_catalog();

    test_scan_filter_project_limit(cat);
    test_hex_binary_literals(cat);
    test_delimited_identifiers(cat);
    test_string_escape_unquote(cat);
    test_cast_modifiers(cat);
    test_array_constructor(cat);
    test_collate(cat);
    test_limit_offset(cat);
    test_inner_join(cat);
    test_self_join_alias_resolution(cat);
    test_table_name_qualifier(cat);
    test_group_by(cat);
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
    test_join_using_multi(cat);
    test_select_star_over_using(cat);
    test_qualified_star_over_join_rejected(cat);
    test_derived_table(cat);
    test_union(cat);
    test_union_all(cat);
    test_intersect_except(cat);
    test_union_chain(cat);
    test_setop_trailing_order_by_limit_hoisted(cat);
    test_setop_no_order_by_unchanged(cat);
    test_setop_trailing_order_by_only(cat);
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
    test_window_same_name_distinct_slots(cat);
    test_window_nested_in_expr(cat);

    test_scalar_subquery(cat);
    test_scalar_subquery_correlated(cat);
    test_in_subquery(cat);
    test_exists_subquery(cat);
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
