// DB25 Logical Plan - Optimizer tests
//
// Parse -> analyze -> bind -> optimize, then assert the constant-folding pass
// rewrote the owned Expr trees as expected (and left non-constant expressions
// and unsafe folds alone).

#include "db25/plan/binder.hpp"
#include "db25/plan/logical_plan.hpp"
#include "db25/plan/optimizer.hpp"

#include "db25/parser/parser.hpp"
#include "db25/semantic/analyzer.hpp"
#include "db25/semantic/catalog.hpp"

#include <cstdio>
#include <string>
#include <string_view>
#include <variant>

using db25::ast::DataType;
using db25::plan::Binder;
using db25::plan::BindResult;
using db25::plan::Expr;
using db25::plan::ExprKind;
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
    return cat;
}

// Parse + analyze + bind + optimize, then hand the optimized plan to `body`.
template <typename F>
void with_optimized_plan(const InMemoryCatalog& cat, std::string_view sql, F&& body) {
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
    db25::plan::LogicalNodePtr optimized = db25::plan::optimize(std::move(res.root));
    std::forward<F>(body)(optimized.get());
}

const LogicalNode* only_child(const LogicalNode* n) {
    return (n != nullptr && n->child_count() == 1) ? n->child(0) : nullptr;
}

void expect_int_literal(const Expr* e, std::int64_t want, const std::string& ctx) {
    check(e && e->kind == ExprKind::Literal, ctx + ": is a Literal");
    if (e && e->kind == ExprKind::Literal) {
        const auto* p = std::get_if<std::int64_t>(&e->value.value);
        check(p != nullptr, ctx + ": literal holds an integer");
        check(p != nullptr && *p == want,
              ctx + ": == " + std::to_string(want));
    }
}

void expect_bool_literal(const Expr* e, bool want, const std::string& ctx) {
    check(e && e->kind == ExprKind::Literal, ctx + ": is a Literal");
    if (e && e->kind == ExprKind::Literal) {
        const auto* p = std::get_if<bool>(&e->value.value);
        check(p != nullptr, ctx + ": literal holds a bool");
        check(p != nullptr && *p == want, ctx + ": bool value");
    }
}

void expect_double_literal(const Expr* e, double want, const std::string& ctx) {
    check(e && e->kind == ExprKind::Literal, ctx + ": is a Literal");
    if (e && e->kind == ExprKind::Literal) {
        const auto* p = std::get_if<double>(&e->value.value);
        check(p != nullptr, ctx + ": literal holds a double");
        check(p != nullptr && *p == want, ctx + ": double value");
    }
}

// -------------------------------------------------------------------------

void test_fold_integer_arithmetic(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT 1 + 2 AS s\n");
    with_optimized_plan(cat, "SELECT 1 + 2 AS s", [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        check(root->exprs.size() == 1, "1 projected expr");
        if (root->exprs.size() == 1) {
            expect_int_literal(root->exprs[0].get(), 3, "1 + 2 folds to 3");
        }
    });
}

void test_fold_nested(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT (1 + 2) * 3 AS s\n");
    with_optimized_plan(cat, "SELECT (1 + 2) * 3 AS s", [](const LogicalNode* root) {
        check(root->exprs.size() == 1, "1 projected expr");
        if (root->exprs.size() == 1) {
            expect_int_literal(root->exprs[0].get(), 9, "(1 + 2) * 3 folds to 9");
        }
    });
}

void test_fold_comparison(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT 1 < 2 AS b\n");
    with_optimized_plan(cat, "SELECT 1 < 2 AS b", [](const LogicalNode* root) {
        check(root->exprs.size() == 1, "1 projected expr");
        if (root->exprs.size() == 1) {
            expect_bool_literal(root->exprs[0].get(), true, "1 < 2 folds to true");
        }
    });
}

void test_fold_double(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT 1.5 + 2.5 AS d\n");
    with_optimized_plan(cat, "SELECT 1.5 + 2.5 AS d", [](const LogicalNode* root) {
        check(root->exprs.size() == 1, "1 projected expr");
        if (root->exprs.size() == 1) {
            expect_double_literal(root->exprs[0].get(), 4.0, "1.5 + 2.5 folds to 4.0");
        }
    });
}

void test_fold_in_predicate(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users WHERE id > 3 + 4\n");
    with_optimized_plan(cat, "SELECT id FROM users WHERE id > 3 + 4",
                        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "child is Filter");
        // The predicate stays `id > <folded>`: a comparison whose right operand
        // folded from 3 + 4 to the literal 7, left operand still a column ref.
        if (filter && filter->predicate) {
            const Expr& p = *filter->predicate;
            check(p.kind == ExprKind::BinaryOp, "predicate is still a comparison");
            check(p.children.size() == 2, "comparison has 2 operands");
            if (p.children.size() == 2) {
                check(p.children[0]->kind == ExprKind::ColumnRef, "lhs stays a column ref");
                expect_int_literal(p.children[1].get(), 7, "rhs 3 + 4 folds to 7");
            }
        }
    });
}

void test_fold_nested_unary(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT NOT (1 = 1) AS b\n");
    with_optimized_plan(cat, "SELECT NOT (1 = 1) AS b", [](const LogicalNode* root) {
        check(root->exprs.size() == 1, "1 projected expr");
        if (root->exprs.size() == 1) {
            // 1 = 1 -> true, then NOT true -> false.
            expect_bool_literal(root->exprs[0].get(), false, "NOT (1 = 1) folds to false");
        }
    });
}

void test_no_fold_division_by_zero(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT 1 / 0 AS x  (NOT folded)\n");
    with_optimized_plan(cat, "SELECT 1 / 0 AS x", [](const LogicalNode* root) {
        check(root->exprs.size() == 1, "1 projected expr");
        if (root->exprs.size() == 1) {
            // Division by zero must be preserved (a runtime error), not folded.
            check(root->exprs[0] && root->exprs[0]->kind == ExprKind::BinaryOp,
                  "1 / 0 is left unfolded");
        }
    });
}

void test_no_fold_column(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id + 1 FROM users  (column not folded)\n");
    with_optimized_plan(cat, "SELECT id + 1 FROM users", [](const LogicalNode* root) {
        check(root->exprs.size() == 1, "1 projected expr");
        if (root->exprs.size() == 1) {
            // id + 1 has a non-constant operand, so it stays a BinaryOp.
            check(root->exprs[0] && root->exprs[0]->kind == ExprKind::BinaryOp,
                  "id + 1 is not folded");
        }
    });
}

// The predicate of a Project's Filter child, or null.
const Expr* filter_predicate(const LogicalNode* root) {
    const LogicalNode* filter = only_child(root);
    if (filter != nullptr && filter->op == LogicalOp::Filter) {
        return filter->predicate.get();
    }
    return nullptr;
}

void test_and_true(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE id = 1 AND 1 = 1  ->  id = 1\n");
    with_optimized_plan(cat, "SELECT id FROM users WHERE id = 1 AND 1 = 1",
                        [](const LogicalNode* root) {
        const Expr* p = filter_predicate(root);
        // 1 = 1 folds to true, then `id = 1 AND true` simplifies to `id = 1`.
        check(p && p->kind == ExprKind::BinaryOp &&
                  p->bin_op == db25::ast::BinaryOp::Equal,
              "predicate reduced to the id = 1 comparison");
    });
}

void test_and_false(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE 1 = 2 AND id = 1  ->  false\n");
    with_optimized_plan(cat, "SELECT id FROM users WHERE 1 = 2 AND id = 1",
                        [](const LogicalNode* root) {
        // 1 = 2 folds to false, then `false AND x` simplifies to false.
        expect_bool_literal(filter_predicate(root), false, "predicate is false");
    });
}

void test_or_true(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE id = 1 OR 2 = 2  ->  filter dropped\n");
    with_optimized_plan(cat, "SELECT id FROM users WHERE id = 1 OR 2 = 2",
                        [](const LogicalNode* root) {
        // 2 = 2 folds to true, `x OR true` simplifies to true, then the
        // always-true Filter is dropped: Project sits directly over the Scan.
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* child = only_child(root);
        check(child && child->op == LogicalOp::Scan,
              "always-true Filter removed (Project over Scan)");
    });
}

void test_double_negation(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE NOT (NOT (id = 1))  ->  id = 1\n");
    with_optimized_plan(cat, "SELECT id FROM users WHERE NOT (NOT (id = 1))",
                        [](const LogicalNode* root) {
        const Expr* p = filter_predicate(root);
        check(p && p->kind == ExprKind::BinaryOp &&
                  p->bin_op == db25::ast::BinaryOp::Equal,
              "NOT (NOT (id = 1)) reduces to id = 1");
    });
}

// Both WHERE conjuncts reference a single join side, so both push down and the
// top Filter disappears: Project -> Join(Filter users, Filter orders).
void test_pushdown_both_sides(const InMemoryCatalog& cat) {
    std::printf("[test] JOIN ... WHERE u.name = 'x' AND o.total > 100  (both pushed)\n");
    with_optimized_plan(
        cat,
        "SELECT u.id, o.total FROM users u INNER JOIN orders o ON u.id = o.user_id "
        "WHERE u.name = 'x' AND o.total > 100",
        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "Filter removed; Project over Join");
        if (join && join->op == LogicalOp::Join && join->child_count() == 2) {
            const LogicalNode* lf = join->child(0);
            const LogicalNode* rf = join->child(1);
            check(lf && lf->op == LogicalOp::Filter, "left input wrapped in a Filter");
            check(lf && lf->child(0) && lf->child(0)->op == LogicalOp::Scan &&
                      lf->child(0)->table_name == "users", "left Filter over Scan users");
            check(rf && rf->op == LogicalOp::Filter, "right input wrapped in a Filter");
            check(rf && rf->child(0) && rf->child(0)->op == LogicalOp::Scan &&
                      rf->child(0)->table_name == "orders", "right Filter over Scan orders");
            // The right conjuncts `o.total > 100` was on join slot #4 and is
            // remapped to slot #2 (total) in the orders input frame.
            if (rf && rf->predicate && rf->predicate->kind == ExprKind::BinaryOp &&
                rf->predicate->children.size() == 2) {
                check(rf->predicate->children[0]->kind == ExprKind::ColumnRef &&
                          rf->predicate->children[0]->input_index == 2,
                      "right predicate remapped to orders slot #2 (total)");
            }
        }
    });
}

// A conjunct spanning both join sides cannot be pushed and stays above the Join;
// the single-side conjunct still pushes into its input.
void test_pushdown_straddling_stays(const InMemoryCatalog& cat) {
    std::printf("[test] JOIN ... WHERE u.name = 'x' AND u.id = o.id  (straddle stays)\n");
    with_optimized_plan(
        cat,
        "SELECT u.id FROM users u INNER JOIN orders o ON u.id = o.user_id "
        "WHERE u.name = 'x' AND u.id = o.id",
        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "straddling Filter stays");
        // The surviving predicate is the cross-side comparison u.id = o.id (#0 = #2).
        if (filter && filter->predicate && filter->predicate->kind == ExprKind::BinaryOp &&
            filter->predicate->children.size() == 2) {
            check(filter->predicate->children[0]->input_index == 0 &&
                      filter->predicate->children[1]->input_index == 2,
                  "surviving predicate is u.id = o.id (#0 = #2)");
        }
        const LogicalNode* join = filter ? only_child(filter) : nullptr;
        check(join && join->op == LogicalOp::Join, "Filter over Join");
        if (join && join->child_count() == 2) {
            check(join->child(0)->op == LogicalOp::Filter, "left side got the name filter");
        }
    });
}

// An OUTER join is NOT eligible for pushdown (would change null-extension
// semantics), so the WHERE Filter is left intact above the Join.
void test_no_pushdown_outer_join(const InMemoryCatalog& cat) {
    std::printf("[test] LEFT JOIN ... WHERE u.name = 'x'  (not pushed)\n");
    with_optimized_plan(
        cat,
        "SELECT u.id FROM users u LEFT JOIN orders o ON u.id = o.user_id "
        "WHERE u.name = 'x'",
        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* filter = only_child(root);
        check(filter && filter->op == LogicalOp::Filter, "Filter stays above the OUTER join");
        const LogicalNode* join = filter ? only_child(filter) : nullptr;
        check(join && join->op == LogicalOp::Join &&
                  join->join_type == db25::ast::JoinType::Left, "child is the LEFT Join");
        if (join && join->child_count() == 2) {
            check(join->child(0)->op == LogicalOp::Scan &&
                      join->child(1)->op == LogicalOp::Scan,
                  "both join inputs remain bare Scans (nothing pushed)");
        }
    });
}

}  // namespace

int main() {
    const InMemoryCatalog cat = make_catalog();

    test_fold_integer_arithmetic(cat);
    test_fold_nested(cat);
    test_fold_comparison(cat);
    test_fold_double(cat);
    test_fold_in_predicate(cat);
    test_fold_nested_unary(cat);
    test_no_fold_division_by_zero(cat);
    test_no_fold_column(cat);
    test_and_true(cat);
    test_and_false(cat);
    test_or_true(cat);
    test_double_negation(cat);
    test_pushdown_both_sides(cat);
    test_pushdown_straddling_stays(cat);
    test_no_pushdown_outer_join(cat);

    std::printf("\n%d checks, %d failures\n", g_checks, g_failures);
    if (g_failures == 0) {
        std::printf("ALL TESTS PASSED\n");
    } else {
        std::printf("TESTS FAILED\n");
    }
    return g_failures == 0 ? 0 : 1;
}
