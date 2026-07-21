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

    std::printf("\n%d checks, %d failures\n", g_checks, g_failures);
    if (g_failures == 0) {
        std::printf("ALL TESTS PASSED\n");
    } else {
        std::printf("TESTS FAILED\n");
    }
    return g_failures == 0 ? 0 : 1;
}
