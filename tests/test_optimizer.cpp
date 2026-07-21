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
#include <functional>
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
    cat.add_table("emp", {
        {"id", DataType::Integer, false},
        {"dept", DataType::VarChar, true},
        {"sal", DataType::Double, true},
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
            // `o.total > 100` was on join slot #4; pushdown re-bases it into the
            // orders frame and column pruning then drops the unused orders.id, so
            // the orders scan becomes [user_id, total] and total lands at slot #1.
            check(rf && rf->child(0) && rf->child(0)->output.size() == 2,
                  "orders scan pruned to [user_id, total]");
            if (rf && rf->predicate && rf->predicate->kind == ExprKind::BinaryOp &&
                rf->predicate->children.size() == 2) {
                check(rf->predicate->children[0]->kind == ExprKind::ColumnRef &&
                          rf->predicate->children[0]->input_index == 1,
                      "right predicate at pruned orders slot #1 (total)");
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

// Descend through single-child operators to the first Scan of the given table.
const LogicalNode* find_scan(const LogicalNode* n, std::string_view table) {
    if (n == nullptr) {
        return nullptr;
    }
    if (n->op == LogicalOp::Scan && n->table_name == table) {
        return n;
    }
    for (std::size_t i = 0; i < n->child_count(); ++i) {
        if (const LogicalNode* s = find_scan(n->child(i), table)) {
            return s;
        }
    }
    return nullptr;
}

// First node of a given op anywhere in the tree (pre-order), or null.
const LogicalNode* find_op(const LogicalNode* n, LogicalOp op) {
    if (n == nullptr) {
        return nullptr;
    }
    if (n->op == op) {
        return n;
    }
    for (std::size_t i = 0; i < n->child_count(); ++i) {
        if (const LogicalNode* r = find_op(n->child(i), op)) {
            return r;
        }
    }
    return nullptr;
}

// True if any Subquery Expr remains represented anywhere in the tree's payloads.
bool any_represented_subquery(const LogicalNode* n) {
    if (n == nullptr) {
        return false;
    }
    bool found = false;
    std::function<void(const Expr*)> scan = [&](const Expr* e) {
        if (e == nullptr) return;
        if (e->kind == ExprKind::Subquery) found = true;
        for (const auto& c : e->children) scan(c.get());
    };
    if (n->predicate) scan(n->predicate.get());
    for (const auto& e : n->exprs) scan(e.get());
    for (const auto& e : n->aggregates) scan(e.get());
    for (std::size_t i = 0; i < n->child_count(); ++i) {
        if (any_represented_subquery(n->child(i))) found = true;
    }
    return found;
}

// A correlated EXISTS that is only ONE conjunct of a Filter over a join must
// still decorrelate to a SemiJoin in a SINGLE optimize() pass - it must not
// depend on a later pushdown isolating the subquery first (which made optimize()
// non-idempotent). The local conjunct is preserved (pushed toward its scan).
void test_decorrelate_exists_in_conjunction(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE local AND EXISTS (correlated) over a join -> SemiJoin (one pass)\n");
    with_optimized_plan(
        cat,
        "SELECT e.dept FROM emp e JOIN orders o ON e.id = o.user_id "
        "WHERE e.sal > 100 AND EXISTS (SELECT 1 FROM users u WHERE u.id = e.id)",
        [](const LogicalNode* root) {
        check(find_op(root, LogicalOp::SemiJoin) != nullptr,
              "conjunctive EXISTS decorrelated to a SemiJoin in one pass");
        check(!any_represented_subquery(root),
              "no represented subquery remains (EXISTS fully decorrelated)");
        // The local conjunct e.sal > 100 survives as a filter somewhere.
        check(find_op(root, LogicalOp::Filter) != nullptr,
              "the local conjunct e.sal > 100 is preserved as a Filter");
    });
}

// A column read by nobody is dropped from the Scan.
void test_prune_single_table(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM users  (name pruned from scan)\n");
    with_optimized_plan(cat, "SELECT id FROM users", [](const LogicalNode* root) {
        const LogicalNode* scan = find_scan(root, "users");
        check(scan && scan->output.size() == 1, "users scan pruned to [id]");
        if (scan && scan->output.size() == 1) {
            check(scan->output[0].name == "id", "surviving column is id");
        }
    });
}

// A wide scan under an Aggregate keeps only the grouped / aggregated columns.
void test_prune_under_aggregate(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT dept, COUNT(*) FROM emp GROUP BY dept  (emp pruned to [dept])\n");
    with_optimized_plan(cat, "SELECT dept, COUNT(*) FROM emp GROUP BY dept",
                        [](const LogicalNode* root) {
        const LogicalNode* scan = find_scan(root, "emp");
        check(scan && scan->output.size() == 1, "emp scan pruned to [dept]");
        if (scan && scan->output.size() == 1) {
            check(scan->output[0].name == "dept", "surviving column is dept");
        }
    });
}

// A join input drops the columns neither the join, a filter, nor the projection
// needs (here orders.id).
void test_prune_join_input(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.id, o.total FROM users u JOIN orders o ...  (orders.id pruned)\n");
    with_optimized_plan(
        cat,
        "SELECT u.id, o.total FROM users u INNER JOIN orders o ON u.id = o.user_id",
        [](const LogicalNode* root) {
        const LogicalNode* orders = find_scan(root, "orders");
        // orders keeps user_id (join key) and total (projected); id is dropped.
        check(orders && orders->output.size() == 2, "orders scan pruned to [user_id, total]");
    });
}

// Nothing is dropped when every column is consumed.
void test_no_prune_all_used(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, name FROM users  (nothing pruned)\n");
    with_optimized_plan(cat, "SELECT id, name FROM users", [](const LogicalNode* root) {
        const LogicalNode* scan = find_scan(root, "users");
        check(scan && scan->output.size() == 2, "users scan keeps [id, name]");
    });
}

// Safety: a correlated subquery makes its owning operator a pruning barrier, so
// the outer column its OuterRef needs (users.id) is NOT dropped even though the
// projection only selects name.
void test_prune_barrier_correlated_subquery(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT name FROM users WHERE EXISTS (... users.id ...)  (id kept)\n");
    with_optimized_plan(
        cat,
        "SELECT name FROM users WHERE EXISTS "
        "(SELECT 1 FROM orders WHERE orders.user_id = users.id)",
        [](const LogicalNode* root) {
        const LogicalNode* scan = find_scan(root, "users");
        // id must survive: the correlated EXISTS references it via an OuterRef.
        check(scan && scan->output.size() == 2,
              "users scan keeps [id, name] (id needed by the correlated subquery)");
    });
}

// Regression: a Window passes its child schema through positionally, so pruning
// must not drop passthrough columns nor shift them. The scan under the Window is
// kept intact and the projection's `id` stays at slot #0 (not replaced by sal).
void test_window_passthrough_not_corrupted(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, RANK() OVER (ORDER BY sal) FROM emp  (window passthrough)\n");
    with_optimized_plan(cat, "SELECT id, RANK() OVER (ORDER BY sal) FROM emp",
                        [](const LogicalNode* root) {
        const LogicalNode* scan = find_scan(root, "emp");
        check(scan && scan->output.size() == 3, "emp scan kept intact under Window");
        check(root->op == LogicalOp::Project && root->exprs.size() == 2, "Project of 2");
        if (root->op == LogicalOp::Project && root->exprs.size() == 2) {
            check(root->exprs[0] && root->exprs[0]->kind == ExprKind::ColumnRef &&
                      root->exprs[0]->input_index == 0,
                  "id stays at slot #0 (not corrupted to sal)");
        }
    });
}

// Regression: a USING join compacts its right frame, so slot arithmetic would
// mis-index; the pass must barrier it and prune nothing (keeping o.total correct).
void test_using_join_not_corrupted(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT u.id, o.total FROM users u JOIN orders o USING (id)  (barrier)\n");
    with_optimized_plan(cat,
                        "SELECT u.id, o.total FROM users u JOIN orders o USING (id)",
                        [](const LogicalNode* root) {
        const LogicalNode* orders = find_scan(root, "orders");
        check(orders && orders->output.size() == 3,
              "orders scan kept intact under a USING join (no mis-indexed prune)");
    });
}

// Regression: DISTINCT de-duplication depends on all its input columns, so a
// column the outer query does not select must not be pruned away underneath it.
void test_distinct_keeps_all_columns(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id FROM (SELECT DISTINCT id, name FROM users) sub  (name kept)\n");
    with_optimized_plan(cat,
                        "SELECT id FROM (SELECT DISTINCT id, name FROM users) sub",
                        [](const LogicalNode* root) {
        const LogicalNode* scan = find_scan(root, "users");
        check(scan && scan->output.size() == 2,
              "users scan keeps [id, name] (name needed for DISTINCT multiplicity)");
    });
}

// A correlated EXISTS filter becomes a SemiJoin whose condition is the hoisted
// correlation orders.user_id = users.id. After column pruning the right input is
// narrowed to just [user_id] and the left to [id], so in the pruned left ++ right
// frame the condition is #1 (orders.user_id) = #0 (users.id).
void test_decorrelate_exists(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE EXISTS (correlated)  ->  SemiJoin\n");
    with_optimized_plan(
        cat,
        "SELECT id FROM users WHERE EXISTS "
        "(SELECT 1 FROM orders WHERE orders.user_id = users.id)",
        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* sj = only_child(root);
        check(sj && sj->op == LogicalOp::SemiJoin, "child is a SemiJoin");
        if (sj && sj->child_count() == 2) {
            check(sj->child(0)->op == LogicalOp::Scan &&
                      sj->child(0)->table_name == "users", "left is Scan users");
            check(find_scan(sj->child(1), "orders") != nullptr, "right is orders relation");
            // Pruning narrowed the right (orders) input to only the join key.
            check(sj->child(1)->output.size() == 1,
                  "right input pruned to the single join-key column");
            check(sj->predicate && sj->predicate->kind == ExprKind::BinaryOp &&
                      sj->predicate->bin_op == db25::ast::BinaryOp::Equal,
                  "condition is the hoisted equality");
            if (sj->predicate && sj->predicate->children.size() == 2) {
                check(sj->predicate->children[0]->input_index == 1 &&
                          sj->predicate->children[1]->input_index == 0,
                      "condition is #1 (orders.user_id) = #0 (users.id) after pruning");
            }
        }
        // The subquery is gone: no owned Subquery remains in the plan.
        check(sj && sj->op == LogicalOp::SemiJoin, "no residual Filter/Subquery");
    });
}

// NOT EXISTS becomes an AntiJoin.
void test_decorrelate_not_exists(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE NOT EXISTS (correlated)  ->  AntiJoin\n");
    with_optimized_plan(
        cat,
        "SELECT id FROM users WHERE NOT EXISTS "
        "(SELECT 1 FROM orders WHERE orders.user_id = users.id)",
        [](const LogicalNode* root) {
        const LogicalNode* aj = only_child(root);
        check(aj && aj->op == LogicalOp::AntiJoin, "child is an AntiJoin");
    });
}

// An uncorrelated EXISTS becomes a conditionless SemiJoin.
void test_decorrelate_exists_uncorrelated(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE EXISTS (uncorrelated)  ->  SemiJoin (no condition)\n");
    with_optimized_plan(cat, "SELECT id FROM users WHERE EXISTS (SELECT 1 FROM orders)",
                        [](const LogicalNode* root) {
        const LogicalNode* sj = only_child(root);
        check(sj && sj->op == LogicalOp::SemiJoin, "child is a SemiJoin");
        check(sj && sj->predicate == nullptr, "no join condition (uncorrelated)");
    });
}

// Skip-level correlation: the outer EXISTS body has NO depth-1 correlation of
// its own (the analyzer flags that subquery "uncorrelated"), but a live OuterRef
// survives in a deeper-nested subquery. Decorrelating it into a conditionless
// SemiJoin would silently drop that correlation and change results, so the whole
// Filter must be left as a represented subquery instead.
void test_no_decorrelate_skip_level_correlation(const InMemoryCatalog& cat) {
    std::printf("[test] skip-level correlated EXISTS  (left as-is, not a SemiJoin)\n");
    with_optimized_plan(
        cat,
        "SELECT id FROM users WHERE EXISTS "
        "(SELECT 1 FROM orders WHERE EXISTS "
        "(SELECT 1 FROM emp WHERE emp.id = users.id))",
        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project, "root is Project");
        const LogicalNode* child = only_child(root);
        check(child && child->op == LogicalOp::Filter,
              "child is still a Filter (not decorrelated to a SemiJoin)");
        check(child && child->predicate &&
                  child->predicate->kind == ExprKind::Subquery,
              "the EXISTS predicate is left as a represented Subquery");
        check(find_scan(child, "users") != nullptr, "left relation preserved");
    });
}

// x IN (uncorrelated subquery) becomes a SemiJoin on the IN equality
// users.id = orders.user_id. After pruning the right input is narrowed to just
// [user_id], so in the pruned frame the condition is #0 (users.id) = #1
// (orders.user_id).
void test_decorrelate_in_uncorrelated(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE id IN (SELECT user_id FROM orders)  ->  SemiJoin\n");
    with_optimized_plan(
        cat, "SELECT id FROM users WHERE id IN (SELECT user_id FROM orders)",
        [](const LogicalNode* root) {
        const LogicalNode* sj = only_child(root);
        check(sj && sj->op == LogicalOp::SemiJoin, "child is a SemiJoin");
        check(sj && sj->predicate && sj->predicate->kind == ExprKind::BinaryOp &&
                  sj->predicate->bin_op == db25::ast::BinaryOp::Equal,
              "condition is the IN equality");
        if (sj && sj->predicate && sj->predicate->children.size() == 2) {
            check(sj->predicate->children[0]->input_index == 0 &&
                      sj->predicate->children[1]->input_index == 1,
                  "condition is #0 (users.id) = #1 (orders.user_id) after pruning");
        }
    });
}

// A correlated IN hoists BOTH the IN equality and the correlation predicate into
// the join condition: (#0 = #2) AND (#3 = #0).
void test_decorrelate_in_correlated(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE id IN (SELECT id FROM orders WHERE user_id = users.id)  ->  SemiJoin\n");
    with_optimized_plan(
        cat,
        "SELECT id FROM users WHERE id IN "
        "(SELECT id FROM orders WHERE orders.user_id = users.id)",
        [](const LogicalNode* root) {
        const LogicalNode* sj = only_child(root);
        check(sj && sj->op == LogicalOp::SemiJoin, "child is a SemiJoin");
        check(sj && sj->predicate && sj->predicate->kind == ExprKind::BinaryOp &&
                  sj->predicate->bin_op == db25::ast::BinaryOp::And,
              "condition is a conjunction (IN eq AND hoisted correlation)");
        // No residual subquery: the right input is a bare orders relation.
        check(sj && sj->child_count() == 2 &&
                  find_scan(sj->child(1), "orders") != nullptr, "right is orders relation");
    });
}

// A local (uncorrelated) WHERE inside the IN subquery is preserved as a Filter on
// the right input, below the SemiJoin.
void test_decorrelate_in_local_filter(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE id IN (SELECT user_id FROM orders WHERE total > 10)  ->  SemiJoin over Filter\n");
    with_optimized_plan(
        cat,
        "SELECT id FROM users WHERE id IN "
        "(SELECT user_id FROM orders WHERE orders.total > 10)",
        [](const LogicalNode* root) {
        const LogicalNode* sj = only_child(root);
        check(sj && sj->op == LogicalOp::SemiJoin, "child is a SemiJoin");
        if (sj && sj->child_count() == 2) {
            check(sj->child(1)->op == LogicalOp::Filter, "right input keeps the local Filter");
            check(find_scan(sj->child(1), "orders") != nullptr, "Filter is over orders");
        }
    });
}

// NOT IN over a NULLABLE projected column must stay a represented subquery: an
// AntiJoin would change results under SQL's three-valued NOT IN semantics.
void test_no_decorrelate_not_in_nullable(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE id NOT IN (SELECT user_id FROM orders)  (nullable -> left as-is)\n");
    with_optimized_plan(
        cat, "SELECT id FROM users WHERE id NOT IN (SELECT user_id FROM orders)",
        [](const LogicalNode* root) {
        const LogicalNode* child = only_child(root);
        check(child && child->op == LogicalOp::Filter,
              "child is still a Filter (nullable NOT IN not decorrelated)");
        check(child && child->predicate &&
                  child->predicate->kind == ExprKind::Subquery,
              "the NOT IN predicate is left as a represented Subquery");
    });
}

// NOT IN where BOTH the probe value and the projected column are NOT NULL is
// sound to turn into an AntiJoin.
void test_decorrelate_not_in_not_null(const InMemoryCatalog& cat) {
    std::printf("[test] WHERE id NOT IN (SELECT id FROM orders)  (not-null -> AntiJoin)\n");
    with_optimized_plan(
        cat, "SELECT id FROM users WHERE id NOT IN (SELECT id FROM orders)",
        [](const LogicalNode* root) {
        const LogicalNode* aj = only_child(root);
        check(aj && aj->op == LogicalOp::AntiJoin, "child is an AntiJoin");
        check(aj && aj->predicate && aj->predicate->kind == ExprKind::BinaryOp &&
                  aj->predicate->bin_op == db25::ast::BinaryOp::Equal,
              "condition is the IN equality");
    });
}

// A correlated aggregate scalar subquery becomes a LEFT JOIN whose right input
// is the inner relation grouped by the correlation key, with the subquery expr
// replaced by a ColumnRef to the aggregate column.
void test_decorrelate_scalar_sum(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, (SELECT SUM(total) FROM orders WHERE user_id = id)  ->  LEFT JOIN\n");
    with_optimized_plan(
        cat,
        "SELECT u.id, (SELECT SUM(o.total) FROM orders o WHERE o.user_id = u.id) "
        "FROM users u",
        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->exprs.size() == 2, "root Project of 2");
        // The scalar subquery item is now a bare ColumnRef (into the joined frame).
        if (root->exprs.size() == 2) {
            check(root->exprs[1] && root->exprs[1]->kind == ExprKind::ColumnRef,
                  "scalar subquery replaced by a ColumnRef");
        }
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join &&
                  join->join_type == db25::ast::JoinType::Left, "child is a LEFT Join");
        if (join && join->child_count() == 2) {
            check(find_scan(join->child(0), "users") != nullptr, "left input is users");
            const LogicalNode* g = join->child(1);
            check(g && g->op == LogicalOp::Aggregate && g->group_keys.size() == 1 &&
                      g->aggregates.size() == 1, "right input is a grouped Aggregate");
            check(join->predicate && join->predicate->kind == ExprKind::BinaryOp &&
                      join->predicate->bin_op == db25::ast::BinaryOp::Equal,
                  "join condition is the correlation equality");
        }
    });
}

// A local (uncorrelated) predicate inside the scalar subquery is preserved as a
// Filter under the grouped Aggregate on the right.
void test_decorrelate_scalar_local_filter(const InMemoryCatalog& cat) {
    std::printf("[test] scalar subquery with a local WHERE  ->  Filter under the Aggregate\n");
    with_optimized_plan(
        cat,
        "SELECT u.id, (SELECT MAX(o.total) FROM orders o "
        "WHERE o.user_id = u.id AND o.total > 5) FROM users u",
        [](const LogicalNode* root) {
        const LogicalNode* join = only_child(root);
        check(join && join->op == LogicalOp::Join, "child is a Join");
        if (join && join->child_count() == 2) {
            const LogicalNode* g = join->child(1);
            check(g && g->op == LogicalOp::Aggregate && g->child_count() == 1 &&
                      g->child(0)->op == LogicalOp::Filter,
                  "the local predicate is a Filter under the Aggregate");
        }
    });
}

// The subquery may sit nested inside a larger projected expression; only the
// subquery node is replaced, the surrounding arithmetic is preserved.
void test_decorrelate_scalar_nested(const InMemoryCatalog& cat) {
    std::printf("[test] (SELECT SUM(total) ...) + 100  ->  BinaryOp over a ColumnRef\n");
    with_optimized_plan(
        cat,
        "SELECT u.id, (SELECT SUM(o.total) FROM orders o WHERE o.user_id = u.id) + 100 "
        "FROM users u",
        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->exprs.size() == 2, "root Project of 2");
        if (root->exprs.size() == 2) {
            check(root->exprs[1] && root->exprs[1]->kind == ExprKind::BinaryOp,
                  "the projected item stays a BinaryOp (+ 100)");
            check(root->exprs[1] && root->exprs[1]->children.size() == 2 &&
                      root->exprs[1]->children[0]->kind == ExprKind::ColumnRef,
                  "its left operand is the substituted aggregate ColumnRef");
        }
        check(only_child(root) && only_child(root)->op == LogicalOp::Join, "child is a Join");
    });
}

// COUNT is NOT decorrelated: it yields 0 over the empty set, which a LEFT JOIN's
// NULL cannot reproduce, so it is left as a represented subquery.
void test_no_decorrelate_scalar_count(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, (SELECT COUNT(*) FROM orders WHERE user_id = id)  (left as-is)\n");
    with_optimized_plan(
        cat,
        "SELECT u.id, (SELECT COUNT(*) FROM orders o WHERE o.user_id = u.id) FROM users u",
        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->exprs.size() == 2, "root Project of 2");
        if (root->exprs.size() == 2) {
            check(root->exprs[1] && root->exprs[1]->kind == ExprKind::Subquery,
                  "COUNT scalar subquery left as a Subquery expr");
        }
        check(only_child(root) && only_child(root)->op == LogicalOp::Scan,
              "no join introduced (still a bare Scan child)");
    });
}

// An uncorrelated scalar subquery in the SELECT list is left as a represented
// subquery, not rewritten (this pass only decorrelates correlated ones).
void test_no_decorrelate_scalar_subquery(const InMemoryCatalog& cat) {
    std::printf("[test] SELECT id, (SELECT MAX(total) FROM orders) FROM users  (left as-is)\n");
    with_optimized_plan(cat, "SELECT id, (SELECT MAX(total) FROM orders) FROM users",
                        [](const LogicalNode* root) {
        check(root->op == LogicalOp::Project && root->exprs.size() == 2, "root Project of 2");
        if (root->exprs.size() == 2) {
            check(root->exprs[1] && root->exprs[1]->kind == ExprKind::Subquery,
                  "scalar subquery left as a Subquery expr (not decorrelated)");
        }
    });
}

// Column pruning treats a semi/anti join as non-opaque: its output is the left
// schema, and the right input is needed only for the columns its condition uses.
// A decorrelated IN over the full orders table keeps only [user_id] on the right.
void test_prune_semijoin_inputs(const InMemoryCatalog& cat) {
    std::printf("[test] SemiJoin right input pruned to the join key\n");
    with_optimized_plan(
        cat, "SELECT id FROM users WHERE id IN (SELECT user_id FROM orders)",
        [](const LogicalNode* root) {
        const LogicalNode* sj = only_child(root);
        check(sj && sj->op == LogicalOp::SemiJoin, "child is a SemiJoin");
        if (sj && sj->child_count() == 2) {
            const LogicalNode* r = find_scan(sj->child(1), "orders");
            check(r && r->output.size() == 1,
                  "orders (right) pruned to [user_id] only (was [id,user_id,total])");
            check(sj->child(0)->op == LogicalOp::Scan && sj->child(0)->output.size() == 1,
                  "users (left) pruned to [id] only");
        }
    });
}

// Predicate pushdown moves a whole Filter below a Semi / Anti join into its LEFT
// input (every conjunct references only left columns, since the join outputs the
// left schema). This shape is not produced by the current SQL front end, so it is
// exercised with a hand-built plan.
void test_pushdown_through_semijoin() {
    std::printf("[test] Filter over SemiJoin -> filter pushed into the left input\n");
    auto mkscan = [](const char* nm, db25::plan::Schema sch) {
        auto s = std::make_unique<LogicalNode>(LogicalOp::Scan);
        s->table_name = nm;
        s->output = std::move(sch);
        return s;
    };
    auto colref = [](std::uint32_t idx) {
        auto e = std::make_unique<Expr>(ExprKind::ColumnRef);
        e->input_index = idx;
        e->type = DataType::Integer;
        return e;
    };
    // SemiJoin( Scan A[a0,a1], Scan B[b0] ) ON #0 = #2
    auto semi = std::make_unique<LogicalNode>(LogicalOp::SemiJoin);
    auto left = mkscan("A", {{"a0", DataType::Integer, false, 0, 0},
                             {"a1", DataType::Integer, true, 0, 0}});
    auto right = mkscan("B", {{"b0", DataType::Integer, true, 0, 0}});
    auto cond = std::make_unique<Expr>(ExprKind::BinaryOp);
    cond->bin_op = db25::ast::BinaryOp::Equal;
    cond->children.push_back(colref(0));
    cond->children.push_back(colref(2));
    semi->output = left->output;  // semi join output = left schema
    semi->predicate = std::move(cond);
    semi->add_child(std::move(left));
    semi->add_child(std::move(right));
    // Filter(#1 > 5) directly over the SemiJoin (a1 > 5, a left column).
    auto flt = std::make_unique<LogicalNode>(LogicalOp::Filter);
    auto gt = std::make_unique<Expr>(ExprKind::BinaryOp);
    gt->bin_op = db25::ast::BinaryOp::GreaterThan;
    auto five = std::make_unique<Expr>(ExprKind::Literal);
    five->value.value = static_cast<std::int64_t>(5);
    gt->children.push_back(colref(1));
    gt->children.push_back(std::move(five));
    flt->predicate = std::move(gt);
    flt->output = semi->output;
    flt->add_child(std::move(semi));

    db25::plan::LogicalNodePtr root = std::move(flt);
    db25::plan::push_down_filters(root);

    check(root->op == LogicalOp::SemiJoin, "root is now the SemiJoin (filter no longer on top)");
    if (root->op == LogicalOp::SemiJoin && root->child_count() == 2) {
        check(root->child(0)->op == LogicalOp::Filter, "filter pushed into the LEFT input");
        check(root->child(0)->child_count() == 1 &&
                  root->child(0)->child(0)->table_name == "A",
              "the pushed Filter now sits directly over left Scan A");
        check(root->child(1)->op == LogicalOp::Scan && root->child(1)->table_name == "B",
              "right input untouched");
    }
}

// optimize() must be idempotent: a filter over stacked joins is pushed all the
// way to its base scan in ONE pass, so a second optimize() changes nothing. The
// EXISTS/IN cases also pin the conjunctive-subquery fix: a `local AND EXISTS`
// filter over a join must decorrelate to a Semi/Anti join in the SAME pass (not
// only after a later pushdown isolates the subquery), or optimize() would differ
// between the first and second run.
void test_optimize_idempotent(const InMemoryCatalog& cat) {
    std::printf("[test] optimize() is idempotent over stacked joins\n");
    const char* sqls[] = {
        "SELECT e.dept FROM emp e JOIN orders o ON e.id = o.user_id "
        "JOIN users u ON e.id = u.id WHERE e.sal > 100",
        "SELECT u.name FROM users u JOIN orders o ON u.id = o.user_id "
        "WHERE o.total > 5 AND u.id > 1",
        // local conjunct AND correlated EXISTS, over a join.
        "SELECT e.dept FROM emp e JOIN orders o ON e.id = o.user_id "
        "WHERE e.sal > 100 AND EXISTS (SELECT 1 FROM users u WHERE u.id = e.id)",
        // local conjunct AND IN-subquery, over a join.
        "SELECT e.dept FROM emp e JOIN orders o ON e.id = o.user_id "
        "WHERE e.sal > 100 AND e.id IN (SELECT id FROM users)",
    };
    for (const char* sql : sqls) {
        db25::parser::Parser parser;
        auto parsed = parser.parse(sql);
        check(parsed.has_value(), std::string{"parse: "} + sql);
        if (!parsed) continue;
        Analyzer analyzer(cat);
        analyzer.analyze(parsed.value());
        check(!analyzer.has_errors(), std::string{"analyze: "} + sql);
        Binder binder(analyzer, cat);
        BindResult res = binder.bind(parsed.value());
        check(res.ok, std::string{"bind: "} + sql);
        if (!res.ok) continue;
        auto once = db25::plan::optimize(std::move(res.root));
        const std::string d1 = db25::plan::dump_plan(once.get());
        auto twice = db25::plan::optimize(std::move(once));
        const std::string d2 = db25::plan::dump_plan(twice.get());
        check(d1 == d2, std::string{"optimize() idempotent: "} + sql);
    }
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
    test_prune_single_table(cat);
    test_prune_under_aggregate(cat);
    test_prune_join_input(cat);
    test_no_prune_all_used(cat);
    test_prune_barrier_correlated_subquery(cat);
    test_window_passthrough_not_corrupted(cat);
    test_using_join_not_corrupted(cat);
    test_distinct_keeps_all_columns(cat);
    test_decorrelate_exists(cat);
    test_decorrelate_exists_in_conjunction(cat);
    test_decorrelate_not_exists(cat);
    test_decorrelate_exists_uncorrelated(cat);
    test_no_decorrelate_skip_level_correlation(cat);
    test_decorrelate_in_uncorrelated(cat);
    test_decorrelate_in_correlated(cat);
    test_decorrelate_in_local_filter(cat);
    test_no_decorrelate_not_in_nullable(cat);
    test_decorrelate_not_in_not_null(cat);
    test_decorrelate_scalar_sum(cat);
    test_decorrelate_scalar_local_filter(cat);
    test_decorrelate_scalar_nested(cat);
    test_no_decorrelate_scalar_count(cat);
    test_no_decorrelate_scalar_subquery(cat);
    test_prune_semijoin_inputs(cat);
    test_pushdown_through_semijoin();
    test_optimize_idempotent(cat);

    std::printf("\n%d checks, %d failures\n", g_checks, g_failures);
    if (g_failures == 0) {
        std::printf("ALL TESTS PASSED\n");
    } else {
        std::printf("TESTS FAILED\n");
    }
    return g_failures == 0 ? 0 : 1;
}
