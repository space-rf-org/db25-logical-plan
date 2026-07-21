// DB25 Logical Plan - Expression-IR lowering tests
//
// Exercises Binder::lower_expr over real parse + analyze output for the design
// memo's worked examples:
//   (a) WHERE o.total > 100        -> BinaryOp(GreaterThan){ ColumnRef, Literal }
//   (b) SUM(sal) + 1               -> BinaryOp(Add){ Aggregate(SUM){ColumnRef}, Literal }
//   (c) column-ref slot resolution against a hand-constructed input Schema
//   (d) join ON, concatenated child0.output ++ child1.output indexing
//   (e) correlated EXISTS -> owned sub_plan + Subquery(correlated); OuterRef
//
// Self-contained harness (no gtest), matching tests/test_binder.cpp. lower_expr
// is private on Binder; a friend access struct (declared in binder.hpp) exposes
// it and the enclosing-schema stack for the OuterRef case.

#include "db25/plan/binder.hpp"
#include "db25/plan/expr_ir.hpp"
#include "db25/plan/logical_plan.hpp"

#include "db25/parser/parser.hpp"
#include "db25/semantic/analyzer.hpp"
#include "db25/semantic/ast_helpers.hpp"
#include "db25/semantic/catalog.hpp"

#include <cstdio>
#include <string>
#include <string_view>

using db25::ast::ASTNode;
using db25::ast::DataType;
using db25::ast::NodeType;
using db25::plan::Binder;
using db25::plan::ColumnSchema;
using db25::plan::Expr;
using db25::plan::ExprKind;
using db25::plan::ExprPtr;
using db25::plan::LogicalOp;
using db25::plan::Schema;
using db25::plan::SubqueryKind;
using db25::semantic::Analyzer;
using db25::semantic::find_child;
using db25::semantic::first_child;
using db25::semantic::InMemoryCatalog;

namespace db25::plan {
// Friend hook: reach the private lowering surface from the test TU.
struct BinderExprTestAccess {
    static ExprPtr lower(Binder& b, const ASTNode* n, const Schema& in, std::string& err) {
        return b.lower_expr(n, in, err);
    }
    static void push_outer(Binder& b, const Schema& s) { b.outer_inputs_.push_back(&s); }
    static void pop_outer(Binder& b) { b.outer_inputs_.pop_back(); }
};
}  // namespace db25::plan

using db25::plan::BinderExprTestAccess;

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
    cat.add_table("lines", {
        {"id", DataType::Integer, false},
        {"oid", DataType::Integer, true},
        {"qty", DataType::Integer, true},
    });
    return cat;
}

// Build a Schema for a catalog table with the same (table_id, column_id) the
// analyzer assigns, so lower_expr's id-based resolution lines up.
Schema schema_of(const InMemoryCatalog& cat, std::string_view table) {
    Schema s;
    const auto* t = cat.find_table(table);
    if (t == nullptr) {
        return s;
    }
    for (const auto& c : t->columns) {
        s.push_back(ColumnSchema{c.name, c.type, c.nullable, t->table_id, c.column_id});
    }
    return s;
}

// Owns the Parser/Analyzer for the lifetime of a lowering test (the analyzer
// must be alive while lower_expr reads types; the AST text must be alive too).
struct Analyzed {
    db25::parser::Parser parser;
    const ASTNode* stmt = nullptr;
    bool ok = false;
};

// A parse + analyze fixture; the caller keeps it alive across lowering.
void analyze_into(Analyzed& out, const InMemoryCatalog& cat, Analyzer& az,
                  std::string_view sql) {
    auto parsed = out.parser.parse(sql);
    out.ok = parsed.has_value();
    check(out.ok, std::string{"parse: "} + std::string{sql});
    if (!out.ok) {
        return;
    }
    out.stmt = parsed.value();
    az.analyze(const_cast<ASTNode*>(out.stmt));
    check(!az.has_errors(), std::string{"analyze clean: "} + std::string{sql});
    (void)cat;
}

const ASTNode* where_predicate(const ASTNode* select) {
    const ASTNode* where = find_child(select, NodeType::WhereClause);
    return where != nullptr ? first_child(where) : nullptr;
}

const ASTNode* first_select_item(const ASTNode* select) {
    const ASTNode* list = find_child(select, NodeType::SelectList);
    return list != nullptr ? first_child(list) : nullptr;
}

// -------------------------------------------------------------------------
// (a) WHERE o.total > 100
// -------------------------------------------------------------------------
void test_predicate_greater_than(const InMemoryCatalog& cat) {
    std::printf("[test] (a) WHERE o.total > 100\n");
    Analyzer az(cat);
    Analyzed a;
    analyze_into(a, cat, az, "SELECT total FROM orders o WHERE o.total > 100");
    if (!a.ok) return;

    const ASTNode* pred = where_predicate(a.stmt);
    check(pred != nullptr, "found WHERE predicate");
    const Schema input = schema_of(cat, "orders");  // id@0, user_id@1, total@2

    Binder binder(az, cat);
    std::string err;
    ExprPtr e = BinderExprTestAccess::lower(binder, pred, input, err);
    check(e != nullptr, std::string{"lowered predicate: "} + err);
    if (!e) return;

    check(e->kind == ExprKind::BinaryOp, "root is BinaryOp");
    check(e->bin_op == db25::ast::BinaryOp::GreaterThan, "op is GreaterThan");
    check(e->type == DataType::Boolean, "predicate type Boolean");
    check(e->nullability == 2, "predicate nullable");
    check(e->children.size() == 2, "binary has 2 children");
    if (e->children.size() != 2) return;

    const Expr& lhs = *e->children[0];
    check(lhs.kind == ExprKind::ColumnRef, "lhs is ColumnRef");
    check(lhs.input_index == 2, "lhs input_index == total slot (2)");
    check(lhs.type == DataType::Double, "lhs type Double");
    check(lhs.ref_table_id == cat.find_table("orders")->table_id, "lhs ref table id");

    const Expr& rhs = *e->children[1];
    check(rhs.kind == ExprKind::Literal, "rhs is Literal");
    check(rhs.type == DataType::Integer, "rhs literal type Integer");
    check(rhs.nullability == 1, "literal not-null");
    check(std::holds_alternative<std::int64_t>(rhs.value.value) &&
              std::get<std::int64_t>(rhs.value.value) == 100,
          "literal value == 100");
}

// -------------------------------------------------------------------------
// (b) SUM(sal) + 1  (arithmetic over an aggregate)
// -------------------------------------------------------------------------
void test_arith_over_aggregate(const InMemoryCatalog& cat) {
    std::printf("[test] (b) SUM(sal) + 1\n");
    Analyzer az(cat);
    Analyzed a;
    analyze_into(a, cat, az, "SELECT SUM(sal) + 1 FROM emp GROUP BY dept");
    if (!a.ok) return;

    const ASTNode* item = first_select_item(a.stmt);
    check(item != nullptr && item->node_type == NodeType::BinaryExpr, "select item is '+'");
    const Schema input = schema_of(cat, "emp");  // id@0, dept@1, sal@2

    Binder binder(az, cat);
    std::string err;
    ExprPtr e = BinderExprTestAccess::lower(binder, item, input, err);
    check(e != nullptr, std::string{"lowered SUM(sal)+1: "} + err);
    if (!e) return;

    check(e->kind == ExprKind::BinaryOp, "root is BinaryOp");
    check(e->bin_op == db25::ast::BinaryOp::Add, "op is Add");
    check(e->type == DataType::Double, "sum+1 type Double (analyzer-reconciled)");
    check(e->children.size() == 2, "binary has 2 children");
    if (e->children.size() != 2) return;

    const Expr& agg = *e->children[0];
    check(agg.kind == ExprKind::Aggregate, "lhs is Aggregate");
    check(agg.func_name == "SUM", "aggregate is SUM");
    check(agg.type == DataType::Double, "aggregate type Double");
    check(agg.children.size() == 1, "aggregate has 1 arg");
    if (agg.children.size() == 1) {
        const Expr& arg = *agg.children[0];
        check(arg.kind == ExprKind::ColumnRef, "agg arg is ColumnRef");
        check(arg.input_index == 2, "agg arg input_index == sal slot (2)");
        check(arg.type == DataType::Double, "agg arg type Double");
    }

    const Expr& one = *e->children[1];
    check(one.kind == ExprKind::Literal, "rhs is Literal");
    check(one.type == DataType::Integer, "rhs literal Integer");
}

// -------------------------------------------------------------------------
// (c) column-ref slot resolution against a hand-constructed input Schema
// -------------------------------------------------------------------------
void test_columnref_handbuilt_schema(const InMemoryCatalog& cat) {
    std::printf("[test] (c) ColumnRef slot resolution (hand-built schema)\n");
    Analyzer az(cat);
    Analyzed a;
    analyze_into(a, cat, az, "SELECT total FROM orders o WHERE o.total > 100");
    if (!a.ok) return;

    // The SELECT-list `total` ColumnRef (orders.total, tid=orders, cid=3).
    const ASTNode* total_ref = first_select_item(a.stmt);
    check(total_ref != nullptr && total_ref->node_type == NodeType::ColumnRef,
          "select item is ColumnRef 'total'");

    const std::uint32_t orders_tid = cat.find_table("orders")->table_id;
    const auto cid = [&](const char* c) { return cat.find_table("orders")->find_column(c)->column_id; };

    // Deliberately reorder the schema: total is placed at slot 0 here, so a
    // correct positional resolution must track the *schema*, not the SQL text.
    Schema reordered = {
        ColumnSchema{"total", DataType::Double, true, orders_tid, cid("total")},
        ColumnSchema{"user_id", DataType::Integer, true, orders_tid, cid("user_id")},
        ColumnSchema{"id", DataType::Integer, false, orders_tid, cid("id")},
    };

    Binder binder(az, cat);
    std::string err;
    ExprPtr e = BinderExprTestAccess::lower(binder, total_ref, reordered, err);
    check(e != nullptr, std::string{"lowered ColumnRef: "} + err);
    if (!e) return;
    check(e->kind == ExprKind::ColumnRef, "is ColumnRef");
    check(e->input_index == 0, "total resolves to slot 0 in reordered schema");
    check(e->type == DataType::Double, "type Double");

    // And against the natural order, total sits at slot 2.
    const Schema natural = schema_of(cat, "orders");
    std::string err2;
    ExprPtr e2 = BinderExprTestAccess::lower(binder, total_ref, natural, err2);
    check(e2 != nullptr && e2->input_index == 2, "total resolves to slot 2 in natural schema");
}

// -------------------------------------------------------------------------
// (d) join ON: concatenated child0.output ++ child1.output indexing
// -------------------------------------------------------------------------
void test_join_concatenated_index(const InMemoryCatalog& cat) {
    std::printf("[test] (d) join ON concatenated indexing\n");
    Analyzer az(cat);
    Analyzed a;
    analyze_into(a, cat, az,
                 "SELECT u.id, o.total FROM users u INNER JOIN orders o ON u.id = o.user_id");
    if (!a.ok) return;

    // Find the ON predicate: FromClause -> JoinClause -> BinaryExpr '='.
    const ASTNode* from = find_child(a.stmt, NodeType::FromClause);
    const ASTNode* join = from != nullptr ? find_child(from, NodeType::JoinClause) : nullptr;
    const ASTNode* on = join != nullptr ? find_child(join, NodeType::BinaryExpr) : nullptr;
    check(on != nullptr, "found ON predicate");
    if (on == nullptr) return;

    // Join input schema = users.output ++ orders.output:
    //   users:  id@0, name@1
    //   orders: id@2, user_id@3, total@4
    Schema input = schema_of(cat, "users");
    const Schema right = schema_of(cat, "orders");
    input.insert(input.end(), right.begin(), right.end());

    Binder binder(az, cat);
    std::string err;
    ExprPtr e = BinderExprTestAccess::lower(binder, on, input, err);
    check(e != nullptr, std::string{"lowered ON: "} + err);
    if (!e) return;

    check(e->kind == ExprKind::BinaryOp && e->bin_op == db25::ast::BinaryOp::Equal,
          "ON is BinaryOp(Equal)");
    check(e->children.size() == 2, "ON has 2 children");
    if (e->children.size() != 2) return;

    const Expr& l = *e->children[0];
    const Expr& r = *e->children[1];
    check(l.kind == ExprKind::ColumnRef && l.input_index == 0, "u.id -> left slot 0");
    check(r.kind == ExprKind::ColumnRef && r.input_index == 3, "o.user_id -> right slot 3");
    check(r.type == DataType::Integer, "o.user_id type Integer");
}

// -------------------------------------------------------------------------
// (e) correlated EXISTS: owned sub_plan + Subquery(correlated), and OuterRef
// -------------------------------------------------------------------------
void test_correlated_exists(const InMemoryCatalog& cat) {
    std::printf("[test] (e) correlated EXISTS -> sub_plan + OuterRef\n");
    Analyzer az(cat);
    Analyzed a;
    analyze_into(a, cat, az,
                 "SELECT id FROM orders o WHERE EXISTS "
                 "(SELECT 1 FROM lines l WHERE l.oid = o.id)");
    if (!a.ok) return;

    const ASTNode* pred = where_predicate(a.stmt);  // UnaryExpr EXISTS
    check(pred != nullptr && pred->node_type == NodeType::UnaryExpr, "predicate is UnaryExpr EXISTS");
    const Schema outer = schema_of(cat, "orders");  // enclosing input

    Binder binder(az, cat);
    std::string err;
    ExprPtr e = BinderExprTestAccess::lower(binder, pred, outer, err);
    check(e != nullptr, std::string{"lowered EXISTS: "} + err);
    if (!e) return;

    check(e->kind == ExprKind::Subquery, "EXISTS lowers to a Subquery Expr");
    check(e->subquery_kind == SubqueryKind::Exists, "subquery kind Exists");
    check(e->correlated, "subquery is correlated");
    check(e->type == DataType::Boolean, "EXISTS type Boolean");
    check(e->sub_plan != nullptr, "owns a sub_plan");
    check(e->sub_plan && e->sub_plan->op == LogicalOp::Project, "sub_plan root is a Project");

    // OuterRef: lower the *inner* predicate `l.oid = o.id` against the inner
    // input (lines), with orders pushed as the enclosing schema. o.id is not a
    // lines column, so it must resolve outward to an OuterRef.
    const ASTNode* subq = nullptr;
    for (const ASTNode* c = first_child(pred); c != nullptr; c = c->next_sibling) {
        if (c->node_type == NodeType::Subquery || c->node_type == NodeType::SubqueryExpr) {
            subq = c;
            break;
        }
    }
    check(subq != nullptr, "found Subquery node");
    const ASTNode* inner_sel = subq != nullptr ? find_child(subq, NodeType::SelectStmt) : nullptr;
    const ASTNode* inner_pred = inner_sel != nullptr ? where_predicate(inner_sel) : nullptr;
    check(inner_pred != nullptr && inner_pred->node_type == NodeType::BinaryExpr,
          "found inner predicate 'l.oid = o.id'");
    if (inner_pred == nullptr) return;

    const Schema inner_input = schema_of(cat, "lines");  // id@0, oid@1, qty@2
    BinderExprTestAccess::push_outer(binder, outer);
    std::string ierr;
    ExprPtr ie = BinderExprTestAccess::lower(binder, inner_pred, inner_input, ierr);
    BinderExprTestAccess::pop_outer(binder);
    check(ie != nullptr, std::string{"lowered inner predicate: "} + ierr);
    if (!ie) return;

    check(ie->kind == ExprKind::BinaryOp && ie->bin_op == db25::ast::BinaryOp::Equal,
          "inner is BinaryOp(Equal)");
    if (ie->children.size() != 2) {
        check(false, "inner has 2 children");
        return;
    }
    const Expr& lo = *ie->children[0];
    const Expr& ro = *ie->children[1];
    check(lo.kind == ExprKind::ColumnRef && lo.input_index == 1, "l.oid -> inner slot 1");
    check(ro.kind == ExprKind::OuterRef, "o.id -> OuterRef");
    check(ro.outer_depth == 1, "OuterRef depth 1");
    check(ro.input_index == 0, "OuterRef resolves to orders.id slot 0");
    check(ro.type == DataType::Integer, "OuterRef type Integer");
}

}  // namespace

// -------------------------------------------------------------------------
// An integer literal too large for int64 must not silently lower to NULL: it is
// promoted to double (SQLite's numeric widening), so comparisons still evaluate.
// -------------------------------------------------------------------------
void test_integer_literal_overflow_promotes_double(const InMemoryCatalog& cat) {
    std::printf("[test] (overflow) WHERE id < 9223372036854775808\n");
    Analyzer az(cat);
    Analyzed a;
    analyze_into(a, cat, az,
                 "SELECT id FROM orders o WHERE o.id < 9223372036854775808");
    if (!a.ok) return;

    const ASTNode* pred = where_predicate(a.stmt);
    check(pred != nullptr, "found WHERE predicate");
    const Schema input = schema_of(cat, "orders");

    Binder binder(az, cat);
    std::string err;
    ExprPtr e = BinderExprTestAccess::lower(binder, pred, input, err);
    check(e != nullptr, std::string{"lowered predicate: "} + err);
    if (!e || e->children.size() != 2) return;

    const Expr& rhs = *e->children[1];
    check(rhs.kind == ExprKind::Literal, "rhs is Literal");
    // INT64_MAX + 1 overflows int64: promoted to Double with a real value, NOT
    // silently left as a NULL (monostate) with an Integer type.
    check(rhs.type == DataType::Double,
          "overflowing integer literal promoted to Double");
    check(std::holds_alternative<double>(rhs.value.value),
          "literal value is a double, not NULL");
}

int main() {
    const InMemoryCatalog cat = make_catalog();

    test_predicate_greater_than(cat);
    test_arith_over_aggregate(cat);
    test_columnref_handbuilt_schema(cat);
    test_join_concatenated_index(cat);
    test_correlated_exists(cat);
    test_integer_literal_overflow_promotes_double(cat);

    std::printf("\n%d checks, %d failures\n", g_checks, g_failures);
    if (g_failures == 0) {
        std::printf("ALL TESTS PASSED\n");
        return 0;
    }
    std::printf("TESTS FAILED\n");
    return 1;
}
