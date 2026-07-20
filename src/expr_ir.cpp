// DB25 Logical Plan - Expression IR helpers (kind names + dump_expr)
//
// See include/db25/plan/expr_ir.hpp for the Expr model. This TU provides the
// non-inline vocabulary helpers: a kind->string map and a positional/typed
// renderer used by tests and debugging.

#include "db25/plan/expr_ir.hpp"

#include "db25/ast/node_types.hpp"

#include <string>
#include <variant>

namespace db25::plan {

const char* expr_kind_to_string(ExprKind kind) noexcept {
    switch (kind) {
        case ExprKind::ColumnRef:      return "ColumnRef";
        case ExprKind::Literal:        return "Literal";
        case ExprKind::BinaryOp:       return "BinaryOp";
        case ExprKind::UnaryOp:        return "UnaryOp";
        case ExprKind::ScalarFunction: return "ScalarFunction";
        case ExprKind::Aggregate:      return "Aggregate";
        case ExprKind::WindowFunction: return "WindowFunction";
        case ExprKind::Case:           return "Case";
        case ExprKind::Cast:           return "Cast";
        case ExprKind::Between:        return "Between";
        case ExprKind::Like:           return "Like";
        case ExprKind::IsNull:         return "IsNull";
        case ExprKind::InList:         return "InList";
        case ExprKind::Subquery:       return "Subquery";
        case ExprKind::Parameter:      return "Parameter";
        case ExprKind::OuterRef:       return "OuterRef";
    }
    return "?";
}

namespace {

std::string type_suffix(DataType t) {
    return std::string{":"} + ast::data_type_to_string(t);
}

std::string literal_text(const LiteralValue& v) {
    return std::visit(
        [](const auto& arg) -> std::string {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>) {
                return "NULL";
            } else if constexpr (std::is_same_v<T, std::int64_t>) {
                return std::to_string(arg);
            } else if constexpr (std::is_same_v<T, double>) {
                return std::to_string(arg);
            } else if constexpr (std::is_same_v<T, bool>) {
                return arg ? "TRUE" : "FALSE";
            } else {  // std::string
                return "'" + arg + "'";
            }
        },
        v.value);
}

void render(const Expr& e, std::string& out) {
    switch (e.kind) {
        case ExprKind::ColumnRef:
            out += "#" + std::to_string(e.input_index) + type_suffix(e.type);
            return;
        case ExprKind::OuterRef:
            out += "outer" + std::to_string(e.outer_depth) + "#" +
                   std::to_string(e.input_index) + type_suffix(e.type);
            return;
        case ExprKind::Literal:
            out += literal_text(e.value) + type_suffix(e.type);
            return;
        case ExprKind::Parameter:
            out += "$" + std::to_string(e.param_index) + type_suffix(e.type);
            return;
        case ExprKind::BinaryOp:
            out += "(";
            if (e.children.size() == 2) {
                render(*e.children[0], out);
                out += std::string{" "} + ast::binary_op_to_string(e.bin_op) + " ";
                render(*e.children[1], out);
            }
            out += ")" + type_suffix(e.type);
            return;
        case ExprKind::UnaryOp:
            out += std::string{"("} + ast::unary_op_to_string(e.un_op) + " ";
            if (!e.children.empty()) {
                render(*e.children[0], out);
            }
            out += ")" + type_suffix(e.type);
            return;
        case ExprKind::Cast:
            out += "CAST(";
            if (!e.children.empty()) {
                render(*e.children[0], out);
            }
            out += " AS " + std::string{ast::data_type_to_string(e.target_type)} + ")";
            return;
        case ExprKind::ScalarFunction:
        case ExprKind::Aggregate:
        case ExprKind::WindowFunction: {
            out += e.func_name + "(";
            if (e.distinct) {
                out += "DISTINCT ";
            }
            for (std::size_t i = 0; i < e.children.size(); ++i) {
                if (i != 0) {
                    out += ", ";
                }
                render(*e.children[i], out);
            }
            out += ")";
            if (e.kind == ExprKind::WindowFunction) {
                out += " OVER(...)";
            }
            out += type_suffix(e.type);
            return;
        }
        case ExprKind::Case: {
            out += "CASE(";
            for (std::size_t i = 0; i < e.children.size(); ++i) {
                if (i != 0) {
                    out += ", ";
                }
                render(*e.children[i], out);
            }
            out += ")" + type_suffix(e.type);
            return;
        }
        case ExprKind::Between: {
            out += "(";
            if (e.children.size() == 3) {
                render(*e.children[0], out);
                out += e.negated() ? " NOT BETWEEN " : " BETWEEN ";
                render(*e.children[1], out);
                out += " AND ";
                render(*e.children[2], out);
            }
            out += ")" + type_suffix(e.type);
            return;
        }
        case ExprKind::Like: {
            out += "(";
            if (e.children.size() >= 2) {
                render(*e.children[0], out);
                out += e.negated() ? " NOT LIKE " : " LIKE ";
                render(*e.children[1], out);
            }
            out += ")" + type_suffix(e.type);
            return;
        }
        case ExprKind::IsNull: {
            out += "(";
            if (!e.children.empty()) {
                render(*e.children[0], out);
            }
            out += e.negated() ? " IS NOT NULL)" : " IS NULL)";
            out += type_suffix(e.type);
            return;
        }
        case ExprKind::InList: {
            out += "(";
            if (!e.children.empty()) {
                render(*e.children[0], out);
            }
            out += e.negated() ? " NOT IN [" : " IN [";
            for (std::size_t i = 1; i < e.children.size(); ++i) {
                if (i != 1) {
                    out += ", ";
                }
                render(*e.children[i], out);
            }
            out += "])" + type_suffix(e.type);
            return;
        }
        case ExprKind::Subquery: {
            const char* k = e.subquery_kind == SubqueryKind::Scalar  ? "SCALAR"
                            : e.subquery_kind == SubqueryKind::In     ? "IN"
                                                                      : "EXISTS";
            out += std::string{"Subquery["} + k;
            if (e.correlated) {
                out += ",correlated";
            }
            out += "]" + type_suffix(e.type);
            return;
        }
    }
}

}  // namespace

std::string dump_expr(const Expr& e) {
    std::string out;
    render(e, out);
    return out;
}

}  // namespace db25::plan
