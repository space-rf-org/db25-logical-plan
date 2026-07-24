// DB25 Logical Plan - IR helper implementations (printing / naming).

#include "db25/plan/logical_plan.hpp"

#include "db25/plan/expr_ir.hpp"  // complete Expr for ~LogicalNode + dump_expr
#include "db25/ast/node_types.hpp"

#include <string>

namespace db25::plan {

// Defined here (not inline in the header) because LogicalNode owns an ExprPtr to
// the forward-declared Expr; the destructor is emitted in this TU, where
// expr_ir.hpp has made Expr complete.
LogicalNode::~LogicalNode() = default;

const char* logical_op_to_string(LogicalOp op) noexcept {
    switch (op) {
        case LogicalOp::Scan:      return "Scan";
        case LogicalOp::Filter:    return "Filter";
        case LogicalOp::Project:   return "Project";
        case LogicalOp::Join:      return "Join";
        case LogicalOp::SemiJoin:  return "SemiJoin";
        case LogicalOp::AntiJoin:  return "AntiJoin";
        case LogicalOp::Aggregate: return "Aggregate";
        case LogicalOp::Window:    return "Window";
        case LogicalOp::Distinct:  return "Distinct";
        case LogicalOp::Sort:      return "Sort";
        case LogicalOp::Limit:     return "Limit";
        case LogicalOp::SetOp:     return "SetOp";
        case LogicalOp::Values:    return "Values";
        case LogicalOp::Insert:    return "Insert";
        case LogicalOp::Update:    return "Update";
        case LogicalOp::Delete:    return "Delete";
        case LogicalOp::Returning: return "Returning";
    }
    return "?";
}

namespace {

// Collect the ExprKind::Subquery nodes reachable from an expression tree (its
// operands, and a window function's PARTITION BY / ORDER BY keys), without
// descending into a subquery's own inner plan - that plan is printed separately.
void collect_subqueries(const Expr* e, std::vector<const Expr*>& out) {
    if (e == nullptr) {
        return;
    }
    if (e->kind == ExprKind::Subquery) {
        out.push_back(e);
    }
    for (const auto& c : e->children) {
        collect_subqueries(c.get(), out);
    }
    if (e->kind == ExprKind::WindowFunction) {
        for (const auto& p : e->window.partition_by) {
            collect_subqueries(p.get(), out);
        }
        for (const auto& k : e->window.order_by) {
            collect_subqueries(k.expr.get(), out);
        }
    }
}

// Gather every subquery embedded in a node's owned expression payloads.
void node_subqueries(const LogicalNode* n, std::vector<const Expr*>& out) {
    collect_subqueries(n->predicate.get(), out);
    for (const auto& e : n->exprs) collect_subqueries(e.get(), out);
    for (const auto& e : n->group_keys) collect_subqueries(e.get(), out);
    for (const auto& e : n->aggregates) collect_subqueries(e.get(), out);
    for (const auto& e : n->window_functions) collect_subqueries(e.get(), out);
    for (const auto& k : n->sort_keys) collect_subqueries(k.expr.get(), out);
    for (const auto& row : n->value_rows) {
        for (const auto& e : row) collect_subqueries(e.get(), out);
    }
    for (const auto& a : n->assignments) collect_subqueries(a.value.get(), out);
}

void append_schema(std::string& out, const Schema& schema) {
    out.push_back('[');
    for (std::size_t i = 0; i < schema.size(); ++i) {
        if (i != 0) {
            out.append(", ");
        }
        const ColumnSchema& c = schema[i];
        out.append(c.name);
        out.push_back(':');
        out.append(ast::data_type_to_string(c.type));
        out.append(c.nullable ? "?" : "");
    }
    out.push_back(']');
}

void dump_rec(const LogicalNode* n, int depth, std::string& out) {
    if (n == nullptr) {
        return;
    }
    for (int i = 0; i < depth; ++i) {
        out.append("  ");
    }
    out.append(logical_op_to_string(n->op));

    switch (n->op) {
        case LogicalOp::Scan:
            out.push_back(' ');
            out.append(n->table_name);
            if (!n->alias.empty()) {
                out.append(" AS ");
                out.append(n->alias);
            }
            break;
        case LogicalOp::Filter:
            if (n->predicate) {
                out.push_back(' ');
                out.append(dump_expr(*n->predicate));
            }
            break;
        case LogicalOp::Project:
            out.append(" (");
            for (std::size_t i = 0; i < n->exprs.size(); ++i) {
                if (i != 0) {
                    out.append(", ");
                }
                out.append(n->exprs[i] ? dump_expr(*n->exprs[i]) : "?");
            }
            out.push_back(')');
            break;
        case LogicalOp::SemiJoin:
        case LogicalOp::AntiJoin:
            if (n->predicate) {
                out.append(" ON ");
                out.append(dump_expr(*n->predicate));
            }
            break;
        case LogicalOp::Join:
            out.append(" (");
            switch (n->join_type) {
                case ast::JoinType::Inner:   out.append("INNER"); break;
                case ast::JoinType::Left:    out.append("LEFT"); break;
                case ast::JoinType::Right:   out.append("RIGHT"); break;
                case ast::JoinType::Full:    out.append("FULL"); break;
                case ast::JoinType::Cross:   out.append("CROSS"); break;
                case ast::JoinType::Lateral: out.append("LATERAL"); break;
            }
            out.push_back(')');
            if (n->predicate) {
                out.append(" ON ");
                out.append(dump_expr(*n->predicate));
            }
            break;
        case LogicalOp::Limit:
            if (n->has_limit) {
                out.append(" limit=");
                out.append(std::to_string(n->limit));
            }
            if (n->has_offset) {
                out.append(" offset=");
                out.append(std::to_string(n->offset));
            }
            break;
        case LogicalOp::Sort:
            out.append(" keys=(");
            for (std::size_t i = 0; i < n->sort_keys.size(); ++i) {
                if (i != 0) {
                    out.append(", ");
                }
                const auto& k = n->sort_keys[i];
                out.append(k.expr ? dump_expr(*k.expr) : "?");
                out.append(k.descending ? " DESC" : " ASC");
            }
            out.push_back(')');
            break;
        case LogicalOp::SetOp:
            out.append(" (");
            switch (n->set_op) {
                case ast::SetOp::Union:        out.append("UNION"); break;
                case ast::SetOp::UnionAll:     out.append("UNION ALL"); break;
                case ast::SetOp::Intersect:    out.append("INTERSECT"); break;
                case ast::SetOp::IntersectAll: out.append("INTERSECT ALL"); break;
                case ast::SetOp::Except:       out.append("EXCEPT"); break;
                case ast::SetOp::ExceptAll:    out.append("EXCEPT ALL"); break;
            }
            out.push_back(')');
            break;
        case LogicalOp::Values:
            out.append(" rows=");
            out.append(std::to_string(n->value_rows.size()));
            for (const auto& row : n->value_rows) {
                out.append(" (");
                for (std::size_t i = 0; i < row.size(); ++i) {
                    if (i != 0) {
                        out.append(", ");
                    }
                    out.append(row[i] ? dump_expr(*row[i]) : "?");
                }
                out.push_back(')');
            }
            break;
        case LogicalOp::Aggregate: {
            out.append(" group=(");
            for (std::size_t i = 0; i < n->group_keys.size(); ++i) {
                if (i != 0) {
                    out.append(", ");
                }
                out.append(n->group_keys[i] ? dump_expr(*n->group_keys[i]) : "?");
            }
            out.append(") aggs=(");
            for (std::size_t i = 0; i < n->aggregates.size(); ++i) {
                if (i != 0) {
                    out.append(", ");
                }
                out.append(n->aggregates[i] ? dump_expr(*n->aggregates[i]) : "?");
            }
            out.push_back(')');
            break;
        }
        case LogicalOp::Window:
            out.append(" fns=(");
            for (std::size_t i = 0; i < n->window_functions.size(); ++i) {
                if (i != 0) {
                    out.append(", ");
                }
                out.append(n->window_functions[i] ? dump_expr(*n->window_functions[i]) : "?");
            }
            out.push_back(')');
            break;
        case LogicalOp::Update:
            out.push_back(' ');
            out.append(n->table_name);
            out.append(" set=(");
            for (std::size_t i = 0; i < n->assignments.size(); ++i) {
                if (i != 0) {
                    out.append(", ");
                }
                out.append("col#");
                out.append(std::to_string(n->assignments[i].target_column_id));
                out.append(" := ");
                out.append(n->assignments[i].value ? dump_expr(*n->assignments[i].value) : "?");
            }
            out.push_back(')');
            break;
        case LogicalOp::Insert:
        case LogicalOp::Delete:
        case LogicalOp::Returning:
            out.push_back(' ');
            out.append(n->table_name);
            break;
        default:
            break;
    }

    out.push_back(' ');
    append_schema(out, n->output);
    out.push_back('\n');

    for (const auto& c : n->children) {
        dump_rec(c.get(), depth + 1, out);
    }

    // Subqueries embedded in this node's owned expressions are printed indented
    // under a marker line so a plan dump shows the represented (but not yet
    // decorrelated) subqueries and their inner plans.
    std::vector<const Expr*> subqueries;
    node_subqueries(n, subqueries);
    for (const Expr* sq : subqueries) {
        for (int i = 0; i < depth + 1; ++i) {
            out.append("  ");
        }
        out.append("SubPlan (");
        switch (sq->subquery_kind) {
            case SubqueryKind::Scalar: out.append("scalar"); break;
            case SubqueryKind::In:     out.append("IN"); break;
            case SubqueryKind::Exists: out.append("EXISTS"); break;
        }
        out.append(sq->correlated ? ", correlated" : ", uncorrelated");
        out.append(")\n");
        dump_rec(sq->sub_plan.get(), depth + 2, out);
    }
}

}  // namespace

std::string dump_plan(const LogicalNode* root) {
    std::string out;
    dump_rec(root, 0, out);
    return out;
}

}  // namespace db25::plan
