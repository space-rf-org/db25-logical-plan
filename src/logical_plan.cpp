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
            out.append(" keys=");
            out.append(std::to_string(n->sort_keys.size()));
            for (const auto& k : n->sort_keys) {
                out.append(k.descending ? " DESC" : " ASC");
            }
            break;
        case LogicalOp::SetOp:
            out.append(" (");
            switch (n->set_op) {
                case ast::SetOp::Union:     out.append("UNION"); break;
                case ast::SetOp::UnionAll:  out.append("UNION ALL"); break;
                case ast::SetOp::Intersect: out.append("INTERSECT"); break;
                case ast::SetOp::Except:    out.append("EXCEPT"); break;
            }
            out.push_back(')');
            break;
        case LogicalOp::Values:
            out.append(" rows=");
            out.append(std::to_string(n->value_rows.size()));
            break;
        case LogicalOp::Window:
            out.append(" fns=");
            out.append(std::to_string(n->window_functions.size()));
            break;
        case LogicalOp::Insert:
        case LogicalOp::Update:
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

    // Attached subquery sub-plans are printed indented under a marker line so a
    // plan dump shows the represented (but not yet decorrelated) subqueries.
    for (const auto& sp : n->subplans) {
        for (int i = 0; i < depth + 1; ++i) {
            out.append("  ");
        }
        out.append("SubPlan (");
        switch (sp.kind) {
            case SubqueryKind::Scalar: out.append("scalar"); break;
            case SubqueryKind::In:     out.append("IN"); break;
            case SubqueryKind::Exists: out.append("EXISTS"); break;
        }
        out.append(sp.correlated ? ", correlated" : ", uncorrelated");
        out.append(")\n");
        dump_rec(sp.plan.get(), depth + 2, out);
    }
}

}  // namespace

std::string dump_plan(const LogicalNode* root) {
    std::string out;
    dump_rec(root, 0, out);
    return out;
}

}  // namespace db25::plan
