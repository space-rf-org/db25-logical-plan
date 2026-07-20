// DB25 Logical Plan - IR helper implementations (printing / naming).

#include "db25/plan/logical_plan.hpp"

#include "db25/ast/node_types.hpp"

#include <string>

namespace db25::plan {

const char* logical_op_to_string(LogicalOp op) noexcept {
    switch (op) {
        case LogicalOp::Scan:      return "Scan";
        case LogicalOp::Filter:    return "Filter";
        case LogicalOp::Project:   return "Project";
        case LogicalOp::Join:      return "Join";
        case LogicalOp::Aggregate: return "Aggregate";
        case LogicalOp::Sort:      return "Sort";
        case LogicalOp::Limit:     return "Limit";
        case LogicalOp::SetOp:     return "SetOp";
        case LogicalOp::Values:    return "Values";
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
        default:
            break;
    }

    out.push_back(' ');
    append_schema(out, n->output);
    out.push_back('\n');

    for (const auto& c : n->children) {
        dump_rec(c.get(), depth + 1, out);
    }
}

}  // namespace

std::string dump_plan(const LogicalNode* root) {
    std::string out;
    dump_rec(root, 0, out);
    return out;
}

}  // namespace db25::plan
