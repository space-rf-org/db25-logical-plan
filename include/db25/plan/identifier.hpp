// DB25 Logical Plan - Identifier case handling for name-based slot resolution
//
// The binder resolves BASE columns by (table_id, column_id) identity, so their
// case never matters here. But COMPUTED columns (aggregate / expression outputs
// carrying synthetic zero ids) and USING/NATURAL merge columns resolve BY NAME
// against a schema. To match the analyzer - which resolves every SQL identifier
// case-insensitively over ASCII (see the analyzer's identifier.hpp and its
// DESIGN.md "Identifier case" section) - those by-name lookups fold case too.
// Otherwise `SELECT MAX(x) AS Hi ... ORDER BY hi` would resolve in the analyzer
// but fail to bind here, a silent cross-layer divergence.
//
// Kept as a small local helper (rather than reusing the analyzer header) so the
// binder need not pin a newer analyzer submodule just for one ASCII comparison.
// Folding is ASCII only, exactly as upstream.

#pragma once

#include <cstddef>
#include <string_view>

namespace db25::plan {

// ASCII lower-case one byte; bytes outside 'A'..'Z' pass through unchanged.
[[nodiscard]] constexpr char ascii_lower(char c) noexcept {
    return (c >= 'A' && c <= 'Z') ? static_cast<char>(c + ('a' - 'A')) : c;
}

// Case-insensitive (ASCII) equality of two identifiers.
[[nodiscard]] constexpr bool iequals(std::string_view a, std::string_view b) noexcept {
    if (a.size() != b.size()) {
        return false;
    }
    for (std::size_t i = 0; i < a.size(); ++i) {
        if (ascii_lower(a[i]) != ascii_lower(b[i])) {
            return false;
        }
    }
    return true;
}

}  // namespace db25::plan
