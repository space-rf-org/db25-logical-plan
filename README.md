# DB25 Logical Plan

The next layer of the DB25 SQL stack: a **binder / logical planner** that lowers
a parsed and semantically-analyzed `SELECT` AST into a relational-algebra
**logical plan**.

```
  SQL text
     |  db25::parser::Parser            (external/parser)
     v
  AST  ------------------------------.
     |  db25::semantic::Analyzer      |  (external/analyzer)
     v                               |
  analyzed AST + projection/types <--'
     |  db25::plan::Binder            (this repo)
     v
  LogicalNode tree  (Scan/Filter/Project/Join/Aggregate/Sort/Limit/...)
```

It is a pure **consumer** of the layers below it: name resolution and type
inference are done by the analyzer, and the binder simply reads those results
(`Analyzer::projection_of` / `type_of` / `nullability_of`) plus the catalog and
assembles the operator pipeline. It does not modify the parser or analyzer,
which are vendored read-only.

## The layer

### Logical IR — `include/db25/plan/logical_plan.hpp`

* `LogicalOp` — `{ Scan, Filter, Project, Join, Aggregate, Sort, Limit, SetOp, Values }`.
* `LogicalNode` — an owning tree (`std::unique_ptr` children) where every node
  carries an **output schema**: a `std::vector<ColumnSchema>` and each
  `ColumnSchema` is `{ std::string name, db25::ast::DataType type, bool nullable,
  uint32_t table_id, uint32_t column_id }` — field-for-field the same shape as
  the analyzer's `ResolvedColumn`.
* Expression payloads (filter/join predicates, projected expressions, group
  keys, aggregates) are **borrowed** pointers into the parser-owned AST, so the
  `Parser` must outlive the plan (the analyzer already imposes the same rule).

### Binder — `src/binder.cpp` (`include/db25/plan/binder.hpp`)

Lowers a single `SELECT` block bottom-up:

```
Scan(s) -> [Join] -> [Filter (WHERE)] -> [Aggregate (GROUP BY)]
        -> Project (SELECT list) -> [Sort (ORDER BY)] -> [Limit]
```

**Lowered today**

* Single-table **Scan** (schema from the catalog, with `table_id` / `column_id`).
* **`WHERE` -> Filter** (borrows the predicate subtree; schema-preserving).
* **`SELECT` list -> Project**, whose output schema is the analyzer's resolved
  projection (`projection_of`) — names, types and nullability, including
  `SELECT *` expansion.
* **`LIMIT` / `OFFSET` -> Limit** (non-negative integer literals parsed to values).
* **`INNER JOIN` -> Join** with a concatenated output schema; outer-join
  nullability (`LEFT` / `RIGHT` / `FULL`) is applied to the null-supplying side.
* **`GROUP BY` -> Aggregate** carrying group keys + detected aggregate calls, with
  a per-item output schema read back from the analyzer.
* **`ORDER BY` -> Sort** (node inserted, schema-preserving).

**Not yet lowered (clearly-marked `TODO`s in the source)**

* Derived tables / subqueries and `VALUES` in `FROM`.
* Comma / cross joins of base tables and `JOIN ... USING`.
* Set operations (`UNION` / `INTERSECT` / `EXCEPT`) and DML.
* `SELECT` without `FROM` (constant projection).
* Sort keys and directions on the `Sort` node.

### Tests — `tests/test_binder.cpp`

A self-contained harness (no gtest, so no network fetch and a clean
`-fno-exceptions` build). It parses + analyzes + binds five queries and asserts
both the logical tree shape and the `Project` output schema (names + types +
nullability). Run via `ctest` or the `test_binder` binary.

## Submodule pattern

Dependencies are consumed as **git submodules under `external/`**, mirroring how
the parser consumes its tokenizer at `external/tokenizer`:

```
external/parser     -> github.com/space-rf-org/db25-sql-parser
external/analyzer   -> github.com/space-rf-org/DB25-Semantic-Analyzer
external/parser/external/tokenizer  (the parser's own sub-submodule)
```

Fresh clone:

```sh
git clone <this-repo> db25-logical-plan
cd db25-logical-plan
git submodule update --init --recursive   # brings in the tokenizer too
```

The parser is self-contained: `add_subdirectory(external/parser)` builds
`db25parser` and its tokenizer. The analyzer is a single translation unit
(`src/analyzer.cpp`); we deliberately **do not** invoke its `CMakeLists.txt`
(which uses `find_package(DB25Parser)` and would force a parser install).
Instead `analyzer.cpp` is compiled directly into `db25logicalplan` with the
in-tree parser / tokenizer include directories. See `CMakeLists.txt`.

## Build

Requires a C++23 compiler (developed with `g++-14`). The whole stack is built
`-fno-exceptions`.

```sh
git submodule update --init --recursive
cmake -S . -B build -DCMAKE_CXX_COMPILER=g++-14 -DCMAKE_BUILD_TYPE=Release
cmake --build build -j
ctest --test-dir build --output-on-failure
```

Expected: `db25logicalplan` static library + `test_binder` build green, and
`test_binder` reports `ALL TESTS PASSED`.
