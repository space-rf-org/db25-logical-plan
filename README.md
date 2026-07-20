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

* `LogicalOp` — `{ Scan, Filter, Project, Join, Aggregate, Window, Sort, Limit,
  SetOp, Values, Insert, Update, Delete, Returning }`.
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
* **`SELECT` without `FROM`** (e.g. `SELECT 1 + 2`, `SELECT now()`) -> a Project
  over a synthetic single-row / zero-column **Values** input.
* **`LIMIT` / `OFFSET` -> Limit** (non-negative integer literals parsed to values).
* **`INNER` / `LEFT` / `RIGHT` / `FULL JOIN` -> Join** with a concatenated output
  schema; outer-join nullability is applied to the null-supplying side.
* **Comma / `CROSS JOIN` -> Join** (`Cross`, no predicate).
* **`JOIN ... USING (cols)` -> Join** with the named columns **merged** to a
  single output column (the right-side duplicates are dropped).
* **Derived tables / subqueries in `FROM`** -> the inner query block is bound and
  used as the Scan-equivalent input; its output schema is the derived
  projection, labeled with the correlation alias.
* **`GROUP BY` -> Aggregate** carrying group keys + detected aggregate calls, with
  a per-item output schema read back from the analyzer.
* **`ORDER BY` -> Sort** carrying real sort keys with `ASC` / `DESC` direction and
  `NULLS FIRST` / `LAST` placement (schema-preserving).
* **Set operations** `UNION` / `UNION ALL` / `INTERSECT` / `EXCEPT` -> a **SetOp**
  node with the two child plans and the analyzer's reconciled output schema
  (`projection_of`), preserving the parser's left-associative folding.
* **DML** — `INSERT` / `UPDATE` / `DELETE` -> **Insert** / **Update** / **Delete**
  nodes carrying the target table and the relevant child plan: a `Values` node
  or bound query source for `INSERT`, and a `Scan` (wrapped in a `Filter` when a
  `WHERE` clause is present) for `UPDATE` / `DELETE`. `UPDATE` also carries its
  borrowed `SET` assignment nodes.
* **`RETURNING` -> Returning** on top of the DML node, with an output schema
  resolved against the target table's catalog columns (`RETURNING *` expands to
  every column; a bare column reference carries its type / nullability / ids).
  Represented for `UPDATE` / `DELETE`; **`INSERT ... RETURNING`** is wired the
  same way but the vendored parser currently drops the clause for `INSERT` (no
  `ReturningClause` node), so it does not yet appear — a parser-side `TODO`.
* **Window functions -> Window** (below the `Project`): a `Window` node carries
  the borrowed window-call nodes (each a `FunctionCall` with a `WindowSpec` child
  holding the `PARTITION BY` / `ORDER BY` / frame refs) and appends one output
  column per function (type / nullability from the analyzer). The `Project`
  above references those outputs. Covers `RANK` / `ROW_NUMBER` / `SUM(..) OVER
  (...)` and friends.
* **Subqueries in expressions** (scalar / `IN` / `EXISTS`) -> represented as
  **`SubPlan`s** attached to the owning node (a `Project` for a scalar subquery
  in the `SELECT` list, a `Filter` for `IN` / `EXISTS` in `WHERE`). Each `SubPlan`
  carries the bound inner query plan, the subquery kind, and its correlation flag
  from `Analyzer::is_correlated`. Correlated subqueries are faithfully
  represented but **not** decorrelated (left to a later optimizer pass).

**Not yet lowered (clearly-marked `TODO`s in the source)**

* `INSERT ... RETURNING` (parser drops the clause), `ON CONFLICT`, and
  multi-table `UPDATE` / `DELETE`.
* `LATERAL` joins (the vendored parser/analyzer do not support them end-to-end:
  the analyzer reports the correlated relation alias as unresolved and
  `CROSS JOIN LATERAL` fails to parse), `GROUPING SETS` / `CUBE` / `ROLLUP`, and
  correlated-subquery **decorrelation**.

### Tests — `tests/test_binder.cpp`

A self-contained harness (no gtest, so no network fetch and a clean
`-fno-exceptions` build). It parses + analyzes + binds a spread of queries —
scan/filter/project/limit, joins (inner, comma/cross, `USING`), `GROUP BY`,
`ORDER BY`, `SELECT` without `FROM`, derived tables, set operations,
`INSERT` / `UPDATE` / `DELETE`, `UPDATE` / `DELETE ... RETURNING`, window
functions, and scalar / `IN` / `EXISTS` subqueries — and asserts both the
logical tree shape and the output schema (names + types + nullability), plus
subquery kind and correlation. Run via `ctest` or the `test_binder` binary.

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
