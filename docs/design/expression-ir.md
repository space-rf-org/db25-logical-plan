# Design: Owned, Typed Expression IR with Positional Column References

**Status: APPROVED — implementation in progress (incremental).** This document is the accepted design
for replacing the logical plan's borrowed-AST expression payloads with an owned, typed `Expr` IR whose
column leaves are **positional** (DuckDB `BoundReferenceExpression` / Calcite `RexInputRef` style).

**Decisions locked** (see §8 for the alternatives that were weighed):
`unique_ptr` per node; **tagged struct + `ExprKind`** representation; `Subquery` Expr **owns** its
sub-plan inline; correlated outer references are a **first-class `OuterRef{depth, input_index}` kind**;
parameters carry `Unknown`/`Any` + `param_index`; **flat `input_index`** slots; `switch(kind)` visitor
with checked `as_*()` accessors. Implementation follows the incremental migration in §6 (tests stay
green at every step).

Date: 2026-07-20. Companion to `ir-landscape.md` (the SOTA survey). Stack: C++23, `-fno-exceptions`,
`unique_ptr` owning trees.

---

## 1. Problem statement — the 4 current limitations

The relational/operator layer of `logical_plan.hpp` is sound (owning `unique_ptr` operator tree, an
explicit `output` `Schema` per node, `table_id`/`column_id` provenance). The **expression layer** is the
gap. Four concrete defects, each with source evidence:

1. **Expressions are borrowed raw pointers into the parser arena.** Every payload is a
   `const ast::ASTNode*` (or a vector of them) aliasing parser-owned memory; the plan owns no expression
   IR of its own:
   - `logical_plan.hpp:119` — `const ast::ASTNode* predicate = nullptr;` (Filter / Join ON)
   - `logical_plan.hpp:128` — `std::vector<const ast::ASTNode*> exprs;` (Project select list)
   - `logical_plan.hpp:131-132` — `group_keys`, `aggregates`
   - `logical_plan.hpp:139` — `window_functions`
   - `logical_plan.hpp:76` — `SortKey{ const ast::ASTNode* expr; ... }`
   - `logical_plan.hpp:153` — `std::vector<std::vector<const ast::ASTNode*>> value_rows;`
   - `logical_plan.hpp:171` — `assignments` (UPDATE SET)
   - `logical_plan.hpp:97` — `SubPlan{ const ast::ASTNode* expr; ... }`
   - Header contract, `logical_plan.hpp:14-17`: *"Expression payloads ... are borrowed pointers into the
     parser-owned AST. The Parser that produced the AST must therefore outlive the LogicalNode tree."*

   Consequence: no optimizer pass can **produce** a rewritten expression (constant fold, decorrelate,
   push down a synthesized predicate) — there is nowhere to put a node that does not already exist in the
   parse tree.

2. **Column references are name-based, not slot-resolved.** Expression leaves are AST `ColumnRef`
   nodes identified by text (`binder.cpp:229-231`, `split_column_ref(item->primary_text)`). Output
   `ColumnSchema` carries `table_id`/`column_id` (`logical_plan.hpp:64-65`), but **interior** expression
   column refs are never resolved to a child-output ordinal. There is no "input column #N of my child."
   Contrast Calcite `RexInputRef(index)` / DuckDB `ColumnBinding`→`BoundReferenceExpression(offset)`.
   Name-based refs also force every consumer to re-do join name-collision reasoning.

3. **Subexpressions are untyped at the plan level.** Types live only on each node's *output*
   `ColumnSchema`. An interior operand (the left side of a predicate, an aggregate argument) has no
   plan-level type; to get it you must round-trip to the analyzer keyed on the AST pointer
   (`binder.cpp:549-550`, `analyzer_.type_of(item)` / `nullability_of(item)`). A standalone optimizer
   holding only the plan cannot answer "what is the type of this predicate's left operand."

4. **Plan lifetime is welded to the parser arena.** The whole plan is valid only while Parser + Analyzer
   + Catalog outlive it (`logical_plan.hpp:14-17`, `binder.hpp:42-46`). It cannot be serialized, cached
   across statements, or shipped to another process, because its expressions are pointers into foreign
   arena memory. (Bonus 5th, noted in the survey: payload fields are union-by-convention on one struct —
   no variant safety. We address it below but it is not a primary driver.)

Every SOTA engine (Calcite, DataFusion, DuckDB, Substrait, Velox) fixes 1–4 the same way: an **owned,
typed expression node with positional column refs**. DuckDB is the closest template (C++, MIT,
`unique_ptr` trees identical to ours).

---

## 2. The `Expr` node model

### 2.1 Representation choice — recommendation and rationale

**Recommendation: a single tagged struct `Expr` — an `ExprKind` enum discriminant, a `DataType type` +
2-bit `nullability` carried on *every* node, and owned `unique_ptr<Expr>` operands** — with kind-specific
scalar payload grouped by kind (the same union-by-convention discipline `LogicalNode` already uses).

```cpp
enum class ExprKind : std::uint8_t {
    ColumnRef, Literal, BinaryOp, UnaryOp, ScalarFunction,
    Aggregate, WindowFunction, Case, Cast,
    Between, Like, IsNull, InList, Subquery, Parameter
};

struct Expr;
using ExprPtr = std::unique_ptr<Expr>;

struct Expr {
    ExprKind  kind;
    DataType  type       = DataType::Unknown;  // typed on EVERY node
    std::uint8_t nullability = 0;              // parser 2-bit: 0 unknown / 1 not-null / 2 nullable
    std::vector<ExprPtr> children;             // operands (kind fixes arity/meaning)

    // --- back-pointer for diagnostics only (see §5) ---
    const ast::ASTNode* source = nullptr;      // source-range / original text; never dereferenced for semantics

    // --- kind-specific payload (only the field(s) for `kind` are meaningful) ---
    // ColumnRef:
    std::uint32_t input_index = 0;             // flat ordinal into the operator's input schema (§3)
    std::uint32_t ref_table_id = 0, ref_column_id = 0;  // provenance echo (diagnostics / re-resolve)
    // Literal:
    LiteralValue value;                        // typed value (see below); type/nullability say the rest
    // BinaryOp / UnaryOp:
    ast::BinaryOp bin_op{};  ast::UnaryOp un_op{};   // reuse parser enums (node_types.hpp:194,236)
    // ScalarFunction / Aggregate / WindowFunction:
    std::string  func_name;                    // canonical (upper-cased) function name
    bool         distinct = false;             // Aggregate DISTINCT
    WindowSpecIR window;                        // WindowFunction only (owned; see below)
    // Cast:
    DataType     target_type = DataType::Unknown;  // == `type`, kept explicit for clarity
    // Like:      children = {input, pattern[, escape]}; negated in semantic_flags below
    // Between:   children = {value, low, high}
    // IsNull / InList / negation carried in:
    std::uint16_t expr_flags = 0;              // NOT-flavor bits (NOT LIKE, IS NOT NULL, NOT IN, NOT EXISTS)
    // Subquery:
    SubqueryKind subquery_kind = SubqueryKind::Scalar;  // Scalar / In / Exists (reuse existing enum)
    bool         correlated = false;
    LogicalNodePtr sub_plan;                   // OWNED bound inner plan (replaces SubPlan)
    // Parameter:
    std::uint32_t param_index = 0;             // 1-based $n / positional ?
};
```

`LiteralValue` is a small typed union of the SQL literal domains we admit today (integer/float via the
parser's `const_value`, string, boolean, null, interval text). A `std::variant<std::monostate,
std::int64_t, double, std::string, bool>` (+ an interval string) is the natural encoding and is
`-fno-exceptions`-clean; `type` already tells consumers which arm is live.

`WindowSpecIR` is an owned lowering of the AST `WindowSpec`: `std::vector<ExprPtr> partition_by;
std::vector<SortKeyIR> order_by; FrameIR frame;`. It becomes fully owned like everything else.

**Rationale for the tagged struct over the alternatives:**

| Option | Verdict | Why |
|---|---|---|
| **Tagged struct + enum** (recommended) | ✅ | Identical idiom to `LogicalNode` (reviewers already read that pattern); reuses our `unique_ptr` ownership with no new allocator; switch-based visitors, no vtables, no RTTI — clean under `-fno-exceptions`; one heap node per expr, swappable to an arena later behind the `ExprPtr` alias. Mirrors DuckDB `Expression` most literally. |
| **Class hierarchy** (`Expr` base + virtual) | ➖ | Also fine `-fno-exceptions`, and is literal DuckDB. But adds virtual dispatch + downcasts, is heavier to serialize, and is a *different* idiom than `LogicalNode`, splitting the codebase's style. |
| **`std::variant<ColumnRef,Literal,…>`** | ➖ | Best static safety (fixes limitation #5 outright, `std::visit` exhaustiveness). But recursive variants need boxing anyway (`ExprPtr` inside each arm), the forward-declaration dance is awkward, and per-arm structs fragment the "type + nullability on every node" invariant we want *uniform*. Worth offering to the human as the safety-max option (§8). |

The one cost of the tagged struct — payload access is by-convention, not type-enforced (limitation #5
survives at the expr level) — is mitigated with small checked accessors (`as_column()`, `as_binary()`)
that assert on `kind` in debug builds.

### 2.2 Kind catalogue — fields, type, nullability

Every node carries `type` (a `DataType`) and `nullability` (parser 2-bit); the table below is the
*additional* payload and how type/nullability are set at lowering.

| Kind | Children | Extra payload | `type` / `nullability` source |
|---|---|---|---|
| **ColumnRef** | — | `input_index` (flat slot, §3); `ref_table_id/ref_column_id` echo | copied from the referenced input `ColumnSchema` |
| **Literal** | — | `LiteralValue value` | literal's inferred type; `nullability = NullLiteral ? 2 : 1` |
| **BinaryOp** | {lhs, rhs} | `bin_op` | `type_of(node)`; `nullable = lhs.nullable OR rhs.nullable` (analyzer-reconciled) |
| **UnaryOp** | {operand} | `un_op` | `type_of(node)`; from operand (NOT is not-null over not-null) |
| **ScalarFunction** | args… | `func_name` | `type_of(node)`; function-dependent |
| **Aggregate** | args… | `func_name`, `distinct` | `type_of(call)`; typically nullable (COUNT not-null) |
| **WindowFunction** | args… | `func_name`, `window` (partition/order/frame, owned) | `type_of(call)` |
| **Case** | {when0,then0,…,[else]} | (WHEN/THEN paired in children; trailing ELSE optional) | `type_of(node)`; nullable if any branch or missing ELSE |
| **Cast** | {operand} | `target_type` (== `type`) | `target_type`; propagates operand nullability |
| **Between** | {value, low, high} | `expr_flags` NOT bit | Boolean; OR of operands |
| **Like** | {input, pattern[, escape]} | `expr_flags` NOT bit | Boolean; OR of operands |
| **IsNull** | {operand} | `expr_flags` IS-NOT bit | Boolean; **not-null** (predicate never yields NULL) |
| **InList** | {value, elem0, elem1, …} | `expr_flags` NOT bit | Boolean |
| **Subquery** | (correlated outer refs appear as ColumnRefs *inside* `sub_plan`) | `subquery_kind`, `correlated`, `sub_plan` (owned) | Scalar: inner projection's single column type; In/Exists: Boolean |
| **Parameter** | — | `param_index` | `type_of(node)` if analyzer bound it, else `Unknown`/`Any` (see §8) |

Ownership of child exprs: **strict `unique_ptr` down the tree**, exactly as `LogicalNode::children`.
A `Subquery` Expr additionally **owns** its `LogicalNodePtr sub_plan` (this subsumes today's `SubPlan`
struct — see §5). No `shared_ptr`; expression trees are not DAGs in this IR (CSE, if ever wanted, is a
later optimizer concern and would introduce its own sharing discipline).

---

## 3. Positional column binding

### 3.1 What a `ColumnRef` resolves to

A `ColumnRef` Expr carries a **flat `input_index`**: an ordinal into the *input schema of the operator
that owns the expression*. For a unary operator (Filter, Project, Aggregate, Sort, Window) the input
schema is `child(0)->output`. For a **binary Join**, the input schema is the **concatenation
`child(0)->output ++ child(1)->output`** — which is exactly the schema `make_join_node` already builds
(`binder.cpp:103-115`). This flat-ordinal-into-the-concatenated-input choice mirrors DuckDB's
`BoundReferenceExpression` indexing straight into the flattened `DataChunk`, and it dissolves join
name-collision handling: two `id` columns from two tables are simply slots *i* and *j*.

> Decision point (§8): flat ordinal vs. an explicit `(child_index, column_ordinal)` pair. Flat is
> simpler for execution and matches DuckDB; the pair is more self-describing for a two-input node. We
> recommend **flat**, with the documented convention "a binary operator's input schema is
> `child0.output ++ child1.output`."

### 3.2 The resolution algorithm (at bind/lower time)

Inputs available when lowering an operator's expressions:
- the **input schema** (`Schema`, a `vector<ColumnSchema>`), already computed for the child(ren), each
  entry carrying `{name, type, nullable, table_id, column_id}`;
- the analyzer's per-node annotation on each AST `ColumnRef`: `context.analysis.{table_id, column_id,
  nullability}` (`ast_node.hpp:84-92`), set during `resolve_column_ref`.

```
resolve_ref(ref_node, input_schema) -> input_index:
    (tid, cid) = (ref_node.context.analysis.table_id, ref_node.context.analysis.column_id)
    if tid != 0 and cid != 0:                       # a base-table / catalog column
        for i, col in input_schema:
            if col.table_id == tid and col.column_id == cid: return i
    # Fallback for COMPUTED child columns (agg outputs, projected exprs, set-op
    # results) whose (table_id,column_id) are synthetic/zero:
    return resolve_by_producer(ref_node, input_schema)   # see §3.3
```

`resolve_by_producer` matches against a side table the binder builds while constructing each operator's
`output`: a map from *the producing AST item* (or its output name) to the output ordinal. Base columns
resolve by id (the fast path); computed columns resolve by this producer map. Concretely: when the
binder emits an Aggregate whose output column *k* is `SUM(x)`, it records `producer[SUM(x)_astnode] = k`;
a HAVING/ORDER BY/outer-Project reference to that aggregate then resolves to slot *k*.

### 3.3 Per-operator specifics

- **Scan.** Produces base columns with real `(table_id, column_id)`. No expressions to lower; its output
  is the resolution target for the operator directly above it.
- **Filter.** Predicate lowered against `child(0)->output` (schema-preserving; output = input).
- **Join.** ON predicate lowered against `child0.output ++ child1.output`. A left-side ref → slot in
  `[0, |child0|)`; a right-side ref → `[|child0|, |child0|+|child1|)`. **USING** columns: the merged
  column keeps the left slot; the right duplicate is dropped from `output` (`binder.cpp:343-356`), so a
  later reference to the USING column resolves to the surviving left slot.
- **Project — renumber.** Each select-list expr is lowered against `child(0)->output`; the Project's
  *own* output is a fresh `[0..n)` numbering (the select-list order). Operators *above* the Project
  reference these fresh slots, not the child's — this is the renumbering boundary. A trivial
  `SELECT a` becomes `ColumnRef(input_index = slot_of(a in child))`; the Project output column 0 is that
  expr's value.
- **Aggregate — two schemas.** Group-key exprs and aggregate-argument exprs are lowered against
  `child(0)->output`. The Aggregate's **output** is `[group keys…, aggregate outputs…]` (the survey/
  binder already build output by walking the select list, `binder.cpp:544-553`). HAVING, ORDER BY, and
  the Project above resolve against **this** Aggregate output (group key *g* → slot *g*; aggregate → its
  slot). `SUM(x)+1` splits: the `SUM(x)` Aggregate node lives in `aggregates`/agg-output slot *k*; the
  `+1` lives in the Project as `BinaryOp{ ColumnRef(k), Literal(1) }`.
- **Window.** Output = input columns pass through + one appended column per window function
  (`binder.cpp:584-592`). Window-fn argument/partition/order exprs are lowered against `child(0)->output`;
  the Project above references the appended slots.
- **SetOp.** No own expressions. Output = reconciled projection (`binder.cpp:462-470`); its columns may
  carry synthetic/zero ids, so an operator above a SetOp resolves **positionally via the producer map**
  (output ordinal = branch column position), not by catalog id. Each branch is an independently lowered
  query block.
- **Values.** Each cell is a lowered `Expr` (usually `Literal`); no column refs in the FROM-less case.

---

## 4. The AST→Expr lowering pass

### 4.1 Where it lives

A new lowering routine in the binder (own TU `expr_lower.cpp`, declared privately on `Binder`):

```cpp
ExprPtr Binder::lower_expr(const ast::ASTNode* n, const Schema& input, std::string& error);
```

It is the single place that reads the analyzer and the AST and emits owned `Expr`. It is called once per
operator, over that operator's input schema, replacing the current "store the borrowed pointer" lines
(`binder.cpp:496, 539, 541, 585, 612, 643-648, 706-710, 765`). Every operator payload assignment
`x = astnode;` becomes `x_ir = lower_expr(astnode, input, error);`.

Per node it:
1. dispatches on `n->node_type` to an `ExprKind`;
2. sets `type = analyzer_.type_of(n)` and `nullability = analyzer_.nullability_of(n)` — **types are read
   once, here, and baked into the node** (kills limitation #3 and the round-trip);
3. for a `ColumnRef`, runs §3.2 `resolve_ref` to fill `input_index` (kills #2);
4. recurses into children with the *same* `input` schema (operands see the same input), except a
   `Subquery`, whose body is bound via `bind_query` into an owned `sub_plan` and whose correlation flag
   is `analyzer_.is_correlated(n)` (folding today's `attach_subqueries`/`SubPlan`, `binder.cpp:884-914`);
5. records `source = n` for diagnostics (§5);
6. on an unlowerable shape, sets `error` and returns null (the whole stack is `-fno-exceptions`; we
   propagate via the existing `std::string& error` convention).

The analyzer must be **alive during lowering** (it already must be — the binder consumes it), but is not
needed afterward: once `lower_expr` returns, the `Expr` is self-contained.

### 4.2 Worked examples

**(a) `WHERE o.total > 100`** — Filter over a Scan of `orders`, whose `output` has `total` at slot 3.

```
lower_expr(BinaryExpr ">", input=orders.output)
└─ BinaryOp{ bin_op=GreaterThan, type=Boolean, nullability=2,
     children:
       ├─ ColumnRef{ input_index=3, type=Decimal, nullability=2, ref=(orders,total) }
       └─ Literal{ value=100, type=Integer, nullability=1 } }
```
The Filter node stores this as `predicate_ir`; the AST pointer is gone from the plan.

**(b) `SELECT SUM(x) + 1 FROM t GROUP BY g`** — Aggregate (child = Scan `t`, `x`@slot0, `g`@slot1) with
output `[g@0, SUM(x)@1]`, then a Project.

```
Aggregate.group_keys   = [ ColumnRef{ input_index=1 (g), type=… } ]      # vs child output
Aggregate.aggregates   = [ Aggregate{ func="SUM", type=BigInt, nullability=2,
                                       children:[ ColumnRef{ input_index=0 (x) } ] } ]
# Aggregate output schema: slot0=g, slot1=SUM(x)

Project.exprs = [ BinaryOp{ bin_op=Add, type=BigInt,               # vs Aggregate output
                    children:[ ColumnRef{ input_index=1 (SUM(x) slot) },
                               Literal{ value=1, type=Integer } ] } ]
```
The `+1` is a genuinely *new* node with no AST counterpart — impossible in today's borrowed IR.

**(c) `WHERE EXISTS (SELECT 1 FROM lines l WHERE l.oid = o.id)`** — correlated EXISTS in a Filter over a
Scan of `orders` (`o.id`@slot2).

```
Filter.predicate_ir =
  Subquery{ subquery_kind=Exists, correlated=true, type=Boolean, nullability=1,
    sub_plan = <bound plan for `SELECT 1 FROM lines l WHERE l.oid = o.id`> }
```
Inside `sub_plan`, the inner Filter's predicate is `BinaryOp{Equal, ColumnRef(l.oid slot in lines),
OuterRef(o.id)}`. The outer reference `o.id` is a `ColumnRef` that resolves against an **enclosing**
input schema, not the subquery's own child — see §8 (correlated-ref representation) for the one open
question this raises.

---

## 5. Integration with `LogicalNode`

Each borrowed-AST payload field is replaced by an owned `Expr` (or a small owned struct):

| Current field (`logical_plan.hpp`) | Becomes |
|---|---|
| `const ast::ASTNode* predicate` (:119) | `ExprPtr predicate` |
| `std::vector<const ast::ASTNode*> exprs` (:128) | `std::vector<ExprPtr> exprs` |
| `group_keys`, `aggregates` (:131-132) | `std::vector<ExprPtr>` each (aggregates are `Aggregate`-kind Exprs) |
| `window_functions` (:139) | `std::vector<ExprPtr>` (`WindowFunction`-kind, owning `WindowSpecIR`) |
| `SortKey{ const ast::ASTNode* expr; … }` (:74-79) | `SortKeyIR{ ExprPtr expr; bool descending; … }` |
| `value_rows` (:153) | `std::vector<std::vector<ExprPtr>>` |
| `assignments` (:171) | `std::vector<Assignment>` where `Assignment{ std::uint32_t target_column_id; ExprPtr value; }` |
| `SubPlan{ expr; kind; correlated; plan }` (:96-101) + `subplans` (:145) | folded into the `Subquery` **Expr** kind, which owns `LogicalNodePtr sub_plan`. The separate `subplans` vector and `attach_subqueries` pass go away — subqueries live inline in the expression tree where they syntactically occur. |

After migration, **`LogicalNode` owns its entire expression forest and no longer references the parser
arena** — killing limitation #1 and #4. The plan can outlive the Parser/Analyzer, be cached across
statements, and (with a serializer over the closed `ExprKind`/`LogicalOp` sets + `LiteralValue`) be
serialized. `#include "db25/ast/ast_node.hpp"` stays only for the enum reuse (`BinaryOp`, `UnaryOp`,
`DataType`, `JoinType`, `SetOp`) and the optional diagnostic back-pointer.

**Keep the source back-pointer (recommended).** Retain `const ast::ASTNode* source` on `Expr` purely for
diagnostics / source-range reporting (`ast_node.hpp:235-242` `get_source_range`). It is **never
dereferenced for semantics** — types, nullability, and slots are all baked in — so it does not re-weld
lifetime: a cached/serialized plan simply carries a null `source`. This preserves good error messages
during binding/optimization while keeping the self-contained guarantee (the back-pointer is a
best-effort convenience, valid only while the parse tree is alive).

---

## 6. Migration path — incremental, tests stay green

Big-bang (delete all borrowed fields, add all Expr fields, rewrite the binder at once) risks the 324
tests going red in a large, hard-to-bisect step. **Recommended: incremental, one payload field at a
time**, with owned and borrowed fields coexisting behind a transition.

1. **Land the vocabulary (no behavior change).** Add `expr_ir.hpp` (`ExprKind`, `Expr`, `ExprPtr`,
   `LiteralValue`, `WindowSpecIR`, `SortKeyIR`, `Assignment`) and a stub `dump_expr`. Compiles, unused.
2. **Land `lower_expr` + the resolver** in `expr_lower.cpp`, with unit tests over hand-built schemas
   (predicate, arithmetic, aggregate arg, column-ref slotting, one subquery). No operator uses it yet.
3. **Migrate one field.** Add the owned field *beside* the borrowed one (e.g. `ExprPtr predicate_ir;`
   next to `predicate;`); populate it in the binder; leave `dump_plan` reading the borrowed field.
   Add a golden-file variant asserting the IR form. Repeat per field in dependency order:
   Filter/Join `predicate` → Project `exprs` → Aggregate `group_keys`/`aggregates` → Window → Sort →
   Values → Subquery (fold `SubPlan`) → DML `assignments`.
4. **Flip `dump_plan`** to print positional/typed IR once all fields have an IR twin. Update the golden
   files in one reviewable diff (names → slots is the visible change — see §7).
5. **Delete the borrowed fields** (`predicate`, `exprs`, `group_keys`, `aggregates`,
   `window_functions`, `value_rows`, `assignments`, `SubPlan`, `subplans`, `SortKey::expr`) and the
   now-dead `attach_subqueries`. `logical_plan.hpp` no longer needs to expose AST pointers.
6. **Sever the arena dependency** in docs/asserts: update the `logical_plan.hpp:9-17` design note; add a
   test that binds, destroys the Parser+Analyzer, then walks/serializes the plan.

Each of steps 3's sub-steps keeps all tests green (the borrowed field still backs `dump_plan` until
step 4). The risky visible change (golden files) is isolated to step 4.

---

## 7. Impact

- **Parser: none.** No AST changes; we only *read* it during lowering.
- **Analyzer: no code change**, but a clarified lifetime contract: it must be alive **during lowering**
  (already required), and is **no longer needed during execution/optimization** of a bound plan (a
  strict relaxation — today the plan needs it forever, `binder.cpp:549-550` round-trips). No new API
  surface: `lower_expr` uses the existing `type_of` / `nullability_of` / `is_correlated` /
  `projection_of` + `context.analysis` ids.
- **Tests (~324).** Two categories change:
  - *Plan-dump golden files*: expression rendering flips from AST text (`o.total > 100`) to typed
    positional IR (`(#3:Decimal > 100:Int)` or similar). Mechanical, one diff at migration step 4. The
    **operator-tree shape assertions are unaffected** (same nodes, same nesting, same `output` schemas).
  - *New expr-level unit tests*: `lower_expr` slot resolution, per-kind typing, join concatenated-index
    resolution, aggregate split, correlated subquery. Net add, not a rewrite.
  - Subquery tests move from asserting on `node->subplans[i]` to asserting on the inline `Subquery` Expr;
    a small, localized update.

---

## 8. Decisions (weighed; the chosen option is recorded in the status header above)

The options below were the decision points; the accepted choice for each is noted in **Decisions
locked** at the top. Retained here for the rationale/alternatives.

- **Ownership: `unique_ptr` per node vs. an expr arena.** Recommend `unique_ptr` (matches `LogicalNode`,
  zero new machinery, `ExprPtr` alias lets us swap to an arena later if expr allocation ever shows up in
  profiles). Arena buys locality + cheap bulk-free but complicates the "plan outlives everything /
  serialize" story. **Lean: `unique_ptr`.**
- **Node representation: tagged struct (recommended) vs. `std::variant` vs. class hierarchy.** Tagged
  struct is most consistent with the codebase; `std::variant` maximizes payload safety (fixes limitation
  #5) at the cost of recursive-boxing ergonomics. Pick the point on the safety/consistency axis.
- **ScalarSubquery ownership/linkage.** Recommend the `Subquery` Expr **owns** its `LogicalNodePtr
  sub_plan` inline (folding away `SubPlan`/`subplans`/`attach_subqueries`). Alternative: keep sub-plans
  in a side vector on `LogicalNode` and have the Expr hold an index — decoupled, but reintroduces a
  by-convention link. **Lean: own it inline.**
- **Correlated outer references.** An outer-column ref inside a subquery cannot be a plain `input_index`
  into the subquery's own child. Options: (a) a distinct `OuterRef{ depth, input_index }` ExprKind
  (Calcite `RexCorrelVariable` style, explicit and decorrelation-friendly); (b) keep it a `ColumnRef`
  resolved against the enclosing operator's input with a `correlation_depth` field. Recommend **(a)** —
  it makes correlation first-class for the future decorrelation pass. Needs a decision because it adds a
  kind.
- **Parameter typing.** Parameters (`?`/`$n`) are often untyped until execution bind. Carry `type =
  Unknown`/`Any` with `param_index`, and let a later "parameter binding" step refine it? Or require the
  analyzer to have inferred a type. **Lean: allow `Unknown`/`Any` + `param_index`.**
- **Flat `input_index` vs. `(child_index, column_ordinal)`.** Recommend **flat** (DuckDB-style, simplest
  for execution, join = concatenated input). Decide if the two-input self-description of the pair is
  worth the extra field.
- **Visitor / type-erasure.** Recommend a plain `switch (kind)` visitor (no vtable, `-fno-exceptions`-
  clean) plus checked `as_*()` accessors. Decide whether to also generate a CRTP/`std::visit`-style
  exhaustiveness-checked walker for optimizer passes.

---

## Executive summary

- **Model:** a single owned, typed `Expr` node — a tagged struct with an `ExprKind` discriminant, a
  `DataType type` + 2-bit `nullability` on **every** node, and owned `unique_ptr<Expr>` operands. Kinds:
  `ColumnRef, Literal, BinaryOp, UnaryOp, ScalarFunction, Aggregate, WindowFunction, Case, Cast, Between,
  Like, IsNull, InList, Subquery, Parameter`. It mirrors DuckDB's `Expression` (C++, MIT) in our own
  `LogicalNode` idiom, needs no new dependency, and is `-fno-exceptions`-clean.
- **Positional refs:** a `ColumnRef` carries a **flat `input_index`** into the operator's input schema
  (for a Join, the concatenated `child0.output ++ child1.output`). Resolution at bind time matches the
  analyzer's `(table_id, column_id)` against the already-computed child `Schema`, with a producer-map
  fallback for computed columns (agg outputs, projected exprs, set-op results). This fixes name-based
  refs and dissolves join name collisions.
- **Lowering:** one `Binder::lower_expr(ASTNode*, input_schema)` pass reads `type_of`/`nullability_of`/
  `context.analysis` **once** and bakes type, nullability, and slots into owned nodes; subqueries lower
  inline into an owned `sub_plan` on a `Subquery` Expr, retiring `SubPlan`/`attach_subqueries`.
- **Payoff:** `LogicalNode` becomes self-contained — no parser arena dependency — so plans can outlive
  parsing, be cached, and be serialized. A `const ASTNode* source` back-pointer is kept for diagnostics
  only (never dereferenced for semantics).
- **Migration:** incremental — land `Expr` + `lower_expr`, migrate one payload field at a time with
  owned/borrowed fields coexisting so all 324 tests stay green, flip `dump_plan` (golden-file diff:
  names → slots), then delete the borrowed fields. Parser unchanged; analyzer unchanged (only its
  lifetime contract relaxes — needed during lowering, not during execution).
- **Open decisions:** `unique_ptr` vs arena; tagged-struct vs `std::variant` vs hierarchy; Subquery owns
  its sub-plan inline vs. side-vector+index; a first-class `OuterRef` kind for correlation vs. a
  depth-tagged `ColumnRef`; parameter typing (`Unknown`/`Any` vs analyzer-required); flat ordinal vs.
  `(child,ordinal)`; switch-visitor vs. generated exhaustive walker.
```