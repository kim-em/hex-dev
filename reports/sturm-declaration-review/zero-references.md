# Declaration references and API disposition

The compiled [inventory](declaration-use.json) contains 241 constants from the eleven
production modules assessed in the [manifest](manifest.json). All 126 handwritten
declarations match uniquely; 115 additional constants are generated equations,
matchers, recursors, projections or compiler declarations. Every handwritten private
helper has a compiled path to another handwritten declaration; the 22 paths are
retained in [helper-paths.json](helper-paths.json).

The imported environment includes the manual, the companion tests, accepted/rejected
replay, semantic replay and computational conformance. The audit records references
from compiled declaration types and bodies in that environment. It does not record
external clients, anonymous examples, linter registration tables or simp registration
as compiled users. An empty reference list therefore requires an API assessment; it
does not by itself justify deleting a public characterization.

The following 19 handwritten public lemmas have no recorded compiled users. Retain
these operations' useful interfaces for the reasons below. Each retains the semantic
hypotheses documented in the separate computational and companion assessments.

| Declaration | Disposition |
| --- | --- |
| `PreparedDomain.ofChecked_sign` | Retain the simp projection exposing the original sign operation after restoration without unfolding the private constructor. |
| `PreparedDomain.ofChecked_head` | Retain the simp projection exposing the original polynomial and literal input binding. |
| `PreparedDomain.ofChecked_lower` | Retain the simp projection exposing the original lower endpoint. |
| `PreparedDomain.ofChecked_upper` | Retain the simp projection exposing the original upper endpoint. |
| `PreparedDomain.ofChecked_squarefree` | Retain the simp projection exposing the retained producer chain. |
| `PreparedDomain.withEndpoints_isSome` | Retain the computational success criterion for retargeting, without assuming a lawful coefficient interpretation. |
| `prepare_ofChecked` | Retain equality of the restored complete object with actual preparation; field projections alone do not establish that equality. |
| `PreparedDomain.changeOps_data` | Retain the literal tuple preserved when transporting between propositionally equal arithmetic instances. |
| `HexSturmMathlib.withEndpoints_domain` | Retain semantic validity of the actual returned object at its new endpoints, complementing the core literal bindings theorem. |
| `HexSturmMathlib.query_rat_nonneg` | Retain query-one nonnegativity over rationals via the integer bridge without the general real-closed-field signed-index foundation. |
| `HexSturmMathlib.query_rat_rootSum` | Retain the explicit ordinary-real root-sum result at finite dyadic bounds for rational callers. |
| `HexSturmMathlib.rootCount_sturm` | Retain the agreement of successful natural counting with positive clearing and the integer half-open count. Success supplies the root-free endpoint requirement. |
| `HexSturmMathlib.countPrepared_nonneg` | Retain nonnegativity of the actual prepared integer count before conversion to a natural number. |
| `HexSturmMathlib.query_bound` | Retain the absolute-value bound by root cardinality and head degree, for clients bounding a general sign sum. |
| `HexSturmMathlib.query_sign` | Retain the direct selected-root sign theorem for singleton intervals; clients need not unfold root sums. |
| `HexSturmMathlib.rootCount_eq` | Retain exact cardinality of the actual successful natural result. |
| `HexSturmMathlib.rootCount_isSome` | Retain the natural frontend's full success-domain criterion over ordered fields without requiring real closedness. |
| `HexSturmMathlib.rootCount_query` | Retain the actual natural-result witness preserving a successful query-one integer answer. |
| `HexSturmMathlib.rootCount_map` | Retain equality of complete optional results after casting natural counts back to integers, including failed domains. |

Names in the first eight rows are relative to `Hex.Sturm`. The generated
zero-reference declarations are covered by their record/equation/compiler roles;
they are not additional handwritten API decisions. Every audited constant has axioms
contained in `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or new axiom
appears in the inventory. This is a reference and API assessment, not a claim of
complete Phase 6: computational regression acceptance remains separate.

## Reproduction and source scope

[Bindings](usage-bindings.json) identify the source revision, production modules,
audit imports, retained audit source and normalized outputs. The audit is a temporary
monorepo consumer, not a public library module: its import of the manual must not
become an ordinary companion dependency. With the pinned toolchain and lock file,
from the repository root:

```sh
cp reports/sturm-declaration-review/audit.lean.txt HexSturmMathlib/DeclarationAudit.lean
lake build +HexSturmMathlib.DeclarationAudit
python3 reports/sturm-declaration-review/normalize.py
rm HexSturmMathlib/DeclarationAudit.lean
```

The normalizer sorts rows, users and axioms and resolves every handwritten manifest
entry to its unique compiled name. It traces all private helpers through generated
users to another handwritten declaration. Its assertions must pass before comparing
output hashes. The compiled audit was run against the bound source revision; later
source changes require their own audit rather than silently reusing these hashes.
