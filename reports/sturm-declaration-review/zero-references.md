# Declaration references and API disposition

The compiled [inventory](declaration-use.json) records 241 constants that Lean's
module table attributes to the eleven audited production modules. All 126
handwritten source declarations match uniquely. The other 115 are compiler
artifacts; creation in an audited module does not make their underlying
operations Sturm-owned. The [generated-origin assessment](generated-origins.json)
separates known foreign bases, local bases and unresolved artifacts. These
artifacts remain in the axiom inventory, not the handwritten API assessment.

All 22 private source helpers have a compiled path to a public handwritten
interface, retained in [helper-paths.json](helper-paths.json).

The audit explicitly imports the manual, companion/replay tests, computational
conformance and the context-transport conformance/public-import consumers.
This is a selected imported environment, not every root-package module.
The compiler module of each user is recorded separately from its name.
Users are categorized as Sturm production, other Hex production,
tests/conformance/manual, or other imported modules. Production means a module
role, not an assertion that a call executes on a measured computational path.
The normalizer gives the rule: test, fixture, diagnostic, benchmark, proof-probe,
manual and consumer-example module names are evidence roles; other Hex module
roots are production. Raw names/module attribution remain in the snapshot.

There are 24 public interfaces without production users in this environment:
13 have no compiled users and 11 have only evidence users. The restoration
projections and `prepare_ofChecked` have named context-conformance clients;
they are not described as unused. Every interface below retains the hypotheses
assessed in the separate computational and companion reviews.

| Declaration | Recorded clients | Disposition |
| --- | --- | --- |
| `PreparedDomain.ofChecked_sign` | Tests/conformance only | Retain the simp projection exposing the original sign operation after restoration without unfolding the private constructor. |
| `PreparedDomain.ofChecked_head` | Tests/conformance only | Retain the simp projection exposing the original polynomial and literal input binding. |
| `PreparedDomain.ofChecked_lower` | Tests/conformance only | Retain the simp projection exposing the original lower endpoint. |
| `PreparedDomain.ofChecked_upper` | Tests/conformance only | Retain the simp projection exposing the original upper endpoint. |
| `PreparedDomain.ofChecked_squarefree` | Tests/conformance only | Retain the simp projection exposing the retained producer chain. |
| `PreparedDomain.withEndpoints_isSome` | None in the imported audit | Retain the computational success criterion for retargeting, without assuming a lawful coefficient interpretation. |
| `prepare_ofChecked` | Tests/conformance only | Retain equality of the restored complete object with actual preparation; field projections alone do not establish that equality. |
| `PreparedDomain.changeOps_data` | None in the imported audit | Retain the literal tuple preserved when transporting between propositionally equal arithmetic instances. |
| `HexSturmMathlib.withEndpoints_domain` | None in the imported audit | Retain semantic validity of the actual returned object at its new endpoints, complementing the core literal bindings theorem. |
| `HexSturmMathlib.countPrepared_nonneg` | None in the imported audit | Retain nonnegativity of the actual prepared integer count before conversion to a natural number. |
| `HexSturmMathlib.query_bound` | None in the imported audit | Retain the absolute-value bound by root cardinality and head degree, for clients bounding a general sign sum. |
| `HexSturmMathlib.query_sign` | None in the imported audit | Retain the direct selected-root sign theorem for singleton intervals; clients need not unfold root sums. |
| `HexSturmMathlib.rootCount_eq` | None in the imported audit | Retain exact cardinality of the actual successful natural result. |
| `HexSturmMathlib.rootCount_isSome` | None in the imported audit | Retain the natural frontend's full success-domain criterion over ordered fields without requiring real closedness. |
| `HexSturmMathlib.rootCount_query` | None in the imported audit | Retain the actual natural-result witness preserving a successful query-one integer answer. |
| `HexSturmMathlib.rootCount_map` | None in the imported audit | Retain equality of complete optional results after casting natural counts back to integers, including failed domains. |
| `HexSturmMathlib.queryReduced_eq` | Tests/conformance only | Retain semantic agreement of value-only remainder reduction with full queries, without unfolding private remainder code. |
| `HexSturmMathlib.queryReducedPrepared_eq` | Tests/conformance only | Retain the corresponding prepared-query agreement with its actual stored domain. |
| `HexSturmMathlib.query_congr` | Tests/conformance only | Retain query invariance under lawful interpretations with equivalent coefficient values and signs; the noncanonical test is its current compiled client. |
| `HexSturmMathlib.rootCount_sturm` | None in the imported audit | Retain the agreement of successful natural counting with positive clearing and the integer half-open count. Success supplies the root-free endpoint requirement. |
| `HexSturmMathlib.query_rat_rootSum` | None in the imported audit | Retain the explicit ordinary-real root-sum result at finite dyadic bounds for rational callers. |
| `HexSturmMathlib.query_rat_nonneg` | None in the imported audit | Retain query-one nonnegativity over rationals via the integer bridge without the general real-closed-field signed-index foundation. |
| `HexSturmMathlib.IntCast.certificate_checks` | Tests/conformance only | Retain acceptance of the actual integer-to-rational certificate translation, separate from semantic value transport. |
| `HexSturmMathlib.DenominatorClearing.certificate_checks` | Tests/conformance only | Retain acceptance after positive denominator clearing with explicit sign and arithmetic hypotheses. |

`Compare.lean` has no other production client in this audit. Its public
`query_congr` uses `check_congr` and `domain_congr` internally. Retain all three
as the lawful-interpretation invariance API, with the noncanonical query test
as the current application; internal theorem references do not disguise that
module's current consumer scope.

## Source occurrences and limitations

The [repository-wide source occurrences](source-occurrences.json) cross-check
all 24 names in tracked Lean sources. Matches include declarations, comments,
anonymous examples, axiom-print commands, unused simp arguments and names in
other namespaces. They are lexical candidates, not additional compiled-use
or production-liveness claims. The restoration/count/transport applications in
`ContextOperationsConformance` are also compiled and recorded above. Anonymous
applications and automation registration remain outside this reference model.
A public characterization can be useful without a current production caller.

Generated equations, projections, recursors and matchers support elaboration
and compilation. Base metadata resolves an existing ancestor of the compiler
name after Lean's private-name decoding; it is not an exhaustive reconstruction
of all generated code ownership. Unresolved origins remain explicit.
The inventory is a source-bound snapshot. Re-attestation is manual; CI does not
regenerate it or silently keep its hashes current after later source edits.

## Reproduction

The [audit source](audit.lean.txt) is a temporary monorepo consumer, not a public
library module. Its manual/conformance imports must not become companion
requirements. With the pinned toolchain and lock, from the repository root:

```sh
cp reports/sturm-declaration-review/audit.lean.txt HexSturmMathlib/DeclarationAudit.lean
lake build +HexSturmMathlib.DeclarationAudit
python3 reports/sturm-declaration-review/normalize.py
rm HexSturmMathlib/DeclarationAudit.lean
```

The normalizer sorts rows/users/axioms, resolves every handwritten manifest
entry, and traces private helpers through generated users to a public source
interface. Assertions must pass before comparing hashes. Input revisions and
generated artifact hashes are separate fields in the retained bindings.
