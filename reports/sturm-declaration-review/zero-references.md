# Declaration references and API disposition

The compiled [inventory](declaration-use.json) records 241 constants attributed
by Lean to eleven production modules. All 126 manifest declarations match
uniquely. Eight source-written `PreparedDomain` fields have their own
[API dispositions](source-fields.json), beside the structure assessment.
The other 107 constants have [generated-origin metadata](generated-origins.json).
Creation in an audited module does not establish ownership of the underlying
operation. Existing raw private and decoded declaration ancestors distinguish
local and foreign bases; unresolved origins remain explicit in the data.

The audit imports the manual, companion/replay tests, computational conformance
and context-transport consumers. The complete imported module table is retained
in [audit-imports.json](audit-imports.json). This is a selected environment,
not every root-package module or external client. A user's actual source path
and role are recorded in [module-roles.json](module-roles.json): `conformance/`,
`bench/`, examples, manual, tests, fixtures, diagnostics and proof probes are
evidence; core and semantic-adapter library source is production. In particular,
SignDet's `NodeChecks`/`TreeChecks` are production and the context public-import
fixture is conformance. External dependency modules are separate.

## Downstream production references

[Reachability](downstream-use.json) starts at production declarations outside
the Sturm pair and follows references back through pair declarations. A
base declaration's own generated equation or congruence artifact is not a
client, even when Lean attributes its creation to a downstream module.
Handwritten methods are retained as genuine edges. Raw users and their base
metadata remain in the inventory. Source role does not establish runtime
execution or computational performance.

There are 61 public manifest declarations without a path to an outside
production client in this environment; 13 have no non-self-generated direct
clients. Each is retained for the separately assessed API purpose below.
Internal theorem references and evidence applications are reported without
turning them into downstream production clients. Anonymous applications,
automation registrations and external projects remain outside this graph.

| Declaration | Direct recorded clients after self-generated filtering | Disposition |
| --- | --- | --- |
| `Hex.RemainderStep.clearDenominators` | Pair declarations and/or evidence only | Retain. Translates a supplied identity's scales and quotient using all three entry factors. It performs no new chain production or polynomial division. |
| `Hex.SignedRemainderChain.clearDenominators` | Pair declarations and/or evidence only | Retain. Clears every stored polynomial, recomputes degrees and translates the supplied initial, step and terminal evidence. Initial scaling includes both head and query factors. |
| `Hex.Sturm.PreparedDomain.changeOps_data` | None | Retain. Exposes literal sign/head/endpoint/chain preservation despite dependent instance parameters. The verbose statement retains the actual source and target dictionaries. |
| `Hex.Sturm.PreparedDomain.ofChecked_data` | Pair declarations and/or evidence only | Retain. Exposes all five data fields together, independently of the constructor representation. |
| `Hex.Sturm.PreparedDomain.ofChecked_head` | Pair declarations and/or evidence only | Retain. A terminating simp projection retains the original polynomial, rather than an equivalent scaled head. |
| `Hex.Sturm.PreparedDomain.ofChecked_lower` | Pair declarations and/or evidence only | Retain. A terminating simp projection exposes the excluded lower endpoint. |
| `Hex.Sturm.PreparedDomain.ofChecked_sign` | Pair declarations and/or evidence only | Retain. A terminating simp projection retains the endpoint guard's exact sign function. |
| `Hex.Sturm.PreparedDomain.ofChecked_squarefree` | Pair declarations and/or evidence only | Retain. A terminating simp projection exposes the actual stored chain, not a newly computed witness. |
| `Hex.Sturm.PreparedDomain.ofChecked_upper` | Pair declarations and/or evidence only | Retain. A terminating simp projection exposes the excluded upper endpoint. |
| `Hex.Sturm.PreparedDomain.withEndpoints_bindings` | Pair declarations and/or evidence only | Retain. Successful retargeting preserves head, sign and chain and binds both new endpoints. This is a literal-data law, not just value equivalence. |
| `Hex.Sturm.PreparedDomain.withEndpoints_isSome` | None | Retain. Gives the exact Boolean success condition for the new endpoint guards; no semantic sign laws are silently introduced. |
| `Hex.Sturm.certifyCountPrepared_eq` | Pair declarations and/or evidence only | Retain. Proves full certificate agreement with prepared query one, including context and endpoint data. |
| `Hex.Sturm.certify_value` | Pair declarations and/or evidence only | Retain. Whole-Option agreement includes failures and successful values; changing the certificate context does not change query value. |
| `Hex.Sturm.prepare_ofChecked` | Pair declarations and/or evidence only | Retain. Supplied exact producer evidence identifies restoration with preparation. The constructor body does not execute preparation to rebuild the stored chain. |
| `Hex.Sturm.queryReduced` | Pair declarations and/or evidence only | Retain. Checks the domain before reduction, retaining domain refusal and avoiding reduction on rejected inputs. |
| `Hex.Sturm.queryReducedPrepared` | Pair declarations and/or evidence only | Retain. Uses the remainder-only worker before the existing prepared query. Semantic preservation needs lawful division; an unreduced certificate remains a different literal contract. |
| `Hex.Sturm.queryReducedPrepared_eq` | Pair declarations and/or evidence only | Retain. Characterizes the actual worker through the ordinary remainder API, exposing no quotient computation to callers. |
| `Hex.Sturm.queryReduced_eq_query` | Pair declarations and/or evidence only | Retain. Whole-Option agreement with querying the remainder handles both failed preparation and its exact successful bindings. Agreement with the *original* query is a separate semantic theorem. |
| `Hex.Sturm.query_prepared` | Pair declarations and/or evidence only | Retain. Every retained prepared object supplies successful querying on its own bound inputs. Its stored endpoint and producer proofs exclude the ordinary domain failure. |
| `Hex.Sturm.rootCount` | Pair declarations and/or evidence only | Retain. Maps query one through `Int.toNat`; preservation of lawful answers depends on the companion's nonnegativity and map laws. Arbitrary sign/operation dictionaries do not make negative values valid counts. |
| `Hex.TarskiCertificate.clearDenominators` | Pair declarations and/or evidence only | Retain. Retains the context while renewing integer head/query data and finite dyadic endpoints/signs. The companion law requires accepted original bindings for the supplied interval. |
| `Hex.TarskiCertificate.toRat` | Pair declarations and/or evidence only | Retain. Maps integer evidence and dyadic endpoints, preserving stored context/sign/value data. Acceptance follows from the companion's exact sign and arithmetic correspondence. |
| `HexSturmMathlib.DenominatorClearing.certificate_checks` | Pair declarations and/or evidence only | Retain. Full accepted rational replay translates to full accepted integer replay with the exact original context/value. It combines translated guards, both supplied chains, the squarefree terminal test and renewed sign arrays. |
| `HexSturmMathlib.DenominatorClearing.chain_checks` | Pair declarations and/or evidence only | Retain. Preserves complete supplied-chain acceptance, including singleton chains, zero initial remainders and nonconstant terminal entries. A separate constant-terminal guard is still needed for squarefreeness. |
| `HexSturmMathlib.DenominatorClearing.signs_eq` | Pair declarations and/or evidence only | Retain. Every translated chain has identical finite endpoint sign arrays under positive entry clearing, independently of producer provenance. |
| `HexSturmMathlib.DenominatorClearing.step_pos` | Pair declarations and/or evidence only | Retain. Positive input clearing factors and positive source step scales give positive integer step scales. This is separate from the unconditional scaling identities. |
| `HexSturmMathlib.DenominatorClearing.step_spec` | Pair declarations and/or evidence only | Retain. Gives all three common-multiplier identities without positivity assumptions on the supplied natural factors; zero factors are allowed. |
| `HexSturmMathlib.IntCast.certificate_checks` | Pair declarations and/or evidence only | Retain. Any accepted integer certificate embeds to accepted rational replay with the same context/value and mapped finite or infinite endpoints. It uses no producer hypothesis. |
| `HexSturmMathlib.certifyCountPrepared_checks` | Pair declarations and/or evidence only | Retain. Query-one chain reuse still passes the complete checker at current endpoints and context. It reuses the full prepared-certificate law. |
| `HexSturmMathlib.check_congr` | Pair declarations and/or evidence only | Retain. Two arbitrary accepted certificates give equal values with positively scaled interpreted head/query inputs and matching interpreted endpoints. Context types and chain normalizations may differ. Each certificate still has its own literal bindings. |
| `HexSturmMathlib.check_rat_value` | Pair declarations and/or evidence only | Retain. Arbitrary accepted rational and integer certificates give the same value. Their literal witnesses need not agree and neither is assumed to be produced. |
| `HexSturmMathlib.countPrepared_nonneg` | None | Retain. Establishes nonnegativity of the actual integer answer before natural conversion. |
| `HexSturmMathlib.countPrepared_sound` | Pair declarations and/or evidence only | Retain. Converts prepared query one to the cardinality of distinct roots in the current open interval. It does not count multiplicities. |
| `HexSturmMathlib.domain_congr` | Pair declarations and/or evidence only | Retain. Head scaling only needs a nonzero factor: squarefreeness, roots and endpoint nonvanishing are unchanged even by negative scaling. This weaker premise is appropriate for domain alone. |
| `HexSturmMathlib.orderSign_eq` | Pair declarations and/or evidence only | Retain. Identifies the canonical executable sign with the mathematical sign using only ordered comparison and zero. |
| `HexSturmMathlib.prepared_domain` | Pair declarations and/or evidence only | Retain. Any prepared object has the mathematical domain under a lawful interpretation of its bound sign function. The exact sign-function equality is essential. |
| `HexSturmMathlib.queryReducedPrepared_eq` | Pair declarations and/or evidence only | Retain. The same value agreement applies to the actual prepared object and matching sign interpretation. Its own axiom guard checks the theorem's ordinary-kernel boundary. |
| `HexSturmMathlib.queryReduced_eq` | Pair declarations and/or evidence only | Retain. Whole-Option equality with the original query uses lawful storage division, interpretation of the remainder and equality of query values at head roots. It includes identical domain refusal. |
| `HexSturmMathlib.query_bound` | None | Retain. Bounds absolute query value by root cardinality and then head degree; it uses zero-reflecting polynomial degree correspondence. |
| `HexSturmMathlib.query_congr` | Pair declarations and/or evidence only | Retain. Combines domain equivalence with accepted-producer certificate comparison. Both failure and success cases are covered; positive query scaling is stronger than mere domain invariance. |
| `HexSturmMathlib.query_count` | Pair declarations and/or evidence only | Retain. Query one is the distinct-root cardinality by unit preservation and the shared root-sum-one theorem. |
| `HexSturmMathlib.query_iff` | Pair declarations and/or evidence only | Retain. Gives both directions: a lawful domain and its root-sum value force the producer to return that value. This includes general production, not just accepted-output soundness. |
| `HexSturmMathlib.query_nonneg` | Pair declarations and/or evidence only | Retain. Justifies the signed-to-natural conversion from the actual produced answer. |
| `HexSturmMathlib.query_rat_count` | Pair declarations and/or evidence only | Retain. Transfers rational query one through positive clearing to the existing real-root count. Clearing unit and nonzero head scaling preserve the root multiset used by the integer result. |
| `HexSturmMathlib.query_rat_domain` | Pair declarations and/or evidence only | Retain. Rational and integer producers have the same success domain after positive clearing; this theorem alone says nothing about successful-value equality. Query clearing is unconstrained by domain validity. |
| `HexSturmMathlib.query_rat_eq` | Pair declarations and/or evidence only | Retain. Whole-Option agreement combines domain correspondence with actual producer acceptance and arbitrary-certificate value comparison, including common factors and zero initial remainders. |
| `HexSturmMathlib.query_rat_nonneg` | None | Retain. Supplies natural-conversion evidence through the specialized real count, without needing the abstract real-closed-field query foundation in its proof. |
| `HexSturmMathlib.query_rat_rootSum` | None | Retain. Connects query-one cardinality to the shared open distinct-root sum at the same dyadic endpoints. It does not generalize to arbitrary weighted queries by this theorem alone. |
| `HexSturmMathlib.query_sign` | None | Retain. On an explicitly singleton semantic root set, the signed sum equals the query's sign at that same root. It does not independently select another root. |
| `HexSturmMathlib.query_sound` | Pair declarations and/or evidence only | Retain. Extracts the actual certificate from successful query production and applies its acceptance/soundness laws. This value-only projection remains useful beside `query_spec`. |
| `HexSturmMathlib.query_spec` | Pair declarations and/or evidence only | Retain. Adds the successful producer's domain to its value contract, retaining the same original head, query and endpoints. |
| `HexSturmMathlib.rootCount_eq` | None | Retain. Natural count equals the semantic cardinality by recovering query one and proving the conversion exact. |
| `HexSturmMathlib.rootCount_isSome` | None | Retain. Characterizes natural-count success on the same domain as query one; this domain-only contract needs no real-closed target. |
| `HexSturmMathlib.rootCount_map` | None | Retain. Whole-Option agreement includes failures and lawful successful values, so conversion does not silently replace a valid signed answer. |
| `HexSturmMathlib.rootCount_query` | None | Retain. Retains both actual natural-count production and exact casting back to the successful integer answer. |
| `HexSturmMathlib.rootCount_sturm` | None | Retain. Successful counting supplies squarefreeness and root-free endpoints; the open count agrees with the legacy half-open count there. The proof handles nonconstant and nonzero constant heads separately, and imposes no positive-degree premise on callers. |
| `HexSturmMathlib.signs_eq` | Pair declarations and/or evidence only | Retain. Equal-size positively corresponding chain entries give identical sign arrays at corresponding finite or infinite endpoints. Strict positive factors prevent a sign flip; bounds/negative/zero laws bind each sign operation. |
| `HexSturmMathlib.signs_rat_eq` | Pair declarations and/or evidence only | Retain. Positive chain-entry correspondence preserves finite dyadic endpoint sign arrays, using exact rational/dyadic evaluation laws. |
| `HexSturmMathlib.toPolyℝ_clearDenominators` | Pair declarations and/or evidence only | Retain. The cleared integer polynomial is the original rational interpretation times its positive clearing factor. Coefficient correspondence supplies the identity. |
| `HexSturmMathlib.withEndpoints_domain` | None | Retain. Validates the returned object's head at the requested new endpoints; core bindings separately retain its sign and chain. |
| `HexSturmMathlib.withEndpoints_isSome` | Pair declarations and/or evidence only | Retain. Characterizes retargeting on the new interval, using fresh preparation agreement rather than old endpoint evidence. |

The complete reduced-query, transport, interpretation-comparison, integer-cast
and denominator-clearing interfaces have no outside production-reference path
in this audit. Their coherent module purposes are remainder-only queries,
certificate translation and lawful semantic comparison. Existing conformance
and ordinary-kernel checks cover these APIs; no alternate production consumer
is invented solely to change a reference count. Public characterizing lemmas
can be useful without a current internal production caller.

All 22 private source helpers have a compiled path to a public manifest
interface, retained in [helper-paths.json](helper-paths.json). The record also
states whether that terminal has a downstream production path. Reaching a
public declaration alone does not demonstrate downstream use or eliminate
the need for its individual API disposition.

## Source occurrences and source bindings

The [repository-wide lexical cross-check](source-occurrences.json) covers every
listed public declaration without a downstream production-reference path.
Matches include declarations, comments, anonymous examples, axiom-print commands,
unused simp arguments and coincident names in other namespaces. These are
candidates for source inspection, not additional compiled-use claims. File
hashes use raw bytes, consistently with the input bindings.

The [bindings](usage-bindings.json) cover all root-package sources in the actual
compiled imported-module table, including manual chapters, tests and downstream
clients, plus matched lexical sources and the lint/control/config/audit tools.
External dependency sources are governed by the lock/toolchain rather than
individually snapshotted. Input revisions and artifact hashes are separate:
reports need not already exist at their input checkpoint. The checker verifies
both current input scope/bytes and committed source bytes, and all artifact
hashes. Re-attestation is manual; CI does not regenerate this report or promise
that later source edits leave its hashes unchanged. Compiler-generated names
can change after harmless elaboration changes, so the raw snapshot is retained.

## Reproduction

The [audit source](audit.lean.txt) is a temporary monorepo consumer, not a public
library module. Its imports must not become companion requirements. Use the
review commit whose source inputs match the recorded checkpoint, with its pinned
toolchain and lock. Remove the temporary
module's cached olean before building: otherwise Lake can replay the build
without recreating the JSON files written during elaboration.

```sh
cp reports/sturm-declaration-review/audit.lean.txt HexSturmMathlib/DeclarationAudit.lean
rm -f .lake/build/lib/lean/HexSturmMathlib/DeclarationAudit.olean
lake build +HexSturmMathlib.DeclarationAudit
python3 reports/sturm-declaration-review/normalize.py
rm HexSturmMathlib/DeclarationAudit.lean
python3 reports/sturm-declaration-review/check_bindings.py
```

The normalizer sorts the inventory, resolves every handwritten entry, removes
self-generated client edges, computes downstream reachability and records source
roles and private-helper paths. Assertions must pass before checking bindings.
All recorded ordinary-kernel axiom sets are subsets of the three standard logical
axioms. These checks establish neither Phase-6 computational regression nor
Phase-7 or publication eligibility.
