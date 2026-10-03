# Real-coefficient adapter evidence

This record covers the implemented optional `HexRCF.RealCoefficients` surface.
It does not attest completion of the planned extension or extend the rational
solver's existing performance claims to real coefficients. The owning
[SPEC](../HexRCF/SPEC/hex-rcf.md#planned-real-coefficient-extension),
[current Phase-4 proof track](../PLAN/Phase4.md#evidence-tracks) and
[shared execution contract](../SPEC/real-closure-execution.md) retain their full
requirements.

## Surfaces and verification

The published `HexRCF` umbrella retains the rational path. The separate default
`HexRCFRealCoefficients` target builds the optional adapter from `adapters/`.
`HexConformance` includes its regression modules. Build-only examples under the
manifest's `bench/HexRCF/ProofProbe` root exercise actual proof generation;
the default `HexRCFProofProbe` target includes representative algebraic,
registered-constant and prepared finite replay examples. These modules import
Mathlib and are never executable benchmark roots.

| Implemented surface | Evidence and limits |
| --- | --- |
| Handler selection and proof assignment | [HandlerTests](../HexRCF/HandlerTests.lean): deterministic names, malformed declarations, declines, wrong-goal proofs, state restoration and terminal failures. The base tactic rejects nonstandard axioms and checks the complete original-target proof in the ordinary kernel. |
| Closed source conversion and selected embeddings | [CheckedConversions](../conformance/HexRCF/CheckedConversions.lean), [NormalizedCoefficients](../conformance/HexRCF/NormalizedCoefficients.lean), [RootAliasesConformance](../conformance/HexRCF/RootAliasesConformance.lean), [CertificationProofs](../conformance/HexRCF/CertificationProofs.lean): checked real/option/getD/QAdjoin conversion, positive/negative roots, square/cubic aliases and independently constructed fields. Common-field authentication covers the delivered witness languages, not all irreducible polynomials. |
| Original divisor preflight | [AlgebraicDivision](../conformance/HexRCF/AlgebraicDivision.lean), [CheckedConversions](../conformance/HexRCF/CheckedConversions.lean), [PreparedCoefficients](../conformance/HexRCF/PreparedCoefficients.lean): original denominators survive cancellation and discarded branches. The prepared finite path checks guards before zero, constant and empty-domain shortcuts. |
| Shared atom specialization | [FieldSpecializeConformance](../conformance/HexRCF/FieldSpecializeConformance.lean): `Specialize.prepare`/`FieldSpecialize.prepare` preserve every atom, including zero and domain guards. Evaluation and semantic degree are proved after coefficient cancellation. The carrier filters zero polynomials only after traversal. |
| Fixed-field finite construction and replay | [FiniteReplay](../conformance/HexRCF/FiniteReplay.lean): exact formula/quantifier/coefficient/divisor/context bindings, complete recorded sign operands, malformed evidence, diagnostic false and preflight-before-search. `Replay.check_domains`, `check_spec`, `check_sound`, `check_original` and `build_spec` use actual real interpretation laws. Bounded production can exhaust. `buildTotal_checked`/`buildTotal_spec` connect the existing complete exact-field producer to finite acceptance for nonzero original divisors, independently of direct proposal depth; false remains diagnostic. |
| Original-goal API proof generation | [PreparedCoefficients](../conformance/HexRCF/PreparedCoefficients.lean) and [Prepared probes](../bench/HexRCF/ProofProbe/Prepared): successful guarded and Ioc proofs use `Replay.check_sound`; proof inspection excludes producer calls. A fresh total-production probe sets direct proposal depth to zero and still quotes an accepted Ioc proof. Wrong transport, omitted guards, incorrect identities and false verdicts fail. Preparation/transport restore state on unsuccessful exits, including runtime exceptions. |
| Root and cell correctness | [FieldRootsConformance](../conformance/HexRCF/FieldRootsConformance.lean), [ProductionProgress](../conformance/HexRCF/ProductionProgress.lean), [AlgebraicProgress](../conformance/HexRCF/AlgebraicProgress.lean), [CarrierModes](../conformance/HexRCF/CarrierModes.lean): selected-field root correspondence, complete carrier roots, squarefree normalization, repeated/common roots and leading cancellation. Samples are ordinary real sections/sectors. General joint nested realization is not supplied by these tests. |
| Caller-registered finite bounds | [NamedConstants](../conformance/HexRCF/NamedConstants.lean), [RegisteredConstants](../conformance/HexRCF/RegisteredConstants.lean), [CoarseConstants](../conformance/HexRCF/CoarseConstants.lean): actual caller-supplied containment proves the specified π/e goals and inverse guard. Missing, stale, cyclic, swapped or nonseparating evidence is rejected/refused. This finite path does not construct a total named-constant field or prove joint independence. |
| Manual | [Existing rcf chapter](../HexManual/Chapters/HexRCF.lean): full Hex source constructions, aliases, common fields, root operations, caller registrations and the explicit prepared/build/check/soundness path. Examples remain actual Lake-built proofs. |

Fresh quoted examples assert their complete theorem axiom inventories. Only
`propext`, `Classical.choice` and `Quot.sound` are accepted. The source admission
scan and DAG/umbrella checks complement those assertions; neither replaces
kernel checking. Native previews and external arithmetic diagnostics are never
proof evidence.

## Cost evidence

The adapter's Mathlib-facing preparation, specialization, quotation and kernel
checking follow the proof track. CI builds representative actual examples;
ordinary theorem applications do not need timing sweeps or a compiled complexity
verdict. The existing Mathlib-free rational `DecisionCheck` executable remains a
separate compiled track. Its old timings are not real-coefficient evidence.
Reusable numerical primitive obligations remain with their existing owners.
No Mathlib-importing adapter module is imported by an executable benchmark.

Targeted retained experiments answer concrete implementation questions:

| Question | Record | Supported conclusion |
| --- | --- | --- |
| Repeated source construction and root proposal work | [Production](hexrcf-production-proofs.md), [production sharing](hexrcf-production-sharing.md) | Selected-field production and syntax sharing observations on the recorded inputs; no physical heap-sharing claim. |
| Quotient coordinate quotation | [Literal quotation](hexrcf-literal-proofs.md) | Two changed-source comparisons did not establish a gain; reduced-coordinate quotation remains off. |
| Full queries versus exact interval sign evidence | [Interval quotation](hexrcf-interval-proofs.md) | The fixed-goal comparison favors interval quotation. Its reconstructed-query control and historical provenance limitations are explicit. |
| Carrier normalization | [Carrier comparison](hexrcf-carrier-proofs.md) | The retained fixed-goal pairs favor monic carriers; the ordinary-kernel normalization laws retain the original product. Signed chains are not arbitrarily made monic. |
| One replay goal versus split conjuncts | [Replay comparison](hexrcf-replay-proofs.md) | The retained comparison did not establish a gain; combined replay stays off. |
| Degree, source atoms and coefficient width | [Input costs and attribution](hexrcf-scaling-proofs.md) | Independent two-point observations in a no-real-root regime, with serialized/expanded syntax and a representative phase profile. These are not asymptotic verdicts or precision/depth evidence. |

Each report states its measured source/import identities and host context,
retains completed samples and distinguishes changed-source studies. Scientific
comparisons use fixed trial-major schedules with adjacent alternating AB/BA
arms and an automatically leased CPU; recorded activity never filters a sample.
Whole fresh-module times include production, quotation, elaboration and kernel
checking. Exclusive profiling categories exclude their child categories;
small exclusive replay figures are not total kernel replay costs.

## Completion limits

The planned extension remains incomplete in these specific respects:

- General common-field irreducibility quotation exceeds the present quadratic
  norm, free-witness and modular degree-pattern certificate languages. The
  degree-eight quartic/√2 example in `CertificationInputs` cannot be repaired
  just by trying more good primes. A diagnostic group calculation is not a
  Lean irreducibility proof.
- Authenticated generator-interval refinement remains separate work. Exact
  interval signs currently use the bound defining their selected literal root,
  with checked rational Sturm evidence when the bound is inconclusive.
- General tower/context integration, complete ordered root/enlargement APIs
  and one ordinary real realization of every finite joint nested constraint
  require the actual owner interfaces. Ordered real-closure existence alone
  does not discharge the joint realization conclusion.
- Algebraic frontend completeness and total acceptance of every supported source
  are not proved by the exact-field total producer. It starts with an already
  authenticated fixed-field environment; frontend irreducibility quotation
  still has the concrete language gap above. Registered constants remain bounded
  certified search unless the stronger child progress/relative transcendence
  laws are supplied.
- The recorded input comparisons do not cover precision, nested depth or
  common/repeated-root cost scaling. New numerical primitive measurements must
  use Mathlib-free owner drivers on explicitly bound adapter-generated inputs;
  preparation costs must be reported separately. Existing correctness examples
  do not stand in for those additional scientific measurements.

These limits prevent closing #10358 or attesting the complete planned adapter.
They do not defer the implemented ordinary-point and fixed-field surfaces while
unrelated owner measurements are unfinished.
