# Real-coefficient adapter evidence

> The drivers under `scripts/bench/hexrcf_*.py` and the probe modules under
> `bench/HexRCF/ProofProbe/` that this report cites, other than `Examples` and
> `Registered/`, were removed from `main` after commit `45a4e4e9a4`. Check out
> that commit to rerun them.

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
| Native representation specialization and ordinary samples | [TowerSamples](../conformance/HexRCF/TowerSamples.lean) applies `RepresentationSpecialize.prepare` to the shared formula over an actual selected native coefficient field. It groups terms by their bound-variable exponent after evaluating coefficient coordinates directly. Evaluation requires preservation of the native arithmetic and zero reflection; degree requires zero reflection alone. No ring/field instance on stored expressions is asserted. Positive and negative selected √2 controls send repeated roots, literally duplicated atoms, zero atoms and leading-cancelled polynomials through `Sample.family`, checking every section/sector sign and the original strict/non-strict domain relations through the shared Boolean fold. The cancelled polynomial contributes an additional root section at zero. Owner `Sample.Family` laws establish real-cell coverage and the whole source sign vector at one ordinary sample, preserving the selected coefficient interpretation. This is direct API consumption, not a new frozen tower tactic backend. |
| Fixed-field finite construction and replay | [FiniteReplay](../conformance/HexRCF/FiniteReplay.lean): exact formula/quantifier/coefficient/divisor/context bindings, complete recorded sign operands, malformed evidence, diagnostic false and preflight-before-search. `Replay.check_domains`, `check_spec`, `check_sound`, `check_original` and `build_spec` use actual real interpretation laws. Bounded production can exhaust. `buildTotal_checked`/`buildTotal_spec` connect the existing complete exact-field producer to finite acceptance for nonzero original divisors, independently of direct proposal depth; false remains diagnostic. |
| Original-goal API proof generation | [PreparedCoefficients](../conformance/HexRCF/PreparedCoefficients.lean) and [archived Prepared probes](https://github.com/kim-em/hex-dev/tree/45a4e4e9a4/bench/HexRCF/ProofProbe/Prepared): successful guarded and Ioc proofs use `Replay.check_sound`; proof inspection excludes producer calls. A fresh total-production probe sets direct proposal depth to zero and still quotes an accepted Ioc proof. Wrong transport, omitted guards, incorrect identities and false verdicts fail. Preparation/transport preserve caller metavariables on success and restore full state on unsuccessful exits, including runtime exceptions. Assigned metavariables cannot hide forbidden dependencies; acceptance closes a fresh uncached theorem of the exact target. Original guards are recovered again from the source before checking, so editing the stored guard arrays cannot omit them. Runtime polynomial/root, formula, quantifier, coefficients and divisor coordinates are bound to their expression data before diagnostics; source/valuation proofs are checked at their required types. Validation-only checks retain no unused auxiliary declarations. |
| Shared source truth over native cells | [Samples](../conformance/HexRCF/Samples.lean): `Samples.run` specializes once and folds the actual native cells through the existing strict QF/quantifier traversal. `run_spec` proves exactly shared `Prenex.toProp` under an actual ordinary-real parent model, with all supplied coefficient coordinates in that parent. Section, sector and cell laws use the same source valuation. Controls distinguish conjugates and two distinct ordered coordinates, diagnostic false, repeated/common roots, zero/cancelled atoms, all comparisons/Boolean forms and half-open/equal/reversed domains. Public-module examples and eight composed axiom guards have only the standard three axioms. Raw row length checks do not authenticate signs or certificates. This diagnostic producer API does not provide frozen replay, frontend source/divisor authentication or arbitrary-depth joint infinitesimal realization; no new performance claim is made. |
| Checked sign retrieval | [SignIndex](../conformance/HexRCF/SignIndex.lean): indexed hits are checked against the original table position and exact key. Missing or malformed routing falls back to the original lookup, preserving every original hit. Actual quoted-tree and linear/indexed proof regressions exercise both routes, including frozen replay failures and state restoration. |
| Generator-window proposals and replay | [GeneratorWindow](../conformance/HexRCF/GeneratorWindow.lean): checked containment and two count-one certificates identify the same selected real root. Production can rebuild all sign entries on the tighter interval; frozen quotation never refines. Malformed, stale, wrong-conjugate and endpoint-root evidence fails, and both lookup modes restore state on replay failure. |
| Root and cell correctness | [FieldRootsConformance](../conformance/HexRCF/FieldRootsConformance.lean), [ProductionProgress](../conformance/HexRCF/ProductionProgress.lean), [AlgebraicProgress](../conformance/HexRCF/AlgebraicProgress.lean), [CarrierModes](../conformance/HexRCF/CarrierModes.lean): selected-field root correspondence, complete carrier roots, squarefree normalization, repeated/common roots and leading cancellation. Samples are ordinary real sections/sectors. General joint nested realization is not supplied by these tests. |
| Caller-registered finite bounds | [NamedConstants](../conformance/HexRCF/NamedConstants.lean), [RegisteredConstants](../conformance/HexRCF/RegisteredConstants.lean), [CoarseConstants](../conformance/HexRCF/CoarseConstants.lean): actual caller-supplied containment proves the specified π/e goals and inverse guard. Missing, stale, cyclic, swapped or nonseparating evidence is rejected/refused. This finite path does not construct a total named-constant field or prove joint independence. |
| Gathered coefficient owners | [Gather](../conformance/HexRCF/Gather.lean): the actual native gatherer transports independently selected positive/negative roots and roots of different polynomials into one context. Original coefficient order, repeated owners, zero/leading cancellation, a further root over the gathered field and empty owners are checked. Nine complete standard-axiom guards cover coefficient interpretation, atom evaluation, native decision semantics, actual gathering success, agreement with separately authenticated original models, ordered-subsequence production for a non-prefix algebraic owner over `[β]` entering a provider-constructed `[α, β]` target, and actual native gathering refusal for reordered and stale keys. The prefix API remains compatible; both negative proofs check `Shared.gather? = none`. Native Boolean checks are diagnostic production controls, not frozen source-goal proof evidence; generic source authentication, literal replay and arbitrary-depth joint realization remain separate obligations. |
| Rational-root source conversion | [RationalRoots](../conformance/HexRCF/RationalRoots.lean): actual square/cube/fourth/fifth-root source proofs authenticate positive rational bases against the denominator-cleared polynomial and checked selected embedding. Guarded cube division, natural powers, a further field root and half-open guards exercise common-field replay. Zero divisions within unsupported root bases/exponents are refused during recognition; an outer cancelled zero divisor fails terminally during guard replay. A prepared false sentence completes authentication before terminal refusal; negative bases, nonreciprocal exponents and shared degree/size exhaustion are distinguished. In common-field preparation, syntactically unsupported sibling coefficients and operands within a root base take precedence over recognition exhaustion in either operand order. Otherwise supported oversized rational and natural radicands return structured budget errors before field construction, with caller state restored. The finite-bound enclosure path checks each leaf’s root syntax and recognition budget before rational normalization or native proposals; errors there are terminal in traversal order. Common-field preparation additionally bounds the product of distinct canonical generator degrees via `rcf.algebraic.commonDegree` (default 64), with typed exponent-dimension exhaustion and duplicate-anchor/state-restoration controls. Intermediate numerator admission also covers reciprocal exponents, normalized dyadic endpoints and rational original-divisor evaluation. A size-only view retains zero-power bases before applying the shared bound once; rational evaluation still uses the original source. Nested rational guards share successful admission of their containing operand while retaining every original zero check in source order. Coverage visits only the arithmetic operand positions actually checked by admission, excluding type and instance arguments. Covered operands use the enclosing operation’s shared numerator or scalar bound, which may be less conservative than a separate numerator bound. All admission precedes zero checks, so a resource refusal can precede an earlier zero-divisor diagnostic; both remain terminal refusals. Controls distinguish standalone and covered bounds, ensure an unsupported outer guard cannot cover an oversized inner guard, and kernel-check beta-reducible type/instance fixtures before verifying they cannot cover a separately evaluated oversized guard. Unsupported nonrational guards remain obligations for their consuming handler, while admission or evaluation failures are terminal. Safe small-budget controls exercise cancellation, zero powers, integer-cast literal recognition, guarded radicands and frontend state restoration; nested unit zero powers remain within budget. This conservative admission does not bound every later operation or prove witness-search completeness. Zero-divisor detection inside a root follows bounded evaluation order and may be preempted by exhaustion; swapped-order controls cover both refusal categories. Inverse notation in bases and exponents and rational constructors in either are supported. Twenty-one tactic proofs, including both orientations of explicit aliases, a rational radicand alias and constructor-wrapped rational bases/exponents, definitionally real power type arguments and inverse-written natural radicands, and an independent false-sentence proof have complete standard-axiom guards. Perfect powers with different canonical/source polynomials and two source polynomials sharing one anchor retain actual selected-root proof markers. Wrong alias parameters refuse with state restoration. This broadens source conversion, without asserting completeness of common-field witness search or conversion of arbitrary algebraic-base radicals. |
| Algebraic-base root source conversion | [AlgebraicRoots](../conformance/HexRCF/AlgebraicRoots.lean) and [AlgebraicRoot](../adapters/HexRCF/RealCoefficients/AlgebraicRoot.lean): the existing `rcf` command authenticates nested roots, shifted and cancelled bases, guarded quotients, reciprocal natural degrees and degree-one negative bases. Thirteen fresh theorem proofs have the standard three axioms; branch, base-embedding, common-field and cell replay markers distinguish this path from rational proofs. Quoted proofs exclude native production. Cancelled zero divisors, unsupported or variable bases, negative higher-degree bases and accepted false certificates refuse. Frozen power/sign checks reject a wrong conjugate, wrong base, zero degree and missing sign evidence; a separate same-polynomial control rejects a different positive conjugate. Typed early degree exhaustion, cache-hit degree revalidation, missing cached proof declarations, exact original guard proofs, negative-base handler decline, and rational/algebraic aliases sharing one anchor are checked. Different root degrees share one authenticated base throughout recursive preparation; the accepted entry supplies its sign-table proof without a second replay. Rational-valued and checked Hex bases have positive proof regressions. Actual tactic proofs cover same-level and recursive cache reuse with degree-one siblings; direct cache controls cover square/cubic reuse without common-field production. Final unsupported-source tactic diagnostics and caller rollback are checked. General root identities defer irreducibility certification until choosing the actual common polynomial. Source conversion still requires the delivered irreducibility witness languages; these examples do not prove generic algebraic acceptance or arbitrary-depth joint infinitesimal realization. |
| Mixed finite coefficients | [MixedConstants](../conformance/HexRCF/MixedConstants.lean): registered π/e bounds compose with unregistered square/cubic aliases, positive rational-root aliases, selected Hex values and supported roots of closed algebraic bases. Six further actual tactic proofs cover nested square roots, square/cube roots of shifted non-rational algebraic bases, an original guarded quotient inside a root, closed division by a mixed named/algebraic coefficient and an algebraic base with a registered subterm. Matched subterm providers remain recorded and checked for both exact rational and algebraic leaves; omitted observations and stale provider versions are rejected. Root bounds authenticate exactly without those providers, so registering π does not admit `sqrt π`. Whole-subject registration matching retains precedence, with a root-specific control; a rational registered subterm retains exact singleton enclosure coverage. Each audits the complete ordinary axiom inventory, exact base/root/cell replay markers and exclusion of native production. General root enclosures authenticate the selected source before proposing endpoints; the existing exact frontend proves containment by literal replay. Original zero divisors inside square roots and general algebraic-base `Real.rpow` expressions are rejected even under zero multiplication and empty domains. Public nested-root enclosures are checked at the original containment target; exact degree/zero-divisor/unsupported diagnostics and false verdicts retain refusal and caller-state restoration. Fresh source proofs pin the named, selected, normalized and selected-field frontends, audit ordinary axioms and exclude approximation/root-production calls. API tests check both inconsistent and coherently forged bounds literals, completed enclosure before false-sentence refusal, the exact singleton bounds of the perfect-square source, public API fresh kernel acceptance and early preparation rollback, replay rollback after earlier auxiliary acceptance and actual guard reuse by closed division and normalized inverse coefficients. Runtime interruptions cannot satisfy rejection assertions. Negative selected-field leaves exercise negative literal endpoints. Positive/negative divisors, cancelled zero denominators, empty-domain preflight and unresolved bounds are exercised; distinct equal aliases can remain unresolved in this finite mode. This remains bounded finite proof search, not general common-field or named-constant completeness. |
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
| Fresh tactic input validation | [Validation comparison](hexrcf-validation-proofs.md) | The original sixteen-arm run is retained as A/A only. Two corrected sixteen-arm studies retain exact common-field routing; the final study also asserts the selected arm and matches production options. Its seven favorable pairs include large retained margins, so no stable speedup magnitude is claimed. Editable public inputs remain fully validated and batch their coordinates. |
| Repeated source construction and root proposal work | [Production](hexrcf-production-proofs.md), [production sharing](hexrcf-production-sharing.md) | Selected-field production and syntax sharing observations on the recorded inputs; no physical heap-sharing claim. |
| Quotient coordinate quotation | [Literal quotation](hexrcf-literal-proofs.md) | Two changed-source comparisons did not establish a gain; reduced-coordinate quotation remains off. |
| Full queries versus exact interval sign evidence | [Interval quotation](hexrcf-interval-proofs.md) | The fixed-goal comparison favors interval quotation. Its reconstructed-query control and historical provenance limitations are explicit. |
| Indexed sign retrieval | [Index comparison](hexrcf-index-proofs.md) | Two retained fixed-goal studies favor indexed retrieval; the default is enabled. These measure whole fresh-module cost, with exact measured-source and later shipping-source identities stated separately. |
| Generator-window refinement | [Window comparison](hexrcf-window-proofs.md) | All 32 fixed-schedule arms are retained. The low-precision fixture removes three full queries at a proof-size cost; the study establishes no useful whole-module speedup, so refinement defaults to zero. |
| Initial generator precision | [Precision comparison](hexrcf-precision-proofs.md) | Eight versus sixty-four bits for the same selected √2 and exact target, with checked transport. Three full queries disappear and private proof size falls; the small mixed paired changes justify no default change. The original pair excludes arm-specific setup. A [separate four-width study](hexrcf-precision-full-proofs.md) includes fresh constructor/transport proofs and retains all 24 arms. Its large mixed margins establish no reliable speedup; the [36-arm production-acceptance study](hexrcf-precision-production-proofs.md) uses the actual tactic acceptance routine and a balanced six-round schedule. Its variable observations justify no default change. None proves general reconstruction or nested-depth costs. |
| Repeated/shared source roots | [Source comparisons](hexrcf-common-root-proofs.md) | Two changed-input comparisons through the named-√2 frontend retain all 16 arms. The normalized carrier has four root sections in each case. Several input dimensions change together; this is not one-parameter or asymptotic scaling evidence. |
| Carrier normalization | [Carrier comparison](hexrcf-carrier-proofs.md) | The retained fixed-goal pairs favor monic carriers; the ordinary-kernel normalization laws retain the original product. Signed chains are not arbitrarily made monic. |
| One replay goal versus split conjuncts | [Replay comparison](hexrcf-replay-proofs.md) | The retained comparison did not establish a gain; combined replay stays off. |
| Degree, source atoms and coefficient width | [Input costs and attribution](hexrcf-scaling-proofs.md) | Independent two-point observations in a no-real-root regime, with serialized/expanded syntax and a representative phase profile. These are not asymptotic verdicts or precision/depth evidence. |

The consumed signed-remainder producer already uses
[`Sturm.normalize`](../HexSturm/Basic.lean), which divides by the positive
absolute leading coefficient. Negative-leading remainders retain their signs,
with literal positive scale witnesses checked during replay. Carrier monicization
does not replace that normalization or assert that every intermediate field gcd
computation is monic.

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
- General frozen tower/context integration, executable assembly of all-live
  enlargement, and one ordinary real realization of every finite joint set of
  nested selected-root and successive-infinitesimal constraints still require
  the actual owner interfaces. Native ordered roots are already available through
  `Tower.Context.roots_all`, `roots?_success`, `roots_spec` and `roots_sorted`.
  Native ordinary samples are available through `Sample.Family.cells_unique`,
  `cell_signs` and `sector_signs`; the adapter consumes those laws in its direct
  API examples, including source signs at each selected root section. A reducible
  defining polynomial also checks leading cancellation between distinct stored
  nonzero expressions whose difference is the canonical zero. They establish
  actual native producer behavior under a real
  predecessor model. A frozen tactic checker must separately validate literal
  context/root/sign data without invoking those producers during replay.
  Ordered real-closure existence alone does not discharge general joint
  nested-root/infinitesimal realization or enlargement assembly. The merged
  `BaseInclusion.sign`, provider-derived `RealPrefix.Model.towerModel` and
  `BaseOrder`/`BaseMapModel` interfaces establish checked base transport through
  ordered real-key subsequences,
  model packaging and ordered base models under their actual child laws; they
  do not establish
  one ordinary real point satisfying a nested tower sample’s complete finite
  set of conditions. Their availability is not a reason to wait for whole-issue
  closure or unrelated measurements. The merged finite-reader
  [sign-evidence interfaces](../adapters/HexRealClosureMathlib/SignEvidence.lean)
  supply `signFacts_coversKeys` and `decodeEvidence_nested`: checked child facts
  cover the upper packet's stored literal support and compose with its actual
  byte decoder under lexical prechecks. Graph checking still uses ordinary
  coefficient arithmetic. These laws do not reconstruct general tower contexts,
  collect every intermediate packing dependency or realize a joint real sample.
  The merged [coefficient-level dependency envelope](../HexSignDet/DependenciesCodec.lean)
  binds serialized results to their ordered full subjects, checks every packet
  once through its supplied local reader, and retains the exact graph and typed
  memo. `Graph.decode_encode` and `Decoded.results_bound` prove the actual byte
  roundtrip and selected-result bindings. These are routing and codec laws;
  the local reader still supplies arithmetic validity. Automatic intermediate
  dependency collection, literal context reconstruction and strict compiled
  arithmetic replay are not supplied by the envelope.
  The merged supplied-fact graph transport in
  [DagOperations](../HexSignDet/DagOperations.lean) preserves memo acceptance,
  rejection, literal trees and indices under the supplied coefficient-operation
  laws. Reciprocal/division packing retains the actual inverse computation.
  Missing-fact compiled fallback remains; this interface does not collect all
  intermediate keys or rebuild general cross-level contexts. The merged
  development theorem `HexSturmMathlib.query_iff` and actual companion
  `RealAlgebraicPoly.roots_spec` establish their lawful query/root contracts.
  The query theorem is still in a development adapter rather than exposed by
  `import HexSturmMathlib`; owner integration remains required for that public
  companion surface. These available laws are not waiting on performance closure.
- Algebraic frontend completeness and total acceptance of every supported source
  are not proved by the exact-field total producer. It starts with an already
  authenticated fixed-field environment; frontend irreducibility quotation
  still has the concrete language gap above. Registered constants remain bounded
  certified search unless the stronger child progress/relative transcendence
  laws are supplied.
- The initial-generator precision comparisons cover one fixed field at four
  widths, including fresh constructor/transport proofs and production proof
  acceptance. The repeated/shared-root comparisons cover two changed-input
  pairs through the named-√2 frontend. Broad precision, nested depth and
  asymptotic common/repeated-root cost scaling remain unmeasured. New numerical primitive measurements must
  use Mathlib-free owner drivers on explicitly bound adapter-generated inputs;
  preparation costs must be reported separately. Existing correctness examples
  do not stand in for those additional scientific measurements.

These limits prevent closing #10358 or attesting the complete planned adapter.
They do not defer the implemented ordinary-point and fixed-field surfaces while
unrelated owner measurements are unfinished.
