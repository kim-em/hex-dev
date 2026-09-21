# Algebraic representations without Mathlib in the executable

## Conclusion

The representation boundary is viable enough to develop further: ordinary
`DensePoly` arithmetic runs on genuine noncanonical algebraic representatives,
without a fake field instance or fallible arithmetic operations. The actual
division and gcd algorithms admit noninjective interpretation theorems in Lean.
This is evidence for the architecture, not a proof of the real-closure library.

Canonical-zero packing has a measurable cost. On the tested products, moving
packing to the boundary of each output coefficient improves median paired times
by 1.98–5.43×. This supports batching for these products, not a production-wide normalization
policy. Division-shaped workloads, cheaper zero tests and representative growth
must be compared before selecting that policy.

## What was tested

[Source and commands](../experiments/RealClosureAlgebraic/README.md).
The experiment uses positive sqrt(2) in `(1,3/2]`, with both `X²−2` and
`(X²−2)(X²−3)` as defining polynomials. A representative is zero exactly when
its remainder is zero, or its gcd with the defining polynomial has a root in
the selected interval. The executable uses existing `DensePoly` routines and
`ZPoly.sturmCount`. It introduces no competing Tarski primitive.

This distinguishes genuinely different branches:

- `X²−2` vanishes at the selected root even though its stored polynomial is
  nonzero. Its nonconstant gcd requires root selection.
- `X²−3` does not vanish there. Inversion discards that factor, works modulo
  `X²−2`, and produces the value −1.
- `X` is inverted without a split, with value `X/2` at sqrt(2).
- Selecting sqrt(3) from the same defining polynomial reverses the zero answers.
- A two-root interval and a nonsquarefree descriptor fail executable validation.
- Distinct nonzero representatives can have zero difference. Structural equality
  therefore remains honest and is not claimed to be semantic equality.
- Explicit transport to the retained factor preserves eight live values.
- A nested representation for positive fourth-root(2), using `Y²−sqrt(2)`,
  checks squaring, fourth powers, inversion, distinct representatives with zero
  difference, and polynomial division. It demonstrates two-level executability;
  it is not the general recursive context construction or a second-level Sturm procedure.

The 48 scalar and 17 polynomial records are checked independently with
python-flint 0.9.0 and exact rational-pair arithmetic for Q(sqrt(2)). Checks
include inverse identities modulo the retained factor, complementary factors,
full quotient/remainder outputs (including zero inputs and divisors), nontrivial
common factors, monic gcds, Bézout identities, signs and both
multiplication arms. The discarded factor is checked against the exact monic
gcd, not merely a valid factorization. The independent sign check bisects
rational enclosures of sqrt(2), rather than repeating the implementation’s
squared-magnitude formula. The verifier rejects incomplete record counts. Six traced products check instrumentation against actual
outputs. The product `[X,1] * [−2,X]` checks the raw nonzero inner coefficient
`X²−2`, which must pack to zero through gcd and root selection. Division
records also exercise semantic cancellation of leading coefficients.
The nested checks are executable algebraic identities, not an independent
fourth-root oracle or a proof of irreducibility.

## What is proved

`Transfer.division` and `Transfer.gcd_map` apply to the existing algorithms.
They assume `f : E → F` preserves subtraction, multiplication and division and
satisfies `f e = 0 ↔ e = 0`. Neither injectivity nor field laws on `E` are
assumed. Zero reflection preserves coefficient-array length, degree, trimming
and the algorithms' structural bounds. The proof follows the actual array
cancellation loop and then the Euclidean loop, including the zero-divisor cases.
It requires only ordinary operation instances on source and target carriers.
The checked axiom lists are `[propext, Quot.sound]`.

The representation also has a generic proved storage invariant:
`pack d q = 0 ↔ isZero d q = true`. Kernel-reduced checks cover the selected-root
examples. Crucially, the experiment does **not** prove the universal soundness of
`isZero`, interpretation preservation for its scalar operations, or semantic
validity of arbitrary descriptors. Those hypotheses remain the first companion
obligations. It does not yet transfer xgcd's Bézout coefficients, derivative,
pseudo-remainder or Tarski/BKR algorithms; executable xgcd results are checked
against an independent oracle.

## Measurement

[Protocol](../experiments/RealClosureAlgebraic/PROTOCOL.md),
[raw data](../experiments/RealClosureAlgebraic/results/timing),
[summary](../experiments/RealClosureAlgebraic/results/summary.json).
The run retained all 144 measured arm samples: 12 cases, six adjacent AB/BA
blocks each, no rerun or activity-based filtering. lean-bench owns timing and
auto-tunes inner repeats to a 50ms floor. Inputs are prepared before timing;
both arms include the same full semantic digest. All paired result hashes agree.
The fixed cases are architecture comparisons, not Phase-4 complexity evidence.

The host was chungus2, AMD EPYC 9455, with the process pinned to automatically
leased logical CPU 11. Starting load averages were 5.37/5.63/9.50. Source base is
`c08268dec030a81a5da124a6d8060c1420c779e7`, Lean 4.34.0, lean-bench
`8a37daf1074c3bdbd0da479b55538bad4a0022db`. Metadata records source hashes and
host details. Timed sources `Algebraic.lean` and `Bench.lean` were unchanged
throughout the measurements. Untimed checks/proofs were extended independently.

The table gives median times and the median/range of six paired each/batch ratios.
"Shared factor" multiplies every input representative by `X²−3`; on the
reducible descriptor this forces the nonconstant-gcd/Sturm path.

| Descriptor | Coefficients | Length | Product, scalar packing (ms) | Batched (ms) | Paired speedup (range) |
|---|---|---:|---:|---:|---:|
| minimal | generic | 4 | 0.200 | 0.087 | 2.31× (2.30–2.41) |
| minimal | generic | 8 | 0.786 | 0.257 | 3.06× (3.02–3.09) |
| minimal | generic | 16 | 3.044 | 0.824 | 3.69× (3.64–3.75) |
| minimal | shared factor | 4 | 0.383 | 0.193 | 1.98× (1.93–2.00) |
| minimal | shared factor | 8 | 1.480 | 0.592 | 2.50× (2.47–3.74) |
| minimal | shared factor | 16 | 5.733 | 1.978 | 2.90× (2.89–2.91) |
| reducible | generic | 4 | 0.327 | 0.116 | 2.80× (2.78–2.82) |
| reducible | generic | 8 | 1.318 | 0.328 | 4.01× (3.94–4.10) |
| reducible | generic | 16 | 5.346 | 0.992 | 5.43× (5.34–5.51) |
| reducible | shared factor | 4 | 0.509 | 0.219 | 2.33× (2.32–2.35) |
| reducible | shared factor | 8 | 1.995 | 0.656 | 3.04× (3.01–3.07) |
| reducible | shared factor | 16 | 7.789 | 2.119 | 3.68× (3.63–3.72) |

For length `n`, the scalar-packing arm makes `2n²` zero tests; the batched arm
makes `2n−1`. At n=16 these are 512 versus 31. On generic reducible inputs all
512/31 calls use gcd but none use Sturm; on shared-factor inputs all use both.
The traced reconstruction itself performs extra packing; these checks are outside
timing and excluded from the logical counts. Matching executable results check the shadow
product, not the count correspondence. The counts follow by source inspection
of `HexPoly/Operations.lean`’s `mulImpl`: one scalar multiplication and one
addition per coefficient pair. The formula check in Python is a regression
check for the shadow, not an independent measurement of kernel call counts.

Batching reuses `DensePoly` convolution over raw coefficient polynomials and
packs at its output boundary. It does not introduce a second polynomial kernel.
Internal raw values may denote zero; they must not escape as packed coefficients.
Nonzero stored representatives are not reduced modulo the defining polynomial,
but the zero test still computes a temporary remainder. This experiment does not
measure the paper's full clean-representation discipline, coefficient growth in
large towers, asymptotic scaling, root isolation, or the cost of persistent caches.
No general speedup claim follows for those workloads.

## Remaining design decisions

Unreduced nonzero representatives grow without bound. For example, repeated
squaring of the representative X stores degrees 1,2,4,8,… even though its
value becomes rational after the first square. Every zero test computes a
temporary remainder but discards it. When the defining polynomial is monic
and clean, retaining that remainder is allowed by the SPEC and can bound raw
degree. It requires no additional division if the zero test returns its
already-computed remainder, but needs an appropriate constructor and invariant.
This does not justify monicizing or reducing by arbitrary non-monic definitions:
that would lose the paper's clean-representation benefit.

The measured baseline is intentionally simple. A *verified* irreducible
minimal polynomial permits a cheaper remainder-only zero test. The minimal
benchmark cases still use the generic gcd procedure. Compare this fast path
explicitly; do not count its absent optimization as an intrinsic cost of all
canonical-zero representations.

Batching also has limits. Division must inspect leading-coefficient zeros at
each cancellation step; postponing those checks would change the algorithm.
At a second level, raw coefficient operations themselves pack predecessor
values. The one-level convolution result gives no evidence that those costs
disappear. Splitting is another independent choice: current inverses are packed
back under the original descriptor, and the explicit refinement test is only
one-level transport. A production opaque-context API must track all dependent
levels and handles when the defining polynomial changes.

## Proposed plan of action

Work proceeds through three distinct stages: experiments supply evidence;
SPEC work fixes the contracts and acceptance criteria; implementation realizes
those contracts. Experimental code and proofs do not become production APIs
merely because they compile. Each implementation directive must link to its
completed, revised owning SPECs and identify its actual prerequisites.

### A. Experiments — resolve the remaining design questions

The selected-root experiment reported above is complete. Two bounded follow-ups
supply the evidence needed to finish the design:

| Experiment | Question | Deliverable and exit criterion |
|---|---|---|
| E1: storage policy | How do per-operation packing, retaining a monic clean remainder, and a justified irreducible fast path behave on division/gcd and nested coefficients? Where is batching applicable? | An isolated comparison using the existing kernels, independent result checks, the fixed shared-host measurement protocol, and time/zero-test/representative-growth results. Recommend a policy, or identify the specific unresolved tradeoff; do not extrapolate multiplication results. |
| E2: context refinement | Can a split at a lower algebraic level preserve live values and descriptors at the next level under the proposed opaque-context API? | A small two-level prototype and explicit transport invariants, exercising old handles and dependent defining polynomials. Establish a workable ownership/transport design or document the obstruction. This is a feasibility check, not the implementation of general towers. |

Keep these under `experiments/` with reports. They may contain executable
prototypes and local proof attempts, but do not change production library
contracts, promote the current prototypes, or discharge library implementation
phases. E1 and E2 can proceed independently. Their conclusions feed the SPEC
revisions below; an inconclusive result remains an explicit open design question.

### B. SPEC writing and revision — make the decisions before implementation

The eight family SPECs already exist. This stage revises them and their shared
boundary; it is not another request to implement their contents. Drafting can
proceed alongside experiments, but settle experiment-dependent choices before
finalizing the affected contracts.

**S1: shared execution contract.** Revise
[real-closure-execution.md](../SPEC/real-closure-execution.md) and the
[family design](../SPEC/future-work.md#real-closures-of-ordered-fields), together
with the affected [hex-poly](../HexPoly/SPEC/hex-poly.md) and
[hex-real-roots](../HexRealRoots/SPEC/hex-real-roots.md) contracts. Specify:

- Ordinary total operations, including `NatCast` and executable sign;
  structural versus semantic equality; canonical-zero storage; the chosen
  storage/normalization policy and permitted optimizations, informed by E1.
- Descriptor validity, context identity, splitting, and transport of live
  values and dependent levels, informed by E2. Separate computational checks
  from companion semantic theorems, keeping executable construction Mathlib-free.
- Exact hypotheses and statements for noninjective interpretation of the
  existing polynomial algorithms. No fake Field instance, fallible arithmetic
  record, or duplicate polynomial kernel is introduced.
- Ownership of the single Tarski primitive and its rational/generic agreement.
  `ZPoly.tarskiQuery` is specified but still unimplemented.

**S2: owning library contracts and companion obligations.** Reconcile all four
pairs with S1, giving concrete APIs, validity/termination hypotheses, theorem
statements, proof dependencies, and conformance/performance acceptance criteria:

| Computational SPEC / companion SPEC | Decisions to write or revise |
|---|---|
| [hex-sturm](../SPEC/Libraries/hex-sturm.md) / [hex-sturm-mathlib](../SPEC/Libraries/hex-sturm-mathlib.md) | Operation-only kernels, sign and endpoint interfaces, Tarski replay and trivial-tower agreement; identify the abstract Sturm–Tarski statements consumed from Tau Ceti and the Hex correspondence proofs. |
| [hex-sign-det](../SPEC/Libraries/hex-sign-det.md) / [hex-sign-det-mathlib](../SPEC/Libraries/hex-sign-det-mathlib.md) | Thom identity/order, BKR certificates including support completeness, and the sample-point interface; state correctness and imported abstract-field obligations. |
| [hex-ordered-fn](../SPEC/Libraries/hex-ordered-fn.md) / [hex-ordered-fn-mathlib](../SPEC/Libraries/hex-ordered-fn-mathlib.md) | Infinitesimal arithmetic and order; caller-supplied approximation with separate containment and requested-width proofs, relative-transcendence termination and its computational proof interface. Keep hex-interval and bundled pi/e providers out of scope. |
| [hex-real-closure](../SPEC/Libraries/hex-real-closure.md) / [hex-real-closure-mathlib](../SPEC/Libraries/hex-real-closure-mathlib.md) | Storage policy, validated descriptors, recursive contexts, splitting/transport, total isolation and extension order; selected-root arithmetic/sign semantics, proof slices, and exploration/tactic integration boundaries. Preserve the existing real-algebraic fast path and its one-way dependency relationship. |

Specify the first rational-algebraic slice explicitly: its owning library,
reuse of existing real-algebraic functionality, general sign interface,
`valid d = true` hypotheses, and interpretation in ℝ. Name the available
`HexRealRootsMathlib.sturmCount_eq_card_roots` theorem, its positive-degree and
rational-squarefreeness assumptions, and the required primitive-part/divisor
bridges. This is theorem and API specification; proving those statements is
stage C. Likewise, specifying root-preserving transport is distinct from
proving it or implementing the runtime context machinery.

The deliverable is a coherent set of revised SPECs with an acyclic dependency
graph and separately closable implementation directives derived from their
acceptance criteria. Audit terminology, relative links, ownership and the
computational/companion split. Land the relevant SPEC revisions before starting
the implementation directives they govern. S2 depends on S1's settled contracts;
completed unaffected contracts need not wait for unrelated revisions.

### C. Implementation — only after the relevant SPEC revisions land

The following are production code/proof work, not further SPEC-writing tasks.
Their detailed boundaries and acceptance tests come from stage B:

| Implementation work | Prerequisites and completion evidence |
|---|---|
| I1: shared polynomial correspondence | Revised polynomial/shared contracts. Promote reviewed generic division/gcd transfer lemmas and prove the specified xgcd, derivative and Horner correspondence for the existing algorithms. |
| I2: rational selected-root slice | Revised real-closure and companion contracts plus the shared interfaces it uses. Implement the chosen storage/validation/sign API, then prove zero testing and scalar arithmetic; inversion and root-preserving splitting/transport; and instantiation of polynomial correspondence. These are separate implementation/proof directives. Use the existing ℝ Sturm development; do not claim the non-Archimedean case. |
| I3: Sturm–Tarski and BKR/Thom | Revised real-roots, sturm and sign-det contracts. Implement the owned Tarski primitive and its generic extension with agreement, then sign determination and Thom operations. Prove correspondence for the new pseudo-remainder kernels, replays and reduced-matrix support completeness. Companion completion requires the specified abstract-real-closed-field results. |
| I4: ordered simple extensions | Revised ordered-fn pair and shared interfaces. Implement infinitesimals and caller-supplied transcendental approximation, with their separate correctness/termination proofs. This can proceed independently of BKR where its specified dependencies permit. |
| I5: recursive real closures | Revised real-closure pair; the required coefficient arithmetic, root-selection kernels and correspondence from I1–I4. Implement recursive contexts, splitting/transport and total root isolation, and prove their semantics. Enforce transcendental-before-infinitesimal-before-algebraic extension order. |
| I6: integration and full validation | Revised user-facing contracts and implemented dependencies. Complete exploration, sample-point and certificate-based tactic interfaces; run trivial-tower conformance, the paper's Example 3, sqrt(epsilon)>epsilon, and 1/epsilon exceeding each supplied integer. Measure tower8 and clean-versus-eager behavior on the actual implementation. |

I1 and the early parts of I2 can progress together once their SPECs land;
I2's final correspondence uses I1. I3 and I4 are separate implementation
branches, not a mandatory serial queue. I5 joins their required results;
I6 follows the functionality it validates. Implementation may expose a SPEC
error: stop the affected directive and revise that SPEC, rather than silently
changing its contract in code. Neither a successful experiment nor an executable
without its required proofs establishes completion of a verified library phase.

**Immediate next work:** E1 and E2, followed by finalizing and landing S1/S2;
then start the unblocked I-series directives. Family monitors and worker queues
remain stopped. The current report proposes this sequence and does not itself
revise the owning SPECs or launch any implementation work.
