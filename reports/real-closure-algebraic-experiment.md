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

1. **Settle the execution contract and storage policy.** Correct the shared
   and owning SPECs to include `NatCast`, executable sign, semantic monicity,
   gcd equality, replay equality and root-preserving transport. Preserve
   ordinary total operations and honest structural `DecidableEq`. Before
   committing to a storage policy, compare current packing, retention of a
   monic clean remainder, and a verified-irreducible fast path on division/gcd
   and a two-level workload; record both time and representative growth.
   Batching is a candidate for ring operations, not an assumed division strategy.
2. **Prove zero testing and scalar arithmetic for one selected Q-algebraic
   root.** Quantify explicitly over `valid d = true`, identify the unique
   selected real root, and prove zero soundness/completeness and interpretation
   of the actual operations. Use the existing
   `HexRealRootsMathlib.sturmCount_eq_card_roots` theorem in
   `HexRealRootsMathlib/ChainCorrespond.lean`, including its positive-degree
   and rational-squarefreeness hypotheses. Supply the primitive-part root
   bridge and squarefreeness of divisors. Production constructors should enforce
   executable descriptor validity, without requiring Mathlib in the executable.
   Add a general rational-algebraic sign by certified interval refinement;
   `signSqrt2` is not that interface. This slice can use semantics in ℝ today.
3. **Prove inversion, splitting and transport on that slice.** Establish the
   gcd/cofactor conditions, inverse identity, and preservation of the selected
   root. Make transport accept evidence of a root-preserving refinement;
   the experimental unrestricted function is not the production contract.
   Fix opaque-context and live-handle behavior before extending to towers.
4. **Instantiate and complete the polynomial correspondence.** Promote the
   reviewed Mathlib-free division/gcd transfer lemmas, instantiate them with
   the established semantic map, and extend transfer to xgcd coefficients,
   derivatives, Horner evaluation and the needed pseudo-remainder operations.
   Keep each proof about the existing executable algorithm; no fake Field
   instance or parallel replacement polynomial kernel is needed.
5. **Implement generic Sturm–Tarski and sign determination.** The repository
   specifies `ZPoly.tarskiQuery` but has no implementation yet. Implement that
   owned primitive and its generic ordered-field extension with explicit
   trivial-tower agreement. Consume the Tau Ceti abstract-real-closed-field
   development for the companions. Add Thom encodings and BKR with
   support-completeness evidence for reduced matrices. The rational vertical
   slice's ℝ semantics does not prove the non-Archimedean case.
6. **Implement recursive contexts and infinitesimals.** Define predecessor
   operations, root identity, validity, context refinements and total isolation
   by tower depth, then validate the paper's Example 3, sqrt(epsilon)>epsilon,
   1/epsilon exceeding each supplied integer, and trivial-tower conformance.
   Measure tower8 and clean-versus-eager behavior only on that implementation.
   Infinitesimal base arithmetic can be developed independently of BKR; general
   algebraic root selection over it needs the generic layer from step 5.
7. **Integrate caller-supplied transcendental oracles and the user surface.**
   Preserve separate `approx : Rat → Bounds` computation and proof functions
   for containment and requested width. Derive termination from these and
   relative transcendence. A finite benchmark success covers only its own
   search. Keep hex-interval and bundled pi/e providers out of scope. Complete
   the exploration/sample-point interfaces and certificate-based tactic
   integration under these contracts, enforcing the tower extension order.

The immediate next action is step 1's focused policy comparison, followed by
steps 2–4 as separately verifiable proof slices. The current conditional
transfer lemmas remain useful whichever monic storage policy wins. Later
issues and dispatch should follow these dependencies; family monitors and
worker queues remain stopped. Computational and benchmark executables remain
Mathlib-free, while companions supply semantic proofs. No full-family completion
or Phase-4 claim follows from this experiment.
