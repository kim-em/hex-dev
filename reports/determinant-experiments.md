# Determinant redesign: questions and experiments

The objective is fast exact determinant computation and fast checked proofs,
over fixed coefficient rings and symbolic matrices. The current algorithm,
matrix storage, polynomial representation, witness format, checker and dispatch
are all candidates for replacement. Existing implementations are experimental
controls, not architectural requirements. This document proposes experiments;
it does not select a replacement architecture or mandate a migration.

Hex determinant entry points must never invoke Mathlib determinant tactics
implicitly. Mathlib is an explicit comparison arm. A Hex decline is recorded
as a failure to solve, even if another tactic could finish immediately.

## Three distinct tasks

1. **Compute a value.** Given a matrix over `Int`, `Rat`, `Dyadic`, a finite
   field or a polynomial ring, return the exact determinant. This API must not
   require constructing proof payload. Its performance includes the requested
   output representation and normalization, not only elimination.
2. **Produce a symbolic result.** Return an expanded polynomial or a shared
   arithmetic expression, with that choice explicit. An independent-variable
   determinant has factorially many distinct monomials in expanded form;
   demanding expansion imposes a cost no choice of elimination removes.
3. **Prove a supplied equality.** Given `det A = e`, establish that identity.
   The target may already be compact. Expanding both sides is one candidate,
   not a required first step. Proof construction, serialization and kernel
   checking all count towards the result.

These tasks share mathematics but need not share one algorithm, physical
representation or execution path. In particular, a fast value routine is not
automatically a fast tactic.

## Existing implementations to include as controls

| Surface | Current role |
|---|---|
| `Hex.Matrix.det` in `HexDeterminant` | Leibniz reference definition and determinant identities |
| `Hex.Det.det` in `HexDet` | Value dispatcher: small formulas, Bareiss for installed exact-quotient carriers, Berkowitz otherwise |
| `HexBareiss.Bareiss` | Array-backed fraction-free computation; the baseline is already array-backed |
| `HexModularMatrix` | Modular images, bounded CRT, Dixon solves and divisor-based integer determinants, with correctness results in the core and companion |
| `HexCharPoly` | Existing Berkowitz computation; use its determinant consequence as a control |
| `HexBareissMathlib` / `HexPolyDetMathlib` | Numeric and symbolic certificate tactics, separate from the value dispatcher |

`HexDet/Int.lean` still installs only the Bareiss arm. Its comment saying the
modular implementation does not yet exist is stale: `HexModularMatrix/Det.lean`
and its companion are present. Integrating that code is a different question
from whether it is competitive. Start from the existing implementations before
writing new modular, storage or characteristic-polynomial prototypes. A new
storage experiment must identify what it changes relative to the current arrays.
`HexDet/SPEC/hex-det.md` also describes the now-existing modular operations as
planned; reconcile that integration contract before choosing its replacement.
There is no dedicated dyadic integration module in `HexDet`; test the proposed
exact scaling independently before deciding its dispatch interface.

## What the evidence says

The [symbolic replay report](hex-poly-det-kernel-performance.md) retains three
counterexamples. General replay improvements reduce observed proof work by
8–23%, but Mathlib still wins every pair in the six-pair comparison. In the
quadratic 4×4 example, the committed final diagnostic recheck on `chungus2`
is about 897 ms of Hex proof work against about 350 ms for Mathlib.
Those totals alone do not isolate producer and checker costs. Separate checking
after a prior whole-proof check overestimated the benefit of splitting; experiments must
include the first kernel check in a fresh module.

The [numeric proof measurements](../HexBareissMathlib/SPEC/hex-bareiss-mathlib.md#the-det-tactic)
tell a different story: retained dense integer cases at dimensions 8 and 16
take about 0.16/0.52 s with Hex against 0.51/18.8 s with Mathlib on `chungus2`.
These are historical host-specific measurements, not new results or a promise that the
same ratios hold after replacement.

The [compiled Bareiss comparisons](hex-bareiss-performance.md) expose another
problem: on their salt-71 tridiagonal integer family on `chungus2`, FLINT
overtakes Hex between dimensions 24 and 32 and is about 8.6 times faster at dimension 512. That is
evidence against making one fraction-free implementation the universal value
engine. It does not identify the complete cause: algorithm, representation,
coefficient growth, compiler specialization and external-call overhead differ.
The same report shows that the choice of exact-division primitive materially
affects runtime. Ring-operation counts alone are inadequate.

The [modular-matrix report](hex-modular-matrix-performance.md) is essential
additional evidence from `chungus2`. On its salt-71 tridiagonal dimension-512
fixture, the divisor route takes 0.288 s against 1.278 s for Bareiss and 0.144 s for FLINT. On dense 8-bit
matrices at dimension 256 it instead takes 3.623 s against 2.158 s and 0.0466 s.
Simply choosing the existing modular method would therefore not solve the
computational problem. Retained attribution also identifies prime generation,
bounds, decomposition and reconstruction costs. These data are compiled value
measurements, not kernel-checking measurements, and must not be mixed with the
symbolic proof timings. The earlier ordinary-CRT table also records 1.584 s
against FLINT's 0.007588 s for dense 128×128 8-bit entries. That much larger
gap merits per-stage investigation before another algorithm portfolio is
proposed. FLINT selects its own algorithm: this is not a controlled isolation
of modular-elimination implementation cost.

Mathlib's installed
[`Bird/Cert.lean`](https://github.com/leanprover-community/mathlib4/blob/1cf325a0cf67aca2b04d76b5380ff6a9e410aefa/Mathlib/Tactic/Determinant/Bird/Cert.lean)
combines arithmetic normal forms with proofs, caches entries and intermediate
certificates, and short-circuits zero products. Hex's list certificate path
instead asks the kernel to compute polynomial identities from quoted data.
The existing comparison changes both determinant algorithm and proof method;
it does not isolate which replacement would give the largest gain.

## Candidates and their obligations

| Layer | Candidates to compare | What can disqualify a candidate |
|---|---|---|
| Integer computation | Existing Bareiss, modular CRT and divisor implementations; storage and arithmetic variants | Coefficient growth, repeated allocation, conversion cost, insufficient deterministic reconstruction bound |
| Rational and dyadic computation | Direct arithmetic; exact row/column scaling into integers; mantissa/exponent representation for dyadics | Repeated gcd normalization, inflated common denominators, enormous materialized shifts |
| Polynomial computation | Sparse or dense arithmetic with fraction-free elimination; modular evaluation and interpolation | Intermediate support growth, expensive exact division, dense interpolation boxes, output-size explosion |
| General ring computation | Division-free Bird or Berkowitz schedules; shared arithmetic expressions | Excess arithmetic, normalization of unused results, loss of expression sharing |
| Proof construction | Mathlib-style proof-producing arithmetic; verified arithmetic-program evaluation; direct algebraic certificates | Repeated normalization, rebuilding types and denotations, large proof terms or kernel replay |
| Identity checking | Explicit polynomial equality; bounded integer packing; deterministic evaluation/interpolation certificates | Loose coefficient/degree bounds, large packed integers, too many evaluation points, expensive transport |

These are algebraic and representation choices, not a catalogue of special
matrix shapes. Zero elimination, common subexpressions and lazy evaluation
should first be tested as general arithmetic mechanisms. A shared arithmetic
program is a hypothesis too: its interpreter and indexing overhead may lose
to specialized straight-line proofs. Do not require every backend to pass
through it before measuring that cost. Keeping expressions factored does not
itself make equality checking cheap: a candidate must account for the cost of
proving that its circuit and the supplied target represent the same polynomial.

FLINT's documented integer determinant interface chooses among cofactor,
Bareiss and modular methods. Its proved modular mode uses a determinant bound;
its accelerated method reconstructs a quotient after obtaining a divisor.
These are useful producer designs, not ready-made Lean certificates.
[FLINT documentation](https://flintlib.org/doc/fmpz_mat.html#determinant)

Bird gives a division-free computation using `O(n M(n))` ring operations,
where `M(n)` is matrix multiplication cost. This supplies a general schedule
to compare, not a prediction of polynomial bit complexity or Lean proof time.
[Bird's paper](https://www.cs.ox.ac.uk/publications/publication5398-abstract.html)

Any CRT checker must certify the congruences and a uniqueness bound: for
example, both the candidate and true integer determinant lie in `[-B,B]`
and the combined pairwise-coprime modulus exceeds `2B`. Candidate verification
must include its bound. The existing `Hex.Matrix.dvd_det_of_mulVec` in
`HexModularMatrix/Algebra.lean`
proves divisibility from a nonsingular integer matrix, a checked equation
`A * y = d * b`, positive `d`, and joint reducedness of `y` and `d`. Reuse or
replace that theorem explicitly. Checking the equation and reducedness is only
part of the payload: the cofactor congruences and bound must also be justified.
The current theorem additionally requests nonsingularity; test eliminating that
assumption rather than making it an architectural requirement (a positive `d`
also divides a zero determinant). Never assume divisibility from a producer hint. Randomness may
guide production, but random evaluations or repeated stable reconstructions
alone cannot justify a theorem.

Two existing bound options are the Mathlib-free row-ℓ¹ product
`rowNormBound` / `natAbs_det_le_rowNormBound`, and the tighter row/column
Hadamard bound justified by the companion's `LawfulDetBound` instance. Compare
bound computation and proof cost against the extra modulus bits needed with
the weaker bound. With a certified positive divisor `d`, the cofactor can use
`floor(B / d)`; neither the bound nor its correctness proof is free.

Polynomial identity certificates similarly need degree and coefficient bounds
or a deterministic interpolation argument. A few matching evaluations do not
prove equality. Arbitrary commutative rings may have zero divisors: symbolic
pivot cancellation cannot silently assume a field. One sound option is to
prove the universal identity over an appropriate free polynomial ring and
then map it to the user's ring. Characteristic-specific identities need their
own justified coefficient reduction. Bounds and these transports must be
included in measured checking cost.

## Experiments in order

### 1. Separate arithmetic proof cost from determinant strategy

Start with the quadratic 4×4 counterexample and its existing exact witness.
Keep the input, witness and final theorem fixed. Compare the current list
checker with a prototype that proves the same polynomial product identities
using cached Mathlib ring normal forms and explicit algebraic proofs. No call
to `norm_det` occurs in the candidate. Check every component in the kernel.

This experiment asks whether the witness itself is competitive once its
arithmetic is proved differently. Report conversion into the alternative
representation separately, but include it in total time. Do not compare a
checker supplied with free normalized operands against a complete tactic.
Use the independent-variable 4×4 and two-block 6×6 only after the first example
works. A substantial residual gap is evidence to question the witness and
schedule, not to add another dispatch shortcut.

### 2. Separate determinant schedule from arithmetic representation

Use the same coefficient representation and instrumentation to compare
fraction-free elimination with division-free Bird, and a determinant-only
use of Berkowitz where feasible. First compare compiled computation without
proofs. Compare complete proofs under a common checking method, using the
proof-producing arithmetic from experiment 1 where applicable; the existing
Bareiss, Bird and Berkowitz proof paths do not isolate schedule cost because
they check different payloads in different ways. Report any full-system
comparison as such. Measure operation counts, coefficient bit sizes,
intermediate supports, live storage
and output size alongside elapsed time. Account for exact-division obligations.

Within a fixed schedule, compare eager polynomial normalization with shared
expressions and normalization on demand. Hold the requested output fixed:
report expanded-result and supplied-target experiments separately. This tests
whether repeated expansion, rather than elimination itself, is the main
symbolic obstruction.

### 3. Establish fixed-ring value performance independently

Start by attributing the existing dense ordinary-CRT/FLINT gap: bounds, prime
generation, modular images, elimination, reconstruction and external-call cost.
Then use small dense integer matrices and vary dimension and coefficient
bits independently. Compare the existing Bareiss, modular CRT and divisor value
routines before introducing storage or arithmetic variants, using FLINT as an
external reference. Include singular inputs and pivot swaps. Add rational and dyadic matrices derived from the same
integer matrices with exact scaling, recording scaling and normalization cost.
Test widely separated dyadic exponents as well as modest ones.

For polynomials, separate univariate degree, variable count, term support and
coefficient size. Compare a small evaluation/interpolation prototype against
direct arithmetic before implementing a general interpolation framework.
Finite fields and generic commutative rings must remain distinct capability
cases; exact division is not available uniformly.

### 4. Test certificates for the winning computations

Compare packed triangular identities, modular determinant certificates and
proof-producing arithmetic against the best complete baselines. Include
input identification, scaling, bounds, modulus proofs, quotation and all
auxiliary checks. A producer-only win is not sufficient for a tactic change.
Conversely, a useful computational improvement need not wait for a winning
proof backend before being considered for the value API.

## Measurement and decision rules

- Computational benchmarks import no Mathlib. Proof experiments are build-only
  fresh Lean modules, not Mathlib-importing benchmark executables. Mathlib
  determinant tactics (`norm_det`/`eval_det`) run only in an explicitly named
  comparison arm. Proof candidates may use Mathlib arithmetic lemmas and proof
  construction; computational libraries remain Mathlib-free.
- Begin each hypothesis with one input and two adjacent AB/BA diagnostic pairs.
  Expand to the small representative set only when the result warrants it.
  Use six adjacent pairs for a shipping claim, with matched import baselines.
- Use one serial measurement process and an automatically leased CPU where
  supported. Retain all completed samples and host context. No quiet-host
  waiting, memory caps, service-based monitoring or retry-until-win loops.
- Give a single measured invocation at most 60 seconds and an exploratory
  batch at most ten minutes. Maintain a cumulative session measurement budget
  below one hour; stop for a decision before approaching that limit.
- Predeclare monotone ladders within each family. After a timeout or resource
  exhaustion, skip all larger points in that ladder. Across independent axes,
  mark comparable larger parameter points as skipped too; unrelated families
  are separate decisions, not an automatic full Cartesian grid.
- Distinguish timeout, resource failure, unsupported input, exhausted budget,
  wrong answer and successful proof. No fallback success, no omitted checking
  component and no ratio between incompatible output contracts.
- Profile only to answer an unexpected result or a specific unresolved cost.
  Kernel performance must be measured with the actual proved checker; compiled
  evaluation of the checker is only a separate producer-side diagnostic.
- Every prototype theorem is fully checked: no `sorry`, `axiom` or
  `native_decide`. Allowed theorem dependencies remain `propext`,
  `Classical.choice` and `Quot.sound` only.

## SPEC questions before a replacement plan

The experiment results should determine which changes to propose in
`SPEC/matrix-tactics.md`, the `hex-det` dispatch contract, the computational
determinant/Bareiss/modular-matrix/polynomial SPECs, and their companions:

- Separate value, symbolic-result and supplied-equality contracts, including
  output representation and where normalization is charged.
- Replace a mandated producer/witness combination with explicit mathematical
  obligations and measured implementations, if the experiments justify it.
- Specify exact-division, field, coefficient and characteristic capabilities
  honestly; identify the required Mathlib-free correctness theorems and the
  companion transport, rather than hiding assumptions in a common interface.
- Define the proof payload and reuse boundaries from evidence. No existing
  transform format, term-list encoding, packing scheme or expression syntax
  receives privileged status merely because consumers already use it.
- Audit downstream consumers before deleting or changing a shared API. Keep
  independent reference definitions and correctness tests through migration;
  remove superseded production paths and shape strategies once replacements
  cover their justified uses. Do not accumulate permanent experimental routes.
- Set separate bars for computational speed, end-to-end proof speed and input
  coverage. State losses and unresolved regimes rather than promising universal
  superiority from a few favorable examples.

A replacement plan should follow those decisions, with theorem dependencies,
consumer migration and deletion scope made concrete. It should not precede the
experiments by choosing the architecture they are supposed to evaluate.
