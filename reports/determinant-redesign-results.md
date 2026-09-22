# Determinant redesign experiments

These are diagnostic experiments, not a production speedup claim or a
selected replacement architecture. The broader questions are in
[the design document](determinant-experiments.md).

## Fixed witness: arithmetic proofs

The input is the retained dense 4×4 matrix with quadratic entries in two
variables. `Determinant.Fixture` runs the existing Hex producer and extracts
its ten row-prefix product identities. The exact operands and results are
retained. Producer, witness and mathematical identities are held fixed.

- **Replay:** existing canonical-list dot products and equality checks,
  accepted by `decide +kernel`.
- **Independent:** Mathlib ring arithmetic, with a fresh atom context for
  each scalar equality.
- **Cached:** one atom context and expression-to-normal-form/proof cache
  across the conjunction. Addition and multiplication reuse the scalar
  arithmetic helpers used by Mathlib's Bird evaluator. No determinant
  evaluator is called.

Replay states Boolean list equalities; the other arms state the corresponding
universally quantified integer polynomial identities. These are equivalent
arithmetic obligations, **not the same complete determinant theorem**.
Replay receives canonical lists; arithmetic receives quoted expressions.
Input conversion and witness production are outside both arms' clocks.

Two adjacent AB/BA pairs were collected per comparison on `chungus2`.
Milliseconds below include tactic execution and the final kernel check.
Auxiliary checks inside the tactic are already inside its clock.

| Comparison | Arm | Tactic median | Final kernel median | Total proof work |
|---|---|---:|---:|---:|
| Replay / independent | Replay | 259.9 | <1 | [259.9, 260.9) |
| Replay / independent | Independent | 238.2 | 107.7 | 345.8 |
| Independent / cached | Independent | 209.9 | 73.4 | 283.3 |
| Independent / cached | Cached | 45.2 | 79.1 | 124.3 |

Every sample is retained. The difference between the two independent-arm
medians is visible rather than pooled away. Caching reduces construction cost
substantially here; it does not reduce the observed final kernel check
relative to the adjacent independent arm.

## Complete proof: the arithmetic win does not survive assembly

The original table below uses profiler-based component clocks. The synchronous
declaration experiment below supersedes it for whole-proof comparisons; its
metric includes statement elaboration and disables profiling.

`full.py` generates four separately checked lemmas from those same operands:

1. The ten identities, now over an arbitrary commutative ring.
2. Assembly of the existing semantic triangular witness, assuming its three
   nontrivial pivots are nonzero in a domain.
3. Specialization to `MvPolynomial (Fin 2) Int`, certifying nonzero pivots
   by evaluation at zero.
4. Evaluation into the user's commutative ring, including matrix entry
   identification and the supplied target.

The final theorem needs no domain hypothesis on the user's ring. Its axioms
are exactly `propext`, `Classical.choice`, and `Quot.sound`. Zero evaluation
certifies nonzeroness for this fixture; a general implementation must find
and certify a suitable evaluation or use coefficient nonzeroness.

The generator spells entries and the target in canonical term order. Both
production controls prove **that same generated statement**, over an abstract
commutative ring. This differs from the integer microbenchmark and from the
historical report's expression order. Absolute times are not comparable
across those experiments.

| Complete proof arm | Samples | Median proof work, ms |
|---|---:|---:|
| Explicit `norm_det` followed by `ring` | 2 | 171.7 |
| Production Hex `det` | 2 | [590.5, 591.5) |
| Cached witness prototype | 4 | 7042.0 |

There are two adjacent AB/BA pairs for Mathlib/prototype and another two for
Hex/prototype. Every prototype sample includes all four lemmas, with fresh
module kernel checks. No lemma is supplied free from an earlier measurement.

| Prototype component | Median tactic, ms | Median kernel, ms | Distinct proof nodes |
|---|---:|---:|---:|
| Generic arithmetic identities | 95.2 | 450.0 | 56,185 |
| Semantic witness assembly | 1182.1 | 31.8 | 22,109 |
| Polynomial model and nonzero pivots | 999.3 | 29.4 | 2,555 |
| Transport and entry identification | 4198.4 | 56.1 | 35,473 |

Component medians need not sum to the median total. Nodes are counted per
declaration; their sum is not a count after sharing across declarations.
Producer/source-generator costs are excluded, so end-to-end prototype cost
would be higher still. Statement elaboration, imports, serialization and Lake
overhead are excluded. External build observations are retained, but are not
presented as matched import-subtracted performance claims.

The prototype loses badly in this experiment. Profiling and declaration context
also affect component timings: the generic arithmetic lemma alone subsequently
measured about 128 ms, versus roughly 500 ms in this full-module profile. The
cause of that sensitivity has not been isolated. Do not infer a universal
kernel disadvantage for generic arithmetic from this table alone.

## Reuse boundaries and transport

Making repeated addition/multiplication certificates opaque, and checking each
auxiliary declaration, increased the isolated generic arithmetic proof from
128.7 ms to 338.1 ms. Its final outer check decreased slightly, but the extra
construction/checking more than consumed that saving. Reject blanket opacity
as the reuse policy. This is a negative result about this policy, not about
all possible proof sharing.

Four general lemmas about mapping matrix row constructors and composing
functions replace repeated `ext; fin_cases; simp` during the final transport.
They impose no determinant-specific matrix shape restriction. A first attempt
left a definitional matrix wrapper unsolved; that failed sample is retained.
The corrected proof closes it with `rfl`.

To avoid the profiler sensitivity, `#measure_decl` sets `Elab.async=false` and
`profiler=false` while elaborating one complete theorem command. Lean's
synchronous `addDecl` checks it before returning. Each sample sums all four
candidate commands, including statements, auxiliary declarations, transport
and every kernel check. Imports, parsing, witness production and Python source
generation remain outside. Production Hex includes its producer; the prototype
still receives a prepared witness. These are not complete tactic interface
measurements, and the prototype is disadvantaged further if its producer is
charged.

| Synchronous declaration experiment | Arm | Median total, ms |
|---|---|---:|
| Same witness and proof, transport comparison | Original transport | 4550.7 |
| Same witness and proof, transport comparison | Constructor transport | 1479.7 |
| Matched production controls | Explicit Mathlib | 287.4 |
| Matched production controls | Production Hex | 592.2 |
| Matched production controls | Constructor transport prototype | 1447.0 |

There are two AB/BA pairs per comparison. The final transport component alone
fell from about 3558 ms to 484 ms. The controls batch includes a short local
`Schedules` development build during its latter part; every sample and host
observation is retained. This does not justify deleting or rerunning samples.
The prototype still loses by a large margin and is not a candidate for shipping.
Retain the general transport idea; question the witness and arithmetic schedule.

## Compiled schedules and exact scaling

The native executable imports no Mathlib, as checked against Lake's transitive
import artifacts. Each case uses identical prepared coefficients and matrix
storage across arms. Bareiss is the existing pivoted exact-division routine;
Berkowitz is the existing characteristic-polynomial schedule, consuming just
the signed final coefficient. Bird is a new **eager** full-matrix recurrence.
It does not reproduce Mathlib's demand-driven evaluator. Internals of the
three schedules still differ in storage/allocation; these measurements hold
the public input and coefficient representation fixed, not every memory access.

The shared `Hex.Matrix` input is flat row-major storage. Bareiss converts to
its row arrays internally; a claim that all existing storage was row arrays
would be inaccurate. Polynomial arithmetic uses the same sparse `MvPoly`
representation for all three schedules.

| Input | Bareiss, ms | Eager Bird, ms | Berkowitz, ms | Scaled integer Bareiss, ms |
|---|---:|---:|---:|---:|
| Dense integer 16×16, signed 8-bit entries | 0.176 | 1.800 | 1.239 | — |
| Fixed quadratic polynomial 4×4, two variables | 0.429 | 0.443 | 0.277 | — |
| Rational 8×8, denominators 1 through 7 | 0.152 | 0.843 | 0.505 | 0.037 |
| Dyadic 8×8, requested precisions 0 through 7 | — | 0.305 | 0.192 | 0.037 |
| Dyadic 8×8, requested precisions 0,64,…,448 | — | 2.768 | 0.516 | 0.171 |

Each comparison has two adjacent AB/BA pairs. Repeated Bareiss/scaled controls
are pooled only for this compact table; raw pair membership remains available.
These sub-millisecond observations motivate experiments, not dispatch thresholds.
No point timed out and there was no ladder expansion after a timeout.

Rational scaling computes a row LCM from the actual reduced input denominators,
scales to integers, computes the determinant and normalizes the rational answer.
Dyadic scaling chooses each row's largest nonnegative precision, shifts its
mantissas to integers, then restores the sum of row precisions. All those steps
are timed. The wider-exponent case tests actual large shifts; it does not
establish safety or superiority for arbitrarily separated exponents.

Input generation and serialization are excluded for all native arms; output
arithmetic normalization is included. Independent validation uses FLINT exact
integer/rational determinants and a Leibniz polynomial reference with FLINT
arithmetic. These are producer prototypes with differential validation, not
new proved determinant algorithms. They make no kernel-speed claim.

An early clock implementation was inspected before collecting native samples:
the compiler had moved pure computation after the stop clock. Both ends now
use IO references, including storing the computed result before the stop.
Retained generated C shows the arithmetic call between the clock reads. The
small reference allocation is included. Merely reading an input reference is
not a sufficient timing barrier.

Decision: retain fraction-free integer computation as a control; investigate
exact scaling as a general coefficient adapter. Do not adopt eager Bird as a
universal value engine. The polynomial Berkowitz result warrants a controlled
proof/symbolic-representation comparison, not a conclusion that computing every
characteristic coefficient is intrinsically best.

## Dense modular gap

The ordinary CRT attribution uses the actual prefix of primes needed to exceed
twice the Hadamard bound. It separately clocks bound construction, the existing
trial-division prime supply, integer-to-residue conversion, existing modular
elimination and CRT pushes. All answers match FLINT and the uninstrumented
ordinary route. No modular or divisor failure is hidden by a Bareiss fallback.

| Dense signed 8-bit input | Bareiss, ms | Ordinary CRT, ms | Divisor route, ms | FLINT determinant, ms |
|---|---:|---:|---:|---:|
| 32×32 | 1.87 | 32.29 | 11.04 | about 0.15 |
| 128×128 | 173.96 | 1513.73 | 381.00 | about 4.60 |

FLINT runs explicitly after each native sample on the identical serialized
input; matrix conversion is outside its determinant clock. These are diagnostic
in-process FLINT timings, not an adjacent native/FLINT shipping comparison or
an external bridge latency measurement. The first 32×32 FLINT observation was
0.907 ms and is retained along with all subsequent observations.

| Ordinary CRT stage | 32×32, ms | 128×128, ms |
|---|---:|---:|
| Hadamard bound | 0.037 | 0.438 |
| Prime supply | 25.76 | 95.42 |
| Matrix reduction | 0.594 | 39.38 |
| Modular elimination | 6.11 | 1378.22 |
| Reconstruction | 0.018 | 0.089 |

The smaller case uses 10 of 11 supplied primes; the larger uses 41 of 43.
Neither rejects an image. Prime generation dominates the smaller case, but
elimination explains about 91% of the larger total. Bound/CRT optimizations
alone cannot close this gap.

A second matched 128×128 comparison substitutes the existing Dixon `flatDet?`
elimination for the recursive trailing-minor implementation, keeping primes,
coefficient arithmetic and the CRT pipeline fixed. Elimination changes from
1407 ms to 1336 ms: a modest saving, not a solution. `flatDet?` can decline on
singular inputs; it is not a drop-in replacement for the ordinary image API.

For the **same 41 primes and same matrix**, FLINT's modular determinant calls
total about 15.2 ms. Every residue is checked against the integer determinant.
This removes prime generation, CRT, integer algorithm selection and input
conversion from that comparison, while still allowing the two modular
implementations to use different elimination schedules and physical storage.
FLINT matrix construction/reduction costs roughly 55–58 ms through Python and
is recorded separately; it is not a native conversion implementation comparison.

Decision: investigate the modular elimination implementation and its memory/
arithmetic costs before designing another integer dispatcher. Neither prime
caching alone nor replacing recursive minors with existing flat elimination
explains the roughly 90-fold modular-elimination gap. The next discriminating
prototype should hold one modulus fixed and compare an owned trailing-block
update loop with the existing word row-update routines.

## Failures, protocol and verification

Initial generated statements left literal exponent types implicit. Two builds
hit the 60-second ceiling; each batch stopped immediately. A bounded diagnostic
then failed in `synthesize pending MVars`, before the tactic, with extensive
`HPow`/`HAdd` inference. Explicit `Nat` exponent annotations allowed completion.
These are harness failures, not mathematical proof-method failures.

Profiler threshold zero was also replaced with 1 ms. A single-identity
diagnostic changed both heartbeat/profiler settings, so it did not isolate
profiling as the cause. Below-threshold kernel checks are reported as
intervals, never silently as zero cost.

All batches are serial, automatically CPU-leased, limited to 60 seconds per
build and four minutes per batch. The measurement ledger records every batch, including failed ones, and
separates differential validation from performance runs. Small development/
diagnostic builds are retained separately. No larger input followed a timeout, no memory cap
was imposed, and no background service or CI monitor was installed.

The fixture producer is Mathlib-free. Proof experiments are build-only Lean
modules. `Determinant.Audit` builds successfully, checks the complete theorem's
axioms, counts proof nodes, and tests generic-ring arithmetic and rejection
of unequal normal forms. Python generators pass syntax compilation. The computational boundary checks
cover empty and one-entry matrices, singular inputs and a forced initial pivot
swap over integers, rationals and dyadics, with exact external answers.

[Raw sources, samples, errors, host context and hashes](bench-results/determinant-redesign/)
and [reproduction commands](../experiments/Determinant/README.md) are retained.

## Open experiments before an architecture recommendation

The fixed witness still loses, and value-only schedule results do not settle
proof architecture. Outstanding work includes common-checker schedule proofs,
eager versus shared/on-demand symbolic normalization with supplied-target
checking, and the owned modular-update experiment suggested above. Polynomial
representation and interpolation hypotheses also need discriminating evidence.
The final SPEC proposals and staged consumer migration/deletion plan depend on
those results. No production replacement or dispatch threshold is selected.
