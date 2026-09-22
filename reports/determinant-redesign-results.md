# Determinant redesign experiments

These diagnostic experiments support the [architecture proposal and staged
replacement plan](determinant-redesign-proposal.md). They do not establish
production dispatch thresholds or universal superiority. The broader questions are in
[the design document](determinant-experiments.md).

The [adversarial search](determinant-adversarial-search.md) extends the initial
four-case shared-proof comparison. It finds losses with Mathlib below one
minute, including prototype timeouts. Those results constrain the normalization
policy; the initial wins do not establish a production architecture.

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

This table used the integer-specific support module retained in
[`arithmetic-typed/Arithmetic.lean.txt`](bench-results/determinant-redesign/arithmetic-typed/Arithmetic.lean.txt).
The working `Arithmetic.lean` now synthesizes arbitrary commutative-ring
instances. Reproducing this exact implementation requires the archived source;
the README commands exercise the generalized version.

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
three schedules still differ in storage/allocation: the eager Bird prototype
allocates `List.range` during every entry's diagonal sum and performs dynamic
bounds checks for entry access. These measurements hold
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
This descriptive summary is not used for paired speedup claims. For example,
all six rational Bareiss observations lie between 0.149 and 0.156 ms. The proof
table keeps comparator groups separate because their variation is substantial.
Native timings are one cold call per fresh process; confirm these small costs
with in-process repetitions before implementing a selection policy.
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
exact scaling as a general coefficient adapter. Do not pursue this eager Bird
value implementation; its allocation/access confounds preclude rejecting the
schedule itself. The polynomial Berkowitz result warrants a controlled
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
explains the roughly 90-fold modular-elimination gap. The owned-loop and C experiments below test that implementation hypothesis
without changing the determinant algorithm.

## Shared symbolic expressions and supplied targets

`Deferred.lean` adapts Mathlib's demand-driven Bird recurrence and its theorem
applications. It caches the recurrence's entry, diagonal and iterate expressions,
but does not normalize every scalar operation while constructing the recurrence.
It then proves equality of the resulting expression with the **supplied target**:

- **Deferred:** ordinary ring normalization traverses that expression.
- **Shared:** the expression cache from `Arithmetic.lean` normalizes repeated
  arithmetic subexpressions once, in the same atom context as the target.

Both construct ordinary kernel-checked proofs. Neither calls a determinant
tactic, invokes a fallback, assumes a domain, or assumes symbolic pivots nonzero.
The final proof uses Bird's universal correctness theorem directly. The
computational experiment remains Mathlib-free; these are companion proof modules.
The adaptation retains Mathlib's copyright and identifies the source it adapts.

On the quadratic 4×4 statement, deferred traversal takes 726 ms against the
adjacent Mathlib control's 372 ms. In the separate deferred/shared pair it takes
701 ms against 303 ms. Merely delaying expansion loses; retaining and using
sharing during normalization changes that result. This comparison holds the
recurrence and target fixed. Compared with Mathlib, syntactic-zero detection
also differs from eager normal-form zero detection, so it is not an isolation
of cache lookup cost alone.

Direct paired comparisons use the synchronous complete-declaration clock.
Each table cell gives median [minimum, maximum] in milliseconds for its own
two AB/BA samples, rounded to whole milliseconds; these are observed ranges,
not confidence intervals. Candidate samples from different comparator pairs
are deliberately **not pooled**.

| Input and supplied target | Mathlib, ms | Shared alongside Mathlib, ms | Production Hex, ms | Shared alongside Hex, ms |
|---|---:|---:|---:|---:|
| Dense quadratic 4×4, two variables; expanded target | 288 [287, 289] | 218 [218, 219] | 757 [599, 916] | 240 [211, 270] |
| Independent-variable 4×4; expanded target | 158 [157, 159] | 88 [88, 88] | 347 [346, 349] | 88 [88, 88] |
| Dense linear 6×6, two variables; expanded target | 5020 [4935, 5105] | 3312 [3270, 3354] | 5287 [4645, 5929] | 3477 [3216, 3738] |
| Quadratic 4×4 multiplied entrywise by a third variable; factored target | 453 [423, 483] | 580 [448, 712] | 1148 [950, 1345] | 364 [316, 412] |

The last input supplies `z^4 * d(x0,x1)`; every algorithm receives the same
factored target. Its shared/Mathlib pairs disagree: 711.7 versus 423.4 ms in
one pair, 447.5 versus 482.6 ms in the other. Record this as a median loss with
substantial observed variation, not a win obtained by pooling the later Hex
comparison. No sample was discarded and no unchanged rerun was made.

The 6×6 fixture uses deterministic small integer coefficients; its expanded
target is generated independently with FLINT arithmetic and the Leibniz sum.
All target generation is outside every arm's clock. All determinant/proof
construction, literal identification, target equality and kernel checking are
inside. Source snapshots contain the exact statements, including the target.
The prototype is not given normalized matrix entries or a determinant witness
for free. These clocks include statement elaboration; they are not the original
issue's profiler-only kernel component measurements.

The result selects shared proof-producing arithmetic and a division-free
recurrence as the symbolic implementation direction. It does **not** establish
that Bird is the optimal proof schedule or that a circuit should replace every
value representation. Bareiss/Bird/Berkowitz were controlled under the same
coefficient representations and external checking in the value experiment;
there is no claimed common-checker theorem proving a complete proof-speed
ranking of all three. That remaining ranking is not needed to reject the fixed
triangular-witness prototype or select this better-supported candidate.

## Modular execution: storage alone is insufficient

An owned Lean flat-array loop keeps `ZMod64` arithmetic and only updates the
trailing block. At 128×128 its complete staged CRT call takes 1712 ms versus
1510 ms for the adjacent existing-flat control. Reject that implementation.
A second version hoists the modulus and uses raw `UInt64` arithmetic with the
same loop: 1615 ms versus 1691 ms for its adjacent owned-residue control. This
small saving does not explain the modular gap.

A separate C diagnostic implements that scalar elimination in contiguous
unboxed words. It uses the same matrix and 41 recorded primes, reduces after
every scalar multiplication, handles row pivoting and sign, and copies input
inside each measured call. It does not use blocking or delayed modular reduction.
Two adjacent C/FLINT AB/BA pairs total **47.76 ms versus 15.30 ms** across those
41 images. Conversion from integers to each library's input format precedes
the clocks; Python/ctypes call overhead remains in the C clock. FLINT's internal
copying is whatever its public determinant operation performs.

This is strong evidence that a faster determinant algorithm is not necessary
to remove most of Hex's current modular gap. It implicates the bundle of
allocation, boxing, generated control flow and call overhead in the Lean
implementation; it does not separately quantify each cause. The C experiment
is not an implementation of a Lean theorem, an FFI linked into Hex, or evidence
of faster kernel checking. It cannot be installed as a trusted native proof
checker. Its role is to justify developing/refining an unboxed execution kernel.

## Univariate representation and interpolation

Use the same 4×4 coefficient triples as the quadratic fixture, interpreting each
entry as `c + b*x + a*x^2`. Compare sparse `MvPoly 1 Int` Bareiss, dense
`DensePoly Int` Bareiss, and evaluation at nine integer points followed by
rational Lagrange interpolation. The last route includes matrix evaluations,
nine integer determinants, interpolation, integrality checking and final
normalization. The degree-eight bound is specific to this fixture. This is a
cold elementary interpolation prototype, not the existing fast multipoint
plan, modular interpolation, or a general interpolation implementation.

| Adjacent comparison | Arm | Median, ms |
|---|---|---:|
| Sparse / dense | Sparse Bareiss | 0.216 |
| Sparse / dense | Dense Bareiss | 0.031 |
| Dense / interpolation | Dense Bareiss | 0.028 |
| Dense / interpolation | Evaluation/interpolation | 0.356 |

All arms return normalized dense integer coefficients; sparse-to-dense output
conversion is timed. Preparing their different input representations is outside
the clocks, deliberately isolating arithmetic on an already represented input.
Every coefficient matches the independent FLINT/Leibniz reference, not just
some evaluation points. Dense arithmetic wins this small low-degree experiment.
It does not establish a representation threshold at large degree or support,
and the interpolation loss does not rule out fast plans at a larger crossover.
Do not build a general interpolation framework on the strength of this result.

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
invocation and at most four minutes per batch (the C diagnostic and validation
runners use a stricter one-minute batch limit). The measurement ledger records
every batch, including failed ones, and
separates differential validation from performance runs. Small development/
diagnostic builds are retained separately. No larger input followed a timeout, no memory cap
was imposed, and no background monitoring service was installed.

The fixture producer is Mathlib-free. Proof experiments are build-only Lean
modules. `Determinant.Audit` builds successfully, checks the complete theorem's
axioms, counts proof nodes, and tests generic-ring arithmetic and rejection
of unequal normal forms. `DeferredAudit` additionally checks both expression
strategies and rejection of a wrong determinant target. Python generators pass syntax compilation. The 46 computational boundary checks
cover empty and one-entry matrices, singular inputs and a forced initial pivot
swap over integers, rationals and dyadics, with exact external answers. The C diagnostic passes 21 differential checks
with UBSan. Its first validation attempt failed to load the sanitizer runtime
before executing numerical checks; the corrected loader and both outcomes
are retained. Total performance-batch wall time is about **558 seconds**
(9 minutes 18 seconds), including failed measurement attempts.

[Raw sources, samples, errors, host context and hashes](bench-results/determinant-redesign/)
and [reproduction commands](../experiments/Determinant/README.md) are retained.

## Decision and limits

The [proposal](determinant-redesign-proposal.md) gives concrete SPEC text and
staged implementation, migration and deletion gates. Retain the reference
algebra, integer Bareiss control and numeric certificates. Develop shared
algebraic proofs for symbolic equalities, exact fixed-ring scaling, and a
refined native modular loop. Reject blanket opaque arithmetic, the losing
owned-loop versions, and cold small-degree interpolation as default choices.

These experiments cover the four redesign questions with bounded tests; they
do not promise the fastest algorithm for every ring, characteristic, dimension
or expression. Full API coverage, proof budgets, shipping-quality six-pair
measurements and production refinements belong to the proposed implementation
stages. No production code or dispatch was replaced by this experimental work.
