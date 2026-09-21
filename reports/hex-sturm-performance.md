# Shared Sturm–Tarski computation measurements

Phase 4 remains incomplete. Nine of thirteen two-sided registrations passed
initially. The single unchanged rerun retained four unresolved registrations;
the wider-ladder investigation below tests a larger coefficient regime and
does not discharge those four original findings. All completed samples are retained, The original query declarations are retained alongside the corrected
[bit-cost derivations](sturm-bit-cost-models.md) and their fresh validation. The observations cover the implemented query/checker paths, not the
missing root-sum theorem or downstream extension infrastructure.

## Protocol and provenance

[Raw results and fixtures](bench-results/sturm-ec8f7c14f914/) were collected from
`ec8f7c14f91432f97ac130595bce7600e41c1562` on `chungus2`, AMD EPYC 9455,
Lean 4.34.0, with lean-bench 0.1.0. The executable and registration source SHA256,
CPU affinity, load observations, exact commands and start/end times are in
[metadata.json](bench-results/sturm-ec8f7c14f914/metadata.json). CPU 1 was selected
automatically for placement. Host activity does not invalidate samples.
Reported `git_dirty` includes newly written evidence and subsequently added
proof-probe sources; neither changed the measured executable. Its hash is
recorded independently. The exact measured registration source is retained as
`registration.lean.txt`, whose SHA256 matches the metadata. The current benchmark
source adds separate axis diagnostics and observations; the original measured
functions are retained; declaration snapshots preserve each measured registration. The wider runs record explicit
schedule overrides and separate source/executable hashes. The executable SHA256 is
identical across the initial run and the unchanged rerun.
No absolute timing is a portable budget.

Each complexity registration used its declared custom ladder, four trial-major
outer trials, a 100 ms tuning target and a three-second operational cap. All
registrations use mode 1 (two-sided parametric). The source derivations precede
measurement: normal Chebyshev derivative chains have one degree drop per step,
so the summed dense work is quadratic; with a fixed quadratic head, the dynamic
pseudo-division recurrence has at most two correction summands per output
coefficient, so increasing query degree gives linear coefficient-operation work.
These are family-specific models within the SPEC bounds, not uniform integer
bit-complexity bounds. The recorded certificate bit sizes do not bound
intermediate products or imply unboxed arithmetic.

The head-degree ladder is `8,10,12,16,20`, with `P=T_n`, `F=1` and endpoints
`(-2,2)`. The query-degree ladder is `16,24,32,48,64,96`, with `P=x²-2` and
`F=x^m+1` on the same interval. Preparation occurs outside timed bodies.
`inspect` verifies both backends and both replay checkers; independent pinned
python-flint 0.9.0 / FLINT 3.6.0 exact qqbar root sums agree on all eleven inputs.
Hashes consume the actual outputs, including coefficients and certificate
scalars where the stage returns a certificate hash.

## Results

Final-rung times are medians in microseconds. The harness omits a fitted slope
when the retained log-parameter span is less than one. For the head-degree
ladder, trimming degree 8 leaves `log(20/10) < 1`, so its verdict uses the
normalized-time range check, not a fitted slope.

| Registration | Declared model | Verdict | Final parameter | Median µs |
| --- | --- | --- | --- | --- |
| `runInteger` | `n ^ 2` | consistent | 20 | 150.455 |
| `runRational` | `n ^ 2` | consistent | 20 | 521.003 |
| `runDomain` | `n ^ 2` | consistent | 20 | 216.526 |
| `runInitial` | `n` | consistent | 20 | 0.470 |
| `runChain` | `n ^ 2` | consistent | 20 | 62.006 |
| `runEndpoints` | `n ^ 2` | consistent | 20 | 25.480 |
| `runSigns` | `n ^ 2` | consistent | 20 | 1.479 |
| `runReplay` | `n ^ 2` | inconclusive | 20 | 105.478 |
| `runClearing` | `n` | consistent | 20 | 5.816 |
| `runIntegerHigh` | `m` | inconclusive | 96 | 15.696 |
| `runRationalHigh` | `m` | consistent | 96 | 187.907 |
| `runInitialHigh` | `m` | inconclusive | 96 | 13.005 |
| `runReplayHigh` | `m` | inconclusive | 96 | 14.585 |

The inconclusive cases are `runReplay`, `runIntegerHigh`, `runInitialHigh` and
`runReplayHigh`. The latter three have residual slopes −0.173, +0.280 and −0.202,
respectively. A faster-than-declared two-sided result is also a failed
characterization. These original results do not satisfy the performance obligation. The
frontend remains at `done_through: 0`. The correction below distinguishes
scalar-operation counts from bit costs; no fixed budget replaces the
parametric models.

### Investigation of the inconclusive results

[The single unchanged rerun](bench-results/sturm-repeat-ff2086080/) uses the
same executable SHA256 and registration settings as the initial run, with a
new automatically leased CPU and retained host observations. The residual
slopes for `runIntegerHigh`, `runInitialHigh` and `runReplayHigh` were
−0.212, +0.267 and −0.212: all remain inconclusive. `runReplay` passed the
range check on this run, with normalized times spanning 321.563–480.641,
against 168.685–263.694 initially. The mixed result leaves replay unresolved;
neither run supersedes the other. No further unchanged rerun is permitted.

The runtime threshold is concrete: Lean 4.34.0's `include/lean/lean.h` defines
`LEAN_MAX_SMALL_INT` as `INT_MAX` on this 64-bit host, namely 2³¹−1.
`lean_int_mul` uses `lean_int64_to_int` for scalar operands and calls the big
integer path for boxed operands. A 50-bit stored coefficient is therefore
already outside the small-integer range. This agrees with the retained GMP
profiles; it does not identify every allocation's cause.

[Certificate diagnostics](bench-results/sturm-repeat-ff2086080/diagnostics.json),
reproducible with the adjacent `analyze.py`, show replay identity products of
31, 42 and 57 bits at head degrees 12, 16 and 20. Stored query-degree
coefficients reach 26, 34 and 50 bits at query degrees 48, 64 and 96. Only
degrees 64 and 96 cross the small-integer threshold. These inspect explicit certificate operands and
products, not peak producer intermediates. The near-flat initial-reduction
normalized times before the threshold and their rise afterward support a
representation-cost explanation. Fixed domain/replay overhead also weighs
more heavily at small query degrees. Their individual contributions remain
unquantified: the coefficient-operation models alone do not establish the
wall-time characterizations on these mixed arithmetic regimes.

The separate fixed-field pseudo-gcd gap is resolved by the wider degree
ladder, with the same quadratic model and all original rungs retained; see
[the polynomial report](hex-poly-performance.md#concerns). Across the fifteen
new registrations, eleven now have consistent characterizations and four
query registrations remain unresolved. No existing library phase is changed.

Stored certificate sizes rise from 959 to 3506 bytes on the head-degree ladder
and 496 to 1152 bytes on the query-degree ladder. Maximum stored integer
coefficient/scalar lengths range from 13 to 37 bits and 10 to 50 bits,
respectively. Rational certificate maxima range from 11 to 24 bits and 10 to
50 bits. These are serialized-certificate observations, not peak live-memory
or peak intermediate-coefficient measurements.

## Adjacent backend comparison

For each family, four fixed blocks alternate integer/rational and
rational/integer order. Each arm runs the full ladder with one outer trial.
All output hashes agree at every common parameter. Every arm and its emitted
verdict is retained; this comparison is separate from the four-trial complexity
measurement above.

Median paired rational/integer ratios at degrees `8,10,12,16,20` are
`5.37,5.30,5.21,4.23,3.44`. At query degrees `16,24,32,48,64,96` they are
`9.74,11.31,12.44,14.35,14.56,11.92`. Thus the integer backend is faster on these
inputs on this host; this is neither an asymptotic result nor a claim about
other coefficient domains. FLINT supplies an independent correctness oracle;
no external root-isolation timing is substituted for a Tarski query comparison.

## Profiles and interpretation

The retained initial whole-process profiles are diagnostic only. The subsequent
profiles use `perf record --clockid mono -F 1999 -g --call-graph dwarf` and
`LEAN_BENCH_TIMED_REGIONS_SIDECAR`. Flat samples are restricted to the child PID
and the union of lean-bench's operation-only monotonic-clock regions. Compressed
raw sample text and all region boundaries are retained, along with commands and
period-weighted exclusive-symbol summaries. Kernel symbol restrictions affect
unresolved kernel samples; no system profiling settings were changed.

For the degree-20 integer query, 612 of 713 samples lie in operation regions.
Trailing-zero arithmetic accounts for 9.44% of sampled event periods,
`malloc`/`free` for 12.91%, and GMP allocation and arithmetic are prominent.
For initial reduction at query degree 96, 877 of 1022 samples lie in operation
regions; the leading pseudo-division recurrence accounts for 9.49%, with GMP
initialization, reference counting, multiplication and array/list construction
also visible. This confirms that stored certificate sizes alone do not justify
a flat unboxed-coefficient cost assumption. The profiles identify actual work
but do not, by themselves, settle all four scaling failures.

The separately timed stored-coefficient sign pass takes 1.479 µs at head degree
20, compared with 62.006 µs for query-chain production and 25.480 µs for endpoint
sign evaluation. These stage observations are not additive decomposition of
the full query: preparation, repeated squarefree/query chains, hashing and
allocation differ. Expensive extension sign-oracle attribution is still absent.

## Fresh conformance-module evidence

[The retained fresh-module run](bench-results/hex-sturm-mathlib-fe5bcdd77.json)
uses the existing `HexConformance` target and four adjacent, alternating AB/BA
pairs per case on automatically selected CPU 3. The runner is
`scripts/bench/sturm_mathlib_sweep.py --shared-host --cpu 3 --samples 4`.
Every candidate rebuild printed only `propext`, `Classical.choice` and
`Quot.sound`; compiler output and artifact sizes are retained. The source hashes
remained unchanged during that run. The later shared-fixture and axiom-guard
changes are measured separately below. All completed samples, including
concurrent host activity, are included.

The acceptance/domain module's median fresh build was 5282.507 ms against
4547.418 ms for its import-only baseline; the median paired difference was
707.062 ms. The rejection/stale-context module's corresponding values were
5252.537 ms, 5030.121 ms and 696.988 ms. These are whole fresh-build observations,
not isolated kernel instruction timings or an absolute performance budget.
The harness labels the differences `no-comparable-control`; no statistically
resolved incremental-cost claim follows. No mandatory null-control protocol or
retry was added.

A second [retained run](bench-results/hex-sturm-mathlib-review.json) measures
commit `b45ddb679857d700064cea9b5407d333a93b702b`, where the literal fixture is
shared by computational conformance and replay modules and axiom sets are also
guarded during CI. It used the same four-pair schedule on automatically selected
CPU 29, from a clean checkout. Acceptance medians were 1928.923 ms candidate,
1806.857 ms baseline and 121.133 ms paired difference; rejection medians were
1928.106 ms, 1801.859 ms and 121.284 ms. Every sample and compiler output is
retained, with the same standard axiom set and `no-comparable-control` result.
The source and dependency hashes identify the measured revision; subsequent
rational-domain correspondence and frontend value/binding theorems are not part
of this measured import graph. The current companion umbrella reaches `Mathlib` through the pre-existing
`HexRealRootsMathlib.ChainCorrespond` import. Those two runs do not measure that
expanded import closure: both report 1984 build jobs. Equal job counts do not
identify identical source graphs or isolate timing causes. These are separate
source snapshots without a controlled comparison; the absolute timing difference
is not attributed to a source change or claimed as an improvement.

A [fresh run at `8a578a437`](bench-results/hex-sturm-mathlib-8a578a437.json)
measures the expanded import closure: 9246 build jobs, with four adjacent
alternating AB/BA pairs for each case on automatically leased CPU 45. The
checkout was clean and all completed samples were retained. Acceptance medians
were 7011.628 ms candidate, 6737.628 ms baseline and
278.697 ms paired difference; rejection medians were 6992.222 ms,
6735.845 ms and 264.191 ms, respectively. Each candidate's
printed axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`.
Both results retain the harness's `no-comparable-control` classification.
These measure the existing checker/domain proof modules with the current
imports, not elaboration of the new universal transport/congruence proofs or
root-sum semantics. The separate source snapshots do not form a controlled
before/after comparison or support a regression/improvement claim.

## Independent size axes and wider-ladder investigation

The [retained axis run](bench-results/sturm-axes/metadata.json) contains eighteen
exact fixtures, four fixed trial-major observations per fixture and stage, and
32 calls per observation. Integer/rational arms are adjacent and alternate
AB/BA. Rational domain preparation, initial reduction, chain production, endpoint
Horner evaluation, coefficient signs and replay are recorded separately. These
are descriptive fixed-workload timings, not additional fitted asymptotic
verdicts. The CPU is leased automatically; source snapshots, executable hashes,
load observations and every completed sample are retained. Preparation occurs
outside measured calls; results are consumed through an IO reference.

The coefficient-size family keeps degrees `(2,1)`, endpoints `(-2,2)` and chain
length three fixed, using `P=(2^b+1)X²-2`, `F=X+1`, `b=8,32,128,512,2048`.
The endpoint-size family keeps `P=T_8`, `F=1`, and its nine-entry chain fixed,
with endpoints `±2^b`, `b=2,8,32,128,512`. The chain family fixes head degree
32 and query degree 40, using `P=X^32-1` and `F=P*X^8+X*T_k`. Varying
`k=1,2,4,8,12,16,24,30` produces chain lengths `3,3,4,6,8,10,14,17`.
The latter holds degrees fixed, but does not claim to hold coefficient sizes
fixed. All eighteen serialized certificates and query sums passed the pinned
python-flint 0.9.0 / FLINT 3.6.0 oracle.

| Axis endpoints | Integer query µs | Rational query µs | Integer replay µs | Certificate bytes |
| --- | ---: | ---: | ---: | ---: |
| Coefficient parameter 8 → 2048 | 3.478 → 480.749 | 17.029 → 37.387 | 2.869 → 469.035 | 463 → 10903 |
| Endpoint parameter 2 → 512 | 20.331 → 29.240 | 105.336 → 155.638 | 13.196 → 22.137 | 959 → 963 |
| Chain length 3 → 17 | 37.644 → 618.361 | 723.325 → 1980.143 | 34.461 → 552.423 | 951 → 16294 |

Medians are over the four retained observations. Integer endpoint evaluation
alone grows from 0.440 to 456.973 µs across the coefficient-size family: a
fixed number of polynomial operations does not make these arithmetic calls
constant-time. This observation is not a measured regression against an older
implementation.

The coefficient family deliberately remains as adversarial evidence: its query
chain has the linear entry `2+(2^b+1)X`, whose value at `-2` is `-2^(b+1)`.
Production dyadic Horner normalizes this cancellation. Lean 4.34.0's
`Init/Data/Dyadic/Basic.lean` implements `Int.trailingZeros` by repeated remainder
and division by two, and `Dyadic.ofIntWithPrec` invokes it to remove the power
of two. This is extra dyadic-normalization work that the integer-Horner
operation counters below do not observe. The growth should not be attributed
to coefficient multiplication costs alone or read as a general integer-versus-
rational comparison.

A separately retained [control run](bench-results/sturm-coefficient-control/metadata.json)
changes only the query to `X+2`, leaving the head, endpoints and degree sizes
fixed. Its linear chain entry is `1+(2^b+1)X`, with odd endpoint values, so the
large trailing-zero cancellation is absent. All five new control fixtures pass
the same exact FLINT oracle. At parameters 8 and 2048 respectively, integer
query medians are 3.278 and 16.925 µs, integer endpoint medians 0.454 and
3.088 µs, and rational-query medians 16.721 and 37.909 µs. The production chain
stage is 1.427 and 11.942 µs. The comparison with the original endpoint median
456.973 µs at 2048 supports the specific normalization attribution. These are
separate fixed-workload observations, not an adjacent before/after code-change
comparison. Every original sample is retained; no complexity verdict follows
from the control.

Untimed instrumentation instantiates the **existing** generic producer and
checker with counted integer operations. It delegates content normalization to
`ZPoly.normalizeContent`, checks the resulting entries and value against the
production integer backend, and runs the actual checker. It adds no polynomial
or Tarski recurrence. Counts cover executed scalar add/sub/mul/neg/sign calls;
peak bit length covers their integer operands/results and normalization inputs.
Endpoint counts use integer Horner at the integral endpoints, whereas timed
integer calls use the production dyadic evaluator. GMP internal temporary
storage and instruction counts are not measured. Normalization coefficients
and bit-volume count the two source-level content folds per normalization call;
they describe gcd input work, not Euclidean iterations or an allocation count.
Instrumented timings are not used as performance samples.

On the coefficient-size family the producer performs 30 additions, 76
multiplications and 15 subtractions throughout, while peak integer bits grow
18 → 4098. On the endpoint family these counts also stay fixed while peak bits
grow 23 → 4103. On the chain family, normalization calls grow 4 → 18, content
fold coefficient visits 72 → 578, and summed input bit-volume 28 → 100986.
This separates the polynomial-operation count from the coefficient costs.

The wider timing schedules retain the original models, four trials, tuning
settings and all samples. They are schedule extensions, not another unchanged
rerun. Head-degree replay uses `8,16,32,64,128`; query-degree stages use
`16,32,64,128,256,512,1024`.

| Registration | Model | Wider verdict | Residual slope |
| --- | --- | --- | ---: |
| `runReplay` | `n²` | inconclusive | +1.399794 |
| `runIntegerHigh` | `m` | inconclusive | +0.163958 |
| `runInitialHigh` | `m` | inconclusive | +0.431976 |
| `runReplayHigh` | `m` | consistent | +0.111655 |

The wider replay-of-high-query result is consistent on that measured range,
but does not resolve its earlier in-range failures. These schedules exceed
the original stored-coefficient bounds (the original inspector caps 60 bits);
the larger bit lengths above are a different arithmetic regime. All four
original findings remain open. The three wider failures show that extending
the unit-cost wall-time models into this regime does not repair them.
The [degree diagnostics](bench-results/sturm-axes/degree-diagnostics.jsonl)
record quadratic growth of counted head-family ring work and linear growth
of query-family ring work while operand sizes grow: replay multiplications
are 460 → 84100 at head degrees 8 → 128, with peak bits 17 → 405;
query producer multiplications are 225 → 10305 at query degrees 16 → 1024,
with peak bits 10 → 514. These counts support the stated **ring-operation**
bounds, not the stronger wall-time models used in those registrations.

The degree diagnostics were collected separately with executable hash
`5dc52b…`, while the original axis timings used `ae0869…`; the full hashes and
the two exact source snapshots are retained separately. The diagnostic-only
command was added between them. Its original collection timestamp was not
recorded and is explicitly unknown; a source SHA256 was subsequently computed
from the retained snapshot. The runner collects axes and diagnostics together; historical timing commands
are retained with their original registration snapshots. The current corrected
registrations do not reproduce the old verdicts merely by reusing their ladders.
The control run was generated by its `--control-only` path and records full
start/end provenance.

These failures remain recorded as failures of their original declarations.
The independently derived correction below accounts for variable-size integer
arithmetic and dyadic normalization. No coefficient-operation bound, oracle
agreement or fresh-module proof measurement by itself validates wall-time scaling.

## Remaining validation gates

The separate fresh-module proof track checks literal acceptance, rejection of a
false terminal identity, stale-context rejection and interpretation of the
accepted domain. It cannot establish query root-sum semantics before the actual
IVT/Rolle and signed-remainder/Cauchy-index foundation is delivered.

The independent size sweeps and operation/normalization diagnostics above are
available. Four original declared wall-time characterizations remain unresolved. Concrete
extension-depth and nested-evidence probes belong downstream under #10376/#10378;
general root-sum/replay soundness and its executable singleton/sign/bound
consequences belong to #10389. The integer query-one finite/whole-line counts
and rational finite-dyadic specialization are proved using the existing real
Sturm theorem; only the arbitrary-field count wrapper remains deferred. Whole-`Option` field-representation and
rational/integer agreement, and literal certificate transport, are proved in
the companion; these timing observations do not discharge those proofs.
The [recorded finding](https://github.com/kim-em/hex-dev/issues/10375#issuecomment-5757400442)
also records the original polynomial pseudo-gcd finding; its wider-ladder
resolution is documented in the polynomial report.
Nothing in these measurements advances the library phase or closes #10375.

The exact benchmark fixtures can be checked again with the pinned oracle
environment using `python scripts/bench/check_sturm_fixtures.py` followed by
the corresponding `fixtures.jsonl` paths above. Query checks include every
serialized chain identity and endpoint sign. Deliberately corrupted query
identities/signs and polynomial multipliers/quotients/gcds are rejected.
