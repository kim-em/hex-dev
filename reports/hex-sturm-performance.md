# Shared Sturm–Tarski computation measurements

The corrected quadratic query-degree models pass for initial reduction,
integer and rational queries, and replay. Head-degree replay now defers dyadic
normalization to the end of each Horner evaluation, with proved equality to
its former result. Its predeclared **mode-2 O(n⁴) upper bound passes (observed
faster)** through degree 2048. This is explicitly weaker than two-sided
consistency: GMP multiplication crossovers prevent a justified tight monomial
claim on this ladder. The earlier cubic and quartic two-sided failures remain
recorded below. [The derivations](sturm-bit-cost-models.md) distinguish the
former repeated-normalization cost from the implemented recurrence products.

All earlier declarations, failures and samples are retained. These observations
cover effective query/checker paths. They do not complete the companions'
Phase 4, the general signed-root-sum theorem or downstream extension evidence.

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

| Registration | Original declared model | Original verdict and regime | Final parameter | Median µs |
| --- | --- | --- | --- | --- |
| `runInteger` | `n ^ 2` | consistent, bounded-coefficient n=8–20 | 20 | 150.455 |
| `runRational` | `n ^ 2` | consistent, bounded-coefficient n=8–20 | 20 | 521.003 |
| `runDomain` | `n ^ 2` | consistent, bounded-coefficient n=8–20 | 20 | 216.526 |
| `runInitial` | `n` | consistent, bounded-coefficient n=8–20 | 20 | 0.470 |
| `runChain` | `n ^ 2` | consistent, bounded-coefficient n=8–20 | 20 | 62.006 |
| `runEndpoints` | `n ^ 2` | consistent, bounded-coefficient n=8–20 | 20 | 25.480 |
| `runSigns` | `n ^ 2` | consistent, bounded-coefficient n=8–20 | 20 | 1.479 |
| `runReplay` | `n ^ 2` | inconclusive | 20 | 105.478 |
| `runClearing` | `n` | consistent, bounded-coefficient n=8–20 | 20 | 5.816 |
| `runIntegerHigh` | `m` | inconclusive | 96 | 15.696 |
| `runRationalHigh` | `m` | consistent, original bounded m=16–96 | 96 | 187.907 |
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
original registrations, eleven had consistent characterizations and four
query findings required the bit-cost investigation below. No existing library phase is changed.

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
the larger bit lengths above are a different arithmetic regime. This wider unit-cost run alone resolves none of the four
original findings; the corrected-cost investigation follows below. The three wider failures show that extending
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

## Corrected bit-cost validation

The [independent derivations](sturm-bit-cost-models.md) distinguish binary
work from scalar-operation counts. For the fixed quadratic head, the initial
quotient has exactly `r(r+3)/2` stored bits at query degree `m=2r`; initial
reduction, full integer query and replay declare `m²`. Head-degree replay
converts the primitive Chebyshev-chain coefficients to dyadics. The current
upstream repeated-division normalizer gives `n⁴` bit work. These declarations
precede their new measurements. No coefficient in a mixed-power timing model
is inferred from the observed slopes.

The [exact closed-form checks](bench-results/sturm-bit-cost-formulas/) match
all five original head chains and six initial quotients. They are untimed
validation of the input-family calculations, not wall-time results. The odd
coefficient control above separately identifies the normalization sensitivity.

Every new parametric run keeps four trial-major samples per rung, with the
same 100 ms tuning target. Larger operational caps accommodate the declared
input volume. The binary and declaration snapshots, CPU assignment, load
observations, exact commands and every sample remain alongside each run.

| Query-degree ladder | Integer query residual | Initial reduction residual | Replay residual | Verdict |
| --- | ---: | ---: | ---: | --- |
| [4,096–65,536](bench-results/sturm-query-bit-cost/) | −0.328922 | −0.279527 | −0.477315 | all inconclusive |
| [65,536–524,288](bench-results/sturm-query-bit-cost-wide/) | −0.156694 | −0.160725 | −0.208469 | all inconclusive |
| [131,072–1,048,576](bench-results/sturm-query-bit-cost-large/) | −0.091054 | −0.092722 | −0.137679 | all consistent |

The first two runs are faster than the declared quadratic scaling, even
though their binary work is quadratic. Neither is relabelled as a pass. The
largest ladder independently passes the same quadratic declaration. Across
the three ladders the negative residual shrinks toward zero, as expected
when linear allocation overhead becomes smaller relative to quadratic limb
work. The replay result is only 0.012 inside the 0.15 slope tolerance; the
three passes do not have equal margin. The retained wider
schedule extends the same model to degree 1,048,576; the [head-degree quartic wall-time run](bench-results/sturm-replay-bit-cost/)
uses degrees 128,256,512,1024 and is inconclusive (residual −0.920844).
Its median replay times are 60.527 ms, 503.829 ms, 4.084 s and 37.045 s.
The exact bit-count derivation is valid, but the limb-work dominance needed
to infer quartic wall time does not hold on this ladder.

The [operation-only degree-512 profile](bench-results/sturm-replay-profile/)
retains raw samples and monotonic-clock region boundaries. Its exclusive
sampled periods include 11.63% in single-limb division, 9.57% in `cfree`,
7.68% in `malloc`, 5.91% in GMP initialization/copy, and 3.20% directly in
`Int.trailingZeros`' loop. The [explicit symbol groups](bench-results/sturm-replay-profile/groups.json)
sum nine division/normalizer symbols to 27.62% of sampled periods. A separate
seven-symbol allocation/copy group accounts for 33.85%; its callers are not
attributed. These are exclusive symbol totals, not an inclusive normalizer
percentage. The profile supports separating iteration/dispatch work from limb
work; it does not establish a wall-time exponent. The source
count of normalization iterations is Θ(n³), separately from Θ(n⁴) bit
volume. The new finite-regime iteration-cost hypothesis and its fresh
validation are specified in the derivation document. The
[fresh iteration-cost run](bench-results/sturm-replay-iterations/) passes the
bounded cubic wall-time hypothesis (residual +0.086071), with medians
60.170 ms, 501.776 ms, 4.080 s and 37.381 s. This is a finite-regime
characterization of the current normalizer. It is not a quartic wall-time pass
or a uniform cubic bit-complexity claim.

The [first degree-2048 extension](bench-results/sturm-replay-iterations-wide/)
retains all sixteen rows. Each of its four degree-2048 children was killed at
the 600-second cap. The harness emits “consistent” with residual +0.110222
from the surviving degrees 256–1024; **this is not a successful validation
through degree 2048**. The limit covers certificate preparation plus timed
replay. A fresh fixed schedule with the same model, degrees and four trials
uses an 1800-second operational cap, declared before collection. Every timeout
and every completed lower-rung measurement from the first attempt is retained.

The [complete larger-cap extension](bench-results/sturm-replay-iterations-cap1800/)
finishes all sixteen measurements. Its cubic verdict is **inconclusive**,
with residual +0.168613, outside the 0.15 tolerance. Median times at degrees
256,512,1024,2048 are 502.692 ms, 4.078 s, 36.651 s and 365.525 s;
all four degree-2048 times lie between 363.935 s and 367.265 s. The narrower
cubic pass does not extend to this ladder. This result is compatible with the
source-derived growing limb work, but it supplies no fitted mixed-cost model
and no passing quartic wall-time characterization. The measured 1024→2048
factor is 9.97, between the independently counted iteration factor 7.97 and
division-bit-volume factor 16.02; this comparison fits no constant or exponent.
This is a performance finding: the polynomial identities and query checks
continue to pass. The degree-512 profile identifies substantial normalization
work in `ZPoly.evalDyadic`, but it does not apportion the degree-2048 residual
between that work and the growing-integer products in recurrence verification.
A local normalization improvement would need its own source-derived model
and validation of the remaining checker work.

The [rational query run](bench-results/sturm-rational-bit-cost/) also passes
its independently derived quadratic model (residual −0.068144). At degrees
131072,262144,524288,1048576 its median times are 1.729 s, 6.255 s, 23.915 s
and 95.944 s. `DensePoly.divMod` divides by the monic fixed quadratic;
`Sturm.normalize` in `HexSturm/Basic.lean` normalizes the linear remainder
to `X`. Quotient coefficients therefore have denominator one. Rational
arithmetic still invokes scalar gcd normalization, but one denominator is
one in those recurrence operations; no growing pair of denominators is
being charged as a constant-cost gcd.

The largest integer query run reached 48.3 GiB RSS on a host with
125 GiB total RAM; doubling degree would roughly quadruple this storage
and exceed host capacity. These were shared-host runs. Other builds and,
during part of collection, the separately pinned replay measurement were
active; no sample is rejected for that activity. Binary hashes remain fixed
within each collection, even when git commits/rebases during collection
change the per-command `git_commit` strings. The query-large run records
that transition from `a452384` to `205086d` in its raw output. Its exact
binary and registration snapshot, not a single clean-tree SHA, identify
the measured code.

## Remaining validation gates

The separate fresh-module proof track checks literal acceptance, rejection of a
false terminal identity, stale-context rejection and interpretation of the
accepted domain. It cannot establish query root-sum semantics before the actual
IVT/Rolle and signed-remainder/Cauchy-index foundation is delivered.

The independent size sweeps and operation/normalization diagnostics above are
available. The query-degree findings have corrected quadratic characterizations.
The earlier head-degree replay test failed its cubic characterization. The
deferred-normalization implementation and its predeclared mode-2 validation
below resolve that performance finding, subject to implementation review. Concrete
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
These measurements do not advance any library phase. Closure of #10375 also
requires the implementation PR, independent review and CI.

The exact benchmark fixtures can be checked again with the pinned oracle
environment using `python scripts/bench/check_sturm_fixtures.py` followed by
the corresponding `fixtures.jsonl` paths above. Query checks include every
serialized chain identity and endpoint sign. Deliberately corrupted query
identities/signs and polynomial multipliers/quotients/gcds are rejected.

## Deferred-normalization validation

The executable `ZPoly.evalDyadic` retains its array fold and exact canonical
result. The numerator/precision fold normalizes once; zero coefficients retain
signed exponents and zero accumulators reset unused precision. This avoids
materializing enormous powers of two for constants or sparse monomials.
`HexRealRootsMathlib.evalDyadic_eq_fold` proves equality with the former
operation at every polynomial and dyadic point. The existing evaluation,
Sturm and Tarski correspondence proofs build through that equality.

The [declaration](sturm-bit-cost-models.md#deferred-normalization-replay-upper-bound)
selects mode 2 before scientific collection, citing GMP's published schoolbook
upper bound and explaining why neither cubic traversal nor schoolbook
multiplication is assumed to dominate. It applies that bound to the actual
O(n²) products on O(n)-bit recurrence scalars and coefficients. The
[untimed calculation](bench-results/sturm-replay-deferred-costs/) verifies all
retained production step formulas, distinguishes Horner volume from recurrence
products, and counts a schoolbook upper bound rather than GMP instructions.

The [operation-only profile](bench-results/sturm-replay-deferred-profile/)
at degree 1024 identifies `__gmpn_addmul_1_x86_64` (17.01%), copying (9.94% in
`__gmpn_copyi_x86_64`), and `__gmpn_mul_2` (4.57%) among the leading exclusive
samples. This covers the growing coefficient-product phase addressed by the
published bound. Allocation/copy samples are not assigned to a caller:
DWARF unwinding recovered no usable kernel call chains, as the retained
`phases.json` records. The 0.784 s profiled operation is attribution only,
not a scientific baseline or a speedup measurement.

The [scientific run](bench-results/sturm-replay-deferred/) retains all sixteen
successful samples on the declared four-trial schedule:

| Degree | Median replay | Minimum | Maximum |
| --- | ---: | ---: | ---: |
| 256 | 30.324 ms | 30.123 ms | 50.269 ms |
| 512 | 135.854 ms | 134.752 ms | 224.448 ms |
| 1024 | 775.889 ms | 772.601 ms | 1.229 s |
| 2048 | 6.943 s | 5.354 s | 8.598 s |

The unchanged two-sided harness emits `inconclusive`, residual −1.396940,
**faster** than `n⁴`. Under the mode-2 contract this is **within declared
upper bound (observed faster)**, not a two-sided consistency verdict. No rows
were dropped or timed out; peak RSS was 580624 KiB. The large spreads (47–66%)
remain visible; no sample was rejected because of shared-host activity and no
rerun was used. This result does not assert unbounded cubic timing or turn the
old failed runs into passes.

The preregistration commit's message was amended solely to include the cost
model derivation required by the structural checker. Recorded head
`0c4c946da` and amended head `f8abcce93` have identical tree
`b546b17ae4755b0a4d40a28adf4ce4c2421d9dd8`. The binary, registration and
derivation hashes in each collection identify the measured code; no executable
change accompanied that metadata amendment.

The aggregate library/manual/conformance build passed (14716 jobs), as did
all 13 benchmark smoke checks. New ordinary-kernel examples cover enormous
positive/negative exponents, sparse monomials, constants and cancellation;
567 rational differential cases cover small signed coefficients/endpoints.
The exact-equivalence theorem's axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`. All [23 newly emitted axis/control
fixtures](bench-results/sturm-replay-deferred-oracles/) are literally identical
to the retained outputs and pass the independent pinned FLINT/qqbar oracle.
These checks are correctness evidence, separate from the timing verdict.

The [adjacent before/after run](bench-results/sturm-replay-deferred-pairs/)
uses four AB/BA blocks at degree 1024 on one automatically leased CPU. Median
replay time is 37.955 s before and 0.774 s after; the median paired speedup is
49.092× (individual pairs 48.420–49.417×). All eight children completed and
returned the same `0xb` result hash. The before binary hash equals the retained
cap1800 binary; the after hash equals the new scientific-run binary. Per-row
checkout names can change during collection, so the fixed binary hashes and
source snapshots identify the two arms.

A fresh-module proof-cost attempt aborted after its final checkout-state check
because repository metadata and report artifacts changed during collection.
Its [failure log](bench-results/sturm-replay-deferred-proof-aborted.log) is
retained. The runner emitted no result artifact, so no timing values from that
attempt are claimed or used; the replacement collection uses a fixed checkout.

The replacement [fresh-module collection](bench-results/hex-sturm-mathlib-deferred.json)
completed all four adjacent AB/BA pairs per case with the checkout fixed.
Acceptance/domain candidate and baseline median builds were 7.045 s and
6.790 s; the median paired difference was 0.268 s. The rejection results and
all compiler output, source/dependency fingerprints, artifact sizes and axiom
sets are retained in the JSON. Both cases have `no-comparable-control`:
these are fresh whole-build observations, not a resolved incremental kernel
cost or a speedup claim. This rational literal track checks the current
companion import closure; it does not itself measure dyadic evaluation or
supply the deferred general semantic theorem. The new dyadic ordinary-kernel
examples and equality axiom audit are covered by conformance above.
