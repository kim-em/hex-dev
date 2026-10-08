# Shared Sturm–Tarski computation measurements

The current [Phase-4 policy](../PLAN/Phase4.md) accepts an independently
derived model or, when no family-specific model is derivable, a cited upper
bound. A predeclared upper bound does not
require multiplication or gcd to dominate a profile. The retained head-degree
replay and growing-bit observations below satisfy their cited upper bounds
on their measured sources, including results the two-sided harness calls
`inconclusive` in the faster direction. This does not admit the failed
two-sided declarations or complete the library's Phase-4 audit.

[Source and sample reconciliation](bench-results/sturm-policy-reconciliation.json)
checks all 260 growing-bit samples, eleven original upper-bound registrations,
twenty-four fixture/timed-body definitions and eleven shared frontend definitions
against the current source. Its [reproduction script](bench-results/sturm-policy-reconciliation-audit.py.txt)
checks the same assertions from the repository root and prints JSON without
overwriting the retained artifact by default. The
selected fixed-degree frontend bodies match the saved benchmark source;
the checked HexPoly, HexPolyZ and HexRealRoots directories have only SPEC
changes since the recorded commit. This is a selected-source comparison,
not an import-cone identity check. The collection records benchmark source
and binary hashes but not every library file in its dirty tree. Full library
source provenance and import-cone reuse scope therefore remain to be checked
before these runs attest current Phase 4. They do not establish
current executable identity, recover lost raw profiles or turn historical
wall-clock values into current absolute timing claims.

The corrected quadratic query-degree models pass for initial reduction,
integer and rational queries, and replay. Head-degree replay now defers dyadic
normalization to the end of each Horner evaluation, with proved equality to
its former result. Its predeclared **mode-2 O(n⁴) upper-bound observation is faster** through degree 2048. This is explicitly weaker than two-sided
consistency: GMP multiplication crossovers prevent a justified tight monomial
claim on this ladder. The earlier cubic and quartic two-sided failures remain
recorded below. [The derivations](sturm-bit-cost-models.md) distinguish the
former repeated-normalization cost from the implemented recurrence products.

All earlier declarations, failures and samples are retained. These observations
cover effective query/checker paths. They do not attest complete frontend Phase-4 coverage or downstream extension
evidence. The general signed-root-sum theorem is exported by ordinary
`HexRealRootsMathlib` and `HexSturmMathlib` imports. `HexQuerySemantics` retains
semantic regression tests; theorem-only companions have no dedicated Phase-4
performance deliverable under the current policy.

## Original protocol and provenance

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

Each original complexity registration used its declared custom ladder, four trial-major
outer trials, a 100 ms tuning target and a three-second operational cap. All
original registrations used mode 1 (two-sided parametric). The source derivations precede
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

## Original results

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
frontend phase state is recorded in `libraries.yml`. The correction below distinguishes
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
accepted domain. The delivered IVT/Rolle and signed-remainder foundation now establishes
query root-sum semantics in the ordinary Mathlib companions; `HexQuerySemantics`
retains ordinary-kernel semantic replay tests and axiom guards, separate from
compiled arithmetic performance.

The independent size sweeps and operation/normalization diagnostics above are
available. The query-degree findings have corrected quadratic characterizations.
The earlier head-degree replay test failed its cubic characterization. The
deferred-normalization implementation supplies the retained one-sided
upper-bound observation below. It satisfies its predeclared bound on the
recorded source; no dominant-phase attribution gate applies. Concrete
extension-depth and nested-evidence probes belong downstream under #10378;
general root-sum/replay soundness, singleton/sign/bound consequences and the
exact-domain natural root-count wrapper are proved and exported by the ordinary
`HexSturmMathlib` companion. Its regression target `HexQuerySemantics` keeps
the semantic replay and axiom tests. Their [semantic proof-cost evidence](sturm-tarski-semantics.md)
is separate from these arithmetic measurements. The integer query-one
finite/whole-line counts and rational finite-dyadic specialization also retain
their proofs using the existing real Sturm theorem. Whole-`Option` field-representation and
rational/integer agreement, and literal certificate transport, are proved in
the companion; these timing observations do not discharge those proofs.
The [recorded finding](https://github.com/kim-em/hex-dev/issues/10375#issuecomment-5757400442)
also records the original polynomial pseudo-gcd finding; its wider-ladder
resolution is documented in the polynomial report.
The shared computation from #10375 is delivered. Its retained measurements
do not establish the remaining frontend performance requirements. General
semantics and exact-domain natural counts are also delivered, independently
of the Phase-4 findings listed below.

The exact benchmark fixtures can be checked again with the pinned oracle
environment using `python scripts/bench/check_sturm_fixtures.py` followed by
the corresponding `fixtures.jsonl` paths above. Query checks include every
serialized chain identity and endpoint sign. Deliberately corrupted query
identities/signs and polynomial multipliers/quotients/gcds are rejected.

## Deferred-normalization validation

The executable `ZPoly.evalDyadic` retains its array fold and exact canonical
result. At integer endpoints the numerator/precision fold normalizes once; zero coefficients retain
signed exponents and zero accumulators reset unused precision. This avoids
materializing enormous powers of two for constants or sparse monomials.
`HexRealRootsMathlib.evalDyadic_eq_fold` proves equality with the former
operation at every polynomial and dyadic point. The existing evaluation,
Sturm and Tarski correspondence proofs build through that equality.

Fractional endpoints use normalized dyadic arithmetic at every Horner step.
For `2X^m + X^(m-1) + ... + X + 1` at `1/2`, this keeps each suffix value 2
compact and takes linear bit work. Deferring normalization there would grow
`(2^(j+1), j)` and take quadratic work; see the
[cancellation analysis](sturm-bit-cost-models.md#fractional-cancellation) and
[the fractional-evaluation report](hex-real-roots-performance.md#fractional-evaluation).
The integer-endpoint measurements below remain scoped to that replay family.
Constants and sparse monomials retain their former compact behavior.

| Current registration | Declared expression | Mode | Degree ladder | Result |
| --- | --- | --- | --- | --- |
| `runReplay` | `n ^ 4` | Cited upper bound | 256, 512, 1024, 2048 | within declared upper bound on measured source (observed faster) |

The original `n²` tables above preserve historical declarations and verdicts;
they are not the current registration.

The [declaration](sturm-bit-cost-models.md#deferred-normalization-replay-upper-bound)
selects mode 2 before scientific collection, citing GMP's published schoolbook
upper bound and explaining why neither cubic traversal nor schoolbook
multiplication is assumed to dominate. It applies that bound to the actual
O(n²) products on O(n)-bit recurrence scalars and coefficients. The
[untimed calculation](bench-results/sturm-replay-deferred-costs/) verifies all
retained production steps at degrees 8, 10, 12, 16 and 20 against the formulas.
The degree-128–2048 volumes are formula-derived calculations; no production
certificates at those degrees are retained by this script. It distinguishes
Horner volume from recurrence products and counts a schoolbook upper bound,
not GMP instructions.

The [operation-only profile](bench-results/sturm-replay-deferred-profile/)
at degree 1024 identifies `__gmpn_addmul_1_x86_64` (17.01%), copying (9.94% in
`__gmpn_copyi_x86_64`), and `__gmpn_mul_2` (4.57%) among the leading exclusive
samples. A single hottest symbol does not establish phase dominance:
allocation/copy/reference-management work collectively accounts for more
samples than multiplication. The bound covers both: O(n²) outer coefficient
operations allocate or copy O(n)-bit integers and at most O(n) array references
each, giving O(n³) storage work; GMP's internal workspace is covered by its
multiplication algorithm. Thus the upper bound does not depend on assigning
allocation samples to multiplication callers. Allocation/copy samples are
not assigned to a caller:
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

This collection ran on CPU 61 from 22:34:57 to 22:36:08 UTC on September 21.
This PR's own adjacent before/after collection ran on CPU 13 from 22:35:35
to 22:40:56, overlapping the later scientific trials. The untimed formula
calculation and an attempted fresh proof build were also observed running,
but their overlapping start/end times were not retained; that observation
supplies no quantitative concurrency attribution. The timestamped overlap
between the two timing runs is context, not proof of the cause of the
larger samples and not a reason to discard them. The paired comparison
continues to use adjacent arms on its own CPU.

`metadata.json` records a clean checkout at the start, while the child logs
record `0c4c946-dirty`: the runner collects git status before writing its
registration/derivation snapshots and logs. Those new untracked result files
make the checkout dirty before the benchmark children start. This does not
indicate a change to the measured binary or its source.

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
measure the subsequently delivered general semantic theorem. The new dyadic ordinary-kernel
examples and equality axiom audit are covered by conformance above.

## Bench targets

Current registrations are in `bench/HexSturm/Bench.lean` and
`bench/HexSturm/Frontend.lean`. The integer backend stages are shared-kernel
diagnostics; their existence does not attest every ordered-field frontend.
The executable at the recorded frontend collection lists and verifies 91
cases, including the 13
`short-chain-degree` registrations below, plus 12 complete-query fixed
comparison endpoints and two protocol-overhead controls in
`Hex.SturmExternalBench` in `bench/HexSturm/Bench.lean`. The latter are expected-result/informational
anchors and make no complexity or absolute-budget claim. Twenty additional
fixed registrations extend count comparisons and protocol controls to degrees
4, 16, 32 and 64; degree 8 uses the existing endpoints. The
[degree comparison](bench-results/sturm-external-degree/README.md) treats
measured elapsed time and backend ratios as informational evidence.

| Frontend/stage targets | Strongest justified evidence | Input |
| --- | --- | --- |
| `runSparseDomain`, `runSparseQuery`, `runSparseInteger`, `runSparsePrepared`, `runSparseCount`, `runSparsePreparedCount`, `runSparseCertificate`, `runSparsePreparedCertificate`, `runSparseCountCertificate`, `runSparseReplay`, `runSparseCachedReplay`, `runSparseClear`, `runSparseEmbed` | Mode 1, `n` | `short-chain-degree`: `2X^n−1`, query one, endpoints ±1, n=16384–131072 |
| `runPreparedHigh`, `runPreparedCertificateHigh` | Mode 1, `m²` | Fixed quadratic head, growing query degree 131072–1048576 |
| `runRetargetWide` | Mode 1, `n²` | Short-chain `X^n−2`, endpoints retargeted to ±3, degree 65536–524288 |
| `runEmbedSparse` | Mode 1, `n` | Literal integer certificate for `X^n−2`, degree 2048–32768 |
| `runInitialWide`, `runClearingWide` | Mode 1, `n²` | Chebyshev coefficient arrays, degree 16384–131072 |
| `runCoefficientBits`, `runEndpointBits` | Mode 2, published `bits²` upper bound | Odd growing coefficients or dyadic mantissas, 2048–32768 bits |
| `runFractionalBits` | Cited `bits²` upper bound satisfied on measured source | Odd dyadic mantissas, 2048–32768 bits |
| `runPreparedBits`, `runCountBits`, `runPreparedCountBits`, `runCertificateBits`, `runPreparedCertificateBits`, `runCountCertificateBits`, `runFieldReplayBits`, `runCachedReplayBits`, `runClearBits`, `runInfiniteBits` | Cited `bits²` upper bounds satisfied on measured source | `T_8(X−z)`, odd growing integer `z`, endpoints `z±2` or infinity |

[Cost derivations](sturm-bit-cost-models.md) precede the corresponding
collections. They describe bit work on these specific families, not the
SPEC's general ring-operation bound or downstream extension-oracle costs.
The translated family keeps degree fixed. Its predeclared quadratic bound
covers a fixed number of scalar operations on O(bits)-wide values, together
with linear copying, sign tests, hashing and allocation. The source argument
covers total work; a small share of general multiplication does not invalidate
this upper bound. It supplies no tight growth model or growing-degree claim.
Cached replay checks the literal cache binding during fixture preparation.

## Verdicts

[Short-chain degree results](bench-results/sturm-short-chain-degree/results.json)
retain all 208 observations for the 13 frontend/backend cases. The independently
[derived linear models](bench-results/sturm-short-chain-degree/derivation.md)
pass with residual slopes from −0.011337 to +0.019652, without signal trimming
or budget truncation. This supplies growing-degree coverage for the named
public operations on a three-entry chain with bounded-word coefficients and
endpoints. It does not resolve the failed long-chain two-sided declarations or add a
tight model to the growing-bit upper bounds.
[Metadata](bench-results/sturm-short-chain-degree/metadata.json) records the clean
source, exact executable, automatically leased CPU, load, commands, fixed
trial-major schedule and matching before/after hashes.

[The growing-operand collection](bench-results/prerequisite-sturm-growing-operands/metadata.json)
records commands, CPU lease, host context, source snapshots and executable
SHA256; every relevant source and the binary remained unchanged. Native
LeanBench's trial-major schedule retains four trials at every rung.

| Case | Declared expression | Residual slope | Interpretation |
| --- | --- | --- | --- |
| `runInitialWide` | `n ^ 2` | -0.064275 | two-sided pass |
| `runClearingWide` | `n ^ 2` | -0.093721 | two-sided pass |
| `runRetargetWide` | `n ^ 2` | -0.018793 | two-sided pass |
| `runEmbedSparse` | `n` | +0.005649 | two-sided pass |
| `runCoefficientBits` | `bits ^ 2` | -0.352125 | within declared upper bound (observed faster) |
| `runEndpointBits` | `bits ^ 2` | -0.586339 | within declared upper bound (observed faster) |
| `runFractionalBits` | `bits ^ 2` | -0.580784 | within declared upper bound (observed faster) |
| `runPreparedBits` | `bits ^ 2` | -0.849544 | within declared upper bound (observed faster) |
| `runCountBits` | `bits ^ 2` | -0.869592 | within declared upper bound (observed faster) |
| `runPreparedCountBits` | `bits ^ 2` | -0.655776 | within declared upper bound (observed faster) |
| `runCertificateBits` | `bits ^ 2` | -0.882864 | within declared upper bound (observed faster) |
| `runPreparedCertificateBits` | `bits ^ 2` | -0.867449 | within declared upper bound (observed faster) |
| `runCountCertificateBits` | `bits ^ 2` | -0.777107 | within declared upper bound (observed faster) |
| `runFieldReplayBits` | `bits ^ 2` | -0.876956 | within declared upper bound (observed faster) |
| `runCachedReplayBits` | `bits ^ 2` | -0.856630 | within declared upper bound (observed faster) |
| `runClearBits` | `bits ^ 2` | -0.829891 | within declared upper bound (observed faster) |
| `runInfiniteBits` | `bits ^ 2` | -0.954303 | within declared upper bound (observed faster) |

The harness wording is `inconclusive`, in the faster direction. All thirteen
runs retain four successful samples at each of five rungs without budget
truncation; its ordinary leading-rung verdict exclusion is recorded separately
in the reconciliation artifact and no raw sample is discarded. Under the
current cited-upper-bound policy these observations satisfy their original
`bits²` declarations on the measured source. This is a one-sided observation,
not a two-sided pass. The total-work explanation is completed here from the
source, extending the original phase-specific derivation; the expression and
schedule are unchanged and no exponent is selected from the measurements. The bounds were declared before collection; no failed
two-sided result is relabelled. Historical profile summaries explain constants
but their missing raw captures supply no reprocessable attribution.

[Prepared nonconstant queries](bench-results/prerequisite-prepared-query-degree/)
pass their two-sided quadratic declarations: residuals −0.066 and −0.077.
At the largest rung the value-only path materializes the same roughly
quadratic-bit quotient as the certificate path, reaching about 33.8 GB peak
RSS. This is a limitation of the shared chain producer, not evidence of a
streaming value implementation. The metadata preserves the original broad
`sources_unchanged: false`; its `retention_scope` independently verifies that
the measured Sturm source and executable remained unchanged while unrelated
real benchmark files changed.

[Wide Chebyshev attempts](bench-results/prerequisite-sturm-head-wide/) and
[the single unchanged coefficient-sign rerun](bench-results/sturm-signs-unchanged/)
remain retained failures of characterization. The latter residual is +0.465232.
The [production sign replacement](bench-results/sturm-sign-comparisons/README.md)
proves equality with `Int.sign` and removes positive multiprecision magnitude
copies from compiled consumers. The bench-local sign traversal of production-generated chains has 32
adjacent before/after samples that agree exactly and improve the ratio of medians by 4.081× at degree 1024. The unchanged
quadratic ladder and its one permitted repeat remain inconclusive, with
residuals +0.326483 and +0.164190; this improvement does not close the concern.
The old Rat quartic candidates remain retired: this audit does not establish
their claimed operation count and intermediate-width bound for every timed
stage, or reinterpret the failed two-sided retarget/count declarations. Their
profiles mainly show allocation and linear-limb work; that fact alone is not
a reason to reject a valid upper bound. The former power-of-two bit fixtures
likewise collapse to a one-bit mantissa or a normalized linear chain and do
not provide the advertised general-operand coverage. Neither those families nor the original short, mixed-word head ladder
justify current Phase 4. No failed two-sided case is relabelled mode 2.

## Remainder-only value queries

`queryReduced` and `queryReducedPrepared` reduce by the validated head using
`DensePoly.modImpl`, then invoke the existing shared producer. The companion
proves equality with the original whole result, including failures, under
lawful coefficient division. These opt-in value APIs avoid retaining the
unreduced query's literal quotient; the existing certificate contract remains
available.

The [controlled storage/runtime comparison](bench-results/sturm-reduced-value-comparison/README.md)
retains all 32 adjacent AB/BA arms with identical rational value-only preparation.
At degree 262144 peak whole-process RSS falls from about 2175 to 137 MiB, and
median kernel time improves about 1.5×. Preparation and process memory are
included in RSS, while kernel timings exclude preparation. All signed-result
hashes agree. Earlier coupled-preparation and quotient-producing prototypes
remain archived with their actual limitations and interrupted parents.

The reduced query's registered quadratic bit-work ladder passes at degrees
131072–1048576 with four trials per rung: residual −0.063658, no truncation or
signal exclusion. Median kernel time at the largest rung is still 78.0 seconds.
The [current representative capture](bench-results/readiness-runtime-profiles/README.md)
attributes 90.79% inclusive share to the remainder-only worker. This provides
family-specific evidence; it does not resolve the failed sign-traversal
or head-degree frontend two-sided claims. The former 33.8 GB observation remains valid for its original
quotient-retaining API and recorded source.

## Comparator ratios

The [short-chain backend pairs](bench-results/sturm-short-chain-degree/analysis.json)
use four adjacent alternating AB/BA blocks on identical inputs. All 16 common
parameter pairs have matching complete Option Int hashes. Median paired
rational/integer ratios at degrees 16384,32768,65536,131072 are
12.377302,12.114607,11.845440,11.778937. Correctness agreement is gating; these
host-specific ratios explain relative implementation cost and supply no
portable speed guarantee. The full arm commands, order, observations and hashes
are retained in [metadata and raw exports](bench-results/sturm-short-chain-degree/).

The adjacent backend comparison above retains the rational/integer pairs and
hash agreement. Correctness agreement is gating; it has no wall-time ratio
goal. The structured informational comparators are **FLINT real-qqbar signed-root sums**
and **Z3 RCF signed-root sums**. Their [complete-query comparisons](bench-results/sturm-external-comparisons/README.md)
retain 64 adjacent alternating AB/BA arms on the fixed T_8 queries one, X,
X−1 and T_8, with exact results 8,0,−8,0. All 32 pairs match complete Option Int
hashes and expected-result checks. Median paired external/native ratios are
FLINT 1.981380,2.691172,2.284023,168.350949 and Z3
1.082383,1.719067,1.399890,4.488035 in that query order.
The [raw exports and metadata](bench-results/sturm-external-comparisons/) retain
the source, commands, order, inner counts and every observation. Protocol
controls have medians 6.734/6.594 µs. Z3 Count exceeds the 5% framing-overhead
threshold (5.989%); its per-pair protocol-adjusted median ratio is 1.017671,
alongside the raw 1.082383. Both ratios remain in the analysis; this adjustment
does not isolate a pure algorithm body.

Inputs and coefficient contexts are prepared. Timed requests call root
production, filter the open interval, evaluate the complete query and sum
exact signs, including JSON transport and temporary cleanup. FLINT uses generic
real-qqbar Horner evaluation via `gr_mul`/`gr_add`; the 168.350949 Common ratio
describes that method, rather than an optimized polynomial-evaluation endpoint
with minimal-polynomial reduction. No roots are
cached by the driver; backend contexts may retain internal caches, and the
harness performs an untimed warmup. These are informational fixed valid-domain
endpoints, not complexity admissions, portable speed claims or isolated
root-isolation timings. Neither external API has a matching Lean literal
certificate/proof-checking surface. Extension/nested-evidence comparisons stay
with the downstream owners; these rational-field fixtures do not attest them.

## Profile

The [short-chain-degree representative](bench-results/sturm-short-chain-degree/sturm-short-chain.summary.json)
uses the actual query at degree 65536 and has 283 operation-window samples.
Calibration residual is 0.614493 ms; sample-count and ±5 ms sensitivity checks
pass. Leaf shares are own code 0.35%, GMP 31.10%, allocation 43.11%, Lean runtime
18.73% and other 6.71%. Inclusive chain production is 67.49%, pseudo-division
47.70%, and rational gcd 78.45%; inclusive percentages overlap. Rat normalization
allocates even on this bounded-scalar family, explaining substantial GMP and
allocation cost without changing the derived linear traversal model.
[The manifest](bench-results/sturm-short-chain-degree/sturm-short-chain.manifest.json)
and [artifact checks](bench-results/sturm-short-chain-degree/artifact-check.json)
retain source/executable identity and verify persistent raw captures, sidecars
and symbols. This attribution covers the new named family only.

[Retained representative captures](bench-results/prerequisite-representative-profiles-62399ddd0/README.md)
on clean source `62399ddd0` supply 548 replay samples and 526 prepared-query
samples. Both pass sample-count, calibration and ±5 ms sensitivity checks.
Replay has 99.82% inclusive certificate-check share, including 77.74% signed
chain checking, with 46.35% allocation self share. The prepared high-degree
query has 92.02% signed-chain-build share, including 87.45% pseudo-division,
with 27.19% allocation self share. Raw perf/samply files, kernel sidecars,
symbols and checksums are retained in persistent storage. This supplies
representative attribution; it does not resolve failed two-sided declarations.

[The profile inventory](bench-results/prerequisite-readiness-profiles/inventory.json)
includes every successful and failed capture, binary fingerprints, commands,
historical raw-profile locations and filtered summaries. Hashing, fixture preparation
and process startup are excluded by the kernel sidecar. Recorded growing-operand
diagnostics pass the ≥100-sample, ≤5 ms calibration and ±5 ms sensitivity checks.
[The artifact check](bench-results/prerequisite-profile-availability.json) finds
all 38 prerequisite-readiness raw capture directories unavailable at their
recorded local paths. Their committed manifests, summaries, diagnostics and
timing samples remain intact, but these raw perf/samply files cannot currently
be reprocessed. Those historical candidate profiles do not supply current raw
attribution if their complexity models are later admitted.

The fractional-endpoint capture at 32768 bits retains 1542 samples, a
1.001 ms calibration residual and passing ±5 ms sensitivity. It has 98.31%
GMP leaves; inclusive multiplication entries include `mul_n` (24.64%),
Toom-3 (21.92%), Toom-2 (20.95%) and basecase (9.21%). These inclusive
percentages overlap and must not be summed. Its recorded implementation and
registration matched the earlier timing source, with only comment changes;
this is historical provenance rather than a current raw-file check.
This historical summary explains the arithmetic constant; its lost raw
capture cannot be reprocessed. Neither profiling nor this upper-bound
observation attests the whole library.

The odd cubic and odd endpoint captures at 32768 bits have 95.25% and 98.38%
GMP leaves respectively. Their generic products/reduction work includes
`addmul_1`, basecase/Toom multiplication and half-gcd steps. The ten translated
frontend captures have 93.71–96.44% GMP leaves and 3.31–5.67% allocation.
Their dominant leaves are `mod_1`, `addmul_1`, `divexact_1`, `copyi` and
`mul_1`; general basecase/Toom products account for roughly 5% or less.
Incomplete outer Hex stacks do not establish that the single-limb leaves
belong to general multiplication. The observed growth is about bits^1.05–1.35,
and infinity checking has no finite-endpoint Horner phase. These summaries
cannot assign the remaining leaves to callers. The source-derived total-work
bound, rather than a dominant-phase profile requirement, justifies their
one-sided interpretation under current policy. No tight exponent is inferred.

The degree-1024 integer-producer diagnostic has 47.51% allocation, 41.69% GMP
and 6.62% runtime leaves. The coefficient-sign map has 61.63% runtime,
20.23% GMP and 14.13% allocation: its wide-ladder failure concerns traversal
and hashing of stored coefficients, not a general multiplication phase. These
profiles explain the old failed hypotheses; they do not manufacture passing
replacement models.

The retained head-degree deferred-replay and query-degree reduction profiles
above continue to apply to their unchanged shared integer kernels. The
frontend profiles are separate evidence for prepared, cached and transport paths.

## Concerns

- The public foundation/frontend integration from
  [#10683](https://github.com/kim-em/hex-dev/pull/10683), owned by
  [#10575](https://github.com/kim-em/hex-dev/issues/10575), is included in this
  source tree. Ordinary `import HexSturmMathlib` exports `query_iff` and the
  reduced-query correspondence. Source availability does not attest Phase 4
  or publish the split repositories.

- The original prepared-query API still materializes a large quotient for
  growing queries against a fixed quadratic. Its retained historical ladder
  reaches roughly 99 seconds and 32 GiB whole-child peak RSS. The new
  remainder-only value-query path avoids retaining that quotient: the current
  degree-262144 comparison observes roughly 137 MiB rather than 2175 MiB.
  It still has quadratic bit work and takes roughly 78 seconds at degree
  1048576. These observations do not establish a general space bound or
  change the existing certificate API.

- The historical two-sided replay/checker and coefficient-sign failures
  remain retained. Deferred replay now has a valid predeclared upper-bound
  observation. The proved production sign compiler replacement improves
  the measured traversal, but fresh validation and its single unchanged repeat
  remain inconclusive for the `n²` characterization (+0.326483 and +0.164190). The previous
  unchanged rerun (+0.465232) is retained separately. Retargeting and
  prepared-count head-degree two-sided failures also remain unresolved;
  short-chain passes do not convert those results into passes.

- The historical raw captures were lost after a reboot. Their summaries remain
  diagnostics and cannot be reprocessed. The [retained representative captures](bench-results/prerequisite-representative-profiles-62399ddd0/README.md)
  supply fresh replay and prepared-query attribution with raw perf/samply data,
  sidecars and checksums in persistent storage. Both pass calibration and
  ±5 ms sensitivity checks. Current policy requires profiles to explain
  surprising results or constants, rather than a new capture for every operation.

- The quadratic growing-bit bounds are intentionally loose. Satisfying them
  does not establish good constants or rule out a subquadratic regression;
  the external curves and actual cost attribution remain relevant.

- [#10577](https://github.com/kim-em/hex-dev/issues/10577): reconcile all advertised frontend operations with registrations/comparators, resolve the retained coefficient-sign characterization, and finish dependency-ordered Phase-4 attestation. The valid family observations and retained failed declarations above do not close this audit.

## Remaining Phase-4 work

| Obligation | Actual state | Next action |
| --- | --- | --- |
| Shared query semantics and exact-domain natural root count | Proved and exported by the ordinary Mathlib companion; kernel guards remain required | Reuse the APIs immediately in downstream work |
| Degree, query-degree, coefficient-size, endpoint-size and short/long-chain coverage | Independent models and predeclared upper bounds have retained scoped observations; fixed anchors check results only | Reconcile the complete advertised frontend surface and declarations; do not schedule a blanket rerun |
| Library-source / import-cone provenance | The 260 growing-bit samples retain benchmark and binary fingerprints; selected definitions match, but the original dirty library tree was not fully hashed | Diff the timed import cone and manifest since `6d78bf3`; justify changes and verify original library-source scope before current Phase-4 reuse |
| Coefficient-sign traversal | Proved production compiler replacement removes magnitude copies and improves paired medians; fresh `n²` validation and its one unchanged repeat remain inconclusive | Explain and resolve the remaining residual without another unchanged scientific repeat; retain all failures |
| Retargeting and prepared-count long-chain models | Earlier two-sided failures remain, alongside distinct passing short-chain families | Resolve the failed claims without relabelling them as bounds |
| Rational versus integer and external comparators | Retained exact agreement and FLINT/Z3 complete-query degree curves | Check each SPEC-named common domain against current registrations; use the curves as orientation with their recorded sources |
| Representative attribution | Retained raw replay/prepared-query captures and reduced-query attribution; older 38 captures lost | Reuse valid captures; profile only a remaining surprising result or constant |
| Dependency eligibility | HexPoly and HexRealRoots both record 7; HexSturm records 3 | Finish the core's actual Phase-4 checks before advancing its theorem-only companion |

The [compiled sign diagnostic](bench-results/sturm-sign-runtime-diagnostic/metadata.json)
shows `Int.sign` calling `lean_big_int_to_nat` on positive multiprecision
values, whose implementation performs `mpz` copy construction. Therefore a
constant-work assumption for each sign test is unsupported by that executable.
This is source/code-generation evidence, not a new timing run or a claim that
all of the observed failure is explained. The diagnostic and the sign rerun
use the same Lean 4.35.0-rc3 library implementation, but different benchmark
binaries; their recorded hashes are not interchangeable.

`HexRealRoots.Sign` now supplies a comparison-based implementation and an
ordinary-kernel equality registered with `@[csimp]`. The production root-query
code and the unchanged benchmark both compile through it. The
[new capture](bench-results/sturm-sign-comparisons/README.md) hashes the complete
tracked local Lean tree and root dependency manifest before collection; the
generated C and exact-binary disassembly show comparisons with zero without
input magnitude copies. The full function equality preserves every input,
and its guarded axiom audit admits only `propext` and `Quot.sound`.

Both fresh scientific runs remain inconclusive under the unchanged declaration.
Their raw points, the adjacent AB/BA comparison, plots and binary/source
fingerprints are retained. The measured benefit is confined to that sign pass;
it does not establish an end-to-end query speedup or explain the remaining
residual. A further fix requires new evidence; a correction of a demonstrated
model error requires an independent derivation before fresh collection, never
an exponent inferred from the timings. #10577 retains this concern.

Extension depth, nested coefficient-oracle scaling, BKR sign determination and
tower assembly remain with #10377/#10378. Their available proved APIs and
#10575's bounded integration work do not wait for #10577 closure. The [local verification](bench-results/sturm-policy-verification.json) builds
all four assigned libraries and both ordinary-kernel companion targets,
checks admission and Mathlib-free boundaries, and passes all 93 current
Sturm result checks with panic rejection enabled. No counter is advanced
by this report reconciliation.
