# Shared Sturm–Tarski computation measurements

Phase 4 remains incomplete. Nine of thirteen two-sided registrations are
consistent with their declared models; four are inconclusive. All completed
samples are retained, and no rerun or timing-driven change to the registrations
was made. The observations cover the implemented query/checker paths, not the
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
recorded independently. The benchmark commit was subsequently reworded to
include the source's cost derivation; `1b7b331f322acccd0376156b47b00a2ba32f47f8`
has exactly the same tree as the measured commit. The exact measured
registration source is also retained as `registration.lean.txt`, whose SHA256
matches the metadata, so subsequent rebases do not obscure the protocol.
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
when its five-rung ladder has too few retained rungs for that statistic; these
verdicts must not be described as regression-slope estimates.

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
characterization. These results leave the performance obligation open under
#10375; the frontend remains at `done_through: 0`. No model was weakened or
replaced with a fixed budget. Further work must distinguish fixed overhead,
integer representation thresholds and intermediate coefficient growth before
claiming a valid performance characterization.

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
remained unchanged. All completed samples, including concurrent host activity,
are included.

The acceptance/domain module's median fresh build was 5282.507 ms against
4547.418 ms for its import-only baseline; the median paired difference was
707.062 ms. The rejection/stale-context module's corresponding values were
5252.537 ms, 5030.121 ms and 696.988 ms. These are whole fresh-build observations,
not isolated kernel instruction timings or an absolute performance budget.
The harness labels the differences `no-comparable-control`; no statistically
resolved incremental-cost claim follows. No mandatory null-control protocol or
retry was added.

## Remaining validation gates

The separate fresh-module proof track checks literal acceptance, rejection of a
false terminal identity, stale-context rejection and interpretation of the
accepted domain. It cannot establish query root-sum semantics before the actual
IVT/Rolle and signed-remainder/Cauchy-index foundation is delivered.

Independent coefficient-bit and endpoint-size sweeps, independently varying
chain length, peak intermediate sizes, gcd work and coefficient-operation call
counts remain required. Extension-depth and nested-evidence probes require the
downstream adapters. Root-sum/replay soundness, count/singleton/sign/bound
consequences and whole-Option backend correspondence remain proof gates.
The [recorded finding](https://github.com/kim-em/hex-dev/issues/10375#issuecomment-5757400442)
also covers the owning polynomial library's separate pseudo-gcd scaling gap.
Nothing in these measurements advances the library phase or closes #10375.
