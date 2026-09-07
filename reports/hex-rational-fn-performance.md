# HexRationalFn performance

## Scope and evidence status

The library is active through Phase 3. Phase 4 has passing degree ladders for
six queries and two witness-replay operations, matched FLINT query measurements,
and timed-region profiles of queries and certificate replay. **Phase 4 remains
incomplete**: five other input families and the remaining operation/bit-cost
models are not qualified. The 35 fixed registrations remain expected-hash anchors
and informational crossover measurements, not asymptotic regression detectors.
A generic timeout is not an operation-specific absolute budget.

## Bench targets

`Hex.RationalFnScaling` registers `equal`, `different`, `inverse`, `negate`,
`evaluate`, `evaluatePole`, `replay`, and `reject`. Each has an independently
derived two-sided linear model and parameters 128 through 16384 by doubling.
Query coefficients and Horner partial sums stay bounded; replay holds the input
fraction degree at one and varies a dense Bezout multiplier. This is not a claim
about generic rational bit complexity or Euclidean coefficient growth.
Inputs are prepared outside timing without normalization or gcd computation.
Canonical polynomial outputs are consumed by complete-array hashes.

Equal inputs use independently rebuilt arrays. The unequal query changes the
constant numerator coefficient: Lean's array equality visits high indices first.
The fixture validator checks this location independently. Its other operand is
a polynomial with denominator one; FLINT can reject the denominator shape early.

All seven SPEC input families have executable anchors: normalization, addition,
multiplication, coefficient-height, queries, calculus, and certificate-replay.
The seven prepared cases vary residual degree (4, 12), common-factor degree
(0, 2, 4, 12), nonmonic scalar factors, and rational coefficient height
(1, 16, 64, 256 input bits). Addition includes equal and partially shared
denominators, coprime denominators, and total cancellation. Multiplication
includes a coprime-product control and complete cross-cancellation. Queries
include a last-coefficient mismatch and prepared poles. Calculus includes both
the derivative of a canonical fraction and its cube, exercising cancellation
in the quotient-rule normalization. Replay includes prepared rejected and valid
witnesses enlarged by a degree-32 polynomial; generation is timed separately.
All polynomial outputs are hashed in full.

Input and certificate preparation occurs in initialization outside measured calls.
Some family anchors intentionally combine operations (for example the height
anchor includes normalization and powering); their times are aggregate latency,
not isolated-kernel throughput. The `sizes` command checks full multiplication
plan agreement and reports raw/final lengths and coefficient bit lengths.
Prime-field plan agreement is also checked in computational conformance.
Polynomial-part division is a **structural-layer** comparison owned by
HexPolyFast. Certificate operations have
**no-comparable-surface-in-named-comparator**.

## Environment and reproducibility

Measured on an AMD EPYC 9455 (48 physical cores, 96 logical CPUs), Linux x86_64,
Lean 4.34.0-rc2, lean-bench 0.1.0. Fixed results below are medians of three
measured child runs after warmup, with an inner-repeat floor of 10 ms.
Scientific ladders use three outer trials, a two-second batch target, and the
unchanged ten-times-startup signal floor.
This is the shared development host `chungus2`, not a controlled dedicated timing runner.
Hardware-dependent conclusions are confined to the measured families.

```sh
lake build hexrationalfn_bench
.lake/build/bin/hexrationalfn_bench sizes
.lake/build/bin/hexrationalfn_bench verify
.lake/build/bin/hexrationalfn_bench run --filter RationalFnBench --export-file /tmp/rationalfn-bench.json
```

The CI integration extends the existing build, bench-verify and oracle steps.
There is no scheduled timing workflow in this checkout to extend; no new workflow
or CI job is introduced.

## Verdicts

The [clean `f1cd0e0a` scientific run](bench-results/hex-rational-fn-scaling-f1cd0e0a-chungus2-cpu5.json)
on logical CPU 5 passes all eight linear models. Every rung has eligible trials.
The normalized log-log slopes (zero is the declared model) are:

| Operation | Slope | Verdict |
| --- | ---: | --- |
| equal | -0.021522 | consistent |
| different | -0.011180 | consistent |
| inverse, before monic fast path | -0.002844 | consistent |
| inverse, monic fast path | -0.007958 | consistent |
| negate | 0.001553 | consistent |
| evaluate | -0.001521 | consistent |
| evaluatePole | -0.004091 | consistent |
| replay | 0.004226 | consistent |
| reject | -0.003719 | consistent |

The unchanged noise rule excludes one replay trial, one pole trial, and two
inverse trials out of 24 each; raw excluded samples remain in the export.
The default 20% leading-rung warmup trimming is also unchanged. The
[monic-fast-path rerun](bench-results/hex-rational-fn-inverse-2d39b1ca-chungus2-cpu6.json)
has all 24 trials above the signal floor; its fitted suffix starts at 256.
At degree 16384, full-output-hashed inversion drops from 4210.65 to 107.86 µs
(39.0×). The algorithm now shares the swapped arrays for a monic numerator;
the remaining linear benchmark cost includes hashing, not coefficient scaling.
The [earlier `78ea53cd` run](bench-results/hex-rational-fn-scientific-78ea53cd-chungus2-cpu2.json)
retains its failed evaluation verdicts: 0.5-second batches did not clear that
run's startup floor. Increasing batch duration, not weakening the signal gate,
produced the eligible run above. This earlier export also contains all 35
passing fixed hashes and the pre-fast-path latency baselines below.

The [initial `e12e8861` run](bench-results/hex-rational-fn-query-e12e8861-chungus2-cpu3.json)
exposed a real fixture error: changing the leading coefficient caused immediate
rejection rather than the declared linear walk. The corrected constant-coefficient
fixture keeps the same model and schedule; see
[#10096](https://github.com/kim-em/hex-dev/issues/10096).

## Multiplication-plan crossover

Dense rational inputs have coefficient lengths 16, 32, 64, 128 and small integer
coefficients. Results of every plan agree coefficient-for-coefficient. Latencies
include the common full-output hash.

| Length | Schoolbook (µs) | Karatsuba cutoff 8 (µs) |
| --- | ---: | ---: |
| 16 | 51.11 | 47.45 |
| 32 | 198.81 | 158.96 |
| 64 | 789.19 | 511.17 |
| 128 | 3128.82 | 1599.72 |

The first sampled recursive length, 16, already shows an advantage for cutoff 8.
Products at or below the cutoff use the schoolbook base case. The aggregate
cutoff search covers both smaller and larger cutoffs on the same four input pairs:

| Cutoff | Combined latency (µs) |
| --- | ---: |
| 1 | 3833.34 |
| 2 | 2958.33 |
| 4 | 2478.37 |
| 8 | 2297.85 |
| 16 | 2432.58 |
| 32 | 2866.56 |
| 64 | 3466.51 |

Schoolbook takes 4191.96 µs over those pairs. The lowest measured
median is at cutoff 8, bracketed by slower tested cutoffs 4 and 16, so the default
is 8. This does not assert an optimal cutoff for every coefficient field, height,
or degree, or locate an exact degree crossover between the sampled lengths.

## Cancellation versus multiply-then-normalize

Both routes receive identical canonical operands `a/(a+1)` and `(a+1)/a`,
where `a` is a dense monic polynomial. Both must return the complete canonical
pair `(1,1)`. Both routes use the default multiplication plan, and the naive
route uses the same default normalization as the library.

| Degree of a | Cross-cancel (µs) | Multiply then normalize (µs) | Naive intermediate degree |
| --- | ---: | ---: | ---: |
| 1 | 13.44 | 13.75 | 2 |
| 2 | 23.78 | 22.75 | 4 |
| 4 | 37.75 | 47.81 | 8 |
| 8 | 73.76 | 127.50 | 16 |
| 16 | 181.77 | 390.46 | 32 |

Degree 1 is approximately tied; degree 2 favors the naive route slightly.
The first sampled sustained advantage for cancellation is degree 4, with a
larger advantage at degrees 8 and 16. Cross-cancellation forms only constant
output products in this family, avoiding the displayed intermediate degrees.
This is the maximal-cancellation family, not a mixed workload or a per-rung
coprime control. No claim is made that cancellation wins on every small coprime input.

The combined multiplication anchor (including the no-cross-cancellation control)
takes 1894.59 µs versus 3098.96 µs
for multiply-then-normalize, with identical frozen full-result hashes.

## Family latency anchors

These rows execute all seven prepared cases; they are not per-single-fraction times.

| Anchor | Median (µs) |
| --- | ---: |
| Normalization | 1433.56 |
| Addition | 4732.61 |
| Height | 2360.21 |
| Queries | 39.20 |
| Calculus | 984094.97 |
| Generate | 1936.78 |
| Replay | 2473.75 |

The height multiplier is applied only to the raw numerator; the denominator's
scalar stays fixed at -2, so normalization does not cancel the height multiplier.
At input heights 16, 64 and 256, maximum canonical numerator widths are
18, 66 and 258 bits, and the corresponding cubed widths are 55, 199 and 775 bits.
Raw numerators reach 259 bits while polynomial shapes stay fixed. The `sizes`
command reports raw and final widths independently from degree; canonical product
widths are not a proxy for all temporary coefficient
growth inside Euclidean arithmetic. Profiling that growth remains Phase-4 work.

## Independent FLINT comparator

**FLINT fmpz_poly_q via a persistent C driver** is informational.
`scripts/bench/rationalfn_flint.c` calls the public `fmpz_poly_q_` routines for
canonicalisation, add/subtract/multiply/divide, inverse, powers, derivative,
equality and rational evaluation. The Python coordinator uses exact `Fraction`
conversion and compares complete canonical coefficient arrays, not hashes or
samples. `--rows` records both FLINT integer-pair and Hex rational-pair
representation lengths and maximum coefficient widths.

The driver stays alive across requests. Parsing, rational-to-integer conversion,
input canonicalisation for arithmetic, output conversion, and output comparison
are outside the measured operation. Normalization starts from a fresh raw copy
each repetition, with the copy outside timing. Total inverse/division at zero
are explicitly adapted to zero without calling FLINT's rejecting operations;
zero raw denominators and evaluation poles remain failures. Rejected raw
denominators have no measured time and are excluded from timing summaries.
These adapted cases
must not be mistaken for timings of a FLINT inverse/division call.

Example build (requires FLINT development headers and library):

```sh
cc -O2 -Wall -Wextra scripts/bench/rationalfn_flint.c -lflint -o /tmp/rationalfn-flint
python3 scripts/bench/rationalfn_flint.py /tmp/rationalfn-flint \
  conformance-fixtures/HexRationalFn/rationalfn.jsonl --repeats 100 --rows
```

The local comparator uses FLINT 3.6.0 and Clang 22.1.8. The committed QQ fixtures
agree in full. The `emit-scaling` command produces 54 further complete matched
fixtures: six query operations at eight degrees plus six trivial-input controls.
The [CPU-10 comparator export](bench-results/hex-rational-fn-flint-60fcb231-chungus2-cpu10.json)
retains three trials of 10000 calls per case, all full-output comparisons,
representation sizes, affinity, and driver/source/fixture SHA-256 fingerprints.

## Comparator ratios

These are native median / FLINT median on the identical canonical inputs
(larger is slower). Native inversion uses the monic fast path; the other
operations use the clean `f1cd0e0a` run. Native complete-output hashing is inside
the timed loop, while FLINT output conversion/comparison is outside; these are
end-to-end native benchmark ratios, not equal-overhead kernel ratios.
Input conversion and process I/O are outside both timers. C dispatch and clock
overhead are inside the FLINT timer. Each operation's trivial-input control
conservatively includes its tiny kernel as well as that overhead.

| Degree | Equal | Inverse | Negate | Evaluate | Pole |
| --- | ---: | ---: | ---: | ---: | ---: |
| 128 | 2.8× | 1.8× | 18.3× | 27.7× | 27.3× |
| 256 | 2.8× | 1.8× | 18.2× | 28.5× | 29.3× |
| 512 | 2.8× | 1.8× | 18.6× | 29.2× | 28.8× |
| 1024 | 2.7× | 1.8× | 18.2× | 28.7× | 30.4× |
| 2048 | 4.2× | 2.8× | 31.8× | 50.7× | 53.2× |
| 4096 | 4.9× | 2.9× | 32.1× | 49.8× | 48.8× |
| 8192 | 2.8× | 2.9× | 31.9× | 50.6× | 52.2× |
| 16384 | 4.7× | 2.9× | 31.7× | 50.5× | 51.2× |

The controls are 34.32 ns (equal), 39.67 ns (inverse), 37.13 ns (negate),
57.57 ns (evaluate), and 39.15 ns (pole). They exceed 5% of measured C time only
at degree 128 for equal (5.15%), inverse (7.75%), and negate (7.13%). Subtracting
the control gives ratios 2.9×, 1.9×, and 19.7× there, respectively; both raw and
adjusted ratios are informational. All other listed control fractions are below
5%. The unequal query is **overhead-dominated and ineligible for a speed ratio**:
its 25–28 ns FLINT calls are indistinguishable from its 27.62 ns control at every
rung. FLINT's early shape rejection differs from Lean's numerator-first traversal.
It remains a complete-output correctness comparison, not a throughput claim.

The inverse baseline was 65–113× slower before the monic fast path. The largest
remaining eligible query gap is pole evaluation, profiled below.
No matched throughput claim is made yet for arithmetic, normalization,
height, or calculus. Replay has no comparable surface in `fmpz_poly_q`.

Reproduction (choose and record an idle CPU before timing):

```sh
.lake/build/bin/hexrationalfn_bench emit-scaling > /tmp/rationalfn-scaling.jsonl
taskset -c CPU python3 scripts/bench/rationalfn_flint.py /tmp/rationalfn-flint \
  /tmp/rationalfn-scaling.jsonl --repeats 10000 --trials 3 --json
taskset -c CPU .lake/build/bin/hexrationalfn_bench run \
  --filter RationalFnScaling --export-file /tmp/rationalfn-scaling-results.json
```

## Profile

The query inverse and certificate replay profiles use deterministic parameter
8192, clean source commit `2d47ce183af8257fdc961b777589546417bbfde8` (before the
monic optimization), AMD EPYC 9455, NixOS/Linux 6.12.100 x86_64, Lean 4.34.0-rc2,
lean-bench 0.1.0, samply 0.13.1 at 999 Hz, and lean-bench-samply
`9356baa2f5757ee40320a897bd284914d5bb9f5e`. Captures are unpinned: a pinned samply
attempt produced zero samples and failed calibration, and is not evidence.
The post-optimization inverse and pole captures use clean commit
`e3075d6134d25d049b59459f268d739d41a9ee66` on the same environment.
Only benchmark-thread samples inside the recorded timed regions are retained;
these loops include the benchmark's complete-result hash.

| Case | Own code | GMP | Allocation/free | Lean runtime | Classified |
| --- | ---: | ---: | ---: | ---: | ---: |
| inverse, before fast path | 0.00% | 37.00% | 38.05% | 21.86% | 96.92% |
| replay | 0.56% | 36.54% | 40.92% | 21.85% | 99.87% |
| inverse, monic fast path | 0.06% | 0.00% | 0.00% | 99.94% | 100.00% |
| pole evaluation | 0.00% | 36.14% | 45.70% | 18.13% | 99.97% |

For post-optimization inversion, the table classifies the identified core
`instHashableRat.hash` leaf (73.18%) as Lean runtime/library support. The generic
summary classifier leaves that symbol in `other`; the raw summary is unchanged.

The [inverse summary](bench-results/hex-rational-fn-inverse-2d47ce18-profile.json)
attributes 95.53% inclusive cost to `RationalFn.inv`, 94.11% to `Rat.mul`, and
85.93% to `lean_nat_gcd`. Inversion scaled both arrays even when the scale was
one. The monic branch now returns the reversed pair directly, with the same
coprimality and monicity proofs. This removes unnecessary coefficient operations;
it is not a change to generic nonmonic inversion or rational arithmetic.

The [post-optimization inverse summary](bench-results/hex-rational-fn-inverse-e3075d61-profile.json)
shows `RationalFn.inv` at only 0.09% inclusive, with no sampled GMP or allocation
leaves. Full-output hashing dominates the remaining loop. This profile measures
the registered operation-plus-hash contract; its linear slope must not be read
as a linear lower bound on monic inversion alone.

The [replay summary](bench-results/hex-rational-fn-replay-2d47ce18-profile.json)
attributes 100% inclusive to `RationalFn.check`, 90.24% to `DensePoly.mulImpl`,
7.71% to `DensePoly.addImpl`, and 2.05% to trailing-zero trimming. These are the
two dense-witness products, sum, and canonical comparison named by the replay
model. Rational multiplication/addition and their gcd/allocation costs dominate
the leaf budget; no Euclidean witness generation occurs in replay.

The [pole summary](bench-results/hex-rational-fn-pole-e3075d61-profile.json) places
99.94% inclusive cost in `RationalFn.eval?` and its array Horner fold, with
`Rat.mul` at 65.86%, `Rat.add` at 32.96%, and `lean_nat_gcd` at 86.15%.
The denominator is evaluated before the numerator, so no numerator evaluation
or rational division occurs at this pole. The observed gap is in the registered
Horner arithmetic and its allocation, not hidden fixture preparation.

Filtering diagnostics (full blocks are retained in the summaries):

| Case | Residual | Timed duration | Retained samples | ±5 ms sensitivity | Confidence |
| --- | ---: | ---: | ---: | --- | --- |
| inverse, before fast path | 0.913 ms | 4339.949 ms | 4313 | passed | passed |
| replay | 1.380 ms | 3773.230 ms | 3749 | passed | passed |
| inverse, monic fast path | 0.881 ms | 3508.679 ms | 3479 | passed | passed |
| pole evaluation | 1.295 ms | 3164.139 ms | 3149 | passed | passed |

Exact capture command, with `OP=inverse` or `OP=replay`:

```sh
python3 /tmp/lean-bench-samply/scripts/profile_bench.py \
  --bench-exe .lake/build/bin/hexrationalfn_bench \
  --bench-name Hex.RationalFnScaling.OP --param 8192 \
  --target-nanos 5000000000 \
  --out /tmp/hex-rationalfn.ycP9Of/OP-unpinned-8192.json.gz \
  --samply-args '--rate 999 --unstable-presymbolicate'
```

Raw compressed profiles remain developer-local, not committed.
The post-optimization commands differ only in the output path
(`/tmp/hex-rationalfn.ycP9Of/inverse-fast-8192.json.gz` and
`/tmp/hex-rationalfn.ycP9Of/pole-8192.json.gz`) and use registered names
`Hex.RationalFnScaling.inverse` and `Hex.RationalFnScaling.evaluatePole`.

## Concerns

Phase 4 remains open. Normalization, addition, multiplication, coefficient-height,
and calculus need operation-specific scientific coverage, matched comparators,
and valid timed-region profiles. Existing fixed registrations cannot currently
be profiled through lean-bench's timed-region interface; this is tracked in
[#10097](https://github.com/kim-em/hex-dev/issues/10097) and
[lean-bench #73](https://github.com/kim-em/lean-bench/issues/73).
The roughly 984 ms aggregate calculus anchor must be attributed before selecting
an optimization. Generic nonmonic inversion, query bit-height effects, certificate
generation, and the Mathlib proof track also remain outside the qualified subset.
Both libraries retain `done_through: 3`.

The build-only `HexRationalFnMathlib.Tests` checks a nontrivial literal
certificate through the headline theorem using kernel reduction, separately
from the native replay timing. Axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`.
