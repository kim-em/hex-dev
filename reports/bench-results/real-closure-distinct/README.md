# Complete root routes with growing root counts

On these fixed rational inputs, the generic tower route is faster for the
`∏(X-i)` family and slower for the quadratic-root family. At eight roots,
its median complete-call cost is 127.5 ms versus 533.1 ms for the canonical
backend on `∏(X-i)`, and 5577.2 ms versus 198.2 ms on
`(X²-2)(X²-3)(X²-5)(X²-7)`. These are descriptive observations on the shared
host, with no fitted scaling law or significance claim.

Both arms run the complete public root operation and the same exact consumer:
root count, multiplicity one, adjacent ordering, prescribed rational values or
quadratic signs/squares. The generic arm is `Trivial.Rational.roots`, including
conversion of every returned native root to a canonical algebraic real; the
canonical arm is `RealAlgebraicPoly.roots`. Coefficient lifting and preparation
are outside the timed batch. Independent python-flint 0.9 / FLINT 3.6 checks
all sixteen functional records by reconstructing their canonical roots and
factoring the original inputs. This is a rational-coefficient comparison;
selected algebraic coefficients and arbitrary towers remain outside its scope.

## Timing observations

Each cell is the median and full range of six retained per-call batch estimates
in milliseconds. Ratios and differences are computed within each adjacent
pair, then summarized; the ratio median is not the ratio of the marginal medians.
`N` is both input degree and distinct real-root count.

| Case | Generic ms [range] | Canonical ms [range] | Paired generic/canonical [range] | Paired generic − canonical ms [range] |
| --- | ---: | ---: | ---: | ---: |
| Rational2 | 0.973 [0.949, 1.014] | 2.125 [2.101, 2.703] | 0.451 [0.375, 0.468] | -1.166 [-1.689, -1.124] |
| Rational4 | 6.606 [6.559, 6.966] | 11.739 [11.622, 26.497] | 0.562 [0.252, 0.582] | -5.127 [-19.824, -4.995] |
| Rational6 | 34.384 [33.915, 39.426] | 76.565 [75.917, 88.205] | 0.449 [0.444, 0.452] | -42.180 [-48.779, -41.767] |
| Rational8 | 127.510 [122.944, 133.512] | 533.075 [518.222, 572.994] | 0.235 [0.228, 0.256] | -408.796 [-442.368, -385.666] |
| Quadratic2 | 6.596 [6.313, 7.247] | 2.500 [2.483, 3.628] | 2.554 [1.997, 2.672] | 3.969 [3.618, 4.170] |
| Quadratic4 | 89.926 [87.872, 100.615] | 10.179 [10.028, 11.163] | 8.813 [8.513, 9.761] | 79.570 [77.844, 90.307] |
| Quadratic6 | 975.010 [924.082, 1224.055] | 37.970 [36.689, 74.028] | 24.986 [16.535, 29.431] | 936.380 [886.671, 1150.027] |
| Quadratic8 | 5577.245 [5446.655, 6402.381] | 198.243 [195.268, 214.328] | 28.298 [27.793, 31.078] | 5379.001 [5250.684, 6188.053] |

![All retained timing batches](root-routes.png)

The markers show medians, the faint dots show every batch, and bars show full
ranges. The logarithmic time axis does not imply a fitted complexity model.
The larger canonical outliers at Rational4 and Quadratic6 remain in the data.
All 96 raw batches, inner repeat counts and paired values are in
[analysis.json](analysis.json).

## Inputs and memory scope

Coefficient bits are the largest integer coefficient bit length. Native
point/selected counts come from an untimed execution of `Roots.roots`; they
are observed branch counts, rather than an external prediction of the finite
bisection policy. Each input's single native count observation is copied onto both method records;
the oracle checks consistency of those copies, not two independent executions.

| Case | Degree / roots | Coefficient bits | Native points / selected |
| --- | ---: | ---: | ---: |
| Rational2 | 2 | 2 | 1 / 1 |
| Rational4 | 4 | 6 | 2 / 2 |
| Rational6 | 6 | 11 | 3 / 3 |
| Rational8 | 8 | 17 | 4 / 4 |
| Quadratic2 | 2 | 2 | 0 / 2 |
| Quadratic4 | 4 | 3 | 0 / 4 |
| Quadratic6 | 6 | 5 | 0 / 6 |
| Quadratic8 | 8 | 8 | 0 / 8 |

All RSS cells below are median [full range] in KiB.

| Case | Generic whole arm | Canonical whole arm | Generic child | Canonical child |
| --- | ---: | ---: | ---: | ---: |
| Rational2 | 74690 [74360, 75072] | 75022 [74256, 75324] | 68624 [65368, 69260] | 68692 [67968, 69068] |
| Rational4 | 74642 [74164, 75072] | 74802 [74136, 75240] | 68696 [68624, 69300] | 68500 [68432, 68568] |
| Rational6 | 74996 [74336, 75260] | 74864 [74288, 75264] | 68530 [67804, 69204] | 68478 [68172, 68944] |
| Rational8 | 74728 [74140, 75160] | 74908 [74396, 75148] | 68558 [68292, 69248] | 68424 [68096, 68856] |
| Quadratic2 | 74384 [74280, 75096] | 74954 [74324, 75236] | 68680 [68536, 69152] | 68856 [68216, 69168] |
| Quadratic4 | 74560 [74096, 75220] | 74650 [74144, 75268] | 68746 [68460, 69100] | 68462 [63044, 69032] |
| Quadratic6 | 74806 [74536, 75076] | 74376 [68508, 74892] | 70424 [66868, 70964] | 68698 [65288, 69016] |
| Quadratic8 | 74614 [72328, 75176] | 74540 [68856, 75048] | 70338 [69900, 71032] | 68740 [68268, 68924] |

![Whole-arm maximum resident set](root-memory.png)

GNU time measures the whole arm, including the driver, all fourteen installed
inputs, warmup, calibration and benchmark children. Its maximum RSS is a
process/child high-water measure, not simultaneous aggregate memory or
operation-exclusive allocation. Similar values here do not establish equal
allocation costs or memory complexity. The measuring child's own Linux
`VmHWM` is retained in LeanBench's `raw_point.peak_rss_kb`; it includes the
child's runtime, installed inputs, tuning and complete batch, rather than
operation-exclusive live memory. The whole-arm maximum exceeds that child's
peak in 95 of 96 arms: another process, such as the driver or a tuning child,
sets the high-water baseline in those arms. These observations cannot identify
which process sets it. `alloc_bytes` is null throughout, so neither RSS series
measures allocation volume. Raw records also retain user/system CPU time,
elapsed time and exit status.

## Capture and reproduction

The [frozen protocol](protocol.md) predates timing at clean source
`85720b978d54bf92dfa47cb262b3639fc88da040`, retained by tag
`measurements/10378/distinct-85720b978d`. The runner used six trial-major rounds,
eight cases in registered order, adjacent generic/canonical arms alternating
AB/BA between rounds, `--repeats 1 --min-total-seconds 0.5`, 120-second per-call
and 3600-second process safeguards. All 96 arms completed in one capture; no
completed sample was discarded and no timing capture was repeated.

The host was `chungus2`, Linux x86_64, AMD EPYC 9455 48-Core Processor,
with automatically leased CPU 5. One-minute load before timing arms ranged
from 7.834 to 43.812, median 18.273; all per-command loads are retained. The enclosing experiment enforced 8 GiB aggregate
memory, zero swap and two Lean worker threads. The toolchain was
`leanprover/lean4:v4.35.0-rc3`, with clean pinned lean-bench
`8a37daf1074c3bdbd0da479b55538bad4a0022db`.
The explicit compiler wrapper used Clang and LLD. The driver C object was
rebuilt with that wrapper; its actual compile trace, generated C and object
hash are recorded. Dependencies may be cached, so this is not a fresh rebuild
of the full graph. The capture records compiler/tool versions, wrapper content,
link recipe, executable digest and selected source snapshots; the source tag
retains the complete implementation.

[capture.tar.gz](capture.tar.gz) contains all 415 indexed retained files except
the executable. [archive-index.json](archive-index.json) identifies every file,
Git source blob and the omitted executable's SHA-256 and size. The original
capture, including that executable, remains at the recorded local capture
path. The checked-in archive is sufficient to reproduce the analysis without
executing Lean or installing FLINT:

```sh
mkdir /tmp/hex-distinct
tar -xzf reports/bench-results/real-closure-distinct/capture.tar.gz -C /tmp/hex-distinct
python3 scripts/bench/analyze_real_closure_trivial.py /tmp/hex-distinct \
  --archive-index reports/bench-results/real-closure-distinct/archive-index.json \
  --output /tmp/hex-distinct-analysis.json
cmp /tmp/hex-distinct-analysis.json reports/bench-results/real-closure-distinct/analysis.json
```

A new collection uses a clean checkout of the measured tag, an explicit
`LEAN_CC`, GNU time and a Python environment with the pinned oracle packages:

```sh
python3 scripts/bench/collect_real_closure_trivial.py /absolute/new/capture \
  --suite distinct --oracle-python /absolute/oracle-env/bin/python3
```

The collector checks the benchmark driver's actual compiler trace, not only
the configured compiler path. If Lake reuses a driver object built by another
compiler, rebuild that derived object before collecting. Keep raw captures
outside the source checkout and use the project's experiment resource limits.
The default collector suite retains the earlier multiplicity comparison.

[figure-source.json](figure-source.json) records the analysis and plot-script
digests, command and rendering environment. [plot-requirements.txt](plot-requirements.txt)
pins the plotting environment. SVG and PDF versions accompany both PNGs.
Regenerate with:

```sh
python3 scripts/bench/plot_real_closure_trivial.py \
  reports/bench-results/real-closure-distinct/analysis.json /absolute/figure-output
```

## Diagnostic attribution

The two profiles target the unexpected route costs above. They use the exact
measured executable (SHA-256
`0db09da465ff0c79f637581955f2148b71f985271e7549bbe9f69ee25f9df1de`),
1000 Hz `cycles:u` perf sampling, `CLOCK_MONOTONIC` timestamps and 65528-byte
DWARF stacks. The source commits differ only in reporting and profile tooling
from the measured tag: Rational8 was captured at `f4f82c2f7a`, Quadratic8 at
`b21874a55e`. Their pushed source tags are
`measurements/10378/distinct-rational-profile-f4f82c2f7a` and
`measurements/10378/distinct-quadratic-profile-b21874a55e`. No benchmark or computational library source changed. Each
capture selected a CPU automatically, without a quiet-core preflight. The
filter uses LeanBench's `kernel` sidecars, excluding preparation, hashing,
sidecar writes and exit. Kernel calls made during profile tuning can be
included; these are attribution samples, not additional scientific timing arms.

| Profile | CPU | Regions / retained samples | Timed ms | Profile per call ms | Timing median ms | 1-min load | Residual ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| rational8 | 68 | 5 / 2593 | 2593.954 | 518.625 | 533.075 | 14.868 | 0.854 |
| quadratic8 | 17 | 1 / 10914 | 12262.288 | 12262.288 | 5577.245 | 71.137 | 0.159 |

Both filter-confidence and boundary-sensitivity checks pass. The quadratic
profile's single call is 2.20 times the timing median and slower than every
retained timing batch (5447–6402 ms), with higher recorded host load. Profiler
perturbation and shared-host activity may affect relative cost shares; the
percentages describe this retained diagnostic run, not the timing distribution.
The rational profile is close to its timing median. No profile was discarded
or repeated because of host activity. The registered fixed wrappers do not
appear in recorded stacks; the common `TrivialMeasurements.measure` body
appears in 98.03% and 99.40% respectively. Wrapper absence can follow compiled
inlining/tail calls, and does not establish that every parent frame survived.
Inclusive percentages remain lower bounds when frames are absent and overlap
along a call stack; do not add them. Unresolved leaf shares are 0.81% and 0.54%.

For Rational8.canonical, complex-root isolation accounts for 96.30%
inclusively, `exactRootFree` for 87.74%, and `taylor` for 73.12%. Allocation,
GMP and Lean-runtime leaf categories are 42.04%, 26.65% and 23.10%.
The source route in `HexRealAlgebraic/Roots.lean` delegates to the general
algebraic-polynomial backend and its complex-root isolation before canonical
real selection. This capture locates the rational-family cost in that path;
it does not show a common-field or factorization bottleneck.

For Quadratic8.generic, descriptor comparison contributes 57.38%
inclusively, with `Descriptor.buildComparison` at 56.84% and
`buildReencoding` at 56.75%. Canonical conversion contributes 41.74%;
complex-root isolation contributes 39.87%. Allocation, GMP and Lean-runtime
leaf shares are 33.13%, 25.96% and 29.49%. The source confirms two distinct
repeated operations: `CompleteRoots.roots?` sorts the generic entries via
checked root comparisons, and `Trivial.Rational.output` maps `Root.toCanonical`
over selected entries. Each `Root.canonical?` independently enumerates the
same head's canonical roots and matches its descriptor. All eight quadratic
roots are selected descriptors. These measurements identify comparison/reencoding
and conversion work to investigate; they do not establish the speedup of an
unimplemented reuse scheme or attribute the slowdown to BKR fallback.

[Profile manifests and summaries](profiles/index.json) retain commands, clean
source and filter revisions, executable hashes, all capture/postprocessing
artifact hashes, inclusive rankings, leaf categories and filter diagnostics.
Raw perf data, filtered profiles and executable snapshots remain outside the
checkout at their manifest paths. The filter revision is
`9356baa2f5757ee40320a897bd284914d5bb9f5e`; the compiled dependency retains the
pin above. Samply 0.13.1 and perf 7.2.8 ran on the same host model as the timing
capture. OS kernel time is excluded by `cycles:u`.

The rational capture's first postprocessing attempt failed because the selected
package checkout lacked `scripts/filter_samply.py`. Its original failure
manifest is retained. The committed postprocess mode validates all original
artifact hashes and the successful measurement row, then processes those same
samples with the clean filter checkout, recording both revisions and the
original manifest digest. No perf capture was repeated. The quadratic capture
and its first postprocessing completed successfully.

Reproduce a diagnostic capture from a clean source commit using the shared
resource-limited launcher and an external clean filter checkout:

```sh
python3 scripts/profile/real_closure.py --stage quadratic8 \
  --raw /absolute/new/raw-profile --output /absolute/new/profile-summary \
  --profiler-root /absolute/lean-bench-filter-checkout
```

The `rational8` stage selects the canonical arm. `--postprocess` reuses a
retained capture manifest without new measurement, writes derived files to a
new output location and verifies the original artifacts first.

## Coverage boundary

This extends the earlier [two-root multiplicity comparison](../real-closure-trivial/README.md)
with root count equal to degree, all roots real, at degrees 2–8. It does not
vary squarefree degree independently of real-root count, include nonreal roots,
or test nondyadic rational roots such as those of `∏(3X-i)`. Those axes,
selected algebraic-coefficient families, arbitrary extension
depth, outer isolation counters, certificate/evidence growth, the censored
canonical MetiTarski arm and the authoritative tower8 correction/archive remain
required. The
[Phase 4 coverage table](../../real-closure-phase4.md#measurement-coverage-and-remaining-work)
retains those independent obligations. Targeted diagnostic profiles explain
the unexpected family-dependent route costs separately from these timings.
