# HexRank performance

HexRank remains at `done_through: 3`. Integer and polynomial-ring evidence is
complete below; the native quotient checker still has an unresolved scaling
result. [#10352](https://github.com/kim-em/hex-dev/issues/10352) owns that
remaining obligation. Tactic/kernel proof evidence remains in the separate
[carrier report](hex-rank-carriers-performance.md).

## Bench targets

```sh
lake build hexrank_bench HexRankMathlib hexrank_emit_fixtures
lake exe hexrank_bench list
lake exe hexrank_bench verify
/tmp/hexvenv/bin/python -m unittest scripts.oracle.test_rank_bench scripts.oracle.test_rank_stages scripts.bench.test_rank_measure scripts.bench.test_rank_analyze
python3 scripts/check_dag.py
python3 scripts/ci/check_benches_mathlib_free.py
python3 scripts/ci/check_rank_compiler.py
```

The Mathlib-free driver has 441 registrations: 48 integer parametric targets,
60 native polynomial fixed cases, eight quotient-witness parametric targets,
288 paired scalar anchors, 12 polynomial rank references, 24 polynomial stage
references, and one protocol control. The existing CI smoke route checks 92
native cases at the smallest smoke input; the quotient smoke dimension is four,
not its scientific floor 128. External anchors are scheduled-only. The
[driver artifacts](bench-results/hex-rank-10352/driver/) retain the list and
both native and external verification outputs. CI adds tests inside its existing
job and preserves its existing bench list/verify route.

| Public surface | Evidence track and measured path |
| --- | --- |
| `rowReduceWith`, `rowReduceFF`; `rankWith`, `rankProfileWith`, `rank`, `rankProfile` | Compiled first pass: integer `runRowReduce*`, polynomial `run{RatPoly,Mv}*Rank*`, and matched scalar anchors. Rank/profile wrappers project the same array reduction. |
| `rankCertWith`, `rankCert` | Complete certificate, including both elimination passes: `runRankCert*` and polynomial `*Cert*`. |
| `rankCertOf` | Assembly from a prepared first pass: `Second.*` and polynomial `*Second*`. Matrix and reduced form are prepared outside timing. |
| `checkRank` | `runCheckRank*` and polynomial `*Check*`; certificate construction is excluded. Integer flattening/reconstruction is included; polynomial inputs are cached actual values. |
| `certifyRankWith`, `certifyRank` | Complete producer plus checker: `Certify.*` and polynomial `*Certify*`. |
| `rankWitness`, `rankWitnessWith` | `Witness.*`, including the modular inverse and self-check. The fixed-modulus entry point is the constituent attempt inside the retrying producer. |
| `PolyWitness.produce` | `Quotient.produce{Full,Deficient}`; its actual private rational preparation and modular completion are separated as `prepare*` and `finish*`. No substitute rank algorithm is used. |
| Native `checkRankPoly` | `Quotient.check*`, with witness construction excluded from timing. |
| Kernel replay through `checkRankList`, `checkRankListPacked`, `checkRankPoly`; tactic elaboration and proof construction | Proof track in HexRankMathlib, owned by the existing fresh-module probes and carrier report. Native checker timing does not replace kernel-proof evidence. |
| Soundness, completeness and correspondence | Mathematical API; `rankCertWith_check`, `checkRank_sound`, and `rankWith_eq` remain present and build. |

`Produce.lean` imports `ReduceImpl` before public producers compile. Generated
code therefore uses the proved array replacement for both certificate passes
and public rank wrappers. The retained [import-only comparison](bench-results/hex-rank-10352/compiler-route/)
uses six adjacent alternating AB/BA pairs of `runMvCert12`: before/after medians
6.741/7.467 s, all six after timings higher, median paired increase 0.456 s.
This repairs inconsistent compiler routing but is not a speedup. Both arms use
the earlier `ae2014190` fixture and 30-second operational cap. The final fixture
has its own independently specified operation budget below; neither its timings
nor its budget retroactively change that comparison.

Integer ladders are `16,24,32,48,64,96,128,192,256`, six trial-major outer trials.
Preparation checks expected rank, the certificate, and the shifted family's
zero-column prefix and first pivot. Polynomial preparation similarly validates
rank and certificate. Every fixed case checks the expected rank/Boolean hash;
parametric integer and quotient outputs are independently checked by the runner.
The quotient preparation tuple is hashed for per-rung agreement, and prep
validates the actual resulting witness. Failures are retained and stop any pass
claim.

- Dense entries use splitmix64 seed `1000003 + 1009*i + j`, reduced modulo 11
  into `[-5,5]`. Rank is checked. These are individually bounded entries.
- Low-rank products use ranks 2/8 and factor sizes 64/1024 bits. Factor seeds
  are `7919*salt + 104729*i + 1299709*j`, salts 3/5; the high bit is set and
  signs alternate with `i+j`. Product terms share a sign and do not cancel.
  Entries can have `2*bits + ceil(log2 r)` bits; no identity pivot block is inserted.
- Deficient products use small splitmix64 factors, salts 7/11, ranks `n-1`
  and `n/2`, including a shifted half-rank matrix with its first `n-r` columns
  zero. Entry magnitude satisfies `B ≤ 25r ≤ 25n`.
- Polynomial fixtures use the original 64-bit LCG, salts 13/17 for rational
  coefficients and 19/23 for two-variable integer coefficients. Dimensions
  are 4/8/12, full and half rank. The driver defines the index offsets/products.
  Scalar rational variants divide integer row i by `1+(i%7)` and serialize the
  actual normalized Lean rationals.
- Quotient fixtures extend the companion's quadratic block example: defining
  polynomial `x²-2`, blocks `[[x,1],[1,x]]` of determinant one, with duplicated
  rows and zero trailing columns for half rank. Coefficients stay bounded.
  They measure quotient-field witnesses, independently of polynomial-ring rank.

## Verdicts

The independent models follow the SPEC's [complexity derivation](../HexRank/SPEC/hex-rank.md#complexity)
and [ordered evidence modes](../HexRank/SPEC/hex-rank.md#benchmarking).
Fixed-rank integer paths use mode 1, `n²`, since rank and minor bit lengths are
bounded independently of n. Their isolated second pass uses the stronger
constant model on the prepared fixed-size pivot block. Dense and growing-rank
products use mode 2: `O(n³)` arithmetic on Hadamard-bounded
`O(n(log n + log B))`-bit minors with a schoolbook quadratic arithmetic bound.
The declarations are `n⁵(log₂ n+3)²` for dense entries and
`n⁵(2 log₂ n+5)²` for products. GMP regime changes preclude a justified tight
wall-time power law. These models were declared before measurement.

All **48 integer paths** satisfy their declared modes; the
[complete verdict table](bench-results/hex-rank-10352/integer-verdicts.md)
links every export, model, slope and eligible-rung count. Here β is the harness
slope of time divided by the model. Negative mode-2 slopes are passing upper
bounds, not two-sided consistency; the harness calls these faster cases
`inconclusive`. All original rows remain, including below-floor observations.
Six initial resolution failures have one configuration-adjusted follow-up each:
rank-2/1024-bit checker at 2 s, `Certify`/`Witness` at 8 s, shifted half-rank
certificate, rank-(n−1) second pass and half-rank `Certify` at 4 s. Other passing
cases were not rerun to improve their presentation. These are batch targets,
not per-call performance budgets. Evidence resolution varies: the original
rank-8/1024-bit checker has only three of nine eligible rungs and a null fitted
slope; its consistency verdict comes from the harness's flat-ratio criterion.
The table exposes this weaker range rather than implying nine resolved rungs.

All **60 polynomial cases** use mode 3, giving up asymptotic regression
detection for these canonical inputs. The dimension-only parametrisation
was audited on the declared 4/8/12 schedule: fixed input support does not bound
minor degree, support or coefficient size independently of dimension, as the
coefficient audit below demonstrates. No tight wall-time law follows from the
field-operation count. The SPEC supplies no published bit-time upper bound
covering the profiled exact polynomial division and monomial-order costs;
a scalar Hadamard bound alone would not cover them. Following its explicit
mode-3 classification, no parametric timing fit is claimed for these cases. The
[budget policy](bench-results/hex-rank-10352/polynomial-budget-policy.json)
was fixed before the matched stage comparisons: twice the sum of the applicable
SymPy reference medians (`rank`, isolated second pass, checker). Complete
certificate sums the first two references; `Certify` sums all three. The
[numeric budgets and verdicts](bench-results/hex-rank-10352/polynomial-verdicts.md)
and [analysis](bench-results/hex-rank-10352/analysis.json) retain every exact
reference. These are fixed absolute ceilings from retained measurements, not
live ratios or the 60-second child timeout. Later runs must compare against
these [frozen numeric ceilings](bench-results/hex-rank-10352/polynomial-budgets.json), read by `rank_analyze.py --budgets`. Verification also checks their exact derivation against the retained reference samples; it never updates a ceiling to accommodate a new native run. The reference second pass ranks the selected pivot
block augmented by identity; the reference checker verifies the same exact
matrix identities using the actual native certificate. Building those operands
is inside the reference timed operation, matching native stage boundaries.

At dimension 12, separate producer/checker medians are:

| Case | First pass ms | Second pass ms | Certificate ms | Checker ms | Certificate/checker |
| --- | ---: | ---: | ---: | ---: | ---: |
| `RatPoly` full | 39.594 | 158.154 | 194.484 | 54.738 | 3.553 |
| `RatPoly` half | 52.511 | 16.394 | 69.759 | 24.278 | 2.873 |
| `Mv` full | 914.390 | 4303.023 | 5201.951 | 318.138 | 16.351 |
| `Mv` half | 1370.156 | 415.900 | 1790.989 | 202.928 | 8.826 |

These are descriptive medians from [polynomial exports](bench-results/hex-rank-10352/polynomial/),
not an assumption of exact additivity. The complete integer certificate/checker
ratios at n=256 include dense 2.580, low-rank-2/64-bit 1.341,
low-rank-8/64-bit 2.334 and low-rank-2/1024-bit 1.364. Integer checker timing
includes rebuilding its flattened input, so these are wrapper ratios.

The actual serialized dimension-12 matrices and certificates are retained in
[compressed input records](bench-results/hex-rank-10352/polynomial-inputs.jsonl.gz),
with capture commands/hashes and a reproducible [coefficient audit](bench-results/hex-rank-10352/coefficient-growth.json).
Full-rank rational input degree/support 1/2 grows to denominator degree/support
12/13 and adjugate 11/12; maximum adjugate numerator/denominator sizes are
45/19 bits. Full-rank multivariate input degree/support 1/2 grows to denominator
12/85 and adjugate 11/72, with maximum adjugate coefficient size 36 bits.
Half-rank product inputs already have degree two; their adjugates reach degree
10, support 11 (rational) or 61 (multivariate). The polynomial timings therefore
include substantial support growth despite small input support.

The quotient model is mode 1, cubic: prefix inverses on these fixed quadratic
blocks scan Θ(k²) entries at prefix k, summing to Θ(n³); lower-quotient and
native verification dots also traverse Θ(n³) entries. Fixed-degree bounded
coefficient arithmetic contributes no growing operand-size factor. This is a
claim about the stated block family, not arbitrary number-field matrices.
The initial `4,8,12,16,24,32,48,64` ladder is retained as inconclusive (faster);
fixed-degree inversion overhead dominates before the cubic scans. The unchanged
model/fixture was extended to `128,192,256,384,512,768,1024`, 2-second batch
target, six trial-major trials, 600-second operational cap including prep.
Seven of eight [large-ladder verdicts](bench-results/hex-rank-10352/quotient-verdicts.md)
are consistent. The full checker is inconclusive slower, β=+0.550; its sole
[unchanged rerun](bench-results/hex-rank-10352/quotient-check-rerun/checkFull.json)
is also inconclusive slower, β=+0.283. Both retain all 42 completed rows. No model downgrade or Phase-4 pass is
inferred from that result.

`finishFull` includes a complete `checkRankPoly` call on the same numerical
witness, after Θ(n²) modular construction. Yet at 1024 its median is 6.740 s,
against standalone checker medians 21.293 s (original) and 10.199 s (rerun).
The rerun spans 6.931–22.323 s; the deficient finish/check medians agree within
about 3% across the ladder. This is evidence of an unresolved measurement/context
interaction, not evidence establishing a super-cubic algorithmic path.
The containing operation's β=+0.062 is relevant evidence, but not a per-call
wall-clock upper bound on a separately scheduled checker: newly constructed
and cached witnesses can differ in memory layout/ownership, and the host
conditions differ. The eight original quotient schedules started within nine
seconds on independently selected CPUs, spanning multiple NUMA nodes. Their
host activity is retained context; it neither invalidates a completed sample
nor licenses a replacement checker pass. The standalone declared gate remains
inconclusive.

Exact scientific commands are recorded in every run's `metadata.json` and
`commands.jsonl`; these commands reproduce the schedules with a built executable:

```sh
python3 scripts/bench/rank_measure.py integer --out /tmp/rank-integer --python /tmp/hexvenv/bin/python
python3 scripts/bench/rank_measure.py attribution --out /tmp/rank-attribution --python /tmp/hexvenv/bin/python
python3 scripts/bench/rank_measure.py polynomial --out /tmp/rank-polynomial --python /tmp/hexvenv/bin/python
python3 scripts/bench/rank_measure.py quotient --out /tmp/rank-quotient --python /tmp/hexvenv/bin/python
python3 scripts/bench/rank_measure.py poly-references --out /tmp/rank-stages --python /tmp/hexvenv/bin/python
python3 scripts/bench/rank_collect.py SOURCE DESTINATION
```

Recorded measurements use frozen executables. Core source is `2b0ff6bf5`,
expanded attribution/polynomial source `bbedb4722`, small quotient source
`8a6e0aced`, large quotient source `a2f2303e1`. The checker-resolution follow-up
uses `b3360aca1` plus its retained dirty patch; the `Certify`/`Witness`
rank-2/1024-bit follow-ups use `655570d58` plus their dirty patches. These two
additional source snapshots back three of the 48 passing integer rows. The
[source manifest](bench-results/hex-rank-10352/source/manifest.json) supplies
compressed patches against merged main commit `ff87b54e3`, including all
Lean/Lake source needed to reconstruct these local revisions from a fresh clone.
The reconstruction helper applies only the recorded source scope, so unrelated
report/CI hunks in a dirty patch are excluded. For example:

```sh
python3 scripts/bench/rank_reconstruct.py --snapshot b3360aca1 --run reports/bench-results/hex-rank-10352/checker-resolution --destination /tmp/rank-reproduce
cd /tmp/rank-reproduce
lake build hexrank_bench
# Use this rebuilt .lake/build/bin/hexrank_bench with rank_measure.py --bench.
```

Both missing follow-up snapshots have been reconstructed and checked against
every recorded source hash. The manifest additionally covers the untimed input
capture's base `01eeb439a` and the capture hook archived as `5e9bc6ab8`. Each run records
binary/source hashes, exact command, CPU, host load and dirty patch (`source.patch.gz` when nonempty); child dirty
flags describe the evolving checkout, not a rebuilt frozen binary.
`hexrank_attribution_bench`, `hexrank_quotient_bench` and `hexrank_scale_bench`
are renamed byte-identical copies of the normal `hexrank_bench` Lake target at
the corresponding recorded revisions, not extra Lake targets. Rebuild that
target and pass its path through `--bench`; old absolute scratch paths in raw
commands need not exist. Each manifest records its frozen executable hash.
The attribution copy's SHA-256 is
`499475eb6ee476c23ff9855d422fd9b5fec05576996307d43c9ca01eabc8932f`.
Each `retention.json` hashes the unmodified exports/journal and losslessly compressed stdout (`.txt.gz`). Environment:
chungus2, AMD EPYC 9455, 96 logical CPUs, Linux 6.12.100, Lean 4.34.0,
lean-bench `8a37daf1074c3bdbd0da479b55538bad4a0022db`. No completed sample
is rejected for host activity. Earlier cap/prep diagnostics remain as diagnostics,
not replacement scientific evidence.

## Comparator ratios

The persistent service `scripts/oracle/rank_bench.py` receives the actual
Lean-generated matrix and, for stage references, certificate. Preparation,
decoding and output validation happen before timing. Each timed request
recomputes the exact operation and includes one JSON request/reply; there is no
result cache. Native scalar anchors use the same prepared matrix, without the
parametric wrappers' extra flattening copy. FLINT uses `fmpz_mat.rank()` and
`fmpq_mat.rank()`; SymPy uses `DomainMatrix.rank()` on `QQ[x]` or `ZZ[x0,x1]`,
with the existing conformance decoders and Python ground types. No numerical
rank or evaluation at sample points is substituted. Versions: Python 3.14.6,
python-flint 0.9.0, FLINT 3.6.0, SymPy 1.14.0; the
[environment supplement](bench-results/hex-rank-10352/comparator-environment.json)
records the underlying FLINT version omitted by the original service replies.
All comparators remain **informational**.

```sh
python3 scripts/bench/rank_measure.py protocol --out /tmp/rank-protocol --python /tmp/hexvenv/bin/python
python3 scripts/bench/rank_measure.py comparisons --out /tmp/rank-comparisons --python /tmp/hexvenv/bin/python
# Reproduce the analysis of the committed exports without rerunning measurements:
python3 -c 'import json, subprocess; subprocess.run(json.load(open("reports/bench-results/hex-rank-10352/analysis-command.json")) + ["--verify", "--check"], check=True)'
python3 scripts/bench/rank_tables.py --check
/tmp/hexvenv/bin/python scripts/plots/hex-rank-comparator.py --family dense-full-rank --check
/tmp/hexvenv/bin/python scripts/plots/hex-rank-comparator.py --family low-rank-large-coefficients --check
/tmp/hexvenv/bin/python scripts/plots/hex-rank-comparator.py --family rank-deficient-by-construction --check
/tmp/hexvenv/bin/python scripts/plots/hex-rank-comparator.py --family polynomial --check
```

The [full ratio table](bench-results/hex-rank-10352/comparator-ratios.md) and
[JSONL curves](bench-results/hex-rank-10352/comparator-curves.jsonl) record all
156 shared cases and six alternating adjacent AB/BA pairs per case. The original
controller handed off only after its active pair finished; the
[handoff record](bench-results/hex-rank-10352/comparisons/handoff.json) retains
that pair's actual exit status and Linux wait record, with unavailable elapsed
metadata explicitly null. The remaining 656 commands were partitioned among
eight CPU-pinned workers. Each case stayed with one worker, preserving block
order, adjacency and the exact frozen executable/service. The journals form a
disjoint union of all 936 scheduled pairs. `rank_resume.py` checks the frozen
handoff and binary hash; it does not repeat completed pairs.

| Request/reply control | Median μs |
| --- | ---: |
| Initial FLINT integer, FLINT rational, SymPy polynomial (one shared transport measurement) | 6.693 |
| Partition controls 0–7 | 7.692, 7.579, 7.708, 7.676, 7.741, 7.806, 7.917, 7.789 |

The comparator and synchronous caller share the selected CPU. Adjustment
subtracts the corresponding block's control before taking the external median;
it does not claim to subtract all cache-key or expected-output checks. Every
row shows raw and adjusted ratios, including overhead-dominated rungs.
Eligibility requires six successful pairs, overhead at most 50% on every pair,
and both arm medians at most 10 s. Values above the 1 s soft limit supply range;
values above 10 s and cap-censored arms remain visible outside eligibility.
A censored arm has no observed rank or per-call time; successful arms still
must match their expected outputs. Stage references have their own complete
24-case table in `analysis.json`; expensive references can set an absolute
budget without becoming eligible comparator-ratio evidence.

There are 142 eligible cases. The [dense plot](figures/hex-rank-comparator-dense-full-rank.svg)
shows a rising Hex/FLINT ratio: integer 43.13× at 24, 208.62× at 64,
392.49× at 128 and 943.62× at 256; rational 472.34× at 24 to 5557.64×
at its top eligible dimension 128. This is the largest eligible gap, profiled
below. FLINT's size-dependent fraction-free/multimodular selection differs
from Hex's fraction-free-only algorithm, as the SPEC's informational
classification anticipates; the gap is not a missed shared-algorithm goal.

The [low-rank plot](figures/hex-rank-comparator-low-rank-large-coefficients.svg)
shows falling ratios for rank two, with an apparent regime change between
32 and 48: at 1024 bits the integer ratio settles near 0.18× through 192,
then 0.14× at 256; rational ratios settle near 0.32–0.40×. At rank eight,
1024-bit ratios are roughly flat over 48–128 (integer 2.29/1.84/1.63/1.77×,
rational 3.43/2.69/2.96/3.09×), with the latter's 192/256 beyond 10 s.
At 64 bits the ratios generally decrease after 32, ending at 0.60/1.38×
(integer rank 2/8) and 2.95/6.36× (rational rank 2/8).

The [deficient plot](figures/hex-rank-comparator-rank-deficient-by-construction.svg)
separates three distinct shapes. Half-rank integer ratios decline from 27.10×
at 24 to 12.37× at 256; rational ratios fluctuate around 85–104× at 32–128.
Rank-(n−1) and shifted-half ratios rise: integer 27.92→241.40× and
25.96→799.50× over 24–256; rational 79.85→770.23× over 16–128 and
51.18→1611.32× over 16–192. These growing-rank gaps also compare the
SPEC's different algorithm classes. Ten paired commands contain native-arm
cap censoring, retained without fabricated ranks or times; none is eligible.

The [polynomial plot](figures/hex-rank-comparator-polynomial.svg) shows all three
canonical dimensions. Rational full/deficient ratios rise from 0.04/0.05× at
4 to 0.11/0.17× at 12; multivariate ratios rise 0.12→0.46→0.51× (full)
and 0.11→0.67→0.94× (deficient). The fixed-input budgets pass separately;
these three points do not establish an asymptotic speed ratio. SymPy chooses
its own exact-domain elimination, and Python/protocol startup contributes more
at the smallest cases. All plots use the same raw median values as the table;
[plot environment](bench-results/hex-rank-10352/plot-environment.json) records
the plotting-only dependencies and this Nix host's library-path setting.

## Profile

Four representative compiled profiles use source/binary `2b0ff6bf5`, the same
host and toolchain as the core ladders. Exact commands, automatic CPU placement,
profiler revision, sampler version and binary hash are in the
[profile manifest](bench-results/hex-rank-10352/profiles/metadata.json).
Reproduce with:

```sh
python scripts/bench/rank_profile.py --out /tmp/hexrank-perf-profiles-10352 --profiler-root /tmp/hex10170-lean-bench-samply
```

Captures use `perf record --clockid mono -e cycles:u -F 999 --call-graph dwarf`,
then samply import, the repository's complete timestamp-sequence normalization,
and filtering to `kernel` regions from `LEAN_BENCH_PROFILE_KERNEL=1`. Preparation,
hashing and post-call disposal are excluded. Bounded ELF symbolization and the
shared summary tool provide the leaf and inclusive tables. Raw profiles remain
at `/tmp/hexrank-perf-profiles-10352`; only analytical summaries are committed.
The initial direct-samply captures contained zero samples; their commands,
failure diagnostics and raw locations are retained under
[profiles/samply-record](bench-results/hex-rank-10352/profiles/samply-record/).
No sample was rejected for host activity.

| Family | Hex own | GMP | Allocation | Lean runtime | Classified | Samples |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| [dense-full-rank](bench-results/hex-rank-10352/profiles/dense-full-rank.json) | 1.69% | 29.36% | 51.84% | 10.76% | 93.65% | 3198 |
| [low-rank-large-coefficients](bench-results/hex-rank-10352/profiles/low-rank-large-coefficients.json) | 0.00% | 95.47% | 4.02% | 0.25% | 99.75% | 1988 |
| [rank-deficient-by-construction](bench-results/hex-rank-10352/profiles/rank-deficient-by-construction.json) | 1.36% | 35.89% | 46.16% | 10.92% | 94.32% | 3096 |
| [polynomial](bench-results/hex-rank-10352/profiles/polynomial.json) | 4.49% | 6.91% | 43.96% | 40.70% | 96.07% | 5211 |

Representatives are `runRankCertDense` at 64,
`runRankCertLowRank8At1024` at 128,
`runRankCertDeficientHalfShifted` at 128, and `runMvCert12`.
All four filtering diagnostics pass calibration, sample count and sensitivity;
the linked summaries contain the full diagnostic blocks and inclusive rankings.

| Family | Timed ms | Calibration residual ms | Sensitivity |
| --- | ---: | ---: | --- |
| `dense-full-rank` | 3203.828 | 0.974 | passed |
| `low-rank-large-coefficients` | 1990.463 | 0.328 | passed |
| `rank-deficient-by-construction` | 3102.313 | 0.898 | passed |
| `polynomial` | 5225.203 | 0.223 | passed |

Dense and deficient profiles put 98.06% and 94.25% inclusive cost in array
elimination, with `rankCertOf` contributing 67.26% and 40.60%. These map to the
first-pass, complete-certificate and isolated second-pass registrations.
Fixed low rank with large coefficients puts 95.47% of leaf samples in GMP,
consistent with large fixed-size minor arithmetic rather than dimension-dependent
coefficient growth. Its unwound Hex-inclusive share is only about 12%, so the
leaf evidence is stronger than fine-grained call-chain attribution in that case.

The polynomial profile puts 82.44% inclusive cost in `rankCertOf`; exact
multivariate division accounts for 50.49% and monomial comparison 43.96%, with
overlapping inclusive shares. These are the polynomial second pass's arithmetic,
not hidden matrix/certificate preparation. Separate `*Second*` targets make that
cost measurable; their individual absolute budgets are recorded with the other polynomial verdicts.


The additional [quotient producer profile](bench-results/hex-rank-10352/profiles/quotient-witness.json)
uses `Quotient.produceFull` at 32: 2977 samples, 91.70% classified,
preparation 97.68% inclusive, elimination 83.71%, inversion 31.78%, and xgcd
28.82% (overlapping shares). Preparation and modular completion map to the
separate `Quotient.prepare*` and `finish*` targets. Its raw profile is at
`/tmp/hexrank-quotient-profile`; the adjacent metadata records the exact command.

The [worst eligible comparator-gap profile](bench-results/hex-rank-10352/profiles/rational-dense.json)
uses the native rational dense anchor at 128: 4332 samples, 94.74% classified,
GMP 52.24%, allocation 32.83%, runtime 9.60%; array reduction accounts for
96.47% inclusive and exact division 25.21%. This is the existing first-pass
path, with rational arithmetic costs rather than external protocol overhead.
Raw capture: `/tmp/hexrank-rational-profile`; its filtering calibration and
sensitivity pass.

The [unexpected checker profile](bench-results/hex-rank-10352/profiles/quotient-checker.json)
at 1024 retains 9987 samples over 10008.470 timed ms; calibration residual
0.141 ms, sensitivity passed, 99.99% classified. Leaf costs are polynomial
`dot` 65.03%, list `nth` 24.74%, `mul` 4.68%, `add` 4.42%, allocation 0.40%.
Deep recursive stacks lose some outer frames, so the 74.21% inclusive `dot`
share cannot be compared directly to the incompletely unwound 44.20%
`checkRankPoly` share. These costs occur in the isolated checker target, not
witness preparation. Raw capture: `/tmp/hexrank-checker-profile`.

## Concerns

- [#10352](https://github.com/kim-em/hex-dev/issues/10352): resolve the full-rank quotient checker's inconclusive 128–1024 result, including its discrepancy with the containing `finishFull` target. The original measurement (β=+0.550), sole unchanged rerun (β=+0.283), and dot/list-access profile are retained. The data do not establish an algorithmic super-cubic path or a wall-time upper bound from separately scheduled `finishFull`. The cubic model is unchanged; no inconclusive evidence is promoted to a pass.
