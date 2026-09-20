# HexRank performance

HexRank remains at `done_through: 3`. The compiled evidence below does not yet
close every Phase-4 gate; [#10352](https://github.com/kim-em/hex-dev/issues/10352)
owns the remaining work. Tactic/kernel proof evidence remains in the separate
[carrier report](hex-rank-carriers-performance.md).

## Bench targets

```sh
lake build hexrank_bench HexRankMathlib hexrank_emit_fixtures
lake exe hexrank_bench list
lake exe hexrank_bench verify
HEX_RANK_BENCH_PYTHON=/tmp/hexvenv/bin/python lake exe hexrank_bench verify --tag external
```

The driver has 48 integer parametric registrations, 60 native polynomial fixed
registrations, 288 paired scalar comparison anchors, 12 external polynomial
anchors and one protocol control. Default smoke verification selects all
integer parametric targets at their scientific floor 16, all native scalar
comparison variants at 16, and every native polynomial operation at 4: 84
checks. Larger scientific inputs are unchanged by smoke selection. External
anchors are scheduled-only and require python-flint and SymPy. The existing
CI target list and smoke route are unchanged.

| Public surface | Evidence track and measured path |
| --- | --- |
| `rowReduceWith`, `rowReduceFF`; `rankWith`, `rankProfileWith`, `rank`, `rankProfile` | Compiled first pass: integer `runRowReduce*`, polynomial `run{RatPoly,Mv}*Rank*`, and matched scalar comparison anchors. Rank/profile wrappers project the same array reduction. |
| `rankCertWith`, `rankCert` | Compiled complete certificate, including both elimination passes: `runRankCert*` and polynomial `*Cert*`. |
| `rankCertOf` | Compiled assembly from a prepared first pass: `Second.*` for integers and polynomial `*Second*`. The actual matrix and reduced form are prepared outside timing. |
| `checkRank` | Compiled `runCheckRank*` and polynomial `*Check*`; certificate construction is excluded from timing. Integer flattening/reconstruction is included; polynomial inputs are cached actual values. |
| `certifyRankWith`, `certifyRank` | Compiled complete producer plus checker: `Certify.*` and polynomial `*Certify*`. |
| `rankWitness`, `rankWitnessWith` | Native integer witness production: `Witness.*`, including the modular inverse and self-check. The fixed-modulus entry point is the constituent attempt inside the retrying producer. |
| `PolyProduce.produce` | Native polynomial-quotient witness production; separate compiled evidence is still missing. Its inclusion in a tactic build does not discharge that obligation. |
| Kernel replay through `checkRankList`, `checkRankListPacked`, `checkRankPoly`; tactic elaboration and proof construction | Proof track in HexRankMathlib, owned by the existing fresh-module probes and carrier report. No Mathlib import into this executable. |
| Soundness, completeness and correspondence theorems | Mathematical API; the existing `rankCertWith_check`, `checkRank_sound`, and `rankWith_eq` bridge is retained and builds. |

`Produce.lean` imports `ReduceImpl`, making its proved compiler replacement
available before public producer entry points compile. Generated code calls
`rowReduceWithImpl` for both certificate passes and the public rank wrappers.
This repairs the earlier mismatch between direct polynomial first-pass targets
and the compiled public producer. The one-line import comparison is retained in
[compiler-route](bench-results/hex-rank-10352/compiler-route/): six adjacent
alternating AB/BA blocks, `runMvCert12`, one measured repeat per arm. Before and
after medians were 6.741 s and 7.467 s; this does **not** establish a speedup.
The repair makes the specified implementation available consistently.

Integer schedules are `16,24,32,48,64,96,128,192,256`, with six trial-major
outer trials. Preparation verifies expected rank and `checkRank`, and verifies
the first pivot follows the zero-column prefix for the shifted family. Invalid
pure prep exits the executable through its explicit panic policy. Polynomial
preparation throws an IO error on rank or certificate disagreement. Every
fixed target has an expected rank/Boolean hash; subprocess replies must also
match the known rank.

- Dense entries use splitmix64 seed `1000003 + 1009*i + j`, reduced modulo 11
  and translated to `[-5,5]`. They are individually bounded, random-looking
  entries, with full rank checked rather than built from unit triangular factors.
- Low-rank products use ranks 2 and 8 and factor sizes 64 and 1024 bits.
  Factor seeds are `7919*salt + 104729*i + 1299709*j`, salts 3 and 5; the
  high bit is set and signs alternate with `i+j`. Matrix entries can have
  `2*bits + ceil(log2 r)` bits. No identity pivot block is inserted.
- Deficient products use splitmix64 small factors with salts 7 and 11,
  ranks `n-1` and `n/2`, and a shifted `n/2` case whose first `n-r` columns
  are zero. Product entries satisfy `B ≤ 25r ≤ 25n`.
- Polynomial inputs retain the original 64-bit LCG, salts 13/17 for rational
  coefficients and 19/23 for multivariate coefficients. Dimensions are 4, 8,
  12, full and half rank. The index offsets and products are defined in the
  driver. Rational comparison variants scale integer row i by `1/(1+i%7)`;
  the serialized values are the actual normalized Lean rationals.

## Verdicts

The independent derivations follow the SPEC's
[operation counts and minor bounds](../HexRank/SPEC/hex-rank.md#complexity)
and its [ordered mode choices](../HexRank/SPEC/hex-rank.md#benchmarking).
Fixed-rank operations use mode 1, `n²`: rank and operand bit lengths are
bounded independently of n. Their isolated second pass uses the stronger
constant model, since its prepared pivot block has fixed dimension and bit
size. Dense and growing-rank products use mode 2: `O(n³)` arithmetic on
`O(n(log n + log B))`-bit minors, bounded by quadratic schoolbook arithmetic.
This gives `n⁵(log₂ n+3)²` for dense entries and
`n⁵(2 log₂ n+5)²` for products. Changing GMP arithmetic regimes and growing
minors preclude a justified tight wall-time power law. These declarations
precede the measurements and do not fit their slopes.

The recorded scientific commands are:

```sh
python scripts/bench/rank_measure.py integer --out /tmp/hexrank-science-integer --python /tmp/hexvenv/bin/python
python scripts/bench/rank_measure.py attribution --out /tmp/hexrank-science-attribution --python /tmp/hexvenv/bin/python
python scripts/bench/rank_measure.py polynomial --out /tmp/hexrank-science-polynomial --python /tmp/hexvenv/bin/python
```

Actual invocations used the frozen executable paths in each `metadata.json`.
Core measurements use local source revision `2b0ff6bf5fbd033943c09c1b49893285497f90aa`
(the same driver/producer sources as commit `3228b9b4d`); attribution and expanded
polynomial measurements use `bbedb4722` (same sources as `b3360aca1`). Full
binary/source hashes, exact commands, CPU placement and host load are retained
with the [integer](bench-results/hex-rank-10352/integer/),
[attribution](bench-results/hex-rank-10352/attribution/) and
[polynomial](bench-results/hex-rank-10352/polynomial/) raw exports.
Only targets named in each manifest's `retained_exports` have evidence in this
report; the declared schedule is also recorded. Every completed row is retained,
including below-floor rows, timeouts and failures. Environment: AMD EPYC 9455,
96 logical CPUs, Linux 6.12.100, Lean 4.34.0, lean-bench
`8a37daf1074c3bdbd0da479b55538bad4a0022db`.

Here β is the harness slope of observed time divided by the declared model.
Mode-2 negative slopes are reported as passing upper bounds, not two-sided
consistency. The harness still prints `inconclusive` for those faster cases.

| Core case | Mode | β | Result |
| --- | ---: | ---: | --- |
| [`runCheckRankDense`](bench-results/hex-rank-10352/integer/runCheckRankDense.json) | 2 | -2.166 | Within upper bound (observed faster) |
| [`runCheckRankLowRank2At1024`](bench-results/hex-rank-10352/integer/runCheckRankLowRank2At1024.json) | 1 | — | No verdict: below signal floor |
| [`runCheckRankLowRank2At64`](bench-results/hex-rank-10352/integer/runCheckRankLowRank2At64.json) | 1 | -0.024 | Consistent with `n²` |
| [`runCheckRankLowRank8At64`](bench-results/hex-rank-10352/integer/runCheckRankLowRank8At64.json) | 1 | -0.074 | Consistent with `n²` |
| [`runRankCertDense`](bench-results/hex-rank-10352/integer/runRankCertDense.json) | 2 | -1.988 | Within upper bound (observed faster) |
| [`runRankCertLowRank2At1024`](bench-results/hex-rank-10352/integer/runRankCertLowRank2At1024.json) | 1 | +0.053 | Consistent with `n²` |
| [`runRankCertLowRank2At64`](bench-results/hex-rank-10352/integer/runRankCertLowRank2At64.json) | 1 | +0.040 | Consistent with `n²` |
| [`runRankCertLowRank8At64`](bench-results/hex-rank-10352/integer/runRankCertLowRank8At64.json) | 1 | +0.042 | Consistent with `n²` |
| [`runRowReduceDense`](bench-results/hex-rank-10352/integer/runRowReduceDense.json) | 2 | -2.002 | Within upper bound (observed faster) |
| [`runRowReduceLowRank2At1024`](bench-results/hex-rank-10352/integer/runRowReduceLowRank2At1024.json) | 1 | +0.051 | Consistent with `n²` |
| [`runRowReduceLowRank2At64`](bench-results/hex-rank-10352/integer/runRowReduceLowRank2At64.json) | 1 | +0.037 | Consistent with `n²` |
| [`runRowReduceLowRank8At64`](bench-results/hex-rank-10352/integer/runRowReduceLowRank8At64.json) | 1 | +0.095 | Consistent with `n²` |

The dense first pass has 17/54 completed rows below the harness signal floor,
including every row at 32 and 128; the raw exports retain these exclusions.
Its bound verdict uses the surviving rungs, not a claim of a resolved fit at
all nine dimensions. The low-rank, rank-2, 1024-bit checker has all 54 rows
below the measured 10×65.932 ms floor despite correct results. Its default
batch target is increased to two seconds. The sole
[follow-up](bench-results/hex-rank-10352/checker-resolution/runCheckRankLowRank2At1024.json)
passes the two-sided model; its manifest records the exact changed configuration
and source patch. No algorithmic failure is inferred from the resolution failure.

At dimension 256, descriptive medians of all completed rows give the following
producer/checker ratios. These exclude certificate preparation from checker
timing. A row with unresolved signal-floor evidence does not become a scaling
pass by appearing in this table.

| Family | First pass ms | Certificate ms | Checker ms | Certificate/checker |
| --- | ---: | ---: | ---: | ---: |
| `Dense`, n=256 | 2869.249 | 11019.909 | 4270.881 | 2.580 |
| `LowRank2At64`, n=256 | 29.179 | 30.052 | 22.412 | 1.341 |
| `LowRank8At64`, n=256 | 182.988 | 185.417 | 79.438 | 2.334 |
| `LowRank2At1024`, n=256 | 258.125 | 264.393 | 192.786 | 1.371 |

Polynomial cases require mode 3 under the SPEC. Their 60-second child timeout
and expected hashes are operational checks, not meaningful absolute performance
budgets. The raw timings cannot establish Phase 4 until operation-specific
SymPy-derived ceilings are recorded and checked. No polynomial performance
verdict is claimed here. The separate native quotient-witness producer also
needs an honest performance registration and evidence.

Earlier preparation diagnostics remain in the artifact root: baseline and
54-case list/verify, six-second-cap failures and the successful thirty-second
check. Their source/CPU limitations are recorded in `metadata.json` and the
individual command records; they are registration diagnostics, not replacement
scientific evidence.

## Comparator ratios

The persistent service is `scripts/oracle/rank_bench.py`. `prepare` receives
an actual Lean-generated matrix in the existing conformance encoding and
replaces the process's cached matrix. `rank` recomputes rank on every request;
there is no result cache. Lean warmup starts the process, transfers/decodes the
matrix and checks its rank before timing. Each measured external call includes
a JSON request/reply. Native comparison anchors use the same prepared matrix.
Integer parametric wrappers additionally reconstruct their flattened matrix;
comparison ratios refer to the prepared fixed anchors, not that extra copy.

FLINT uses `fmpz_mat.rank()` and `fmpq_mat.rank()`. SymPy calls
`DomainMatrix.rank()` on `QQ[x]` or `ZZ[x0,x1]`, through the existing conformance
decoders; this is generic exact-domain rank, never numerical rank or evaluation
at a sample point. SymPy uses the same Python ground-type setting as the
conformance oracle. Recorded versions are Python 3.14.6, python-flint 0.9.0,
SymPy 1.14.0. All three comparators remain **informational**.

```sh
python scripts/bench/rank_measure.py protocol --out /tmp/hexrank-science-protocol --python /tmp/hexvenv/bin/python
python scripts/bench/rank_measure.py comparisons --out /tmp/hexrank-science-comparisons --python /tmp/hexvenv/bin/python
```

The comparison runner executes six adjacent AB/BA blocks, alternating which
arm goes first at every shared rung. Every completed export is retained and
output status/hash checks are recorded. The common protocol control has median
6.693 μs (six retained repeats, 6.652–6.720 μs); see
[protocol](bench-results/hex-rank-10352/protocol/).

| Comparator | Request/reply control |
| --- | ---: |
| FLINT integer | 6.693 μs |
| FLINT rational | 6.693 μs |
| SymPy polynomial | 6.693 μs |

These reuse one measurement of the identical transport path, not three
independent experiments. The control excludes matrix preparation and does not
claim to subtract all Lean cache-key/expected-result checks. Full six-block
curves, raw and overhead-adjusted ratios, and eligible ranges remain to be
consolidated. The ratio report must retain every rung, mark overhead-dominated
and >10 s rungs, and avoid treating informational gaps as algorithmic failures.

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
cost measurable; their absolute-budget verdicts remain outstanding. The final
comparator report must still check whether its worst-gap family is represented.

## Concerns

- [#10352](https://github.com/kim-em/hex-dev/issues/10352): finish and consolidate all declared integer and attribution verdicts, retain the original checker signal-floor failure alongside its passing follow-up, and complete six-block comparator curves with eligible ranges and overhead-adjusted ratios.
- [#10352](https://github.com/kim-em/hex-dev/issues/10352): establish and verify operation-specific polynomial absolute budgets. Operational timeouts and hash agreement are insufficient.
- [#10352](https://github.com/kim-em/hex-dev/issues/10352): supply separate compiled evidence for `PolyProduce.produce`, while retaining the companion's ownership of tactic and kernel-proof builds; close the public-surface and dominant-cost attribution audit before advancing the manifest.
