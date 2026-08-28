# HexHensel Performance Report

All scientific and comparator measurements in this report use clean revision
`c22f45d28e6ea06156c1018d99c02b6010fe59ba` on `chungus2` (AMD EPYC 9455,
Linux 6.12.100 x86-64). Fixtures are deterministic and use `p = 5`; there is
no random seed.

## Bench targets

The declared expressions below are copied from the `setup_benchmark` sites in
`bench/HexHensel/Bench.lean`.

| registration | declared expression | isolated axis | input family |
|---|---|---|---|
| `runModPChecksum` | `n` | degree | bridge-operations |
| `runLiftToZChecksum` | `n` | degree | bridge-operations |
| `runReduceModPowChecksum` | `n` | degree | bridge-operations |
| `runLinearHenselStepChecksum` | `n * n` | degree, fixed exponent | linear-hensel |
| `runHenselLiftChecksum` | `n * n` | degree, `k = 64` | linear-hensel |
| `runHenselPrecisionChecksum` | `linearPrecisionUpper k` | precision, degree 128 | linear-hensel |
| `runQuadraticHenselStepChecksum` | `n * n` | degree, fixed exponent | quadratic-hensel |
| `runPolyProductChecksum` | `productTreeUpper n` | number of factors | multifactor-lifting |
| `runPolyProductFoldChecksum` | `productFoldUpper n` | number of factors | multifactor-lifting |
| `runPolyProductTreeChecksum` | `productTreeUpper n` | number of factors | multifactor-lifting |
| `runMultifactorLiftChecksum` | `n * n` | degree, `k = 64` | multifactor-lifting |
| `runMultifactorLiftQuadraticChecksum` | `n * n` | degree, `k = 64` | multifactor-lifting |
| `runMultifactorPrecisionChecksum` | `linearPrecisionUpper k` | precision, degree 128 | multifactor-lifting |
| `runQuadraticPrecisionChecksum` | `quadraticPrecisionUpper k` | precision, degree 128 | quadratic-hensel |

The two within-Lean compare groups use the complete common domains
`n = 64, 80, 96, 128, 160, 192, 256, 384, 512` at `k = 64` and
`k = 4, 8, 16, 32, 64, 128, 256` at degree 128. Both report that all functions
agree at every common parameter. The 61 fixed registrations are comparator or
protocol anchors only; they make no complexity claim and have no mode.

## Verdicts

The scientific command was:

```sh
.lake/build/bin/hexhensel_bench run \
  Hex.HenselBench.runModPChecksum \
  Hex.HenselBench.runLiftToZChecksum \
  Hex.HenselBench.runReduceModPowChecksum \
  Hex.HenselBench.runLinearHenselStepChecksum \
  Hex.HenselBench.runHenselLiftChecksum \
  Hex.HenselBench.runHenselPrecisionChecksum \
  Hex.HenselBench.runQuadraticHenselStepChecksum \
  Hex.HenselBench.runPolyProductChecksum \
  Hex.HenselBench.runPolyProductFoldChecksum \
  Hex.HenselBench.runPolyProductTreeChecksum \
  Hex.HenselBench.runMultifactorLiftChecksum \
  Hex.HenselBench.runMultifactorLiftQuadraticChecksum \
  Hex.HenselBench.runMultifactorPrecisionChecksum \
  Hex.HenselBench.runQuadraticPrecisionChecksum \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-hensel-c22f45d2-headline-chungus2.json
```

The clean 14-result export is
`reports/bench-results/hex-hensel-c22f45d2-headline-chungus2.json`, SHA-256
`20e041371cec11981415d73d12cc6d4bfd2fa6d6e9a1bd66c6f6897e7d916f28`.
Every child completed and recorded `git_dirty=false`.

| registration | mode | largest rung median | harness verdict and slope | Phase-4 result |
|---|---:|---:|---|---|
| `runModPChecksum` | 1 | 12.552 ms | consistent, β=+0.119 | consistent with declared complexity |
| `runLiftToZChecksum` | 1 | 2.636 ms | consistent, β=+0.006 | consistent with declared complexity |
| `runReduceModPowChecksum` | 1 | 865.618 µs | consistent, β=+0.001 | consistent with declared complexity |
| `runLinearHenselStepChecksum` | 1 | 15.132 ms | consistent, β=−0.035 | consistent with declared complexity |
| `runHenselLiftChecksum` | 1 | 1.967 s | consistent, β=−0.046 | consistent with declared complexity |
| `runHenselPrecisionChecksum` | 2 | 582.765 ms | inconclusive, β=−1.817, looks faster | within declared upper bound (observed faster) |
| `runQuadraticHenselStepChecksum` | 1 | 8.727 ms | consistent, β=+0.091 | consistent with declared complexity |
| `runPolyProductChecksum` | 2 | 157.451 ms | inconclusive, β=−1.287, looks faster | within declared upper bound (observed faster) |
| `runPolyProductFoldChecksum` | 2 | 157.020 ms | inconclusive, β=−0.888, looks faster | within declared upper bound (observed faster) |
| `runPolyProductTreeChecksum` | 2 | 158.452 ms | inconclusive, β=−1.286, looks faster | within declared upper bound (observed faster) |
| `runMultifactorLiftChecksum` | 1 | 1.964 s | consistent, β=−0.051 | consistent with declared complexity |
| `runMultifactorLiftQuadraticChecksum` | 1 | 278.471 ms | consistent, β=−0.139 | consistent with declared complexity |
| `runMultifactorPrecisionChecksum` | 2 | 570.210 ms | inconclusive, β=−1.820, looks faster | within declared upper bound (observed faster) |
| `runQuadraticPrecisionChecksum` | 2 | 47.132 ms | inconclusive, β=−1.084, looks faster | within declared upper bound (observed faster) |

Mode 1 applies where fixing precision leaves an independently derived tight
coefficient-operation model. Mode 2 is necessary on the precision and product
axes because coefficient widths grow with the parameter and the executable
crosses GMP and Kronecker implementation regimes; no tight family-specific
wall-clock model follows from the source. The upper bounds use the published
schoolbook integer multiplication and division bounds in
[Brent--Zimmermann, *Modern Computer Arithmetic*, Chapter 1](https://members.loria.fr/PZimmermann/mca/pub226.html):

- coefficients modulo `5^j` have `O(j)` bits; `O(k)` linear corrections with
  `O(j²)` integer operations sum to `linearPrecisionUpper k = k³`;
- exact quadratic lifting halves the exponent recursively, so the geometric
  sum of `O(j²)` corrections is `quadraticPrecisionUpper k = k²`;
- after `j` bounded linear factors, the fold accumulator has `O(j)`
  coefficients of `O(j)` bits, giving `productFoldUpper n = n³` after summing;
- a `j`-leaf subtree packs `O(j)` coefficients of `O(j)` bits into an
  `O(j²)`-bit integer; schoolbook packed multiplication is `O(j⁴)`, and the
  balanced-tree sum is root-dominated, giving `productTreeUpper n = n⁴`.

These declarations were derived from representation and control flow before
the final measurement; no observed slope was fitted. The profiles below show
the cited multiplication/division phases dominating each mode-2 family.

One isolated scheduler outlier inflated the full export's `runModPChecksum`
largest-rung spread without changing its median or pass. A clean five-trial
confirmation at the same commit gave β=+0.030 and a 9.980 ms largest-rung
median. Its artifact is
`reports/bench-results/hex-hensel-c22f45d2-modp-confirm-chungus2.json`,
SHA-256
`04ee257861d7f82ed8ea848455e68c40f9f38fffc8357eca46b22f8916ae4f43`.

### Diagnosis of issue #9741

The three original failures were fixture/schedule failures, not an
implementation defect on the isolated degree axis.

- The old scalar encoding co-varied degree and precision, while its numeric
  spacing was dominated by degree. It therefore did not isolate either
  scaling claim, and the optimized high-precision rung introduced a second
  implementation regime into the same regression.
- The old iterative fixture kept one factor linear, so it did not exercise the
  intended degree-growing correction products. The replacement uses dense
  monic `g` and `q` and sets `h = g*q + 1`; `h - q*g = 1` proves coprimeness
  while both factor degrees grow.
- The error polynomial now has `g.size + h.size - 2` coefficients. Its degree
  is strictly below `g*h`, so adding `5*e` preserves the monic leading
  coefficient required by the lifting model.

With `k = 64` fixed, direct linear, linear multifactor, and quadratic
multifactor lifting all pass their tight `n²` mode-1 verdicts. Their separate
fixed-degree precision registrations pass the independently qualified mode-2
upper bounds. The all-target rerun also exposed the product dispatcher's old
`n²` declaration as a coefficient-operation count rather than a wall-clock
bound; the coefficient-bit-aware product registrations above close that
separate evidence gap.

## Comparator ratios

The declared informational comparator is
`FLINT nmod_poly_hensel_lift_* via python-flint`. python-flint 0.9.0 does not
bind those C entry points directly;
the shared persistent driver emulates the same Newton-style schema with
`fmpz_poly`, so the figures orient implementation work but do not gate Phase 4.
Hex returns non-negative residues and the driver returns centred residues;
each fixed registration's five observed hashes agree internally, but Hex and
FLINT hashes are not expected to match across representations.

The exact campaign selected all fixed registrations from the relinked binary
and ran:

```sh
mapfile -t names < <(.lake/build/bin/hexhensel_bench list | awk '/\[fixed\]/{print $1}')
uv run --with python-flint .lake/build/bin/hexhensel_bench run "${names[@]}" \
  --export-file reports/bench-results/hex-hensel-c22f45d2-flint-chungus2.json
```

The 61-result clean export is
`reports/bench-results/hex-hensel-c22f45d2-flint-chungus2.json`, SHA-256
`725259756cef20dcb36946c8137085b6160cd4f9ec72b4acda9f341234bf20a7`.
All points completed, all per-registration hashes agree, every FLINT target
records `warmup_first_iter=true`, and every batch was amortised for at least
0.1 s. The in-harness `runFlintOverhead` median is **6.198 µs**. It is at most
3.66% of any FLINT median below, and all calls are below the 1 s soft ceiling,
so all 30 paired rungs are eligible. `adjusted` subtracts 6.198 µs from FLINT
before forming FLINT/Hex.

### Linear single step

| n | Hex median | FLINT median | raw FLINT/Hex | adjusted FLINT/Hex |
|---:|---:|---:|---:|---:|
| 64 | 288.460 µs | 175.055 µs | 0.607× | 0.585× |
| 128 | 1.019 ms | 341.645 µs | 0.335× | 0.329× |
| 192 | 2.213 ms | 521.065 µs | 0.236× | 0.233× |
| 256 | 3.886 ms | 685.879 µs | 0.176× | 0.175× |
| 384 | 8.550 ms | 4.134 ms | 0.483× | 0.483× |
| 512 | 15.005 ms | 5.298 ms | 0.353× | 0.353× |

FLINT is faster throughout. The ratio falls through `n = 256`, then shows a
representation/algorithm threshold at 384 and ends at 0.353×.

### Quadratic single step

| n | Hex median | FLINT median | raw FLINT/Hex | adjusted FLINT/Hex |
|---:|---:|---:|---:|---:|
| 64 | 76.316 µs | 169.666 µs | 2.223× | 2.142× |
| 160 | 868.379 µs | 422.299 µs | 0.486× | 0.479× |
| 192 | 1.237 ms | 482.612 µs | 0.390× | 0.385× |
| 256 | 2.173 ms | 642.527 µs | 0.296× | 0.293× |
| 384 | 4.869 ms | 2.061 ms | 0.423× | 0.422× |
| 512 | 8.804 ms | 2.253 ms | 0.256× | 0.255× |

Hex wins only at the smallest rung. Past setup-dominated `n = 64`, FLINT is
about 2.1× to 3.9× faster and finishes at 0.255×.

### Iterated linear lift at k = 8

| n | Hex median | FLINT median | raw FLINT/Hex | adjusted FLINT/Hex |
|---:|---:|---:|---:|---:|
| 32 | 731.107 µs | 456.703 µs | 0.625× | 0.616× |
| 64 | 2.588 ms | 1.556 ms | 0.601× | 0.599× |
| 96 | 5.662 ms | 3.759 ms | 0.664× | 0.663× |
| 128 | 9.909 ms | 6.113 ms | 0.617× | 0.616× |
| 192 | 22.112 ms | 15.071 ms | 0.682× | 0.681× |
| 256 | 38.630 ms | 27.186 ms | 0.704× | 0.704× |

The adjusted ratio stays in a narrow 0.599×–0.704× band, with FLINT's
emulation about 1.4× faster at the top rung.

### Linear multifactor lift at k = 8

| n | Hex median | FLINT median | raw FLINT/Hex | adjusted FLINT/Hex |
|---:|---:|---:|---:|---:|
| 32 | 729.560 µs | 442.210 µs | 0.606× | 0.598× |
| 64 | 2.580 ms | 1.489 ms | 0.577× | 0.575× |
| 96 | 5.798 ms | 3.636 ms | 0.627× | 0.626× |
| 128 | 9.888 ms | 5.997 ms | 0.607× | 0.606× |
| 192 | 22.071 ms | 14.761 ms | 0.669× | 0.668× |
| 256 | 38.992 ms | 26.181 ms | 0.671× | 0.671× |

This mirrors the direct linear wrapper, as expected from the two-factor
delegation: the adjusted ratio remains 0.575×–0.671×.

### Quadratic multifactor lift at k = 8

| n | Hex median | FLINT median | raw FLINT/Hex | adjusted FLINT/Hex |
|---:|---:|---:|---:|---:|
| 32 | 154.491 µs | 442.186 µs | 2.862× | 2.822× |
| 64 | 781.305 µs | 1.489 ms | 1.906× | 1.898× |
| 96 | 1.784 ms | 3.637 ms | 2.038× | 2.035× |
| 128 | 3.058 ms | 5.901 ms | 1.930× | 1.928× |
| 192 | 6.817 ms | 14.715 ms | 2.159× | 2.158× |
| 256 | 12.052 ms | 26.377 ms | 2.189× | 2.188× |

After the smallest fixed-cost rung, Hex's production quadratic lifter remains
about 1.9×–2.2× faster than the python-flint emulation.

## Profile

Profiles were captured from the same clean commit on the same host with
LeanBench 0.1.0, samply 0.13.1 at 999 Hz, and lean-bench-samply commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`. Raw Firefox Profiler artifacts
remain developer-local under `/tmp` as required by `SPEC/profiling.md`.
The exact commands were:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexhensel_bench \
  Hex.HenselBench.runModPChecksum 131072 3000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexhensel_bench \
  Hex.HenselBench.runHenselPrecisionChecksum 256 3000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexhensel_bench \
  Hex.HenselBench.runQuadraticPrecisionChecksum 256 3000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexhensel_bench \
  Hex.HenselBench.runPolyProductChecksum 1024 3000000000
```

There is no random seed. Each row records leaf self-time categories; the
inclusive ranking names the executable phase to which the cost is attributed.

| input family and exact case | classified leaf cost | principal inclusive Hex functions |
|---|---|---|
| bridge-operations: `runModPChecksum`, `n=131072` | allocation 42.99%, runtime 44.69%, own code 11.50%, other 0.81% (99.19%) | `runModPChecksum` 25.66%, `ZPoly.modP` 19.62%, checksum 13.86% |
| linear-hensel: `runHenselPrecisionChecksum`, `k=256`, degree 128 | allocation 44.05%, runtime 21.99%, GMP 17.72%, own code 15.83%, other 0.41% (99.59%) | `henselLift` / `linearHenselStep` 96.63%, `DensePoly.mulImpl` 84.55%, division 6.61% |
| quadratic-hensel: `runQuadraticPrecisionChecksum`, `k=256`, degree 128 | allocation 57.44%, GMP 29.58%, runtime 11.41%, own code 1.04%, other 0.52% (99.48%) | `henselLiftFactorsImpl` 92.95%, `liftExactImpl` 78.35%, bignum step 69.90%, modular division 63.88% |
| multifactor-lifting: `runPolyProductChecksum`, `n=1024` | allocation 74.12%, GMP 18.48%, runtime 7.17%, other 0.22% (99.78%) | `runPolyProductChecksum` 97.42%, `DensePoly.mulImpl` 92.79% |

The bridge profile attributes its cost to coefficient conversion, construction,
and the registered checksum. The linear precision profile is dominated by the
dense multiplication inside every linear correction, directly supporting the
coefficient-bit upper bound. The quadratic precision profile is dominated by
the exact bignum correction and modular division phases; its geometric
precision recursion is therefore present rather than hidden in preparation.
The product profile is dominated by the registered dense multiply path, with
allocation and GMP accounting for 92.60% of leaf cost. No dominant timed phase
is outside a registered target.

Diagnostics quoted from the timed-region postprocessor:

```text
bridge:    residual=0.305 ms; total timed=1370.982 ms; retained=1356; sensitivity ±5 ms=passed; confidence=passed
linear:    residual=0.817 ms; total timed=2920.228 ms; retained=2906; sensitivity ±5 ms=passed; confidence=passed
quadratic: residual=0.784 ms; total timed=3092.646 ms; retained=3076; sensitivity ±5 ms=passed; confidence=passed
product:   residual=0.556 ms; total timed=2680.409 ms; retained=2678; sensitivity ±5 ms=passed; confidence=passed
```

## Concerns

None.
