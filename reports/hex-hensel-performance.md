# HexHensel Performance Report

Current implementation evidence was measured on `chungus2` (AMD EPYC 9455,
Linux x86-64) with Lean 4.34.0-rc2. The clean scientific and profile revision
is `cdbe3acd8dcc8bf6b09f4c882ad4f371cb6fc5ea`.

## Bench targets

The nine Phase-4 operation registrations use mode 1 on branch-isolated degree
families. The retained fold and balanced tree are additional parametric
registrations required by the SPEC's product-crossover compare group.

| registration | declaration | schedule | role / input family |
|---|---|---|---|
| `runModPChecksum` | `n` | coefficient count | Phase 4 / bridge-operations |
| `runLiftToZChecksum` | `n` | coefficient count | Phase 4 / bridge-operations |
| `runReduceModPowChecksum` | `n` | coefficient count | Phase 4 / bridge-operations |
| `runLinearHenselStepChecksum` | `n²` | degree | Phase 4 / linear-hensel |
| `runHenselLiftChecksum` | `n²` | degree, `k = 64` | Phase 4 / linear-hensel |
| `runQuadraticHenselStepChecksum` | `n²` | degree | Phase 4 / quadratic-hensel |
| `runPolyProductChecksum` | `n²` | factors 1024--2048, retained branch | Phase 4 / multifactor-lifting |
| `runMultifactorLiftChecksum` | `n²` | degree, `k = 64` | Phase 4 / multifactor-lifting |
| `runMultifactorLiftQuadraticChecksum` | `n²` | degree, `k = 64` | Phase 4 / multifactor-lifting |
| `runPolyProductFoldChecksum` | `n²` | factors 128--1024 | crossover diagnostic |
| `runPolyProductTreeChecksum` | `productTreeUpper n = n⁴` | factors 128--1024 | crossover diagnostic |

The SPEC-named compare groups are:

- `compare runPolyProductFoldChecksum runPolyProductTreeChecksum`;
- `compare runMultifactorLiftChecksum runMultifactorLiftQuadraticChecksum`.

## Verdicts

The clean three-trial scientific command was:

```sh
.lake/build/bin/hexhensel_bench run \
  Hex.HenselBench.runModPChecksum \
  Hex.HenselBench.runLiftToZChecksum \
  Hex.HenselBench.runReduceModPowChecksum \
  Hex.HenselBench.runLinearHenselStepChecksum \
  Hex.HenselBench.runHenselLiftChecksum \
  Hex.HenselBench.runQuadraticHenselStepChecksum \
  Hex.HenselBench.runPolyProductChecksum \
  Hex.HenselBench.runPolyProductFoldChecksum \
  Hex.HenselBench.runPolyProductTreeChecksum \
  Hex.HenselBench.runMultifactorLiftChecksum \
  Hex.HenselBench.runMultifactorLiftQuadraticChecksum \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-hensel-cdbe3acd-headline-chungus2.json
```

The 11-result artifact has SHA-256
`1426a1582a4c9e0715e3aaea1427d16e7c9ebd44925fbedb753e6dd86d1e105b`.
Every child completed at clean revision `cdbe3acd`; all ten mode-1 rows pass,
and the mode-2 tree row is faster than its upper bound.

| registration | mode | largest rung median | harness verdict | Phase-4 result |
|---|---:|---:|---|---|
| `runModPChecksum` | 1 | 10.129 ms | consistent, β=+0.048 | consistent with declared complexity |
| `runLiftToZChecksum` | 1 | 2.626 ms | consistent, β=+0.007 | consistent with declared complexity |
| `runReduceModPowChecksum` | 1 | 850.501 µs | consistent, β=−0.003 | consistent with declared complexity |
| `runLinearHenselStepChecksum` | 1 | 14.995 ms | consistent, β=−0.044 | consistent with declared complexity |
| `runHenselLiftChecksum` | 1 | 2.017 s | consistent, β=−0.038 | consistent with declared complexity |
| `runQuadraticHenselStepChecksum` | 1 | 8.696 ms | consistent, β=+0.107 | consistent with declared complexity |
| `runPolyProductChecksum` | 1 | 769.500 ms | consistent, narrow-range ratio test | consistent with declared complexity |
| `runMultifactorLiftChecksum` | 1 | 1.987 s | consistent, β=−0.040 | consistent with declared complexity |
| `runMultifactorLiftQuadraticChecksum` | 1 | 279.403 ms | consistent, β=−0.142 | consistent with declared complexity |
| `runPolyProductFoldChecksum` | 1 | 159.845 ms | consistent, β=+0.118 | consistent with declared complexity |
| `runPolyProductTreeChecksum` | 2 | 159.728 ms | inconclusive, β=−1.287, faster | within declared upper bound (observed faster) |

Mode 1 is independently derived for every Phase-4 operation target. At fixed
`k = 64`, each affected lift performs a constant number of dense corrections;
both factor degrees grow linearly with `n`, so the tight degree model is `n²`.
The public product ladder lies wholly at `n ≥ Array.treeProductLimit`, where
the dispatcher selects the retained fold; adding one linear factor grows the
accumulator degree by one, giving `1 + ... + n = O(n²)` coefficient work. The
retained fold has the same derivation.

The balanced tree is mode 2. No tighter single family-specific model follows
from the source: `ZPoly.fastPlan` dispatches among schoolbook and KS1--KS4 as
node degree and coefficient width grow, while GMP independently changes its
integer-multiplication kernel. At a `j`-leaf node, `O(j)` coefficients of
`O(j)` bits pack into `O(j²)` bits. Composing the published schoolbook integer
multiplication bound from Brent--Zimmermann, *Modern Computer Arithmetic*,
Chapter 1, gives `O(j⁴)`, and the geometric tree sum is root-dominated. This is
the report author's source composition of the published base bound, not a
fitted exponent. The profile below confirms that the cited packed integer
multiplication phase dominates.

### Diagnosis of issue #9741

The three failed verdicts were fixture and schedule defects, not an
implementation defect on the intended degree family.

- The scalar encoding co-varied degree and precision, but its spacing was
  dominated by degree. It therefore isolated neither component of the old
  product model, and the high-precision rung changed arithmetic regimes inside
  the same regression.
- The old iterative fixture kept one factor linear. `denseCoprimePair` now
  constructs dense monic `g` and `q` and sets `h = g*q + 1`; the identity
  `h - q*g = 1` proves coprimeness modulo every prime while both factor degrees
  grow.
- The error has `g.size + h.size - 2` coefficients, so its degree is strictly
  below `g*h`; adding `5*e` preserves the monic leading coefficient.

Fixing `k = 64` produces one controlled degree ladder for each failed target,
and all three now pass their independently derived mode-1 `n²` verdicts. The
public product's scientific ladder similarly stays in one dispatcher branch.

The compare evidence was captured cleanly at `cdbe3acd`:

```sh
.lake/build/bin/hexhensel_bench compare \
  Hex.HenselBench.runPolyProductFoldChecksum \
  Hex.HenselBench.runPolyProductTreeChecksum \
  --param-floor 4 --param-ceiling 1024 --param-schedule doubling \
  --cache-mode warm --outer-trials 3 --signal-floor-multiplier 1 \
  --export-file reports/bench-results/hex-hensel-cdbe3acd-product-compare-chungus2.json

.lake/build/bin/hexhensel_bench compare \
  Hex.HenselBench.runMultifactorLiftChecksum \
  Hex.HenselBench.runMultifactorLiftQuadraticChecksum \
  --cache-mode warm --outer-trials 3 --signal-floor-multiplier 1 \
  --export-file reports/bench-results/hex-hensel-cdbe3acd-lift-compare-chungus2.json
```

Both commands reported `all functions agree on common params`. The product
artifact covers 4 through 1024 and has SHA-256
`a73912f6b2f501863663bc358a4fd3c1041d8bde44c53ea9fc6e82d852c62128`;
the lift artifact covers 64 through 512 and has SHA-256
`911a2300a7a6f878b32fa79ce815386769b09c96b1f589593bef849a879d58e7`.

## Comparator ratios

The declared informational comparator is `FLINT fmpz_poly Newton-style Hensel emulation via python-flint`.
python-flint 0.9.0 does not expose FLINT's native
Hensel entry points; the persistent driver implements the same correction
schema with `fmpz_poly`. These figures orient implementation work but do not
gate Phase 4 and are not a native-FLINT Hensel performance claim. Hex returns
non-negative residues while the driver returns centred residues, so each side
checks its own stable hashes rather than cross-representation equality.

The fixed-target code and fixtures have not changed since clean revision
`c22f45d2`. Its campaign ran:

```sh
mapfile -t names < <(.lake/build/bin/hexhensel_bench list | awk '/\[fixed\]/{print $1}')
uv run --with python-flint .lake/build/bin/hexhensel_bench run "${names[@]}" \
  --export-file reports/bench-results/hex-hensel-c22f45d2-flint-chungus2.json
```

The 61-result export has SHA-256
`725259756cef20dcb36946c8137085b6160cd4f9ec72b4acda9f341234bf20a7`.
All points completed, all per-registration hashes agree, every FLINT target
records `warmup_first_iter=true`, and every batch was amortised for at least
0.1 s. The in-harness `runFlintOverhead` median is **6.198 µs**, at most 3.66%
of any FLINT median below. `adjusted` subtracts that overhead before forming
FLINT/Hex. Both endpoints include deterministic fixture construction inside
their timed fixed-registration bodies, so these are symmetric end-to-end
endpoint ratios rather than pure-kernel ratios.

### Linear single step

| n | Hex median | FLINT median | raw FLINT/Hex | adjusted FLINT/Hex |
|---:|---:|---:|---:|---:|
| 64 | 288.460 µs | 175.055 µs | 0.607× | 0.585× |
| 128 | 1.019 ms | 341.645 µs | 0.335× | 0.329× |
| 192 | 2.213 ms | 521.065 µs | 0.236× | 0.233× |
| 256 | 3.886 ms | 685.879 µs | 0.176× | 0.175× |
| 384 | 8.550 ms | 4.134 ms | 0.483× | 0.483× |
| 512 | 15.005 ms | 5.298 ms | 0.353× | 0.353× |

FLINT is faster throughout. The ratio falls through `n = 256`, crosses a
representation/algorithm threshold at 384, and ends at 0.353×.

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

The adjusted ratio stays in a narrow 0.599×--0.704× band, with FLINT's
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

This mirrors the direct linear wrapper: the adjusted ratio remains
0.575×--0.671×.

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
about 1.9×--2.2× faster than the python-flint emulation.

## Profile

Profiles were captured from clean revision
`cdbe3acd8dcc8bf6b09f4c882ad4f371cb6fc5ea` on `chungus2` with LeanBench
0.1.0, samply 0.13.1 at 999 Hz, and lean-bench-samply revision
`9356baa2f5757ee40320a897bd284914d5bb9f5e`. There is no random seed. Raw
Firefox Profiler files remain developer-local under `/tmp` as required by
`SPEC/profiling.md`.

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply scripts/profile/run_profile.sh \
  .lake/build/bin/hexhensel_bench Hex.HenselBench.runModPChecksum 131072 3000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply scripts/profile/run_profile.sh \
  .lake/build/bin/hexhensel_bench Hex.HenselBench.runHenselLiftChecksum 512 3000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply scripts/profile/run_profile.sh \
  .lake/build/bin/hexhensel_bench Hex.HenselBench.runQuadraticHenselStepChecksum 512 3000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply scripts/profile/run_profile.sh \
  .lake/build/bin/hexhensel_bench Hex.HenselBench.runMultifactorLiftChecksum 512 3000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply scripts/profile/run_profile.sh \
  .lake/build/bin/hexhensel_bench Hex.HenselBench.runMultifactorLiftQuadraticChecksum 512 3000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply scripts/profile/run_profile.sh \
  .lake/build/bin/hexhensel_bench Hex.HenselBench.runPolyProductTreeChecksum 1024 3000000000
```

| family and exact case | classified leaf cost | principal inclusive Hex functions |
|---|---|---|
| bridge-operations: `runModPChecksum`, `n=131072` | runtime 51.60%, allocation 36.30%, own 11.46%, other 0.64% (99.36%) | target 23.56%, `ZPoly.modP` 19.15%, checksum 13.88% |
| linear-hensel: `runHenselLiftChecksum`, `n=512`, `k=64` | allocation 51.29%, runtime 22.94%, own 18.39%, GMP 7.02%, other 0.35% (99.65%) | target / `henselLift` / `linearHenselStep` 99.65%, `DensePoly.mulImpl` 91.11% |
| quadratic-hensel: `runQuadraticHenselStepChecksum`, `n=512` | runtime 98.46%, allocation 0.95%, own 0.36%, other 0.23% (99.77%) | target 100%, `quadraticHenselStepWord?` 99.95%, division 1.13% |
| multifactor-lifting: `runMultifactorLiftChecksum`, `n=512`, `k=64` | allocation 48.56%, runtime 24.73%, own 19.28%, GMP 7.02%, other 0.40% (99.60%) | target / `multifactorLiftList` 99.65%, `henselLift` 99.56%, `DensePoly.mulImpl` 91.28% |
| multifactor-lifting: `runMultifactorLiftQuadraticChecksum`, `n=512`, `k=64` | allocation 51.21%, runtime 25.53%, GMP 19.77%, own 3.05%, other 0.44% (99.56%) | target 96.92%, `henselLiftFactorsImpl` 95.80%, modular division 70.56%, `liftExactImpl` 67.25% |
| product crossover: `runPolyProductTreeChecksum`, `n=1024` | GMP 89.37%, allocation 9.23%, runtime 0.89%, own 0.15%, other 0.37% (99.63%) | target 43.83%, product tree 43.65%, `KS3.digits` 43.42%, `mulKS4` 37.72% |

The two linear profiles have the same correction call graph and are dominated
by the registered dense product, confirming that the multifactor wrapper adds
no hidden phase. The quadratic single-step profile exercises the word path;
the production quadratic multifactor profile attributes its larger-width work
to exact lifting and modular division. The tree profile attributes 89.37% of
leaf samples to GMP and its leading inclusive entries to KS packing/recovery,
which is precisely the packed-integer phase covered by its mode-2 bound. No
dominant timed cost falls outside a registered target.

```text
bridge:          residual=0.994 ms; timed=1423.755 ms; retained=1405; sensitivity ±5 ms=passed; confidence=passed
linear:          residual=0.229 ms; timed=1987.162 ms; retained=1979; sensitivity ±5 ms=passed; confidence=passed
quadratic step:  residual=0.715 ms; timed=2226.530 ms; retained=2209; sensitivity ±5 ms=passed; confidence=passed
linear multi:    residual=0.566 ms; timed=2530.941 ms; retained=2519; sensitivity ±5 ms=passed; confidence=passed
quadratic multi: residual=0.967 ms; timed=2637.780 ms; retained=2617; sensitivity ±5 ms=passed; confidence=passed
product tree:    residual=0.641 ms; timed=2701.336 ms; retained=2699; sensitivity ±5 ms=passed; confidence=passed
```

## Concerns

None.
