# HexRoots Performance Report

**Phase 4 is claimed for HexRoots.** The final registration split keeps the one
honestly modelled helper sweep parametric and tracks all GMP-transition
kernels, whole-polynomial drivers, and strategy experiments as canonical fixed
regressions. The parametric registration is consistent, all fixed hashes agree, and §Concerns
is empty. This report records the Phase-4 evidence per
[PLAN/Phase4.md](../PLAN/Phase4.md) and
[SPEC/benchmarking.md §Headline reports](../SPEC/benchmarking.md#headline-reports).

Final numbers come from `reports/bench-results/hex-roots-973c2cd-round5.json`,
recorded on quiet `chungus2` (AMD EPYC 9455 48-Core, 96 CPUs; load 2.26 with
two runnable processes), Lean `4.32.0-rc1`, lean-bench `0.1.0`. The export's
`git_dirty: true` records the staged benchmark/report update; its branch point
is commit `ed0086001407`.

## Bench Targets

Parametric registrations:

- `runMahlerPrec`: `n` on seeded bounded-coefficient polynomials.

Canonical fixed registrations (`repeats = 5`) are `runIsolate`
(fixed-separation degree 8), `runTaylor` (seeded degree
128, unit centre), `runWitnessCheck`, `runNkWitnessCheck`, and
`runNewtonSquare` (bounded-height degree 128), `runRefine1` (degree 8),
`runCertify` (degree-128 pinned NK branch), `runIsolateAll` (fixed-separation
degree 12), `runRefineTo` (achieved precision 131077), the three strategy
drivers (shared `linProdPoly 10`), and `runSameRoot`.

The fixed classification is intentional: exact Taylor shifts have intrinsic
linear output-bit growth and the reachable GMP transition admits no honest
single scalar asymptotic model. Three calibration rounds, including a direct
limb model, produced falling normalized constants because maximum output width
is not mean operand width across the triangular computation. Fixed cases retain
regression signal without asserting an inexpressible slope; lean-bench#67
tracks structured op-count/operand-growth reporting.

### Superseded round-one target record

Declared complexities copied verbatim from the `setup_benchmark` registration
sites in `bench/HexRoots/Bench.lean`. These are *wall-time* models: the SPEC
op-count contract multiplied by the family's working-bit-length growth `B`
where that growth is asymptotically significant on the schedule (each
registration's comment records the reconciliation).

- `Hex.RootsBench.runTaylor`: `n * n`
- `Hex.RootsBench.runMahlerPrec`: `n`
- `Hex.RootsBench.runWitnessCheck`: `n * n`
- `Hex.RootsBench.runNkWitnessCheck`: `n * n`
- `Hex.RootsBench.runNewtonSquare`: `n * n`
- `Hex.RootsBench.runRefine1`: `n * n`
- `Hex.RootsBench.runCertify`: `n * n`
- `Hex.RootsBench.runIsolateAll`: `n * n * n * n * n`
- `Hex.RootsBench.runIsolate`: `n * n * n * n * n`
- `Hex.RootsBench.runRefineTo`: `t * t`
- `Hex.RootsBench.runIsolateNk`: `n * n * n * n * n`
- `Hex.RootsBench.runIsolatePellet`: `n * n * n * n * n`
- `Hex.RootsBench.runIsolateNkThenPellet`: `n * n * n * n * n`
- `Hex.RootsBench.runSameRoot`: fixed benchmark, `repeats = 5`

Three input families (`libraries.yml: HexRoots.phase4.input_families`):
`seeded-dense` (seed-`0xC0FFEE` dense integer polynomials, coefficients in
`[-10, 10]`, generically distinct irrational roots — the whole-polynomial
drivers, `taylor`, `mahlerPrec`, `refine1`, `certify`), `wilkinson-linprod`
(`∏(X−j)`, `j = 1..n`, integer roots — the witness/Newton primitives and the
dual-route compare group), and `refine-fixed` (the degree-3 `(x−1)(x−2)(x+3)`
whose atom `refineTo?`/`sameRoot` sharpen).

### Op-count-vs-wall reconciliation (Phase4.md performance rationale)

The registration comments were retuned from pure exact-dyadic op-counts to
wall-time models. Which op-count models changed, and why:

- **`runTaylor` stays `n²`.** The SPEC op-count is `n²` synthetic-division
  multiply/adds. The fixed centre `1/4 + i/8 = 2^{−3}(2+i)` is *non-integer*,
  so `z^{j−k}` carries denominator `2^{3(j−k)}` and the coefficients reach
  `B = Θ(n)` bits; each inner op multiplies a `B`-bit operand by the fixed
  `3`-bit centre (`O(B)`), giving an `n³` bit-cost asymptote. On the reachable
  `16..256` (probed to `1024`) schedule the operands stay `≤ 48` GMP words —
  the allocation-dominated transition band — so wall tracks `~n^{2.25}`, short
  of the `n³` asymptote. `n²` is declared as the SPEC op-count; the residual is
  a Concern (below).
- **`runMahlerPrec`, `runWitnessCheck`, `runNkWitnessCheck`, `runNewtonSquare`,
  `runRefine1`, `runCertify` stay at their op-counts (`n`, `n²`).** `mahlerPrec`
  is word-size integer arithmetic (`B` constant). The witness/Newton/refine
  primitives run on integer-centred `wilkinson-linprod` (no denominator growth,
  integer Taylor coefficients of `O(n log n)` bits staying sub-word `≤ 44` bits
  through `n = 16`) or on low-precision seeded mid-refinement components
  (`O(n)`-bit coefficients staying sub-word through `n = 12`), so the operands
  are flat and wall tracks the op count. The bit-growth sits in the constant.
- **`runIsolateAll`, `runIsolate`, and the three compare-group targets changed
  `n³ → n⁵`.** The SPEC contract is `O(n³·B²)` bit operations; the
  whole-polynomial drivers reach a working bit-length `B = Θ(n)` (target
  precision plus the seeded `n·log‖p‖∞` term plus the Taylor coefficients'
  `Θ(prec·n)` denominator growth), and the growing-precision dyadic arithmetic
  — notably the `invAtPrec` reciprocal — is schoolbook `O(B²)`. `O(n³·B²)` with
  `B = Θ(n)` gives the `n⁵` wall model, folding the bit-growth into the
  exponent because it is asymptotically significant here (unlike the flat-band
  primitives above).
- **`runRefineTo` stays `t²`.** At fixed degree the parameter is the target
  precision `t`; the dominant final witness does a fixed number of `t × t`
  schoolbook multiplies, `O(t²)`.

## Verdicts

Quiet-machine command:

```sh
lake exe hexroots_bench run <all 14 registration names> \
  --export-file reports/bench-results/hex-roots-973c2cd-round5.json
```

The single parametric verdict is consistent:

| registration | model | verdict | evidence | final hash |
|---|---|---|---|---|
| `runMahlerPrec` | `n` | consistent | `β=-0.097`, `cMin=6.954`, `cMax=8.431` over `16..256` | `0xc83` |

(`runIsolate` was parametric at `n⁵` in the previous revision of this
report and its `4..10` range check passed, but post-merge review showed
the adjacent derivation could not support `n⁵` on this family:
`separatedPoly n` has `log ‖p‖∞ = Θ(n·log n)`, so the `separationDepth`
floor makes the emission-level bit-length `B = Θ(n²·log n)` and the
honestly derived wall from `O(n³·B²)` is `~n⁷`, unreachable in the
30 s/call band. Per the no-fitting rule the registration was demoted to
a fixed case rather than kept on a fitted model; see issue #8750.)

Fixed medians (all five repeats agree on the shown hash):

| registration | canonical input | median | hash |
|---|---|---:|---|
| `runIsolate` | fixed-separation degree 8 | 144.621 ms | `0x16c307fd2a36d31e` |
| `runTaylor` | seeded degree 128, centre 1 | 2.199 ms | `0x9917b7b230496af4` |
| `runWitnessCheck` | bounded-height degree 128 | 2.328 ms | `0xb` |
| `runNkWitnessCheck` | bounded-height degree 128 | 2.244 ms | `0xb` |
| `runNewtonSquare` | bounded-height degree 128 | 2.151 ms | `0x450307c7dcbe905c` |
| `runRefine1` | fixed-separation degree 8 | 2.197 ms | `0xc5cb1ba3f05326fd` |
| `runCertify` | pinned-NK degree 128 | 6.530 ms | `0x1698ec123da6112f` |
| `runIsolateAll` | fixed-separation degree 12 | 1.726 s | `0xecd908d19d73e5c4` |
| `runRefineTo` | achieved precision 131077 | 313.285 ms | `0x05eb22e5c1f4a7a5` |
| `runIsolateNk` | `linProdPoly 10` | 2.627 s | `0xda631bdf13415a4f` |
| `runIsolatePellet` | `linProdPoly 10` | 484.986 ms | `0xda631bdf13415a4f` |
| `runIsolateNkThenPellet` | `linProdPoly 10` | 501.670 ms | `0xda631bdf13415a4f` |
| `runSameRoot` | fixed refined atom | 131 ns | `0xb` |

### Superseded round-one verdict record

Scientific run, one command, exporting
`reports/bench-results/hex-roots-b08a66cce522.json`:

```sh
lake exe hexroots_bench run \
  Hex.RootsBench.runTaylor Hex.RootsBench.runMahlerPrec \
  Hex.RootsBench.runWitnessCheck Hex.RootsBench.runNkWitnessCheck \
  Hex.RootsBench.runNewtonSquare Hex.RootsBench.runRefine1 \
  Hex.RootsBench.runCertify Hex.RootsBench.runIsolateAll \
  Hex.RootsBench.runIsolate Hex.RootsBench.runRefineTo \
  Hex.RootsBench.runIsolateNk Hex.RootsBench.runIsolatePellet \
  Hex.RootsBench.runIsolateNkThenPellet \
  --export-file reports/bench-results/hex-roots-b08a66cce522.json
```

Inputs are deterministic; no random seeds are involved. Every verdict verbatim
(`β` is the residual log-log slope of `C = per-call / model`; the harness calls
a run *consistent* iff `|β| ≤ 0.15`, or, on a log-x range too narrow to fit a
slope, iff `cMax/cMin ≤ max(1.5, exp(0.15·xRange))`):

| registration | model | verdict | β / range | final-param hash |
|---|---|---|---|---|
| `runTaylor` | `n²` | **inconclusive** | `β=+0.415` (slower by `~n^0.42`) | `0x1242736d713af35b` @256 |
| `runMahlerPrec` | `n` | consistent | `β=−0.148` | `0xc83…` @256 |
| `runWitnessCheck` | `n²` | **inconclusive** | `β=−0.227` (faster by `~n^0.23`) | `0xb` @16 |
| `runNkWitnessCheck` | `n²` | consistent | `β=−0.095` | `0xb` @16 |
| `runNewtonSquare` | `n²` | **inconclusive** | `β=+0.198` (slower by `~n^0.20`) | `0x450307c7dcbe905c` @16 |
| `runRefine1` | `n²` | consistent | range check (`cMax/cMin=1.33`) | `0x67a4e6fe2931f85d` @12 |
| `runCertify` | `n²` | **inconclusive** | range check (`cMax/cMin=2.38`) | `0x7c47cfcdaf58dbfb` @12 |
| `runIsolateAll` | `n⁵` | **inconclusive** | `β=+0.266` (slower by `~n^0.27`) | `0xe04d9a38cc8e2885` @20 |
| `runIsolate` | `n⁵` | **inconclusive** | range check (`cMax/cMin=1.57`) | `0x83846a2a71bf4090` @16 |
| `runRefineTo` | `t²` | **inconclusive** | range check (`cMax/cMin=2.96`) | `0x9de10954e8ec1aa1` @256 |
| `runIsolateNk` | `n⁵` | consistent | range check (`cMax/cMin=1.25`) | `0x6519358031d0ea70` @6 |
| `runIsolatePellet` | `n⁵` | **inconclusive** | range check (`cMax/cMin=1.68`) | `0x6519358031d0ea70` @6 |
| `runIsolateNkThenPellet` | `n⁵` | **inconclusive** | range check (`cMax/cMin=1.81`) | `0x6519358031d0ea70` @6 |

**4 consistent, 9 inconclusive.** The fixed `runSameRoot` benchmark:
median `132 ns` (min `130`, max `134`, `×2^13` inner repeats), all repeats
agree on hash `0xb`, matching the registered `expectedHash`.

The nine inconclusive verdicts are analysed in §Concerns. They fall into four
root causes, none of which is a wrong-asymptotic *implementation* bug that a
`done_through` rollback of the `def` would fix: the fixed non-integer Taylor
centre's transition-band growth, the startup-dominated microsecond band of the
small-degree witness benches, the seeded family's degree-dependent (hence
non-power-law) root geometry, and `refineTo`'s Newton-doubling precision
quantisation. They are benchmark-family / schedule findings.

## Comparator Ratios

Declared informational comparator: `python-flint fmpz_poly.complex_roots`,
scoped to the whole-polynomial isolation surface.

The final fixed strategy trio shares `linProdPoly 10`; all hashes are
`0xda631bdf13415a4f`, preserving the bench-side agreement regression. The
agreement was also checked directly with:

```text
lake exe hexroots_bench compare Hex.RootsBench.runIsolateNk Hex.RootsBench.runIsolatePellet Hex.RootsBench.runIsolateNkThenPellet
agreement: all functions agree on output
```

The canonical artifact medians are NK `2.627 s`, Pellet `484.986 ms`, and
NK-then-Pellet `501.670 ms`.
The independent round-four scaling experiment over degrees `2..10` is retained
as informational dual-route data: normalized against `n⁵`, NK-only grew with
residual `β=+0.991`, while Pellet-only and NK-then-Pellet were below that model
at `β=-0.314` and `-0.382`. This reverses the simple constant-factor picture
seen on the smaller integer-root ladder; no asymptotic conclusion is drawn.

`HexRoots/SPEC/hex-roots.md` names python-flint (`fmpz_poly.complex_roots`, the
ci-tier oracle) as the sole Phase-4 performance comparator. It is classified
`informational` in `libraries.yml: HexRoots.phase4.comparators` and does not
gate Phase 4. The per-library yardstick is the SPEC's time budgets, not a
constant-factor `1×` goal, because FLINT's multiprecision ball engine is
structurally different from this library's decidable exact-integer
certificates. MPSolve remains a local correctness oracle for the adversarial
corpus, not a Phase-4 performance comparator.

### python-flint (`informational`, run)

`scripts/bench/hexroots_flint_compare.py` times `fmpz_poly.complex_roots()` at
`ctx.prec = 32` on the same fixed-separation products as the whole-polynomial
drivers. The final fixed canonical points are `runIsolate` at degree 8 and
`runIsolateAll` at degree 12. A pre-demotion `runIsolateParam` diagnostic
ladder at degrees `4..10` is retained solely to show the ratio's shape; it is
not an asymptotic verdict or a registered complexity claim. The degree-12
comparison matches `runIsolateAll`'s target precision 32. The `runIsolate`
diagnostic and canonical rows are same-input orientation rather than
equal-precision work: Lean continues to its degree-dependent
`separationDepth`, while FLINT starts from `ctx.prec = 32` and internally
raises precision as needed to certify its balls. All degrees run in one warm
process. The measured per-call overhead
(`complex_roots` on `x²−2`) is `1.111 µs`, below 5 % of comparator wall time at
every rung, so no adjusted column is required. Data:
`reports/bench-results/hex-roots-flint-round5.json`; diagnostic Lean values
come from `hex-roots-isolate-diagnostic-round5.json`, and canonical fixed
values from `hex-roots-973c2cd-round5.json`.

Diagnostic ratio shape (unregistered `runIsolateParam` helper):

| degree | hex | flint | ratio hex/flint |
|---:|---:|---:|---:|
| 4 | 7.078 ms | 63.419 µs | 111.6 |
| 5 | 18.299 ms | 93.254 µs | 196.2 |
| 6 | 43.282 ms | 109.722 µs | 394.5 |
| 7 | 113.879 ms | 135.967 µs | 837.5 |
| 8 | 159.871 ms | 215.234 µs | 742.8 |
| 9 | 346.203 ms | 301.942 µs | 1146.6 |
| 10 | 597.162 ms | 406.227 µs | 1470.0 |

Final registered canonical points:

| degree | Lean surface | hex | flint | ratio hex/flint |
|---:|---|---:|---:|---:|
| 8 | `runIsolate` | 144.621 ms | 215.234 µs | 671.9 |
| 12 | `runIsolateAll` | 1.726 s | 591.777 µs | 2915.9 |

**Trend.** On the diagnostic ladder, apart from the degree-8 local dip, the
ratio diverges from `112×` at degree 4 to `1470×` at degree 10; the
equal-precision canonical `runIsolateAll` point is `2916×` at degree 12. That
direction is expected: the Lean drivers perform certified exact isolation
with degree- and precision-dependent exact-dyadic work, while FLINT uses a
structurally different multiprecision ball algorithm. No scalar asymptotic
model is asserted for the diagnostic curve. Under the informational-comparator doctrine,
expected divergence between documented different complexity classes is an
orientation finding rather than a Concern; the absolute SPEC time budgets
remain the performance yardstick.

The other registered surfaces are the separation-bound helper and internal
Taylor/witness/Newton, component/refined-atom, or individual-strategy kernels.
The library SPEC declares `no-comparable-surface-in-named-comparator` for them
because python-flint does not expose those operations as callable APIs. With only one
declared Phase-4 comparator, the multi-comparator per-family plot rule does not
apply; `scripts/plots/hex-roots-comparator.py` remains a reproducible optional
plot of the shared fixed-separation ladder.

### Historical parametric cross-strategy run

```sh
lake exe hexroots_bench compare \
  Hex.RootsBench.runIsolateNk Hex.RootsBench.runIsolatePellet \
  Hex.RootsBench.runIsolateNkThenPellet
```

reports `agreement: all functions agree on common params` over the shared
`wilkinson-linprod` domain (`n = 2, 3, 4, 5, 6`): the strategy-invariant
`rootsDigest` (atom count + integer-grid centre buckets) is identical across
`.nk`, `.pellet`, and `.nkThenPellet` (final hash `0x6519358031d0ea70` at
`n = 6` for all three), the cross-implementation conformance check the compare
group exists for. This is the dual-route experiment's measurement record. The
per-degree strategy timings and the `pellet/nk` ratio:

| degree | `.nk` | `.pellet` | `.nkThenPellet` | pellet/nk |
|---:|---:|---:|---:|---:|
| 2 | 0.414 ms | 0.273 ms | 0.288 ms | 0.659 |
| 3 | 2.203 ms | 1.832 ms | 2.050 ms | 0.832 |
| 4 | 8.227 ms | 5.781 ms | 6.220 ms | 0.703 |
| 5 | 27.71 ms | 14.71 ms | 15.18 ms | 0.531 |
| 6 | 78.35 ms | 34.97 ms | 36.16 ms | 0.446 |

On this integer-root family the **Pellet-only route is the faster one, and
increasingly so with degree** (ratio `0.66 → 0.45`): Pellet certifies at a
coarser precision than the sup-norm Newton-Kantorovich witness needs, so the
`.nk` route subdivides more levels. `.nkThenPellet` tracks `.pellet` closely
(NK does not fire early on these coarse squares, so the default falls through to
Pellet after one NK attempt). This is a genuine dual-route finding for the
companion's eventual route-retirement decision: on well-separated integer roots
Pellet wins; the NK route's advantage (exact first-order bounds, no `√2`) is not
visible on this family at these degrees.

## Profile

`perf record -g -F 999` on the in-process `_child` batch runner
(`hexroots_bench _child --bench <NAME> --param <N> --target-nanos 3000000000`),
one representative case per `phase4.input_families` entry. The seeded and
Wilkinson profiles are retained from the original `b08a66cce522` family audit
at the parameters named in their headings; those families and inclusive kernel
paths are unchanged even though their final registrations use different
canonical parameters. The fixed-separation and refine-fixed families were
re-profiled at their final canonical inputs on the rebased round-five tree;
refine-fixed uses the final
131077-bit precision. Leaf self-time is categorised across
{own code, GMP, allocation, Lean runtime}; own code = `l_Hex_*`, `lp_Hex_*`,
`l_Dyadic_*`, `l_GaussDyadic_*`, and the dyadic-mantissa integer leaves
(`l_Int_*`). `perf.data` artefacts are developer-local under `/tmp` and are not
committed.

### `seeded-dense` — `runIsolateAll` at `n = 16` (2447 samples)

Leaf self-time: GMP 32.9 % (`__gmpz_init_set` 7.6 %, `__gmpz_cmp_si` 2.6 %,
`__gmpz_add` 2.1 %, `__gmpz_realloc`/`__gmpn_*`), allocation 21.5 %
(`malloc` 7.5 %, `cfree` 7.1 %, `realloc`, `mi_*`), Lean runtime 22.7 %
(`lean_dec_ref_cold`, `lean::mpz_to_int`, `lean::mpz::~mpz`), own code 19.0 %
(`l_Dyadic_add` 3.8 %, `l_Dyadic_mul` 1.9 %, `l_Int_trailingZeros_aux`,
`lp_Hex_…taylor`); 96.2 % classified. This is the growing-precision regime the
`n⁵` model predicts: the working bit-length reaches multiple GMP words, so GMP
big-integer arithmetic and its allocation/box-unbox traffic dominate, flowing
inclusively through the registered `isolateAll?` → `taylor`/`witnessCheck`
path.

### `fixed-separation-product` — fixed `runIsolate` at degree 8 (3822 samples)

Quiet-host `perf record -g -F 999` across twenty final canonical repeats
(median `144.629 ms`, expected hash `0x16c307fd2a36d31e`). Leaf self-time is
97.6 % classified: own dyadic/integer code 34.6 % (`Int.trailingZeros` 9.9 %,
`Dyadic.add` 5.7 %, `Dyadic.mul` 3.1 %, shifts/Taylor folds), Lean runtime
25.1 % (`lean_dec_ref_cold` 4.4 %, mpz box/unbox and reference counting), GMP
19.3 % (`gmpz_init_set` 3.0 %, add/mul-2exp/realloc), and allocation 18.6 %
(`free` 4.1 %, `malloc` 3.6 %, realloc and mimalloc); 2.3 % unresolved.
Inclusive cost terminates in the registered fixed `runIsolate` driver; the
mixture confirms that exact dyadic work, limb management, allocation, and
runtime traffic all remain material. Artefact: developer-local
`/tmp/hexroots-separated-n8.perf`.

### `wilkinson-linprod` — `runIsolateNkThenPellet` at `n = 6` (2489 samples)

Leaf self-time: **own code 44.9 %** (`l_Int_trailingZeros_aux` 9.3 %,
`l_Dyadic_add` 7.4 %, `l_Dyadic_mul` 5.3 %, `l_Dyadic_ofIntWithPrec` 3.0 %,
`l_Int_shiftLeft`), GMP 19.3 % (`__gmpz_mul_2exp` 3.2 %), allocation 15.1 %,
Lean runtime 17.6 %; 97.0 % classified. The own-code share is more than double
the seeded family's, exactly the flat, sub-word band the `n²`/`n⁵`-op-count
derivations claim for the integer-centred `linProdPoly`: operands stay small,
so the actual `Dyadic` arithmetic (own code) dominates rather than GMP. The
inclusive path is the registered `isolate`/compare-group driver.

### `refine-fixed` — `runRefineTo` at achieved precision 131077 (~4000 samples)

Final canonical fixed case, profiled across ten timed repeats and **4026
retained samples** (median
`316.658 ms`, matching expected hash `0x5eb22e5c1f4a7a5`). Leaf self-time is
classified 98.6 % across the required categories: GMP 81.7 %, allocation
8.0 %, Lean runtime 8.1 %, and own code 0.7 %; 1.6 % is unresolved. GMP is
dominated by `__gmpn_divrem_1_x86_64` 65.3 % and
`__gmpn_copyi_x86_64` 13.2 %. Allocation is led by `_int_malloc` 2.4 % and
free/realloc helpers; individual own-code leaves are each below 0.5 %. The
high-precision reciprocal/division is therefore the
actual canonical bottleneck, inclusively terminating in the registered
`refineTo?`. Artefact: developer-local
`/tmp/hexroots-refineto-131077.perf`.

**Attribution rule.** Every dominant inclusive path terminates in a registered
bench target (`isolateAll?`/`isolate`, `taylor`, `witnessCheck`/
`nkWitnessCheck`, `newtonSquare`, `refine1`/`certify`, `refineTo?`), so no
unregistered helper dominates and no new target is required. (Lean's
closure-call unwinding fragments some inclusive attribution into an unresolved
`0x1` frame ~6 %, a `perf`/RTS artefact, not an unregistered hot path.)

## Resolved Historical Concerns

The preceding Phase-3 audit blocked Phase 4 and kept `done_through` at `3`.
Each Concern below is retained as historical evidence, together with the
diagnosis and resolution that now permit `done_through: 4`.
None is a wrong-asymptotic implementation bug that rolling back a `def` would
fix; the resolutions are Phase-4 benchmark re-scaffolding (new schedules, a
smooth driver family, an integer Taylor centre) plus a SPEC time-budget
re-appraisal.

1. **`runIsolate`, `runIsolateAll` inconclusive — seeded-family
   non-monotonicity.** At `n⁵` the residual is small (`β=+0.266` for
   `isolateAll`), but the seeded polynomials' degree-dependent root geometry
   makes wall time non-monotonic in `n` (e.g. `isolateAll` at `n=18` is
   `6.52 s` but `n=20` is `4.02 s`, because `seededPoly 18` happens to have a
   closer root pair), so no power-law fit is clean. Resolution: replace the
   per-degree-varying seed with a family whose isolation difficulty is smooth
   in `n` (e.g. a fixed root-separation product), then re-measure `n⁵`.

2. **`runIsolatePellet`, `runIsolateNkThenPellet` inconclusive — narrow-range
   range check.** `n⁵` is the right model (`runIsolateNk` on the same domain is
   *consistent*), but the 5-rung `n=2..6` schedule is too narrow for a slope
   fit, so the verdict falls to the multiplicative range check, which the
   slightly-sub-`n⁵` Pellet growth (`cMax/cMin = 1.68`, `1.81`) fails against
   the `1.5` noise floor. Resolution: widen the compare-group schedule
   (larger degrees, or in-fill rungs) so a slope fit governs the verdict.

3. **`runTaylor` inconclusive — non-integer-centre transition band.** The fixed
   centre `1/4 + i/8` gives `Θ(n)` denominator growth, so wall scales
   `~n^{2.25}` (probed to `n=1024`), between the `n²` op-count and the `n³`
   bit-op asymptote; neither clean power is consistent (`n²` gives `β=+0.42`).
   The analogous hex-real-roots `runMobiusTransform` is consistent at `n²`
   precisely because it uses an *integer* interval endpoint. Resolution: an
   integer Taylor centre for the benchmark, or declare and reach the `n³`
   multiplication-bound regime (operand word counts an order of magnitude past
   the wallclock cap).

4. **`runWitnessCheck`, `runNewtonSquare`, `runCertify` inconclusive —
   startup-dominated microsecond band.** These run in `1–45 µs` on the small
   `n ≤ 12/16` schedules, where the fixed per-call overhead (array allocation,
   checksum) makes the `C` curve U-shaped (`witnessCheck` `β=−0.23`,
   `newtonSquare` `β=+0.20`, `certify` monotone-decreasing), so `n²` does not
   fit cleanly even though the operands are provably flat. `runRefine1` and
   `runNkWitnessCheck` on the same band happen to pass. Resolution: raise the
   schedules into a signal band clear of startup (larger degrees, keeping
   operands sub-word), or hoist more of the per-call fixed cost out of the
   timed body.

5. **`runRefineTo` inconclusive — Newton-doubling precision quantisation.**
   Speculative Newton doubles precision per jump, so `refineTo?` reaches a
   *discrete* precision ladder and the per-call work is a step function of the
   target `t` (`t=96` and `t=128` do equal work; likewise `t=192`, `t=256`),
   not smooth in `t`. `t²` cannot fit a staircase. Resolution: parametrise the
   benchmark by the *number of Newton jumps* (monotone in work) rather than the
   raw target precision.

6. **SPEC time budget: degree 50 @ prec 64 FAILS.** SPEC target `< 10 s`.
   Measured with `isolateAll? (seededPoly 50) 64` (used because
   `separationDepth(deg 50) ≫ 64`, per the SPEC note): single call
   **495.85 s** (`chk = 4218`, 50 atoms), **`49.6×` over budget**. Resolution:
   this is a rough-first-guess budget the implementation does not meet at `n⁵`
   scaling; either the absolute budget is re-appraised or the driver is
   optimised (Graeffe iteration, deferred in the SPEC, would cut the
   `ceilLog2(deg)` separation-depth factor).

7. **SPEC time budget: degree 100 @ prec 128 FAILS.** SPEC target `< 1 min`.
   Measured with `isolateAll? (seededPoly 100) 128`: the single call did **not
   complete within a 19-minute window** (`> 1143 s`, already `> 19×` the budget,
   then stopped; extrapolating the `n⁵·B²` model from the degree-50 point puts
   the true time in the hours). Same resolution as Concern 6.

For reference, the one budget that is met: **degree 10 @ prec 32** runs in
`0.137 s` (`isolateAll? (seededPoly 10) 32`, compiled, calibrated against the
`runIsolateAll` `n=10` bench row of `138 ms`), comfortably under the `< 1 s`
target.

The transition-band and family/schedule items above are resolved by the final
fixed/parametric split. The two obsolete time-budget items were reality-anchored
by #8762; #8751 is a non-blocking future tightening programme.

## Concerns

None.
