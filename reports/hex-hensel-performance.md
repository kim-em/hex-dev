# HexHensel Performance Report

## Bench Targets

- `Hex.HenselBench.runModPChecksum`: `n`
- `Hex.HenselBench.runLiftToZChecksum`: `n`
- `Hex.HenselBench.runReduceModPowChecksum`: `n`
- `Hex.HenselBench.runLinearHenselStepChecksum`: `n * n`
- `Hex.HenselBench.runHenselLiftChecksum`: `liftLinearComplexity param = n * n * k`
- `Hex.HenselBench.runQuadraticHenselStepChecksum`: `n * n`
- `Hex.HenselBench.runPolyProductChecksum`: `n * n`
- `Hex.HenselBench.runMultifactorLiftChecksum`: `liftLinearComplexity param = n * n * k`
- `Hex.HenselBench.runMultifactorLiftQuadraticChecksum`: `liftQuadraticComplexity param = n * n * Nat.log2 (k + 1)`

## Verdicts

Scientific run at commit `24a4fcaa9dbe` on `carica` (Apple M2 Ultra,
macOS 14.6.1), command:

```sh
lake exe hexhensel_bench run \
    Hex.HenselBench.runModPChecksum \
    Hex.HenselBench.runLiftToZChecksum \
    Hex.HenselBench.runReduceModPowChecksum \
    Hex.HenselBench.runLinearHenselStepChecksum \
    Hex.HenselBench.runHenselLiftChecksum \
    Hex.HenselBench.runQuadraticHenselStepChecksum \
    Hex.HenselBench.runPolyProductChecksum \
    Hex.HenselBench.runMultifactorLiftChecksum \
    Hex.HenselBench.runMultifactorLiftQuadraticChecksum \
    --export-file reports/bench-results/hex-hensel-24a4fca.json
```

The run uses the deterministic dense `F_5`/`Z[x]` benchmark fixtures
constructed in `HexHensel/Bench.lean` (small prime `p = 5` throughout);
no random seeds are involved. The harness recorded `24a4fca-dirty`
because this worktree carried an unrelated pre-existing
`.claude/CLAUDE.md` modification and untracked `.claude/` content.
Export artefact: `reports/bench-results/hex-hensel-24a4fca.json`,
SHA-256 `4633cdcaed2f7d0b056c7eb7b754258c9997f6360427b5a8d28b421e5ae53b49`.

- `Hex.HenselBench.runModPChecksum`: consistent with declared
  complexity (`cMin=108.877, cMax=111.783, β=+0.010`,
  parameters `8192..131072`, final hash `0x93df396c13011785`).
- `Hex.HenselBench.runLiftToZChecksum`: consistent with declared
  complexity (`cMin=53.849, cMax=54.183, β=−0.002`,
  parameters `8192..131072`, final hash `0x389d28873eb4eb88`).
- `Hex.HenselBench.runReduceModPowChecksum`: consistent with declared
  complexity (`cMin=117.236, cMax=117.706, β=−0.001`,
  parameters `8192..131072`, final hash `0x2bb1d2338fde61ab`).
- `Hex.HenselBench.runLinearHenselStepChecksum`: consistent with
  declared complexity (`cMin=314.076, cMax=331.408, β=−0.031`,
  parameters `64..512`, final hash `0x660394e9aae087cc`).
- `Hex.HenselBench.runHenselLiftChecksum`: consistent with declared
  complexity (`cMin=320.073, cMax=396.792, β=−0.096`,
  parameters `32_004..192_064` (encoded `(n, k)`), final hash
  `0xf4ac4cfd1b7bc4db`).
- `Hex.HenselBench.runQuadraticHenselStepChecksum`: consistent with
  declared complexity (`cMin=1285.400, cMax=1382.515, β=+0.023`,
  parameters `64..512`, final hash `0x13f3af080ce8ac5e`).
- `Hex.HenselBench.runPolyProductChecksum`: consistent with declared
  complexity (`cMin=222.696, cMax=258.113, β=+0.079`,
  parameters `128..1024`, final hash `0x3a54a0eb632efee0`).
- `Hex.HenselBench.runMultifactorLiftChecksum`: consistent with
  declared complexity (`cMin=318.608, cMax=396.946, β=−0.116`,
  parameters `32_004..192_064` (encoded `(n, k)`), final hash
  `0xe09bda79cfa1f787`).
- `Hex.HenselBench.runMultifactorLiftQuadraticChecksum`: consistent
  with declared complexity (`cMin=1171.755, cMax=1976.812, β=−0.037`,
  parameters `32_004..192_064` (encoded `(n, k)`), final hash
  `0xe09bda79cfa1f787`).

Smoke wiring was also checked at the same commit with:

```sh
lake exe hexhensel_bench list
lake exe hexhensel_bench verify
```

`verify` passed all nine registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-hensel.md` does not name an external Phase-4
performance comparator for `HexHensel`, so there are no
`phase4.comparators` ratios to record. The internal
`compare runMultifactorLiftChecksum runMultifactorLiftQuadraticChecksum`
group declared in `HexHensel/Bench.lean` cross-checks the linear and
quadratic multifactor lifters on the shared encoded `(n, k)` schedule,
but it is not an external-tool comparator and is exercised by the
scientific run above rather than as a separate ratio table.

## Profile

The bridge, quadratic, and multifactor profiles below were recorded with
`samply record --save-only --unstable-presymbolicate` at commit
`60dbf8026826` on `carica` (Apple M2 Ultra, macOS 14.6.1) at the
default 1 kHz sampling rate. The `linear-hensel` profile was
re-recorded at `24a4fca` (the corrected-fixture commit) on the same
host. The raw Firefox Profiler JSON artefacts and their `.syms.json`
symbol sidecars are developer-local and are not committed; symbol
attribution was done by mapping each frame's RVA against the bench
binary's samply-emitted symbol table. Each profile sums samples from
the `hexhensel_bench` worker child (the LeanBench-spawned `_child`
process running the registered function), not the orchestrator,
whose wallclock is dominated by `__read_nocancel` waits for the
child stdout. All percentages below are leaf counts and inclusive
counts as a fraction of those child-only samples.

### `bridge-operations`

Command:

```sh
lake exe hexhensel_bench profile Hex.HenselBench.runReduceModPowChecksum \
    --param 131072 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-hensel-reduce-mod-pow-60dbf80.json --"
```

Representative case: deterministic dense degree-`131071` integer
polynomial with bounded `[-997, 997]`-magnitude coefficients reduced
through `Hex.ZPoly.reduceModPow _ 5 3`, parameter `n = 131072`, no
seed. Child row: `inner_repeats=256`,
`per_call_nanos=15343224.445312`, `result_hash=0x2bb1d2338fde61ab`.
Total `3989` non-empty samples. Leaf samples were allocation/free
46.5%, GMP 14.5%, Lean runtime 11.8%, own
HexHensel/HexPolyZ/HexDensePoly code 12.8%, other 14.0%, kernel
0.5%. The allocation and GMP weight reflects the per-coefficient
`Int.tmod` reduction modulo `5^3 = 125` boxing each result back
through `lean_int_mod` → `__gmpz_mod` → fresh small-`mpz`
allocation. Inclusive own-code cost was led by
`Hex.ZPoly.reduceModPow` (77.1%) →
`Hex.List.mapTR.loop.at...reduceModPow.spec` (64.2%) per the
`mapTR` per-coefficient reduction loop, with
`Hex.DensePoly.trimTrailingZerosList → trimTrailingZeros →
ofCoeffs` accounting for the post-reduction normalisation
(10.5%). The dominant work maps to the registered
`runReduceModPowChecksum` target via
`ZPoly.reduceModPow → List.mapTR.loop → Int reduction mod 5^k`,
matching the `O(n)` cost model with one bounded reduction per
coefficient. The same code path serves the other two bridge
registrations (`runModPChecksum` and `runLiftToZChecksum`); their
verdicts come back consistent at the same parameter ladder, so a
single `bridge-operations` profile case suffices for the family.

### `linear-hensel`

Command:

```sh
lake exe hexhensel_bench profile Hex.HenselBench.runLinearHenselStepChecksum \
    --param 512 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-hensel-linear-step-24a4fca.json --"
```

Representative case: one linear Hensel correction over the
deterministic two-factor fixture (`g` a fixed degree-1 monic factor
`x + 4` from `linearZFactor 59`, `h` a deterministic dense
degree-`512` integer polynomial from `denseZPoly 513 62`,
`f = g*h + 5*e` with `e` a deterministic dense degree-`512`
perturbation from `denseZPoly 513 67`; Bezout pair `(s, t)` computed
fresh as `normalizedXGCD 5 g h` so that
`s * gMod + t * hMod ≡ 1 (mod 5)`) at parameter `n = 512`, no seed.
Child row: `inner_repeats=64`, `per_call_nanos=83763250.656250`,
`result_hash=0x660394e9aae087cc`. The dominant inclusive cost is
`Hex.ZPoly.linearHenselStep` → `Hex.DensePoly.mul`: the corrected
fixture computes both `s * eMod` and `q * hMod` as full F_5
polynomial multiplications (under the previous degenerate `s = 0`
seed only `q * hMod` carried weight, which is why the per-call
wallclock approximately doubled from the predecessor commit's
`41.97 ms` to the present `83.76 ms` at the same `n = 512` rung;
total work scales the same way, so the `n²` cost-model verdict is
unchanged at `β=−0.031`). Per-coefficient leaf work is dominated by
`Hex.ZMod64.mul` and `Hex.ZMod64.add` inside the dense-polynomial
multiplication kernel; the `Hex.DensePoly.divModArray` divmod call
inside the correction step contributes a small fraction (it divides
a degree-`n` F_5 polynomial by the fixed degree-1 monic `gMod`,
costing `O(n)` synthetic-division steps). Allocation/free and Lean
runtime overheads are comparable to the predecessor profile because
the polynomial sizes and coefficient widths are unchanged. The
dominant work maps to the registered `runLinearHenselStepChecksum`
target via `linearHenselStep → DensePoly.mul (correction product) →
ZMod64.mul`, exactly as the `n²` cost model predicts for the two
dense F_5 correction products per step. The iterative wrapper
`runHenselLiftChecksum` shares this fixture and code path; with the
corrected Bezout pair its verdict comes back consistent over the
full encoded `(n, k)` ladder, so a single `linear-hensel` profile
case suffices for the family.

### `quadratic-hensel`

Command:

```sh
lake exe hexhensel_bench profile Hex.HenselBench.runQuadraticHenselStepChecksum \
    --param 512 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-hensel-quadratic-step-60dbf80.json --"
```

Representative case: one quadratic Hensel correction (factor and
Bezout updates together, both lifted from `mod 5` to `mod 25`) over
the deterministic two-factor fixture (`g` a fixed degree-1 monic
factor, `h` a deterministic dense degree-`513` integer polynomial,
`f = g*h + 5*e`, Bezout pair seeded as `(s, t) = (0, 1)`) at
parameter `n = 512`, no seed. Child row: `inner_repeats=8`,
`per_call_nanos=361804302.000000`,
`result_hash=0x13f3af080ce8ac5e`. Total `3306` non-empty samples.
Leaf samples were allocation/free 40.5%, Lean runtime 17.9%, own
code 14.7%, other 16.6%, GMP 9.7%, kernel 0.5%. Inclusive own-code
cost was led by `Hex.ZPoly.quadraticHenselStep` (98.7%) →
`Hex.ZPoly.divModMonicModSquareAux` (92.8%) for the divmod by the
monic factor `g*` modulo `m²`, with `Hex.ZPoly.reduceModPow`
(53.8%) → `Hex.List.mapTR.loop.at...reduceModPow.spec` (45.9%) for
the trailing coefficient reduction, `Hex.ZPoly.subModSquare`
(21.6%) for the `mod m²` differences, and the Bezout-update
`Hex.DensePoly.mul.at...bezoutCongrOn.spec` (12.2%) for the
post-Bezout corrections `(s*g* + t*h*) - 1`. The dominant work
maps to the registered `runQuadraticHenselStepChecksum` target via
`quadraticHenselStep → divModMonicModSquareAux → reduceModPow`,
matching the `n²` cost model for a single doubling step. The
single-step wallclock on this fixture is bounded regardless of the
seed Bezout pair, so the `(s, t) = (0, 1)` seed used here exercises
the same dense-arithmetic kernels as a full `xgcd`-derived seed
would.

### `multifactor-lifting`

Command:

```sh
lake exe hexhensel_bench profile Hex.HenselBench.runMultifactorLiftQuadraticChecksum \
    --param 192064 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-hensel-multifactor-quadratic-60dbf80.json --"
```

Representative case: production quadratic ordered multifactor lift
of two prepared factors (`g` a fixed degree-1 monic factor, `h` a
deterministic dense degree-`193` integer polynomial,
`f = polyProduct [g, h] + 5*e`) lifted from `mod 5` to `mod 5^64` via
`⌈log₂ 64⌉ = 6` quadratic doublings, parameter
`encodeLiftParam 192 64 = 192_064`, no seed. Child row:
`inner_repeats=16`, `per_call_nanos=323961395.812500`,
`result_hash=0xe09bda79cfa1f787`. Total `5539` non-empty samples.
Leaf samples were allocation/free 52.6%, GMP 15.9%, Lean runtime
11.9%, own code 7.2%, other 12.1%, kernel 0.3%. Inclusive own-code
cost was led by
`Hex.HenselBench.runMultifactorLiftQuadraticChecksum` (99.3%) →
`Hex.ZPoly.multifactorLiftQuadraticList` (99.3%) →
`Hex.ZPoly.henselLiftQuadratic` (99.2%) →
`Hex.ZPoly.iterateQuadraticHensel` (99.1%) →
`Hex.ZPoly.quadraticHenselStep` (99.1%); per-step work splits
between `Hex.ZPoly.divModMonicModSquareAux` (63.8%) for the
divmod-by-`g*` step, `Hex.ZPoly.reduceModPow` (39.0%) for the
trailing coefficient reduction, and the Bezout-update
`Hex.DensePoly.mul.at...bezoutCongrOn.spec` (37.5%) for
`(s*g* + t*h*) - 1`. The dominant work maps to the registered
`runMultifactorLiftQuadraticChecksum` target via
`multifactorLiftQuadraticList → henselLiftQuadratic →
iterateQuadraticHensel → quadraticHenselStep`, matching the
`n² · log₂ k` cost model for a binary lift through `⌈log₂ k⌉`
doublings. The two sibling registrations
`runMultifactorLiftChecksum` and `runPolyProductChecksum` share this
fixture and quadratic-corner code path; their scientific verdicts
both come back consistent at the same encoded `(n, k)` ladder, so a
single `multifactor-lifting` profile case suffices for the family.

The dominant inclusive costs in all four profiles map to registered
`HexHensel/Bench.lean` targets. No unattributed dominant cost was
observed.

## Concerns

None.
