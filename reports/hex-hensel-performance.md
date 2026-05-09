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

Scientific run at commit `60dbf8026826` on `carica` (Apple M2 Ultra,
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
    --export-file reports/bench-results/hex-hensel-60dbf8026826.json
```

The run uses the deterministic dense `F_5`/`Z[x]` benchmark fixtures
constructed in `HexHensel/Bench.lean` (small prime `p = 5` throughout);
no random seeds are involved. The harness recorded `60dbf80-dirty`
because this worktree carried an unrelated pre-existing
`.claude/CLAUDE.md` modification and untracked `.claude/` content.
Export artefact: `reports/bench-results/hex-hensel-60dbf8026826.json`,
SHA-256 `dcc9d91f2932aacc09bbb5cb30c4c419705f62f83026aed0d85e311169ee4504`.

- `Hex.HenselBench.runModPChecksum`: consistent with declared
  complexity (`cMin=102.700, cMax=108.741, β=−0.015`,
  parameters `8192..131072`, final hash `0x93df396c13011785`).
- `Hex.HenselBench.runLiftToZChecksum`: consistent with declared
  complexity (`cMin=51.766, cMax=54.019, β=−0.018`,
  parameters `8192..131072`, final hash `0x389d28873eb4eb88`).
- `Hex.HenselBench.runReduceModPowChecksum`: consistent with declared
  complexity (`cMin=109.714, cMax=112.629, β=+0.006`,
  parameters `8192..131072`, final hash `0x2bb1d2338fde61ab`).
- `Hex.HenselBench.runLinearHenselStepChecksum`: consistent with
  declared complexity (`cMin=156.795, cMax=174.149, β=−0.045`,
  parameters `64..512`, final hash `0xb96ef44d7e5545bc`).
- `Hex.HenselBench.runHenselLiftChecksum`: **inconclusive**
  (`cMin=1575.340, cMax=6084.578, β=+0.158`, looks slower than
  declared by `~param^0.158`); the encoded `(n, k)` ladder ran the
  `param=128064` rung into the per-call wallclock cap (`6.000s`)
  and the harness skipped the remaining `param=192064` rung.
  Deepest successful rung is `param=96_042` (encoded `(96, 42)`)
  with hash `0x25610f735c94cdc5`. See §Concerns.
- `Hex.HenselBench.runQuadraticHenselStepChecksum`: consistent with
  declared complexity (`cMin=1221.642, cMax=1331.961, β=+0.027`,
  parameters `64..512`, final hash `0x13f3af080ce8ac5e`).
- `Hex.HenselBench.runPolyProductChecksum`: consistent with declared
  complexity (`cMin=219.947, cMax=251.231, β=+0.066`,
  parameters `128..1024`, final hash `0x3a54a0eb632efee0`).
- `Hex.HenselBench.runMultifactorLiftChecksum`: consistent with
  declared complexity (`cMin=311.966, cMax=387.050, β=−0.101`,
  parameters `32_004..192_064` (encoded `(n, k)`), final hash
  `0xe09bda79cfa1f787`).
- `Hex.HenselBench.runMultifactorLiftQuadraticChecksum`: consistent
  with declared complexity (`cMin=1125.096, cMax=1968.005, β=−0.022`,
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

Profiles were recorded with
`samply record --save-only --unstable-presymbolicate` at commit
`60dbf8026826` on `carica` (Apple M2 Ultra, macOS 14.6.1) at the
default 1 kHz sampling rate. The raw Firefox Profiler JSON
artefacts and their `.syms.json` symbol sidecars are
developer-local and are not committed; symbol attribution was done
by mapping each frame's RVA against the bench binary's
samply-emitted symbol table. Each profile sums samples from the
`hexhensel_bench` worker child (the LeanBench-spawned `_child`
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
        -o /tmp/hex-profiles/hex-hensel-linear-step-60dbf80.json --"
```

Representative case: one linear Hensel correction over the
deterministic two-factor fixture (`g` a fixed degree-1 monic factor,
`h` a deterministic dense degree-`513` integer polynomial,
`f = g*h + 5*e` with `e` a deterministic dense degree-`513`
perturbation; Bezout pair seeded as `(s, t) = (0, 1) mod 5`) at
parameter `n = 512`, no seed. Child row: `inner_repeats=64`,
`per_call_nanos=41966613.921875`,
`result_hash=0xb96ef44d7e5545bc`. Total `2771` non-empty samples.
Leaf samples were allocation/free 48.1%, Lean runtime 21.8%, GMP
10.3%, own code 8.3%, other 10.8%, kernel 0.6%. Inclusive own-code
cost was led by `Hex.ZPoly.linearHenselStep` (98.4%) →
`Hex.DensePoly.mul` (95.4%) → `Hex.DensePoly.mul.redArg.lam`
(87.9%); per-coefficient work appears as `Hex.ZMod64.mul` (68.7%)
and `Hex.ZMod64.add` (8.9%), with `Hex.DensePoly.divModArray`
(2.2%) → `Hex.DensePoly.divModArrayAux` (2.1%) covering the
`F_5[x]` divmod call inside the correction. The dominant work maps
to the registered `runLinearHenselStepChecksum` target via
`linearHenselStep → DensePoly.mul (correction product) → ZMod64.mul`,
exactly as the `n²` cost model predicts for a single dense
correction product. The iterative wrapper
`runHenselLiftChecksum` shares this fixture and code path; its
inconclusive scientific verdict is discussed in §Concerns rather
than reflected in a separate profile case here.

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
matching the `n²` cost model for a single doubling step.

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

- **`runHenselLiftChecksum` verdict is inconclusive.** The
  scientific run reported `cMin=1575.340, cMax=6084.578, β=+0.158`,
  meaning the per-call time grows roughly as `param^(2 + 0.158)`
  rather than the declared `n²·k` cost model. The fastest rung
  (`64_016`, `103.241 ms`) and the slowest rung (`32_042`,
  `261.686 ms`) bracket a 3.9× spread in normalised cost across the
  ladder, far above the harness tolerance for "consistent". The
  `param=128_064` rung exceeded `maxSecondsPerCall = 6.000s` and was
  killed; the `param=192_064` rung was skipped, so the ladder
  effectively terminated at `n = 96`. The same fixture under
  `runMultifactorLiftChecksum` (which calls into the linear lifter
  internally) returned `consistent with declared complexity`
  (`β = −0.101`) over the full ladder, so the cost-model gap is
  specific to the direct `Hex.ZPoly.henselLift` surface measured by
  `runHenselLiftChecksum` and is not visible through the multifactor
  wrapper. Plausible explanations are (a) the declared
  `liftLinearComplexity = n * n * k` cost model does not account for
  the bigint cost of arithmetic on `Z/p^k` coefficients (which grows
  at least linearly with `k` per multiplication for schoolbook
  GMP), or (b) `henselLift` skips a per-step coefficient reduction
  that the multifactor wrapper performs implicitly, letting
  intermediate coefficients grow past `p^k`. Either way,
  re-promoting `HexHensel.done_through` to 4 requires reaching a
  consistent verdict on the iterative linear lift surface, either by
  refining the declared cost model or by tightening `henselLift`'s
  reduction strategy. Follow-up issue: #2791.

While this concern is open, `HexHensel.done_through` stays at 3.
