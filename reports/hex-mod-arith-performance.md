# HexModArith Performance Report

## Bench Targets

- `Hex.ModArithBench.runConstructChecksum`: `ZMod64.ofNat`, `n`
- `Hex.ModArithBench.runCastChecksum`: natural and integer casts, `n`
- `Hex.ModArithBench.runAddChecksum`: `ZMod64.add`, `n`
- `Hex.ModArithBench.runSubChecksum`: `ZMod64.sub`, `n`
- `Hex.ModArithBench.runMulChecksum`: extern-backed `ZMod64.mul`, `n`
- `Hex.ModArithBench.runPow`: exponentiation by squaring over an `n`-bit exponent, `n`
- `Hex.ModArithBench.runInvChecksum`: `ZMod64.inv`, `n`
- `Hex.ModArithBench.runBarrettMulModChain`: `BarrettCtx.mulMod`, `n`
- `Hex.ModArithBench.runMontToChecksum`: `MontCtx.toMont`, `n`
- `Hex.ModArithBench.runMontMulChain`: `MontCtx.mulMont`, `n`
- `Hex.ModArithBench.runMontFromChecksum`: `MontCtx.fromMont`, `n`
- `Hex.ModArithBench.runBarrettCompareChain`: common-domain Barrett multiplication comparison, `n`
- `Hex.ModArithBench.runMontCompareChain`: common-domain Montgomery multiplication comparison, `n`

## Verdicts

Scientific run at commit `f5bfa6409349b42d02ece03f5cb5193c89118bb4` on
`carica` (macOS, arm64), command:

```sh
lake exe hexmodarith_bench run Hex.ModArithBench.runPow Hex.ModArithBench.runMulChecksum Hex.ModArithBench.runCastChecksum Hex.ModArithBench.runMontToChecksum Hex.ModArithBench.runMontMulChain Hex.ModArithBench.runMontCompareChain Hex.ModArithBench.runBarrettCompareChain Hex.ModArithBench.runMontFromChecksum Hex.ModArithBench.runConstructChecksum Hex.ModArithBench.runAddChecksum Hex.ModArithBench.runSubChecksum Hex.ModArithBench.runInvChecksum Hex.ModArithBench.runBarrettMulModChain --signal-floor-multiplier 1.0 --export-file reports/bench-results/hex-mod-arith-f5bfa6409349.json
```

The run used deterministic inputs from `HexModArith/Bench.lean`; random
seeds are not involved. Export artefact:
`reports/bench-results/hex-mod-arith-f5bfa6409349.json`, SHA-256
`d658944d021eab8cf2a797ad0e30294b029660c5d96e719052c0432a4e3742a7`.
The working tree was dirty during the run because this audit branch also
contained the benchmark/report edits and a pre-existing `.claude/CLAUDE.md`
modification outside this report's scope.

- `Hex.ModArithBench.runPow`: consistent with declared complexity
  (`β=-0.004663`, parameters `65536..262144`, final hash
  `0x89972e72daba2d86`).
- `Hex.ModArithBench.runMulChecksum`: consistent with declared complexity
  (`β=+0.001480`, parameters `131072..524288`, final hash
  `0x21c1d20bc381ef20`).
- `Hex.ModArithBench.runCastChecksum`: consistent with declared complexity
  (`β=+0.000198`, parameters `8192..131072`, final hash
  `0x2cba60d5674341f6`).
- `Hex.ModArithBench.runMontToChecksum`: consistent with declared complexity
  (`β=+0.003680`, parameters `8192..131072`, final hash
  `0x515f49d9bfa4b3a6`).
- `Hex.ModArithBench.runMontMulChain`: consistent with declared complexity
  (`β=-0.001203`, parameters `8192..131072`, final hash `0x0`).
- `Hex.ModArithBench.runMontCompareChain`: consistent with declared
  complexity (`β=-0.001675`, parameters `8192..131072`, final hash `0x0`).
- `Hex.ModArithBench.runBarrettCompareChain`: consistent with declared
  complexity (`β=-0.003020`, parameters `8192..131072`, final hash `0x0`).
- `Hex.ModArithBench.runMontFromChecksum`: consistent with declared complexity
  (`β=+0.003580`, parameters `8192..131072`, final hash
  `0x515f49d9bfa4b3a6`).
- `Hex.ModArithBench.runConstructChecksum`: consistent with declared
  complexity (`β=+0.002486`, parameters `131072..1048576`, final hash
  `0xb67643c72ce84800`).
- `Hex.ModArithBench.runAddChecksum`: consistent with declared complexity
  (`β=-0.004086`, parameters `65536..262144`, final hash
  `0x1f291d64ff7d8e00`).
- `Hex.ModArithBench.runSubChecksum`: consistent with declared complexity
  (`β=-0.011061`, parameters `131072..1048576`, final hash
  `0xb5cf661b6d76f000`).
- `Hex.ModArithBench.runInvChecksum`: consistent with declared complexity
  (`β=-0.001259`, parameters `2048..32768`, final hash
  `0x3ef5f7d74f82d064`).
- `Hex.ModArithBench.runBarrettMulModChain`: consistent with declared
  complexity (`β=-0.004271`, parameters `131072..1048576`, final hash
  `0x0`).

Smoke wiring was checked with:

```sh
lake exe hexmodarith_bench list
lake exe hexmodarith_bench verify
```

`verify` passed all 13 registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-mod-arith.md` does not name an external Phase-4
comparator for `HexModArith`, so there are no external comparator ratios to
record.

The within-Lean Barrett/Montgomery common-domain comparison was checked with:

```sh
lake exe hexmodarith_bench compare Hex.ModArithBench.runBarrettCompareChain Hex.ModArithBench.runMontCompareChain --signal-floor-multiplier 1.0
```

The common parameters were `8192, 16384, 32768, 65536, 131072`; lean-bench
reported `agreement: all functions agree on common params`. The run used
`--signal-floor-multiplier 1.0` because the Barrett compare body is
sub-millisecond at these parameters under the child-process harness floor.

## Profile

Profiles were captured at 1 kHz with `samply 0.13.1` on `carica` (Apple M2
Ultra, macOS 14.6.1). Each profile used the compiled bench child mode so the
profiled process was the measured benchmark body, not the parent harness:

```sh
samply record --save-only --unstable-presymbolicate --include-args=6 --rate 1000 -o /tmp/hexmodarith-profiles/word-residue-core-child-runMulChecksum-n524288.json.gz -- .lake/build/bin/hexmodarith_bench _child --bench Hex.ModArithBench.runMulChecksum --param 524288 --target-nanos 800000000
samply record --save-only --unstable-presymbolicate --include-args=6 --rate 1000 -o /tmp/hexmodarith-profiles/barrett-hot-loop-child-runBarrettMulModChain-n1048576.json.gz -- .lake/build/bin/hexmodarith_bench _child --bench Hex.ModArithBench.runBarrettMulModChain --param 1048576 --target-nanos 800000000
samply record --save-only --unstable-presymbolicate --include-args=6 --rate 1000 -o /tmp/hexmodarith-profiles/montgomery-hot-loop-child-runMontMulChain-n131072.json.gz -- .lake/build/bin/hexmodarith_bench _child --bench Hex.ModArithBench.runMontMulChain --param 131072 --target-nanos 800000000
```

The raw profile artefacts are local-only per `SPEC/profiling.md`; the paths
above record their developer-local locations. The commit recorded by each child
profile was `f5bfa6409349b42d02ece03f5cb5193c89118bb4` with
`git_dirty=true` from the unrelated `.claude/CLAUDE.md` worktree change.

### `word-residue-core`

- Representative case: `Hex.ModArithBench.runMulChecksum`, `n=524288`,
  deterministic `prepBinaryInput` samples over modulus `65537`.
- Non-wait leaf categorisation: allocation/free 54.3%, GMP 15.1%, Lean runtime
  13.9%, own code 5.1%, other 11.6%. The largest leaves were allocator paths
  (`_nanov2_free`, `nanov2_malloc`, `_free`, `_malloc_zone_malloc`) under the
  extern-backed multiplication loop.
- Inclusive ranking: `Hex.ModArithBench.runMulChecksum_go` 95.4%,
  the generated loop wrapper 95.4%, and `lean_hex_zmod64_mul` 95.2%.
- Dominant-cost narrative: the profile lands in the registered
  `runMulChecksum` target. The inclusive path is the public `ZMod64.mul`
  extern hot loop; the leaf budget is mostly allocation/GMP support below that
  call boundary, so no unregistered dominant library function was found.

### `barrett-hot-loop`

- Representative case: `Hex.ModArithBench.runBarrettMulModChain`, `n=1048576`,
  deterministic `prepUnaryInput` residues over modulus `65537`.
- Non-wait leaf categorisation: own code 97.4%, Lean runtime 0.9%,
  allocation/free 0.3%, other 1.4%, GMP 0%.
- Inclusive ranking: `Hex.ModArithBench.runBarrettMulModChain_go` 97.0%,
  `Hex.BarrettCtx_mulMod` 91.9%, `Hex.ZMod64_ofNat` 45.3%,
  `Hex.barrettReduce` 24.7%, and `lean_hex_uint64_mul_hi` 11.1%.
- Dominant-cost narrative: the cost is attributable to the registered Barrett
  chain target. The main inclusive entries are the benchmark loop,
  `BarrettCtx.mulMod`, reduction, and the UInt64 high-multiply extern used by
  Barrett reduction.

### `montgomery-hot-loop`

- Representative case: `Hex.ModArithBench.runMontMulChain`, `n=131072`,
  deterministic `prepMontInput` residues over modulus `65537`.
- Non-wait leaf categorisation: Lean runtime 75.6%, allocation/free 8.8%,
  own code 5.6%, other 9.9%, GMP 0%.
- Inclusive ranking: `Hex.redc` 93.2%,
  `Hex.ModArithBench.runMontMulChain` 87.8%,
  `lean_hex_uint64_add_carry` 44.0%, and `lean_hex_uint64_mul_full` 32.2%.
- Dominant-cost narrative: the cost is attributable to the registered
  Montgomery multiplication-chain target. The dominant inclusive function is
  the REDC reduction used by `MontCtx.mulMont`; the leaf runtime/allocation
  samples are below that registered hot path.

The dominant inclusive costs all map to registered `HexModArith.Bench`
targets. No unattributed dominant cost was observed.

## Concerns
