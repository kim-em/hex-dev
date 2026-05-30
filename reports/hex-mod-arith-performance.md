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

Profiles were captured with timed-region filtering through
`scripts/profile/run_profile.sh` at `--rate 999` with `samply 0.13.1` on
`carica` (Apple M2 Ultra, arm64, macOS 14.6.1). The filtered profiles retain
only bench-thread samples that fall inside the bench library's timed regions.
Each run used the compiled bench executable built from commit
`3bc24c50fbe57487776c433106894ee544a6d656`; the child environment reported
`git_dirty=true` because of the pre-existing `.claude/CLAUDE.md` worktree
change outside this report's scope. The harness was `lean-bench` `0.1.0`
(manifest rev `91412dba8350c29ddf52c9ace56f8a3d2240b6c7`) and the filtering
orchestrator checkout was `lean-bench-samply`
`602da96df3537341b50de9add2f137b0a75a68df`.

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexmodarith_bench Hex.ModArithBench.runMulChecksum 524288 2000000000
scripts/profile/run_profile.sh ./.lake/build/bin/hexmodarith_bench Hex.ModArithBench.runBarrettMulModChain 1048576 2000000000
scripts/profile/run_profile.sh ./.lake/build/bin/hexmodarith_bench Hex.ModArithBench.runMontMulChain 131072 2000000000
```

The raw profile artefacts are local-only per `SPEC/profiling.md`; the filtered
developer-local paths were `/tmp/hex-profile-runMulChecksum-524288.json.gz`,
`/tmp/hex-profile-runBarrettMulModChain-1048576.json.gz`, and
`/tmp/hex-profile-runMontMulChain-131072.json.gz`. The inputs are deterministic
benchmark fixtures, so no random seed is involved.

### `word-residue-core`

- Representative case: `Hex.ModArithBench.runMulChecksum`, `n=524288`,
  deterministic `prepBinaryInput` samples over modulus `65537`.
- Leaf categorisation: allocation/free 62.5%, GMP 15.7%, Lean runtime 12.9%,
  own code 1.0%, other 7.9%. The largest leaves were allocator paths in
  `libsystem_malloc.dylib` (57.8%), `__gmpz_init_set_ui` (3.1%),
  `__gmpz_add` (2.5%), `lean_is_scalar` (2.4%), `__gmpz_realloc` (2.0%),
  `lean_dec_ref` (1.9%), `lean_dec_ref_cold` (1.8%), and
  `lean_uint64_to_nat` (1.7%).
- Inclusive ranking: `Hex.ModArithBench.runMulChecksum.go` 100.0%, the
  generated `Std.Legacy.Range.forIn'` loop wrapper 100.0%, and
  `lean_hex_zmod64_mul` 99.8%.
- Dominant-cost narrative: the profile lands in the registered
  `runMulChecksum` target. The inclusive path is the public `ZMod64.mul`
  extern hot loop; the leaf budget is mostly allocation/GMP support below that
  call boundary, so no unregistered dominant library function was found.
- Diagnostics:

  ```text
  bench thread:       name='Thread <4892425>' tid=4892425
  regions:            1, total timed = 1812.8 ms
  expected samples:   ~1811 on bench thread
  retained samples:   1811 on bench thread (28 rejected outside windows)
  other-thread noise: 0 samples on non-bench threads within timed windows (informational)
  filtered profile:   /tmp/hex-profile-runMulChecksum-524288.json.gz
  spawn_anchor_wall_ns: 1780142596912771000
  spawn_anchor_mono_ns: 330630833298250
  sidecar_mono_anchor_ns: 330631771189708
  samply_meta_start_time_ms: 1780142596919.383
  ```

### `barrett-hot-loop`

- Representative case: `Hex.ModArithBench.runBarrettMulModChain`, `n=1048576`,
  deterministic `prepUnaryInput` residues over modulus `65537`.
- Leaf categorisation: own code 100.0%, GMP 0%, allocation/free 0%, Lean
  runtime 0%, other 0%. The largest leaves were `Hex.ZMod64.ofNat` (44.6%),
  `Hex.BarrettCtx.mulMod` (22.8%), `Hex.barrettReduce` (14.6%),
  `lean_hex_uint64_mul_hi` (12.2%), and
  `Hex.ModArithBench.runBarrettMulModChain.go` (5.8%).
- Inclusive ranking: `Hex.ModArithBench.runBarrettMulModChain.go` 100.0%,
  the generated `Std.Legacy.Range.forIn'` loop wrapper 100.0%,
  `Hex.BarrettCtx.mulMod` 94.2%, `Hex.ZMod64.ofNat` 44.6%,
  `Hex.barrettReduce` 26.7%, and `lean_hex_uint64_mul_hi` 12.2%.
- Dominant-cost narrative: the cost is attributable to the registered Barrett
  chain target. The main inclusive entries are the benchmark loop,
  `BarrettCtx.mulMod`, reduction, and the UInt64 high-multiply extern used by
  Barrett reduction.
- Diagnostics:

  ```text
  bench thread:       name='Thread <4893373>' tid=4893373
  regions:            1, total timed = 3012.0 ms
  expected samples:   ~3009 on bench thread
  retained samples:   3006 on bench thread (37 rejected outside windows)
  other-thread noise: 0 samples on non-bench threads within timed windows (informational)
  filtered profile:   /tmp/hex-profile-runBarrettMulModChain-1048576.json.gz
  spawn_anchor_wall_ns: 1780142604035082000
  spawn_anchor_mono_ns: 330637955687500
  sidecar_mono_anchor_ns: 330638208476750
  samply_meta_start_time_ms: 1780142604042.073
  ```

### `montgomery-hot-loop`

- Representative case: `Hex.ModArithBench.runMontMulChain`, `n=131072`,
  deterministic `prepMontInput` residues over modulus `65537`.
- Leaf categorisation: Lean runtime 80.7%, allocation/free 8.5%, own code
  5.9%, other 4.9%, GMP 0%. The largest leaves were `lean_is_ctor` (10.8%),
  `lean_ptr_tag` (10.0%), `lean_alloc_ctor` (9.6%), `lean_align` (8.6%),
  `lean_usize_add_checked` (5.0%), `lean_dec_ref_cold` (5.0%),
  `mi_malloc_small` (5.0%), `lean_usize_mul_checked` (4.8%),
  `lean_ctor_num_objs` (4.6%), `lean_set_st_header` (3.8%), and
  `Hex.redc` (3.8%).
- Inclusive ranking: `Hex.ModArithBench.runMontMulChain` 99.9%,
  the generated `Std.Legacy.Range.forIn'` loop wrapper 99.9%, `Hex.redc`
  99.5%, `lean_hex_uint64_add_carry` 47.7%, and
  `lean_hex_uint64_mul_full` 37.9%.
- Dominant-cost narrative: the cost is attributable to the registered
  Montgomery multiplication-chain target. The dominant inclusive function is
  the REDC reduction used by `MontCtx.mulMont`; the leaf runtime/allocation
  samples are below that registered hot path.
- Diagnostics:

  ```text
  bench thread:       name='Thread <4894088>' tid=4894088
  regions:            2, total timed = 1538.2 ms
  expected samples:   ~1537 on bench thread
  retained samples:   1534 on bench thread (65 rejected outside windows)
  other-thread noise: 2 samples on non-bench threads within timed windows (informational)
  filtered profile:   /tmp/hex-profile-runMontMulChain-131072.json.gz
  spawn_anchor_wall_ns: 1780142611311776000
  spawn_anchor_mono_ns: 330645232462041
  sidecar_mono_anchor_ns: 330646821148125
  samply_meta_start_time_ms: 1780142611320.4019
  ```

The dominant inclusive costs all map to registered `HexModArith.Bench`
targets. No unattributed dominant cost was observed.

## Concerns
