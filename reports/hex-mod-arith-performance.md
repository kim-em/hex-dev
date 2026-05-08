# HexModArith Performance Report

## Bench Targets

- `Hex.ModArithBench.runConstructChecksum`: `n`
- `Hex.ModArithBench.runCastChecksum`: `n`
- `Hex.ModArithBench.runAddChecksum`: `n`
- `Hex.ModArithBench.runSubChecksum`: `n`
- `Hex.ModArithBench.runMulChecksum`: `n`
- `Hex.ModArithBench.runPow`: `n`
- `Hex.ModArithBench.runInvChecksum`: `n`
- `Hex.ModArithBench.runBarrettMulModChain`: `n`
- `Hex.ModArithBench.runMontToChecksum`: `n`
- `Hex.ModArithBench.runMontMulChain`: `n`
- `Hex.ModArithBench.runMontFromChecksum`: `n`

## Verdicts

Scientific run at commit `f5bfa6409349b42d02ece03f5cb5193c89118bb4`
(`git_dirty=true`, from an unrelated local `.claude/CLAUDE.md` change) on
`carica` (Apple M2 Ultra, macOS 14.6.1), command:

```sh
.lake/build/bin/hexmodarith_bench run --export-file reports/bench-results/hex-mod-arith-f5bfa64.json Hex.ModArithBench.runConstructChecksum Hex.ModArithBench.runCastChecksum Hex.ModArithBench.runAddChecksum Hex.ModArithBench.runSubChecksum Hex.ModArithBench.runMulChecksum Hex.ModArithBench.runPow Hex.ModArithBench.runInvChecksum Hex.ModArithBench.runBarrettMulModChain Hex.ModArithBench.runMontToChecksum Hex.ModArithBench.runMontMulChain Hex.ModArithBench.runMontFromChecksum
```

The run used deterministic inputs from `HexModArith/Bench.lean`; random seeds
are not involved. Export artefact:
`reports/bench-results/hex-mod-arith-f5bfa64.json`.

- `Hex.ModArithBench.runConstructChecksum`: consistent with declared
  complexity (`β=+0.000`, parameters `131072..1048576`).
- `Hex.ModArithBench.runCastChecksum`: consistent with declared complexity
  (`β=-0.016`, parameters `8192..131072`).
- `Hex.ModArithBench.runAddChecksum`: consistent with declared complexity
  (`β=+0.011`, parameters `65536..262144`).
- `Hex.ModArithBench.runSubChecksum`: consistent with declared complexity
  (`β=+0.011`, parameters `131072..1048576`).
- `Hex.ModArithBench.runMulChecksum`: consistent with declared complexity
  (`β=+0.034`, parameters `131072..524288`).
- `Hex.ModArithBench.runPow`: consistent with declared complexity
  (`β=-0.023`, parameters `65536..262144`).
- `Hex.ModArithBench.runInvChecksum`: consistent with declared complexity
  (`β=-0.006`, parameters `2048..32768`).
- `Hex.ModArithBench.runBarrettMulModChain`: consistent with declared
  complexity (`β=+0.008`, parameters `131072..1048576`).
- `Hex.ModArithBench.runMontToChecksum`: consistent with declared complexity
  (`β=+0.003`, parameters `8192..131072`).
- `Hex.ModArithBench.runMontMulChain`: consistent with declared complexity
  (`β=-0.009`, parameters `8192..131072`).
- `Hex.ModArithBench.runMontFromChecksum`: consistent with declared complexity
  (`β=-0.005`, parameters `8192..131072`).

Smoke wiring was checked with:

```sh
lake exe hexmodarith_bench list
lake exe hexmodarith_bench verify
```

`verify` passed all eleven registered benchmarks at the same commit.

## Comparator Ratios

`SPEC/Libraries/hex-mod-arith.md` does not name an external Phase-4
comparator for `HexModArith`, so there are no external comparator ratios to
record.

The internal opt-in hot-loop alternatives use the shared small odd modulus
`65537`, but they do not have a single common semantic-domain compare group:
Barrett operates on standard `ZMod64` residues, while Montgomery multiplication
operates on `MontResidue` values between explicit `toMont` and `fromMont`
conversions. The benchmark registrations cover both paths separately.

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
