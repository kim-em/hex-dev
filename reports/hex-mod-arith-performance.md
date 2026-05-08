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

Profile coverage is not yet usable for the `HexModArith.phase4.input_families`
entries in `libraries.yml`:

- `word-residue-core`
- `barrett-hot-loop`
- `montgomery-hot-loop`

Local attempts used `samply record --save-only --rate 1000` against
`.lake/build/bin/hexmodarith_bench` on `carica` and wrote raw artefacts under
`/tmp/hex-profiles/`:

- `/tmp/hex-profiles/hex-mod-arith-word-residue-core.json.gz`
- `/tmp/hex-profiles/hex-mod-arith-barrett-hot-loop.json.gz`
- `/tmp/hex-profiles/hex-mod-arith-montgomery-hot-loop.json.gz`

The generated Firefox Profiler JSON files contained zero sampled stacks for
the benchmark processes, so no leaf-cost percentages or inclusive-cost ranking
are claimed in this report snapshot. Issue #2756 tracks producing usable
profiles and applying the attribution rule.

## Concerns

- #2756: Record representative Phase-4 profile coverage for the three
  `HexModArith.phase4.input_families` entries and clear the attribution
  review before re-promoting `HexModArith` to `done_through: 4`.
