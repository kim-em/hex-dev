# HexArith Performance Report

## Bench Targets

- `Hex.ArithBench.runBarrettMulChain`: `n`
- `Hex.ArithBench.runMontgomeryMulChain`: `n`
- `Hex.ArithBench.runPowMod`: `n`
- `Hex.ArithBench.runNatExtGcdShapes`: `n`
- `Hex.ArithBench.runIntExtGcdShapes`: `n`
- `Hex.ArithBench.runUInt64ExtGcdShapes`: `n`

## Verdicts

Scientific run at commit `9d5abccc06778f4a6f10fdb9e1f58433d1871410` on
`carica` (macOS arm64), command:

```sh
lake exe hexarith_bench run Hex.ArithBench.runBarrettMulChain Hex.ArithBench.runMontgomeryMulChain Hex.ArithBench.runPowMod Hex.ArithBench.runNatExtGcdShapes Hex.ArithBench.runIntExtGcdShapes Hex.ArithBench.runUInt64ExtGcdShapes --export-file reports/bench-results/hex-arith-9d5abccc0677.json
```

The run used the deterministic benchmark inputs from `HexArith/Bench.lean`;
random seeds are not involved. The harness recorded `9d5abcc-dirty` because
this worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-arith-9d5abccc0677.json`.

- `Hex.ArithBench.runBarrettMulChain`: consistent with declared complexity
  (`β=-0.001`, parameters `8192..131072`).
- `Hex.ArithBench.runMontgomeryMulChain`: consistent with declared complexity
  (`β=+0.002`, parameters `8192..131072`).
- `Hex.ArithBench.runPowMod`: consistent with declared complexity
  (`β=+0.065`, parameters `1024..16384`).
- `Hex.ArithBench.runNatExtGcdShapes`: consistent with declared complexity
  (`β=-0.093`, parameters `8192..24576`).
- `Hex.ArithBench.runIntExtGcdShapes`: consistent with declared complexity
  (`β=+0.006`, parameters `8192..24576`).
- `Hex.ArithBench.runUInt64ExtGcdShapes`: consistent with declared complexity
  (`β=-0.013`, parameters `8192..24576`).

Smoke wiring was also checked with:

```sh
lake exe hexarith_bench list
lake exe hexarith_bench verify
```

`verify` passed all six registered benchmarks at the same commit.

## Comparator Ratios

`SPEC/Libraries/hex-arith.md` does not name an external Phase-4 comparator for
`HexArith`, so there are no external comparator ratios to record.

The internal compare-relevant domains are covered by shared result hashes:
Barrett and Montgomery agree on the modular-multiplication chain, and the Nat,
Int/GMP, and UInt64 extended-GCD registrations agree on normalized
gcd/Bezout-shape hashes.

## Profile

Profiles were captured with `samply record --save-only` through the
`hexarith_bench profile` subcommand on `carica` (Apple M2 Ultra, macOS 14.6.1).
Sampling rate was samply's default 1000 Hz. The profiled binary was built from
commit `f5bfa6409349b42d02ece03f5cb5193c89118bb4`; the benchmark row reported
`git_dirty=true` because of a pre-existing local `.claude/CLAUDE.md` edit.
Random seeds are not involved in the deterministic HexArith benchmark inputs.
Raw profiler JSON artefacts are developer-local and are not committed.

- `modular-multiplication-chain`
  - Command: `lake exe hexarith_bench profile Hex.ArithBench.runMontgomeryMulChain --param 131072 --profiler "samply record --save-only --output /tmp/hexarith-montgomery-chain-131072.json.gz" --target-inner-nanos 5000000000`
  - Child row: `inner_repeats=128`, `per_call_nanos=38372592.773438`,
    `result_hash=0x1`, artefact `/tmp/hexarith-montgomery-chain-131072.json.gz`.
  - Leaf cost: Lean runtime 81.2%, allocation 7.6%, HexArith own code and
    FFI helpers 7.3%, other 3.9%, GMP 0%.
  - Inclusive ranking: `Hex.ArithBench.runMontgomeryMulChain` accounted for
    the profiled work, with `Hex.redc` at 98.8% inclusive, `lean_hex_uint64_add_carry`
    at 49.0%, `lean_hex_uint64_mul_full` at 34.3%, and Lean constructor/boxing
    paths below that. This is attributable to the registered
    `runMontgomeryMulChain` target.
- `word-powmod`
  - Command: `lake exe hexarith_bench profile Hex.ArithBench.runPowMod --param 16384 --profiler "samply record --save-only --output /tmp/hexarith-powmod-16384.json.gz" --target-inner-nanos 5000000000`
  - Child row: `inner_repeats=256`, `per_call_nanos=14041132.484375`,
    `result_hash=0xf00`, artefact `/tmp/hexarith-powmod-16384.json.gz`.
  - Leaf cost: Lean runtime 60.7%, HexArith own code and FFI helpers 15.8%,
    GMP 11.1%, allocation 4.7%, other 7.8%.
  - Inclusive ranking: the exponentiation path ran through
    `HexArith.powModWordOdd`, `HexArith.powMontBitsGo`, and `Hex.redc`;
    `Hex.redc` was 68.2% inclusive, with `lean_hex_uint64_add_carry` at 32.3%,
    `lean_hex_uint64_mul_full` at 25.1%, and `lean_nat_big_shiftr` at 18.3%.
    This is attributable to the registered `runPowMod` target.
- `bounded-word-extgcd`
  - Command: `lake exe hexarith_bench profile Hex.ArithBench.runIntExtGcdShapes --param 24576 --profiler "samply record --save-only --output /tmp/hexarith-int-extgcd-24576.json.gz" --target-inner-nanos 5000000000`
  - Child row: `inner_repeats=1`, `per_call_nanos=3314702833.000000`,
    `result_hash=0xbc822323529dd715`, artefact
    `/tmp/hexarith-int-extgcd-24576.json.gz`.
  - Leaf cost: Lean runtime 77.0%, HexArith own code and FFI helpers 7.2%,
    GMP 6.6%, allocation 0.8%, other 8.4%.
  - Inclusive ranking: `Hex.ArithBench.runIntExtGcdShapes` accounted for the
    profiled work, with `lean_hex_mpz_gcdext` and its fallback wrapper both at
    82.8% inclusive. The dominant self-time was Lean scalar/int conversion and
    boxing around the GMP call. This is attributable to the registered
    `runIntExtGcdShapes` target.

The dominant inclusive costs all map to registered `HexArith/Bench.lean`
targets. No unattributed or suspicious dominant cost was observed.

## Concerns
