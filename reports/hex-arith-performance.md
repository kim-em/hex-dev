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

Profiles were captured with `scripts/profile/run_profile.sh`, which runs
`samply record --save-only --no-open --rate 999 --unstable-presymbolicate` and
filters the Firefox Profiler JSON to the bench thread during lean-bench timed
regions only. The host was `carica` (Apple M2 Ultra, macOS 14.6.1, arm64).
The profiled binary was built from commit
`eec3a76fab8cfe59ba2b62cb71f3a21b92aae51c`; the child rows report
`git_dirty=true` because of a pre-existing local `.claude/CLAUDE.md` edit.
The run used lean-bench `91412dba8350` and lean-bench-samply `602da96df353`.
Random seeds are not involved in the deterministic HexArith benchmark inputs.
Raw profiler JSON artefacts are developer-local and are not committed.

- `modular-multiplication-chain`
  - Command: `scripts/profile/run_profile.sh ./.lake/build/bin/hexarith_bench Hex.ArithBench.runMontgomeryMulChain 131072 5000000000`
  - Child row: `inner_repeats=128`, `per_call_nanos=38730926.757812`,
    `result_hash=0x1`, filtered artefact
    `/tmp/hex-profile-runMontgomeryMulChain-131072.json.gz`.
  - Leaf cost after filtering: Lean runtime 80.5%, allocation/free 7.7%,
    HexArith own code and FFI helpers 2.2%, other 9.6%, GMP 0%.
  - Inclusive ranking: all retained samples run under the registered
    `Hex.ArithBench.runMontgomeryMulChain` target. The dominant library
    path is the Montgomery loop through `Hex.redc` (99.6% inclusive), with
    `lean_hex_uint64_add_carry` at 48.7% and `lean_hex_uint64_mul_full` at
    35.2%. The dominant self-time remains Lean constructor/tag/box/refcount
    runtime around the word-level reduction. This is attributable to the
    registered `runMontgomeryMulChain` target.
  - Diagnostics:

    ```text
    regions:            2, total timed = 4997.5 ms
    expected samples:   ~4993 on bench thread
    retained samples:   4992 on bench thread (54 rejected outside windows)
    other-thread noise: 2 samples on non-bench threads within timed windows (informational)
    spawn_anchor_wall_ns=1780141015992269000
    spawn_anchor_mono_ns=329049889965500
    sidecar_mono_anchor_ns=329050253617250
    samply_meta_start_time_ms=1780141015999.488
    ```

- `word-powmod`
  - Command: `scripts/profile/run_profile.sh ./.lake/build/bin/hexarith_bench Hex.ArithBench.runPowMod 16384 5000000000`
  - Child row: `inner_repeats=256`, `per_call_nanos=14258392.250000`,
    `result_hash=0xf00`, filtered artefact
    `/tmp/hex-profile-runPowMod-16384.json.gz`.
  - Leaf cost after filtering: Lean runtime 55.7%, allocation/free 22.2%,
    GMP big-integer arithmetic 11.7%, HexArith own code and FFI helpers 1.4%,
    other 9.0%.
  - Inclusive ranking: all retained samples run under the registered
    `Hex.ArithBench.runPowMod` target. The dominant library path is
    `HexArith.powModWordOdd` / `HexArith.powMontBitsGo`, with `Hex.redc`
    at 68.3% inclusive, `lean_hex_uint64_add_carry` at 32.5%, and
    `lean_hex_uint64_mul_full` at 24.4%. The GMP self-time comes from Nat
    bit/exponent manipulation inside the public `powMod` path, not from an
    unregistered prep phase. This is attributable to the registered
    `runPowMod` target.
  - Diagnostics:

    ```text
    regions:            2, total timed = 3664.6 ms
    expected samples:   ~3661 on bench thread
    retained samples:   3661 on bench thread (7 rejected outside windows)
    other-thread noise: 2 samples on non-bench threads within timed windows (informational)
    spawn_anchor_wall_ns=1780141028014847000
    spawn_anchor_mono_ns=329061912648208
    sidecar_mono_anchor_ns=329062170920958
    samply_meta_start_time_ms=1780141028020.8098
    ```

- `bounded-word-extgcd`
  - Command: `scripts/profile/run_profile.sh ./.lake/build/bin/hexarith_bench Hex.ArithBench.runIntExtGcdShapes 24576 5000000000`
  - Child row: `inner_repeats=1`, `per_call_nanos=3347414250.000000`,
    `result_hash=0xbc822323529dd715`, filtered artefact
    `/tmp/hex-profile-runIntExtGcdShapes-24576.json.gz`.
  - Leaf cost after filtering: Lean runtime 72.8%, allocation/free 15.9%,
    GMP big-integer arithmetic 6.5%, HexArith own code and FFI helpers 1.6%,
    other 3.3%.
  - Inclusive ranking: all retained samples run under the registered
    `Hex.ArithBench.runIntExtGcdShapes` target. The dominant library path is
    the benchmark's `intExtGcdShapes` fold, with `lean_hex_mpz_gcdext` and
    `lean_int_extgcd_fallback` both at 82.6% inclusive. The largest leaf
    entries are Lean scalar/Int conversion and boxing around the GMP call.
    This is attributable to the registered `runIntExtGcdShapes` target.
  - Diagnostics:

    ```text
    regions:            1, total timed = 3347.4 ms
    expected samples:   ~3344 on bench thread
    retained samples:   3344 on bench thread (8 rejected outside windows)
    other-thread noise: 2 samples on non-bench threads within timed windows (informational)
    spawn_anchor_wall_ns=1780141036126763000
    spawn_anchor_mono_ns=329070024635333
    sidecar_mono_anchor_ns=329070251752625
    samply_meta_start_time_ms=1780141036132.917
    ```

The dominant inclusive costs all map to registered `HexArith/Bench.lean`
targets. No unattributed or suspicious dominant cost was observed.

## Concerns
