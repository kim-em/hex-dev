# HexArith Performance Report

## Bench Targets

- `Hex.ArithBench.runBarrettMulChain`: `n`
- `Hex.ArithBench.runMontgomeryMulChain`: `n`
- `Hex.ArithBench.runPowMod`: `n`
- `Hex.ArithBench.runNatExtGcdShapes`: `n`
- `Hex.ArithBench.runIntExtGcdShapes`: `n`
- `Hex.ArithBench.runUInt64ExtGcdShapes`: `n`

## Verdicts

Scientific run at commit `b161a1b1626f32495ec041d206fe99e8486b55b5` on
`carica` (Apple M2 Ultra, macOS 14.6.1), command:

```sh
lake exe hexarith_bench run Hex.ArithBench.runBarrettMulChain Hex.ArithBench.runMontgomeryMulChain Hex.ArithBench.runPowMod Hex.ArithBench.runNatExtGcdShapes Hex.ArithBench.runIntExtGcdShapes Hex.ArithBench.runUInt64ExtGcdShapes --export-file reports/bench-results/hex-arith-b161a1b1626f.json
```

The run used the deterministic benchmark inputs from `HexArith/Bench.lean`;
random seeds are not involved. Export artefact:
`reports/bench-results/hex-arith-b161a1b1626f.json`.

- `Hex.ArithBench.runBarrettMulChain`: consistent with declared complexity
  (`β=+0.004`, parameters `8192..131072`, hashes include `0x525b`,
  `0xb646`, `0xff01`, `0x1`, `0x10000`).
- `Hex.ArithBench.runMontgomeryMulChain`: consistent with declared complexity
  (`β=+0.002`, parameters `8192..131072`, same modular-chain hashes as
  Barrett on the shared domain).
- `Hex.ArithBench.runPowMod`: consistent with declared complexity
  (`β=+0.069`, parameters `1024..16384`, hash `0xf00`).
- `Hex.ArithBench.runNatExtGcdShapes`: consistent with declared complexity
  (`β=-0.012`, parameters `8192..24576`, hashes include
  `0xb1b59077645662db`).
- `Hex.ArithBench.runIntExtGcdShapes`: consistent with declared complexity
  (`β=-0.003`, parameters `8192..24576`, same normalized-shape hashes as the
  Nat registration on the shared nonnegative input domain).
- `Hex.ArithBench.runUInt64ExtGcdShapes`: consistent with declared complexity
  (`β=+0.034`, parameters `8192..24576`, same normalized-shape hashes as the
  Nat and Int registrations on the shared nonnegative input domain).

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

Profile coverage is not yet recorded for the `HexArith.phase4.input_families`
entries in `libraries.yml`:

- `modular-multiplication-chain`
- `word-powmod`
- `bounded-word-extgcd`

Issue #2752 tracks the representative samply profile runs, leaf-cost
categorisation, inclusive-cost ranking, and attribution review required before
`HexArith` can return to `done_through: 4`.

A local `samply record --save-only` attempt during issue #2716 produced no
sampled stacks for the benchmark child process, so no profile percentages are
claimed in this report snapshot.

## Concerns

- #2752: Record representative Phase-4 profile coverage for the three
  `HexArith.phase4.input_families` entries and clear the attribution review
  before re-promoting `HexArith` to `done_through: 4`.
