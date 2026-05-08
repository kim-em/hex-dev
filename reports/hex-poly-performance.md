# HexPoly Performance Report

## Bench Targets

- `Hex.PolyBench.runAddChecksum`: `n`
- `Hex.PolyBench.runSubChecksum`: `n`
- `Hex.PolyBench.runMulChecksum`: `n * n`
- `Hex.PolyBench.runEval`: `n`
- `Hex.PolyBench.runComposeChecksum`: `n * n * n * n`
- `Hex.PolyBench.runDerivativeChecksum`: `n`
- `Hex.PolyBench.runDivModChecksum`: `n * n`
- `Hex.PolyBench.runDivChecksum`: `n * n`
- `Hex.PolyBench.runModChecksum`: `n * n`
- `Hex.PolyBench.runModByMonicChecksum`: `n * n`
- `Hex.PolyBench.runGcdChecksum`: `n * n`
- `Hex.PolyBench.runXGcdChecksum`: `n * n`
- `Hex.PolyBench.runContent`: `n`
- `Hex.PolyBench.runPrimitivePartChecksum`: `n`
- `Hex.PolyBench.runPolyCRTChecksum`: `n * n`

## Verdicts

Scientific verdicts are not yet recorded for this report snapshot.
`lake exe hexpoly_bench list` and `lake exe hexpoly_bench verify` were run
at commit `7e7b45b0ef37e68c30e0b1481661c641a798b4d1`; `verify` passed all
15 registered benchmarks. Those commands verify wiring only and do not satisfy
the Phase-4 scientific verdict requirement.

## Comparator Ratios

`SPEC/Libraries/hex-poly.md` does not name an external Phase-4 comparator for
`HexPoly`, so there are no comparator ratios to record in this snapshot.

## Profile

Profile coverage is not yet recorded for the `HexPoly.phase4.input_families`
entries in `libraries.yml`:

- `dense-int-arithmetic`
- `field-euclidean`
- `integer-content`
- `polynomial-crt`

Issue #2718 tracks the representative profile runs, leaf-cost
categorisation, inclusive-cost ranking, and attribution review required before
`HexPoly` can return to `done_through: 4`.

## Concerns

- #2718: Re-promote `HexPoly` Phase 4 with traceable scientific verdicts,
  profile coverage, and an empty final Concerns section.
