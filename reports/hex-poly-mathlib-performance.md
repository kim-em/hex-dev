# HexPolyMathlib Performance Report

## Bench Targets

- `HexPolyMathlib.PolyBench.runToPolynomialChecksum`: `n`
- `HexPolyMathlib.PolyBench.runOfPolynomialChecksum`: `n`
- `HexPolyMathlib.PolyBench.runRoundTripChecksum`: `n`
- `HexPolyMathlib.PolyBench.runGcdBridgeChecksum`: `n * n`
- `HexPolyMathlib.PolyBench.runXGcdBridgeChecksum`: `n * n`

## Verdicts

Scientific verdicts are not yet recorded for this report snapshot.
`lake exe hexpolymathlib_bench list` and
`lake exe hexpolymathlib_bench verify` were run at commit
`bd9162100839336b60ca5180a45eb8cf07f02613`; `verify` passed all 5
registered benchmarks. Those commands verify wiring only and do not satisfy
the Phase-4 scientific verdict requirement.

## Comparator Ratios

`SPEC/Libraries/hex-poly-mathlib.md` does not name an external Phase-4
comparator for `HexPolyMathlib`, so there are no comparator ratios to record
in this snapshot.

## Profile

Profile coverage is not yet recorded for the
`HexPolyMathlib.phase4.input_families` entries in `libraries.yml`:

- `dense-to-mathlib-conversion`
- `mathlib-to-dense-conversion`
- `bridge-round-trip`
- `euclidean-bridge`

#2730 tracks the representative profile runs, leaf-cost
categorisation, inclusive-cost ranking, attribution review, and scientific
benchmark verdicts required before `HexPolyMathlib` can return to
`done_through: 4`.

## Concerns

- #2730: Re-promote `HexPolyMathlib` Phase 4 with traceable scientific
  verdicts, profile coverage, and an empty final Concerns section.
