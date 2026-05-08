# HexGfqRing Performance Report

## Bench Targets

- `Hex.GFqRingBench.runReduceModChecksum`: `n * n`
- `Hex.GFqRingBench.runOfPolyReprChecksum`: `n * n`
- `Hex.GFqRingBench.runAddChecksum`: `n`
- `Hex.GFqRingBench.runMulChecksum`: `n * n`
- `Hex.GFqRingBench.runNegSubChecksum`: `n`
- `Hex.GFqRingBench.runPowChecksum`: `n * n * Nat.log2 (n + 1)`
- `Hex.GFqRingBench.runNsmulNatCastChecksum`: `n * Nat.log2 (n + 1)`

## Verdicts

Scientific verdicts are not yet recorded for this report snapshot.
`lake exe hexgfqring_bench list` and `lake exe hexgfqring_bench verify` were
run at commit `b26b681156f25e7ba7002aac9d574dbd45ecd2bb`; `list` built the
executable and listed all seven registered benchmarks above, and `verify`
passed all seven smoke checks. Those commands verify wiring only and do not
satisfy the Phase-4 scientific verdict requirement.

## Comparator Ratios

`SPEC/Libraries/hex-gfq-ring.md` does not name an external Phase-4 performance
comparator for `HexGfqRing`, so there are no comparator ratios to record in
this snapshot.

## Profile

Profile coverage is not yet recorded for the
`HexGfqRing.phase4.input_families` entries in `libraries.yml`:

- `dense-reduction`
- `quotient-arithmetic`

Issue #2734 tracks representative profile runs,
leaf-cost categorisation, inclusive-cost ranking, and attribution review before
`HexGfqRing` can return to `done_through: 4`.

## Concerns

- #2734: Restore `HexGfqRing` Phase 4 with traceable scientific verdicts,
  profile coverage, and an empty final Concerns section.
