# BZ factor-path cleanup part 5 — rename tiers and lattice internals to SPEC names (#8582)

## Accomplished
- Pure mechanical, behaviour-neutral rename sweep aligning code identifiers
  with the SPEC's timeless tier vocabulary. Five renames applied as
  whole-identifier substring replacements across all non-history files:
  - `factorSlowTrial` → `factorTrial` (cascades to `factorTrialWithBound`,
    `factorTrialFactorsWithBound`, and every embedding lemma name)
  - `factorFastPrecisionCap` → `latticePrecisionCap`
  - `factorFastCoreWithBound` → `bhksRecoveryCoreWithBound`
  - `factorFastCoreLoop` → `bhksRecoveryLoop`
  - `fastCoreFloor` → `bhksRecoveryFloor` (cascades to `bhksRecoveryFloorGate`)
- Files touched: HexBerlekampZassenhaus/{Basic,CrossCheck}.lean,
  HexBerlekampZassenhausMathlib/{Basic,IntReductionMod,LatticeTier,
  PartitionRefinement}.lean, bench/HexBench/LatticeSpike.lean,
  bench/HexBerlekampZassenhaus/Bench.lean,
  conformance/HexBerlekampZassenhaus/Conformance.lean, and the
  hex-lean-mathlib-boundary skill doc.
- `git diff --stat`: 321 insertions / 321 deletions (balanced = pure rename).
- SPEC and DEV.md already carried the `factorTrial`/`latticePrecisionCap`
  vocabulary (de-named in #8577), so they needed no changes.

## Current frontier
- Whole-graph `lake build` green (4088 jobs); BZ bench + conformance targets
  built; `hexbz_bench verify` all 16 pass; conformance `#guard` module compiles.
- `git grep` for the five old tokens over *.lean/*.py/*.md (excl.
  progress/reports/status) returns nothing.
- sorry/axiom counts in touched files unchanged (11 == 11).
- No conformance fixture / jsonl / bz-trace-baseline changed; the
  FactorTrace.tier role strings are untouched.

## Next step
- None for this issue; ready to merge. Part 5 of the BZ factor-path cleanup done.

## Blockers
- None.
