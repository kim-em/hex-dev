# Issue #8521 — core-aware BHKS precision cap

## Accomplished

Fixed the executable precision reconciliation for the fast/lattice BZ tiers.
`factorFastPrecisionCap f` now computes the BHKS separation side from
`(normalizeForFactor f).squareFreeCore` while preserving the original input's
`defaultFactorCoeffBound f` for coefficient reconstruction.  Updated
`bhksBound_le_factorFastPrecisionCap` to expose the core bound, and added
`coreBhksPrecision_lt_factorFastPrecisionCap`, proving the exact
`toMonicLiftData` precision inequality needed by the #8521 reduction.

Verification:

- `lake build HexBerlekampZassenhaus` green.
- `lake build HexBerlekampZassenhausMathlib` green, with the pre-existing
  lattice theorem `sorry` still reported in `IntReductionMod.lean`.
- `lake build HexConformance` green.
- `python3 scripts/oracle/bz_flint.py --check` reports 100 cases, 0 failures.

## Current frontier

The executable soundness gap identified by #8521 is fixed.  This checkout does
not contain the partial `factorLatticeFactorsWithBound_factor_irreducible` proof
body described by the issue; the theorem is still a top-level `sorry`, so the
new precision lemma is available but not yet wired into a full lattice
irreducibility proof.

## Next step

Open the PR with the core-aware cap and precision lemma.  A follow-up proof pass
can use `coreBhksPrecision_lt_factorFastPrecisionCap` at the former `hprec`
site once the lattice theorem proof body is present.

## Blockers

No implementation blocker for the executable fix.  Full discharge of the
lattice irreducibility theorem remains blocked on the broader #8417 proof body
in this worktree.
