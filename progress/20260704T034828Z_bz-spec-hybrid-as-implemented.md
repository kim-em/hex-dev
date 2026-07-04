# BZ SPEC: hybrid as implemented, bounded combinator dropped

## Accomplished

Authored the SPEC PR for the BZ factor-path cleanup (plan reviewed by a
Codex second opinion; decisions: SPEC-to-code on dispatch, delete
factorWithBound rather than re-shape). All changes in
HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md:

- Dispatch section retitled "Hybrid dispatch: classical-first with
  budgeted decline"; pseudocode replaced with the implemented shape
  (classical first, product-reconstruction acceptance guard per tier,
  lattice on decline, factorTrial backstop) mirroring
  factorHybridFactors (Basic.lean:10849). The never-implemented
  `dispatchTier` cost estimator and the near-threshold prime-retry
  clause are gone; the cost control is documented as the classical
  tier's level-aware subset budget (#8537).
- Intro paragraph and front-matter dispatch description aligned
  (classical at defaultFactorCoeffBound, lattice at its own cap).
- C2: dropped `factor_product_of_bound` (never implemented); product
  preservation is headline clause 1 + the acceptance guard.
- Implementation note: `factor` is the only public combinator;
  `factorFast`, `factorSlowModular`, `factorWithBound` marked legacy,
  scheduled for deletion via directives (target state).
- Groups A/B naming note recast: historical names in obligation bodies,
  concrete carriers factorClassical+factorTrial (A) and factorLattice
  (B, realized by factorLatticeFactorsWithBound_factor_irreducible).
- De-naming: `factorFastPrecisionCap` / `factorSlowTrial` /
  `factorHybrid` def names removed from SPEC prose (role names instead)
  so the upcoming renames don't re-stale it.
- Cross-system sweep list: dropped `factorFast` / `hex-fast`.

## Current frontier

SPEC PR ready. Next: file the seven implementation directives
(A: delete bounded combinator surface; B: retire factorFast;
C1: prune Mathlib exhaustive-core proof clusters; C2: retire
factorSlowModular; D: rename tiers/lattice internals; E: collapse
factorHybrid* into factor*; F: SPEC final pass), strictly sequential,
per the approved plan at
~/.claude/plans/yes-we-should-certainly-adaptive-dusk.md.

## Next step

File the issues with dependency lines; pod workers execute
A -> B -> C1 -> C2 -> D -> E -> F.

## Blockers

None.
