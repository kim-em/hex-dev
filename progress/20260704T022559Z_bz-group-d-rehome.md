# BZ SPEC Group D re-home onto the cost-based hybrid

## Accomplished

Re-homed the stale Group D leaf-performance section of
`HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md` onto the current
cost-based hybrid vocabulary. Group D still described D1/D2 against the
defunct linear combinator `factorFast -> factorSlowModular -> factorSlowTrial`
and old theorem names, contradicting the SPEC's own timeless design section
(lines 30-424) and line 426-428, which already say "Group D obligation D1
below" is about `factorLattice`.

Changes (all in the one SPEC file):

- D1 re-stated as the CLD lattice tier's completeness:
  `toMonicPrimeData? (normalizeForFactor f).squareFreeCore != none ->
  factorLattice f != none`, cap `factorFastPrecisionCap f` (core-keyed), not
  `bhksBound f`. Final theorem renamed `factorLattice_ne_none_of_goodPrime`.
- D2's dispatch reasoning updated to the cost-based hybrid: `factorTrial`
  reached only when no admissible hot-path prime exists; given a good prime,
  D1 + classical completeness resolve in a modular tier.
- Two coupled cross-references fixed (`factorSlowTrial` -> `factorTrial`;
  `bhksBound` described as the BHKS component of `factorFastPrecisionCap`).
- BHKS math pathway (resultant/Hadamard, Lemma 3.2, Theorem 5.2, primorial
  bound) preserved verbatim; only names/combinator vocabulary changed.

Verified against code: `factorHybridFactors` (Basic.lean:10849) dispatches
classical -> lattice -> trial via `factorClassicalFactorsWithBound` /
`factorLatticeFactorsWithBound f (factorFastPrecisionCap f)` /
`factorSlowTrialFactorsWithBound`; `factor = factorHybrid` (Basic.lean:11155).

Matches the live re-homing in issues #8369 (D1 -> factorLattice totality) and
#8370 (D2 -> hybrid backstop-unreachability), which stay open.

Also reconciled the Groups A/B/C correctness narrative and the Historical
note with the current hybrid (second commit):

- Historical note (was lines 40-46): it described the pre-hybrid impl as
  "current" (lattice-first precision-cap dispatch named factorFast /
  factorSlowModular). Rewritten as an Implementation note: `factor =
  factorHybrid` (classical-first / lattice-on-decline / trial backstop),
  with factorFast/factorSlowModular noted as the surviving proof-facing
  defs behind Group A/B.
- Naming note (Proof obligations preamble): corrected the false equations
  "`factorSlow` is `factorClassical`" and "`factorFast` is `factorLattice`".
  Confirmed in code they are distinct defs: `factorFast` (Basic.lean:10488)
  is the CLD fast core without the cert arm; `factorLattice` (10727) adds
  the #8395 all-ones certifying arm; `factorClassical` (9811) is the
  budgeted size-ordered tier, distinct from the exhaustive `factorSlowModular`
  (9760). Re-stated with abstract `factorSlow`/`factorFast` names mapped to
  the concrete tier family.
- C1 sketch: was `factor = (factorFastWithBound).getD (factorSlowWithBound)`;
  now `factor = factorHybrid` three-branch case analysis, matching the
  bridge headline `factor_headline` (FactorSoundness.lean:205) assembled via
  `factorHybridFactors_factor_irreducible`.
- Precision-schedule termination bullet + cap rationale: `factorFast`/
  `factorSlow` two-path fallback -> CLD tier / `factorSlowTrial` backstop;
  HO-4 -> D1.

## Current frontier

The BZ SPEC's factor-path vocabulary (dispatch, tiers, Groups A-D, naming
note, Historical note) is now uniformly the cost-based hybrid.

## Next step

Out of scope, flagged for a possible follow-up: (1) the code docstring on
`factor` (Basic.lean:11144) still describes the old three-tier
`factorFast -> factorSlowModular -> factorSlowTrial` combinator; (2) the
SPEC's "Cost-based hybrid dispatch" pseudocode (~351-364) shows a
`dispatchTier` cost estimate, whereas the impl is classical-first-then-
lattice (no cost estimate). Both are separate logical units.

## Blockers

None.
