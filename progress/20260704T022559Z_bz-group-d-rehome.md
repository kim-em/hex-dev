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

## Current frontier

Group D is now internally consistent and consistent with the timeless
design section.

## Next step

Separate follow-up (NOT in this PR, deliberately out of scope): the Groups
A/B/C conditional-correctness narrative and the "Historical note" (lines
41-46, 551-573, 597-628) still use `factorFast`/`factorSlowModular` as the
implementation-naming convention. The code has since split `factorFast`
(proof-facing standalone tier) from `factorLattice` (production), so
line 573 "`factorFast` is the lattice tier `factorLattice`" and the
Historical note's "dispatches by a precision cap" are themselves drifting.
Reconciling them touches the correctness-side SPEC and needs the exact
factorFast-vs-factorLattice relation confirmed in code first.

## Blockers

None.
