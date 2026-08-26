# Prune Mathlib-layer exhaustiveCoreFactorsWithBound proof clusters (#8580)

## Accomplished
Deleted every declaration in the Mathlib layer whose name or statement
mentioned the executable def `exhaustiveCoreFactorsWithBound`, the proof
surface of the retiring `factorSlowModular` exhaustive tier.

- `HexBerlekampZassenhausMathlib/Basic.lean`: 14 named lemmas across three
  clusters (`_mem_of_recombinationSearchMod_*` / `_mem_of_scaledRecombinationSearchMod_some`;
  the `_factor_count_*` / `_factor_irreducible_*` / `_factor_zpolyIrreducible_*` family;
  the `_coverage_of_henselSubsetCorrespondence*` /
  `_factor_zpolyIrreducible_of_henselSubsetCorrespondence*` family). Also
  dropped a stale docstring reference in the surviving
  `factors_irreducible_of_choosePrimeData_of_some`.
- `HexBerlekampZassenhausMathlib/IntReductionMod.lean`: the self-contained
  dead cluster `structure MonicReductionCorrespondence`,
  `monicReductionCorrespondence_of_normalizeForFactor_squareFreeCore`,
  `monicReductionCorrespondence_liftedFactor_facts_of_normalizeForFactor_squareFreeCore`,
  `reassemblyComplete_of_slowSubstrate_bound`, `reassemblyComplete_of_slowSubstrate`.

## Current frontier
`rg exhaustiveCoreFactorsWithBound HexBerlekampZassenhausMathlib/` is empty.
The executable def in `HexBerlekampZassenhaus/Basic.lean` is untouched and
now has zero Mathlib-layer lemmas about it, ready for the follow-up (C2)
deletion.

Kept all generic `recombinationSearchMod*` / `scaledRecombinationSearchMod*`
infrastructure. Kept the private helpers `dvd_acc_foldl_mul_zpoly`,
`mem_dvd_foldl_mul_zpoly`, `factorPower_size_lower_bound` (still consumed by
the live `fastCoreReassemblyComplete_of_coreIrreducible`). No generic
recombination-search lemma was deleted.

## Verification
Whole-graph `lake build` (4088 jobs), Mathlib layer, `hexbz_bench`,
`hexbz_emit_fixtures`, and `HexConformance` all green. Classical / headline /
lattice chain intact. Zero new `sorry` / `axiom`.

## Next step
Follow-up issue C2 deletes the executable `exhaustiveCoreFactorsWithBound`
def and the rest of the `factorSlowModular` tier.

## Blockers
None.
