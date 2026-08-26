# BZ factor-path cleanup: final consistency pass (F, #8584)

## Accomplished
Closed out the BZ factor-path cleanup (issues #8578-#8584). All six code
issues (A-E) are merged. This final pass:
- Confirmed the SPEC is fully free of legacy vocabulary and uses the
  timeless names (factorTrial / factorClassical / factorLattice); no SPEC
  change needed.
- Renamed the two D-rename stragglers that D's substring pass missed
  (they contain factorFastCore but not the exact renamed tokens):
  factorFastCoreGuardPrimeData -> bhksRecoveryGuardPrimeData (private test
  fixture + its 3 #guards, Basic.lean), and the DEV.md architecture note
  (factorFastCore* -> bhks* machinery).
- Refreshed the two open lattice-totality directive bodies #8369 and #8370
  to the post-cleanup names (factorTrial, latticePrecisionCap,
  bhksRecoveryCoreWithBound, factorFactors; #8369 substrate pointer moved
  from the deleted factorFast_ne_none_of_core_recovery_on_schedule to the
  surviving bhksRecoveryCoreWithBound_ne_none_of_recovery_on_schedule;
  #8370 target theorem factorHybrid_not_slowTrial_of_good_prime ->
  factor_not_trial_of_good_prime), and marked their now-done SPEC-update
  instructions as complete.

End state: git grep over *.lean/*.py/DEV.md/SPEC (history exempt) for
factorWithBound|factorSlowModular|factorFast|factorSlowTrial|factorHybrid|
exhaustiveCoreFactorsWithBound|dispatchTier returns nothing. Public surface
is factor / factorTraced / factorFactors / factorClassical / factorLattice
/ factorTrial.

## Current frontier
The BZ factor path is now the clean hybrid: one public combinator, three
tiers, no legacy indirection or dead proof surface.

## Next step
None for this cleanup. The lattice-totality leaf theorems (#8369/#8370)
remain open as future non-blocking work, now correctly named.

## Blockers
None.
