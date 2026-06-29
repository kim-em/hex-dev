# PartitionRefinement premise check

## Accomplished

Read the cited `PartitionRefinement.lean`, `Basic.lean`, `Recovery.lean`,
`LiftBridge.lean`, and the prior progress note to check whether the refined
plan's proposed source produces the witnesses required by
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_coreLiftDataRecoveryData`.

Confirmed that `ForwardRecoveryInputsCore` / `candidatesOfScaledCenteredLift`
packages aggregate indicator-candidate recovery, not the per-support descent
bundle (`factor`, `cof`, `modPSubset`, `hrepP`, `hfactor_product`,
`hmonic_dvd`, `hsupp`) required by the M1 endpoint.

## Current frontier

`factorFastCore_irreducible_of_liftedTrueSupport` still needs a clean source for
per-support `coreLiftData`/M1 witnesses. The existing to-monic descent produces a
monic correspondent for `(toMonic core).monic` plus a dilation equality back to
the original factor; it does not directly produce the endpoint's
`monicTarget (factor S)` representation over `choosePrimeData?`/`coreLiftData`.

## Next step

Build a small core/M1 per-support descent package, or weaken/refactor the 1020
endpoint to consume the nearest existing package if an equivalent bridge is
proved. The likely missing lemma should produce the `monicTarget` representation
and subset identity for `coreLiftData` true supports directly, then feed
`coreLiftData_subset_congr_monicTarget`.

## Blockers

No proof files were edited. The identified gap is mathematical/API-level: the
current recovery candidate-fold constructors are not a substitute for
per-support descent data.
