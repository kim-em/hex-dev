# FactorSoundness plan critical review

## Accomplished

Reviewed the proposed Step 4b-4e plan against the current code around
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_coreLiftDataRecoveryData`,
`cutProjectionHypotheses_of_recoveryData`, `RecoveredAtLiftM1`,
`coreLiftData_subset_congr_monicTarget`, the fast-core success extractors, and
the BHKS coefficient-floor producers.

## Current frontier

The plan's two major risky assumptions are not just proof-engineering gaps:
`hmonic_dvd` is an exact divisibility premise for `monicTarget (factor S)` and
appears not to be produced by the M1/coreLiftData congruence stack, while
`hsep`/`hthr` at `B = defaultFactorCoeffBound f` conflicts with the current
`cldCoeffFloor` acceptance design.

## Next step

Revise the proof route before implementing Step 4. Either change the endpoint to
avoid exact `monicTarget (factor) ∣ monicTarget core`, or supply a different
monic-coordinate witness than `monicTarget (factor)` with exact divisibility and
only congruence to the selected product. Separately, instantiate cut/separation
at the success precision extracted by `factorFastCoreWithBound_some_indicatorCandidates`
or prove a new default-bound-to-floor theorem, which currently looks false in
general.

## Blockers

No code was changed beyond this progress note. No Lean build was run for this
review.
