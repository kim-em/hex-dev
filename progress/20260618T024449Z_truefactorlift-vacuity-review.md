# Progress — TrueFactorLift vacuity adversarial review

## Accomplished

Reviewed the upstream `origin/main` declarations for `BHKS.supportProduct`,
`TrueFactorLift`, `TrueFactorLiftSemantics`, `RecoveredLift`,
`tightColumnBound_of_lift`, and the `PartitionRefinement` fast-core consumer.
The working tree is behind upstream, so the review used `git show origin/main`
without changing files.

The review found no strong refutation of the vacuity claim for irreducible
integer factors with recombination supports. `supportProduct` is a raw
`Array.polyProduct` over `ZPoly`; `TrueFactorLift.support_product_eq` asserts raw
equality to `factor`; and the tight-column proof uses that equality to rewrite
the represented factor as a product of the selected lifted factors. Upstream has
also introduced `RecoveredLift` specifically to record only the centered/dilated
modular recovery equality, which supports the diagnosis that raw equality is too
strong for recovery-side recombination data.

## Current frontier

The remaining engineering question is how to retarget the tight CLD column-bound
line from `TrueFactorLift` to a recovered/modular aggregate interface without
assuming raw `supportProduct = factor`.

## Next step

Define the intended replacement theorem against `RecoveredLift` or a narrower
mod-`p^a` aggregate package, and re-check which parts of
`tightColumnBound_of_lift` genuinely need raw divisibility of each selected
lifted factor versus only the aggregate congruence/carry facts.

## Blockers

No code changes were made beyond this progress note. I did not run `lake build`
because the task was an adversarial source review and the relevant declarations
are only present in upstream commits, not this checkout.
