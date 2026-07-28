# Number-field tower Mathlib contract repair

## Accomplished

- Incorporated the independent review of `HexNumberFieldTowerMathlib`.
- Required `LevelsValid lower` for the one-level resultant correspondence and
  made both Mathlib resultant degree parameters explicit.
- Restricted the executable irreducibility equivalence to monic polynomials.
- Required factor irreducibility at the factor-selection boundary instead of
  claiming it from multiplicity and vanishing alone.
- Replaced the vacuous absolute-root relation theorem with a semantic
  interpretation of the stored relative polynomial over its lower tower.
- Proved the direct `eval?` mapping lemma and rebuilt the four affected
  companion modules successfully.

## Current frontier

- The documentation and resultant-testing pull requests are stacked above
  this branch and need rebasing after this repair is pushed.
- Independent reviews of those two pull requests are still running in
  background sessions.

## Next step

- Push this contract repair, restack the downstream branches, then continue
  with the next testing milestone while monitoring the outstanding reviews.

## Blockers

- None.
