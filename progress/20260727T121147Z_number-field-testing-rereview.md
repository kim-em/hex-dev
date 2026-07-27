# NumberField testing follow-up review repair

## Accomplished

- Strengthened lazy add/sub conformance assertions so they distinguish the
  intended selected conjugates rather than checking only a shared minimal
  polynomial and coarse sign.
- Extended benchmark root checksums with the exact dyadic real centre,
  imaginary centre, and precision.  The root-set checksum now includes the
  same selected-root data, and all affected expected hashes were regenerated.
- Replaced the closed `runIsolateAdd` expression with a runtime `IO.Ref` input
  carrying the precomputed simple-root proof and separation depth, so the timed
  body measures only isolation and hashes every resulting square.
- Extended arithmetic fixtures with selected input and result boxes.  The PARI
  oracle now selects the operand roots independently and checks the computed
  add, subtract, multiply, or inverse value against Lean's result box in
  addition to checking the FLINT-derived result polynomial.
- Added the reciprocal degree-drop fixture for the selected root `2` of
  `X^2 - 2X`, plus checked/total Lean assertions and a total division-by-zero
  assertion.  The fixture stream now has 51 records and 11 result cases.
- Tightened the degree-ten fixed-field benchmark caps to the SPEC's 100 ms
  budget.
- Passed the NumberField bench, conformance, and emitter builds; all eight
  benchmark hashes pass verification; fixture regeneration is deterministic;
  the full `lake build`, Python syntax check, diff hygiene, and an independent
  quadratic-root/result-box smoke check pass.

## Current frontier

The follow-up review's merge-facing root-selection and constant-folding
findings are repaired, together with the adjacent reciprocal degree-drop case.
Broader per-operation case-count and parametric timing ladders remain coverage
debt rather than defects in the checked paths.

## Next step

Commit and publish this repair, rebase NumberFieldTowerTesting onto it, rerun
the tower verification after restacking, and retry the tower follow-up reviewer
without waiting on it before continuing the stack.

## Blockers

The local Python environment lacks `python-flint` and `cypari2`, so the external
oracle reports its designed skip rather than executing.  CI installs both; the
emitter/oracle protocol was checked locally through deterministic regeneration,
Python compilation, and an independent analytic smoke check of every emitted
arithmetic box.
