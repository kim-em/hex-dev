# Tower flattening focused re-review

## Accomplished

- Incorporated the focused independent re-review of the recovery-collision
  repair.
- Replaced the nested one-element search call with a single-shift
  `candidateAt?`; `searchRecoveredAux` now owns the enumeration and begins at
  the first nonzero signed shift.
- Corrected the collision argument: degree and recovery failures are one set
  of at most `deg(theta) * (deg(alpha) - 1) ≤ choose(d, 2)` shifts, so restored
  the sharp `choose(d, 2) + 1` bound instead of presenting two overlapping
  failure classes as additive.
- Clarified that checked canonicalization completeness is discharged by the
  Mathlib companion rather than hidden inside collision slack.
- Reconciled all stale two-round-trip documentation and explained the
  irreducibility/dimension squeeze that makes the returned inverse
  multiplicative.
- Fixed the fourth-root regression to multiply the two primitive-side
  coordinates, making its multiplicativity check non-vacuous.
- Built `HexNumberFieldTower.Flatten` and passed `git diff --check`.

## Current frontier

The reviewed algorithm and its SPEC now agree on retry behavior, the finite
bound, and the executable certificate. The remaining requested regression is a
concrete case where shift `+1` has full degree but non-linear recovery and the
search succeeds at `-1`; it belongs in the conformance descendant.

## Next step

Publish this refinement, rebase the conformance branch, add the cyclotomic
retry regression there, and rerun its exact fixture and PARI checks.

## Blockers

None.
