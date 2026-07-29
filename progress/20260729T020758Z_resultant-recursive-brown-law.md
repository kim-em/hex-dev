# Resultant recursive Brown law

## Accomplished

- Proved the signed pseudo-remainder endpoint and the cross-multiplied
  subresultant-family descent law, including defective degree drops.
- Built the integral `BrownInv` initialization, scale, factor, and preservation
  proofs and used fuel induction to discharge `subresultantOrdered_brownLaw`
  without `sorry`.
- Added shared power, nonzero, scalar-cancellation, and alternating-sign lemmas;
  removed duplicate local proofs and the umbrella-only sign bridge.
- Added theorem-level conformance examples and updated the Resultant SPEC and
  manual to describe the base-ring proof.
- Completed a fresh independent mathematical review and ran the full 9,573-job
  `lake build` successfully.

## Current frontier

The computational Resultant library now proves the recursive Brown exactness
and nonzero obligations for every ordered nonzero input pair. The next
Resultant obligations are in the Mathlib correspondence layer.

## Next step

Open one ready PR for this milestone, keep it as the only active Resultant PR,
and merge it before starting the Resultant Mathlib work.

## Blockers

None.
