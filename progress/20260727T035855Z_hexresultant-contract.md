# HexResultant exact-division and Brown recurrence contract

## Accomplished

- Replaced the underspecified quotient premise with a Mathlib-free
  `ExactDivLaws` contract over the existing `Div` operation and deterministic
  zero-denominator wrappers.
- Pinned Brown's ordered subresultant state, both exact divisors, every sign
  and exponent, defective degree drops, the corrected terminal scalar, and the
  nonzero-only chain convention from the verified AFP recurrence.
- Corrected the tight chain and pseudo-division bounds and specified all zero,
  constant, reversed-degree, and discriminant edge cases.
- Repaired the companion SPEC's displayed Mathlib declarations: qualified
  correspondence names, argument order, explicit formal degrees, bivariate
  specialization/evaluation, complex `aeval`, root multiset notation, and
  discriminant assumptions.
- Elaborated the repaired declarations in a temporary module against the
  pinned Lean/Mathlib revisions, then removed that check module.
- Rebuilt `HexResultant` and reran the DAG and diff checks successfully.

## Current frontier

The contract diff is ready for independent review and publication. PR #8880
merged green while this work continued, so this branch can now be replayed
directly onto its squash merge.

## Next step

Start the Claude contract review as a background monitor, publish the contract
milestone, and immediately begin the exact-division wrappers, instances, and
Brown worker on a stacked implementation branch.

## Blockers

No blocker. The recursive `ExactDivLaws (DensePoly R)` instance will require
generalizing HexPoly's exact-multiple division theorem from positive-degree to
arbitrary nonzero divisors; its underlying array proof already supports that
case.
