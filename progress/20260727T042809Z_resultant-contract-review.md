# HexResultant contract review repair

## Accomplished

- Verified the independent review's positive-characteristic counterexample:
  a derivative can lose its nominal `n - 1` term, so the default-degree
  resultant alone does not compute Mathlib's standard discriminant.
- Repaired the contract by promoting the derivative resultant to formal degree
  `n - 1` with the exact leading-coefficient gap power before division.
- Pinned equal-degree caller order and documented the runtime recurrence twins,
  fuel exhaustion, and unreachable zero-next branch.

## Current frontier

The contract now states a generically valid discriminant formula. The
executable value branch and regressions still need the same correction on the
stacked implementation branch.

## Next step

Propagate the contract commit through the PR stack, implement the formal-degree
correction, and verify both the reported `ZMod 5` counterexample and integer
higher-degree cases.

## Blockers

None.
