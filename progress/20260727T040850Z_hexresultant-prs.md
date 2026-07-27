# HexResultant exact division and Brown PRS

## Accomplished

- Generalized HexPoly's exact-multiple `divMod` theorem from positive-degree
  divisors to every nonzero divisor, preserving its existing callers and
  enabling exact division by nonunit constants.
- Implemented `ExactDivLaws`, deterministic `exactDiv`, executable natural
  powers, Brown's `divExp`, and kernel/runtime `divScalar` twins with a proved
  `@[csimp]` correspondence.
- Proved exact-division cancellation, no-zero-product, coefficientwise scalar
  reconstruction, and recursive `ExactDivLaws (DensePoly R)`; supplied `Int`
  and generic field instances.
- Implemented the fuel-total Brown PRS state, ordered wrapper, nonzero-only
  `subresultantChain`, both exact quotient sites, corrected terminal scale,
  and stable zero/reversed-input behavior.
- Added compiled regressions for equal-degree signs, common factors, two
  defective drops, nonunit exact quotients, nested `DensePoly Int`
  coefficients, and zero/reversed inputs.
- Built `HexPoly`, `HexPolyZ`, and the complete `HexResultant` umbrella; ran
  DAG, copyright, line-count, diff, and forbidden-form checks successfully.

## Current frontier

The executable exact-division and chain data paths are complete. Five
propositional Phase 1 obligations remain explicit: the two pseudo-division
proofs and the chain nonzero, strict-descent, and size-bound proofs. There are
no data-level sorries.

PR #8881 is still building and its independent Claude review is still running
asynchronous to this implementation.

## Next step

Propagate the newly required Mathlib-free `powNat` helper into the contract PR,
address its review findings, then publish this implementation milestone and
continue directly to executable `resultant` and `disc`.

## Blockers

No implementation blocker. The contract's displayed `divExp` signature must
drop generic `HPow`: nested dense-polynomial coefficients deliberately have no
global power instance, so Brown uses the new explicit `powNat` recurrence.
