# Number-field lazy arithmetic totality

## Accomplished

- Proved multiplication-eliminant nonzeroness and root transport, including
  removal of the spurious maximal `X` factor for nonzero products.
- Proved reciprocal coefficient reversal, nonzeroness, root transport, and the
  reciprocal Cauchy lower bound for nonzero selected roots.
- Proved explicit multiplication- and inversion-ball guard bounds, including
  successful separation of reciprocal balls from zero.
- Completed checked soundness, bounded-search totality, and total complex
  semantics for multiplication, inversion, and division. Added axiom guards for
  the completed addition, multiplication, inversion, and division headlines.
- Updated the NumberField specs and manual with the implemented guard bounds
  and totality contracts. Confirmed the superseded
  `SPEC/hex-number-field-expansion-plan.md` had already been deleted on the
  current branch ancestry.
- Verified `HexNumberFieldMathlib`, `HexManual`, `HexConformance`, the
  NumberField fixture emitter, and all nine NumberField benchmark checks.
- Completed an independent pre-merge review and corrected its one concrete
  documentation finding: addition has two bits of operation-ball slack, while
  multiplication and inversion have four.
- Rebased onto current `main`, updated proof scripts for the new DensePoly and
  elaborator behavior, and passed the full 9,907-target build. Recorded the
  exact proof-only `HexPolyZ/Decomposition.lean` blob transition so its two new
  theorems do not falsely invalidate factorization runtime measurements.

## Current frontier

The factorization-lazy addition, multiplication, inversion, and division
pipelines now have `sorry`-free Mathlib soundness and totality proofs. The
cohesive arithmetic milestone is in PR #9135 with auto-merge armed.

## Next step

Pass PR #9135 CI and merge it, then audit the Resultant, NumberField, and
NumberFieldTower specs for the next remaining proof stage.

## Blockers

None.
