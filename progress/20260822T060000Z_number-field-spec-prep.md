# NumberField cluster SPEC preparation

## Accomplished

- Specified the `Hex.AlgebraicPoly.Common` public surface in the
  hex-number-field SPEC (new §Common-field construction: the bounded
  primitive-element search, checked canonical arithmetic, trace
  pairing, coordinate recovery, and presentation assembly the tower
  libraries consume), replacing the stale "internal" wording.
- Reconciled both stale file-organisation tables: the
  hex-number-field-mathlib SPEC now lists all 16 modules (noting the
  four that verify the Common surface), and the tower SPEC lists all
  11 (Data/RawArithmetic/RawEvaluation/FactorRaw declared, Embed.lean
  recorded as the compiled extension-regression module, with
  Extension/ofQAdjoin homed in Basic.lean).
- Recorded the tower's sealed-type convention as a pointer to the
  hex-number-field SPEC's existing opaque-as-boundary paragraph.
- Resolved the audit's dead-code question by specifying rather than
  deleting: `AlgebraicPoly.coeff`, `size`, `beq`, and the `BEq`
  instance are exercised by the module's compiled regressions and are
  now in the SPEC's core-types block, tied to the existing
  Boolean-equality doctrine.
- Reworded the QAdjoin regression comment so casual trust-surface
  greps stay quiet (the mechanical check strips comments and already
  passed).

## Current frontier

- The cluster's SPECs now match the source, clearing the way for the
  Phase 1/2 attestations once the BZ edge lands (wave task C14).

## Next step

- C12: the three missing TowerMathlib SPEC declarations
  (dim/finrank via toField, the Grind.Field package, the public
  Extension.embed homomorphism statement).

## Blockers

- None.
