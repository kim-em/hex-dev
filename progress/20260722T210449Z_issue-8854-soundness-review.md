# issue #8854: adversarial soundness review

## Accomplished

- Checked the guarded and unconditional equality theorem statements and the fallback case split.
- Audited the word-division transport, multiplicative transport, and monic-division uniqueness proof.
- Confirmed the new public proof chain uses only `propext`, `Classical.choice`, and `Quot.sound`, with no
  added `sorry`, `axiom`, `native_decide`, `unsafe`, or `opaque` escape.
- Rebuilt `HexHensel.Quadratic` successfully.
- Found a concrete downstream instance-coherence defect when `HexHensel.Quadratic` and
  `HexModArithMathlib.WordMod` are imported together: the duplicate power and integer-scalar
  instances make `pow_succ` and `Lean.Grind.Ring.neg_zsmul` fail to elaborate against the selected
  notation instances.

## Current frontier

The dispatch and its equality proof appear sound. The remaining review finding is the global
`WordMod` instance diamond between the new Mathlib-free Grind support and the existing Mathlib bridge.

## Next step

Centralize the `WordMod` power/cast/scalar operations as single canonical instances in the
Mathlib-free base module, remove the duplicate Mathlib bridge instances, and rebuild the combined
Mathlib aggregate with small coherence regression examples.

## Blockers

None.
