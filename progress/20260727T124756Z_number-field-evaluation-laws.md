# Number-field evaluation laws

## Accomplished

- Proved that `QAdjoin.reduceCoeffs` preserves evaluation at the selected
  complex root, using the executable division reconstruction identity and the
  certified root equation.
- Proved that fixed-presentation evaluation preserves addition,
  multiplication, zero, one, negation, subtraction, and rational scalar
  multiplication.
- Added `HexPolyMathlib.toPolynomial_scale`, the reusable bridge identifying
  executable coefficient scaling with multiplication by a constant Mathlib
  polynomial.
- Built `HexNumberFieldMathlib`, `HexNumberFieldTowerMathlib`, and `HexManual`
  together successfully.
- Kept the independent Claude review monitor running while continuing proof
  work; its authentication remains expired.

## Current frontier

- `QAdjoin.map_inv` and the resulting division law remain the next semantic
  laws for the fixed-presentation field interface.
- The Resultant pseudo-division reconstruction proof now has an exact local
  decomposition into fold/push indexing, powers, active recurrence,
  convolution, and high-coefficient reindexing lemmas.

## Next step

- Publish this fixed-evaluation milestone as a stacked draft PR, then begin the
  pseudo-division helper layer without waiting for review completion.
- Continue reconciling and merging the bottom of the existing PR stack as CI
  permits.

## Blockers

- The Claude second-opinion CLI cannot authenticate because its OAuth session
  is expired; the retrying monitor remains active.
- No implementation blocker for the next proof stage.
