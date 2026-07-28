# Number-tower scalar evaluation

## Accomplished

- Exposed the exact coordinate array produced by rational scalar
  multiplication.
- Proved coordinatewise rational scaling commutes with mixed-radix block
  extraction and direct complex tower denotation.
- Retired the public `map_smul` placeholder.
- Built `HexNumberFieldTowerMathlib` and `HexManual` and passed the DAG,
  Phase-4, copyright, diff, and banned-declaration checks.

## Current frontier

- `map_inv` is the only remaining primitive arithmetic correspondence
  placeholder in `HexNumberFieldTowerMathlib.Arithmetic`.
- Its executable xgcd proof needs a semantic division/Bezout bridge for
  canonical lower-tower coefficients; the existing later factor bridge imports
  arithmetic and therefore cannot be imported back without a cycle.

## Next step

- Open this milestone as a draft PR stacked on `NumberFieldTowerRawMul`.
- Isolate the minimal canonical-coefficient division invariant below the factor
  layer, then use it to prove the xgcd result is the selected inverse.

## Blockers

- Claude second-opinion capacity remains unavailable until the provider quota
  reset; implementation and GitHub CI continue independently.
