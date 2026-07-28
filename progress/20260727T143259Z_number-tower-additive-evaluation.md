# Number-tower additive evaluation

## Accomplished

- Defined a direct complex Horner denotation for raw mixed-radix coordinates
  and proved that every successful lazy evaluation agrees with it.
- Proved fixed-width block extraction commutes with coordinate addition and
  used this to establish additivity of the recursive Horner denotation.
- Connected the direct denotation to the tower's selected `toComplex`
  interpretation and retired the `map_add` placeholder.
- Validated `HexNumberFieldTowerMathlib` and `HexManual`, all 19 tower smoke
  benchmarks, and the repository policy checks.

## Current frontier

- The additive semantic API is complete: zero, addition, negation,
  subtraction, and zero recognition are all proved.
- The next primitive field obligation is `map_mul`; inversion and rational
  scalar multiplication remain after it.

## Next step

- Open this milestone as a draft PR stacked on
  `NumberFieldTowerMapAddNeg`.
- On the next branch, prove that recursive reduced multiplication preserves
  the direct Horner denotation, then use it to close `map_mul`.

## Blockers

- Claude second-opinion capacity remains unavailable until the provider quota
  reset; implementation and GitHub CI continue independently.
