# Number-tower zero recognition and negation

## Accomplished

- Exposed the fixed coordinate width of every tower element and proved that
  tower zero has the all-zero coordinate array.
- Proved the executable Boolean zero test is equivalent to equality with the
  tower zero, then transported that equivalence through the injective complex
  interpretation to close semantic zero recognition.
- Proved coordinatewise negation is an additive inverse and used `map_add` and
  `map_zero` to derive the semantic negation correspondence, retiring another
  bridge placeholder without duplicating the evaluator proof.
- Validated `HexNumberFieldTowerMathlib` and `HexManual`, all 19 tower smoke
  benchmarks, and the repository policy checks.

## Current frontier

- `map_add` is now the sole primitive additive semantic obligation: negation,
  subtraction, and zero recognition are derived from it plus structural core
  identities.
- Its proof requires exposing the recursive lazy Horner evaluator as a linear
  complex-valued interpretation of mixed-radix coordinates.

## Next step

- Open this milestone as a draft PR stacked on `NumberFieldZeroSemantic`.
- On the next branch, prove the raw evaluator's Horner semantics and use its
  coordinate linearity to close `map_add`.

## Blockers

- Claude second-opinion capacity remains unavailable until the provider quota
  reset; implementation and GitHub CI continue independently.
