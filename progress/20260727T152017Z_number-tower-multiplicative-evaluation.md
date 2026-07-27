# Number-tower multiplicative evaluation

## Accomplished

- Refactored recursive raw multiplication into named convolution and
  structurally recursive monic-reduction helpers with fixed-size theorems.
- Proved the direct complex denotation of block convolution and every
  descending reduction step, then composed those invariants across the full
  reducer.
- Proved recursive raw multiplication denotes complex multiplication and used
  it to retire the public `map_mul` placeholder.
- Built `HexNumberFieldTowerMathlib`, `HexManual`, the tower conformance target,
  and the tower benchmark executable; all 19 fixed benchmarks pass with their
  committed checksums.
- Passed the DAG, Phase-4, copyright, status, diff, and banned-declaration
  checks.

## Current frontier

- Zero, addition, negation, subtraction, multiplication, division's
  multiplicative step, and zero recognition now have proved complex semantics.
- Recursive inversion and rational scalar multiplication remain the primitive
  field-operation correspondence obligations.

## Next step

- Open this milestone as a draft PR stacked on `NumberFieldTowerRawAdd`.
- On the next branch, prove the recursive extended-gcd inversion invariant and
  close `map_inv`; continue review monitoring independently.

## Blockers

- Claude second-opinion capacity remains unavailable until the provider quota
  reset; implementation and GitHub CI continue independently.
