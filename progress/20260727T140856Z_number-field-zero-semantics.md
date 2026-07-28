# Number-field zero semantics

## Accomplished

- Proved that successful `AlgebraicNumber.ofNormalized?` construction retains
  its supplied normalized polynomial, and specialized this to identify the
  canonical zero polynomial as `ZPoly.X`.
- Used that structural identity and the existing root semantics to prove that
  canonical algebraic zero denotes complex zero.
- Added fixed-width normalization and coordinate exposure lemmas for number
  tower elements, including the rational presentations of zero and one and the
  identity `a - b = a + (-b)`.
- Closed the tower Mathlib correspondence theorems `map_zero`, `map_one`, and
  `map_sub` without adding `sorry`, `axiom`, or `native_decide`.
- Validated `HexNumberFieldMathlib`, `HexNumberFieldTowerMathlib`, and
  `HexManual`; all 8 number-field and all 19 tower smoke benchmarks; copyright,
  line-count, DAG, Phase-4, Mathlib-free bench, conformance-target, and diff
  checks.

## Current frontier

- The remaining tower arithmetic bridge obligations are the primitive semantic
  proofs for coordinate addition, negation, multiplication, inversion, scalar
  action, and zero recognition. Derived subtraction and division are now
  discharged from those primitives.
- The earlier resultant and number-field milestone PRs remain stacked while CI
  and review complete.

## Next step

- Open this change as a draft PR stacked on `NumberFieldTotalWrappers`, then
  attack the next primitive semantic bridge, starting with coordinate
  evaluation for addition and negation.
- Continue repairing and merging the earlier stacked PRs independently of the
  proof work.

## Blockers

- Fresh Claude second-opinion runs are quota-blocked until the provider reset at
  16:00 UTC; implementation and PR preparation can continue meanwhile.
