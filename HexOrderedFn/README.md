# hex-ordered-fn

`HexOrderedFn` is part of [Hex](https://github.com/kim-em/hex-dev), a computer
algebra library for Lean 4. The aim is fast executable code, fully verified,
built with spec-driven development.

It supplies positive infinitesimals, exact rational bounds and total refinement
for canonical rational functions. It depends on `HexRationalFn`, `HexPoly` and
`HexPolyFast` and is Mathlib-free. `HexOrderedFnTheory` supplies interpretation
and order proofs. Both are unreleased development libraries.
The [manual](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-ordered-fn)
explains the computational and semantic APIs with checked examples.

# Quickstart

Use these imports from the `hex-dev` monorepo; there is no released package yet.

```lean
import HexOrderedFn
open Hex Hex.OrderedFn
open scoped Hex.OrderedFn.Infinitesimal

def epsilon : RationalFn Rat := RationalFn.X
def delta : RationalFn (RationalFn Rat) := RationalFn.X
#guard delta < RationalFn.C (epsilon ^ 3)
#guard Infinitesimal.sign orderSign (1 / (epsilon - 1)) = -1
```

# Functionality

- `Infinitesimal.sign` scans the lowest nonzero numerator and denominator
  coefficients. `compare` signs a difference. Scoped comparisons leave the
  predecessor order intact and support successive infinitesimals.
- `Oracle.Bounds` supports exact singletons and dyadics, negation, addition,
  four-corner multiplication, intersection and conditional division.
  `sign?` requires strict separation; `exactSign?` also accepts singleton zero.
- `Oracle.Approximation` fixes the coefficient and constant providers.
  `ApproximationWidth` records positive-request widths separately from
  semantic containment in the companion.
- `Real.enclose` refines coefficients and the argument together in the actual
  Horner loop. `sign` and `approx` execute trials under erased termination
  proofs. `requestWidth` sends nonpositive requests to width one.
- `Real.sign?` is a bounded sign attempt that also checks the stored denominator.
  It is independent of the registered field's total sign operation.
- `Real.Extension` fixes one registration and reuses canonical fraction
  arithmetic. It supplies total sign, comparison and approximation;
  `approximation` provides coefficient bounds for the next real level.
- `firstSome` executes the first successful trial. Finite-witness and
  eventual-success lemmas prove termination without supplying a runtime answer.

# Verification

Native arithmetic and equality come from canonical `RationalFn` operations.
The computational library proves first-success search laws, width bounds and
literal preservation through provider transport. Termination evidence alone
proves no semantic validity.

The companion proves containment, finite-sign soundness, infinitesimal order
laws and total progress under containment, shrinking widths and relative
transcendence over the entire predecessor field. Provider transport preserves
order only when both sources describe the same embedding and subject.
Expression consumers must retain original divisor guards through cancellation.

`HexOrderedFnTests` and the conformance suite cover finite exhaustion, poles,
negative denominators, joint refinement and successive levels. Exact Z3/FLINT
oracles check the emitted fixtures. The [performance report](https://github.com/kim-em/hex-dev/blob/main/reports/hex-ordered-fn-performance.md)
records the computational evidence; benchmark verification is a correctness
check. See [the specification](SPEC/hex-ordered-fn.md) for the full contract.

# Contributing

Development happens in [hex-dev](https://github.com/kim-em/hex-dev).
Contributions are welcome as PRs to `SPEC/`: describe the behavior you want.
