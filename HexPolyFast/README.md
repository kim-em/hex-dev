# hex-poly-fast

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-poly-fast` provides fast dense-polynomial algorithms with proofs of
agreement with the reference operations. It depends on
[`hex-poly`](https://github.com/leanprover/hex-poly) and
[`hex-truncated-series`](https://github.com/leanprover/hex-truncated-series).
It has no separate Mathlib companion; polynomial correspondence lives in
[`hex-poly-mathlib`](https://github.com/leanprover/hex-poly-mathlib).

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-poly-fast"
git = "https://github.com/leanprover/hex-poly-fast.git"
rev = "main"
```

```lean
import HexPolyFast

open Hex Hex.DensePoly

def a : DensePoly Int := #p[3, -2, 0, 5, 1]
def b : DensePoly Int := #p[-1, 6, 2]
def plan : MulPlan Int := karatsubaPlan 2

#guard mulWith plan a b = a * b
#guard squareWith plan a = a * a
#guard mulSlice plan 2 3 a b = schoolbookSlice 2 3 a b

example : mulWith plan a b = a * b := mulWith_eq plan a b
```

# Functionality

- Explicit `MulPlan` values, including `schoolbookPlan` and `karatsubaPlan`,
  provide full products, squares, and clipped windows through `mulWith`,
  `squareWith`, `mulLow`, and `mulSlice`.
- Cyclic and negacyclic products with `mulCyclic?` and `mulNegacyclic?`.
- Series reciprocals with `reciprocalWith`; Newton division through
  `divModWith` and reusable `DivPlan` values.
- Half-gcd through `gcdWith`, `xgcdWith`, and `xgcdLeftWith`.
- Balanced `ProductTree` and `RemainderTree` values, multipoint evaluation
  with `EvalPlan`, and interpolation with `InterpPlan`.
- Homogeneous and normalized Padé approximation with `padeHomogeneous`
  and `pade?`.

# Verification

The executable library is Mathlib-free. Multiplication, reciprocal, division,
and Euclidean algorithms have exact agreement theorems with the existing
`DensePoly` and `TSeries` operations. Product and remainder trees have node
and remainder laws; interpolation has soundness and uniqueness theorems.
Padé results carry degree and congruence proofs, and the normalized operation
returns `none` exactly when no approximant with denominator equal to one
at the origin exists.

```lean
theorem mulWith_eq (plan : MulPlan R) (a b : DensePoly R) :
    mulWith plan a b = a * b
```

See the [manual chapter](https://kim-em.github.io/hex-dev/HexPolyFast___-fast-dense-polynomials/)
for examples and the computational boundary.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this
published mirror. Contributions are welcome as pull requests to the
`SPEC/` directory there: describe the behaviour you want and leave the
implementation to the maintainer.
