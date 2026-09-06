# hex-number-field

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Executable exact algebraic numbers in `ℂ`, implemented in Lean 4 without
Mathlib. The package provides fixed-field arithmetic in one irreducible
presentation, factorization-lazy arithmetic on certified roots, and a
canonical minimal-polynomial form with decidable equality. It builds on
[`hex-poly-z`](https://github.com/leanprover/hex-poly-z),
[`hex-roots`](https://github.com/leanprover/hex-roots),
[`hex-resultant`](https://github.com/leanprover/hex-resultant),
[`hex-berlekamp-zassenhaus`](https://github.com/leanprover/hex-berlekamp-zassenhaus),
and the matrix stack; its Mathlib counterpart is
[`hex-number-field-mathlib`](https://github.com/leanprover/hex-number-field-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-number-field"
git = "https://github.com/leanprover/hex-number-field.git"
rev = "main"
```

```lean
import HexNumberField

open Hex

-- The roots of an integer polynomial, real roots first in
-- increasing order: index 1 of `X² - 2` is `+√2`.
def sqrt2 : AlgebraicNumber :=
  (ZPoly.algebraicRoots #p[-2, 0, 1])[1]!
def sqrt3 : AlgebraicNumber :=
  (ZPoly.algebraicRoots #p[-3, 0, 1])[1]!

-- Arithmetic is exact; `p` is the minimal polynomial.
#guard (sqrt2 + sqrt3).p = #p[1, 0, -10, 0, 1]
-- Equality is decidable. Without the Mathlib companion,
-- compare with `==`; with it, `=` works too.
#guard (sqrt2 + sqrt3)⁻¹ == sqrt3 - sqrt2

/-- info: (ZPoly.algebraicRoots #p[1, 0, -10, 0, 1])[3]! -/
#guard_msgs in
#eval sqrt2 + sqrt3
```

# Functionality

Three complementary exact representations:

- `Hex.QAdjoin p x`: rational power-basis coordinates in a fixed
  irreducible presentation `ℚ(x)`, with `Hex.QAdjoin.reduce`, arithmetic,
  extended-gcd inversion, and threaded dyadic approximation
  (`Hex.QAdjoin.approx`).
- `Hex.AlgebraicRoot`: a certified selected root of a squarefree integer
  polynomial that need not be minimal. Arithmetic (`add?`, `mul?`, `inv?`,
  `div?`) builds resultant eliminants and postpones factoring until
  `Hex.AlgebraicRoot.exact` is requested.
- `Hex.AlgebraicNumber`: the canonical form, a selected root of its
  normalized irreducible minimal polynomial, with rational construction,
  casts, powers, and Boolean equality that compares represented values.

`Hex.ZPoly.algebraicRoots` turns an integer polynomial into its distinct
complex roots as canonical algebraic numbers, real roots first in increasing
order, with `isReal`, a dyadic `approx`, and a `Repr` that prints the minimal
polynomial and twelve decimals. `Hex.AlgebraicPoly` supplies polynomials with
algebraic coefficients and semantic trailing-zero normalization, with root
APIs (`roots?`) for both fixed-field and algebraic-coefficient polynomials.

# Verification

Certificates are exact and kernel-checkable: every stored root carries a
refined isolation, so identity and approximation are certified eagerly even
though factorization is lazy. The `Option`-valued operations are the honest
computational boundary; their total wrappers are backed by companion
`_isSome` completeness theorems rather than silent assumptions. The
companion
[`hex-number-field-mathlib`](https://github.com/leanprover/hex-number-field-mathlib)
interprets every representation in `ℂ`, proves the arithmetic computes the
corresponding complex operations (including the convention `0⁻¹ = 0`),
proves `Hex.AlgebraicNumber.toComplex` injective, and installs a lawful
`Field` instance over the unchanged executable operations. See the
[SPEC](SPEC/hex-number-field.md) for contracts and budgets.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
