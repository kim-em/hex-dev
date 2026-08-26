# hex-resultant

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Polynomial resultants and discriminants for `Hex.DensePoly R` over a
commutative exact-division domain, implemented in Lean 4 without Mathlib.
The algorithm is the subresultant pseudo-remainder sequence of Collins and
Brown, the standard fraction-free method. The package depends on
[`hex-poly`](https://github.com/leanprover/hex-poly) and
[`hex-basic`](https://github.com/leanprover/hex-basic); its Mathlib
counterpart is
[`hex-resultant-mathlib`](https://github.com/leanprover/hex-resultant-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-resultant"
git = "https://github.com/leanprover/hex-resultant.git"
rev = "main"
```

```lean
import HexResultant

open Hex

def f : DensePoly Int := DensePoly.ofList [-2, 0, 1]  -- X^2 - 2
def g : DensePoly Int := DensePoly.ofList [-3, 0, 1]  -- X^2 - 3

#guard DensePoly.resultant f g = 1
#guard DensePoly.disc f = 8
```

# Functionality

- `Hex.DensePoly.pseudoDivMod`: total polynomial pseudo-division with all
  coefficients kept in `R`.
- `Hex.DensePoly.subresultantRun` and `Hex.DensePoly.subresultantChain`:
  Brown's nonzero subresultant pseudo-remainder sequence with its corrected
  terminal scale.
- `Hex.DensePoly.subresultantChainExt`: the same chain carrying the Bezout
  cofactors `(uₖ, vₖ)` that produce each entry from the two inputs.
- `Hex.DensePoly.resultant`: the resultant under Mathlib's
  default-formal-degree conventions, total on zero and reversed inputs.
- `Hex.DensePoly.disc`: the standard discriminant, with the
  leading-coefficient correction that keeps the quotient exact in every
  characteristic.

The main instantiations are `Int`, `Hex.ZPoly` coefficients for bivariate
elimination, and the number-tower element types used by
[`hex-number-field-tower`](https://github.com/leanprover/hex-number-field-tower).
The chain costs `O(n·m)` coefficient operations rather than the `O((n+m)³)`
of a Sylvester determinant.

# Verification

The resultant surface has a complete correctness API. The companion
[`hex-resultant-mathlib`](https://github.com/leanprover/hex-resultant-mathlib)
proves the end-to-end theorem `Hex.DensePoly.toPolynomial_resultant`: the
executable value agrees exactly with Mathlib's `Polynomial.resultant`,
units, powers, and signs included, with no hypotheses beyond the
algorithm's own typeclass context. This package itself proves the
Mathlib-free algebra of the chain: pseudo-division identities, the
Brown--Traub minor correspondence, and exact-division totality.

The extended cofactor chain is proved to the same standard.
`Hex.DensePoly.subresultantChainExt_bezout` gives `u * f + v * g = S` for
every stored entry, `subresultantChainExt_exact` gives the divisibility
that makes each transformation row's exact division legitimate, and
`subresultantChainExt_values` identifies the stored values with
`subresultantChain`. The gcd libraries build their Bezout certificates on
these.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
