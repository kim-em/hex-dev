# hex-poly-z-gcd

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-poly-z-gcd` provides checked modular gcds, exact cofactors, coprimality
witnesses, and fast square-free decomposition for dense polynomials in
`ℤ[x]`. It depends on `hex-poly-z`, `hex-poly-fp`, `hex-modular`, and
`hex-resultant`. Its Mathlib correspondence is
[`hex-poly-z-gcd-mathlib`](https://github.com/leanprover/hex-poly-z-gcd-mathlib).

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-poly-z-gcd"
git = "https://github.com/leanprover/hex-poly-z-gcd.git"
rev = "main"
```

```lean
import HexPolyZGcd

open Hex

def x1 : ZPoly := DensePoly.ofList [1, 1]
def x2 : ZPoly := DensePoly.ofList [2, 1]
def left : ZPoly := x1 * x1 * x2
def right : ZPoly := x1 * x2 * x2

#eval ZPoly.gcd left right
#eval ZPoly.cofactors left right
#eval ZPoly.sqfDecomp left
```

# Functionality

- Checked exact division with `ZPoly.divExact?` and decidable divisibility.
- Certificate production and replay with `ZPoly.GcdCert`, `ZPoly.gcdCert`,
  and `ZPoly.checkGcd`.
- Modular, heuristic, and subresultant gcd routes behind `ZPoly.gcd`.
- Exact paired cofactors with `ZPoly.cofactors`, plus `ZPoly.gcdList` and
  `ZPoly.lcm`.
- Fast primitive square-free decomposition with `ZPoly.sqfDecomp`.

# Verification

Every public gcd result comes from a certificate accepted by `checkGcd`.
The checker proves both cofactor identities and absence of a common nonunit
cofactor. The maximality layer proves the usual greatest-common-divisor
universal property. The fast square-free decomposition proves signed
reassembly and square-freeness of every nonzero core.

```lean
theorem dvd_gcd (d f h : ZPoly) (hf : d ∣ f) (hh : d ∣ h) :
    d ∣ gcd f h

theorem sqfDecomp_squareFreeCore (f : ZPoly)
    (hcore : (sqfDecomp f).squareFreeCore ≠ 0) :
    SquareFreeRat (sqfDecomp f).squareFreeCore
```

The executable library is Mathlib-free. The sibling Mathlib package
transports divisibility and maximality to `Polynomial ℤ`.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want and leave
the implementation to the maintainer.
