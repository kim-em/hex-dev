# hex-poly-z-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

This package supplies Mathlib semantics and analytic bounds for its
computational counterpart,
[`hex-poly-z`](https://github.com/leanprover/hex-poly-z). It depends on
`hex-poly-z`, `hex-hensel`, `hex-poly-mathlib`, `hex-mod-arith-mathlib`, and
Mathlib. It identifies `Hex.ZPoly` with `Polynomial ℤ` and provides the proofs
shared by integer factorization and certified root isolation.

# Quickstart

```toml
[[require]]
name = "hex-poly-z-mathlib"
git = "https://github.com/leanprover/hex-poly-z-mathlib.git"
rev = "main"
```

```lean
import HexPolyZMathlib

open HexPolyZMathlib

#check equiv

example (f : Hex.ZPoly) :
    ofPolynomial (toPolynomial f) = f := by
  simp
```

# Functionality

- `equiv`, `toPolynomial`, and `ofPolynomial` identify `Hex.ZPoly` with
  `Polynomial ℤ` and preserve coefficients and ring operations.
- `toPolynomial_content`, `toPolynomial_dilate`, and
  `coeff_toZMod_modP_eq_coeff_map_intCast` transport integer-specific
  operations.
- `squareFreeRat_iff` connects the executable rational-gcd test to Mathlib
  squarefreeness.
- `mignotte_bound`, `one_le_mahlerDist`, and the discriminant, Hadamard, and
  Robinson-form APIs provide the analytic results used downstream.
- `PolyParse.parsePoly` supplies shared elaboration-time polynomial parsing.

# Verification

The representation correspondence covers both conversion directions,
coefficients, and the ring operations. Specialized theorems cover content,
primitive parts, dilation, reduction modulo `p`, rational squarefreeness, and
the Mignotte bound. The discriminant and Mahler developments provide the
Mathlib-side analytic surface used by root isolation.

Executable polynomial arithmetic and natural-number coefficient bounds remain
in `hex-poly-z`; this package provides proofs over `Polynomial ℤ`,
`Polynomial ℚ`, and `Polynomial ℂ`. See the
[SPEC](SPEC/hex-poly-z-mathlib.md) for the theorem map.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
