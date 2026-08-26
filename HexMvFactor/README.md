# hex-mv-factor

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-mv-factor` provides bounded, checked factorization of sparse
multivariate integer polynomials. It combines structural decomposition,
square-free splitting, Kronecker substitution, evaluation-point search, and
extended EEZ lifting. Complete answers additionally carry an independently
replayed irreducibility certificate for every factor.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-mv-factor"
git = "https://github.com/leanprover/hex-mv-factor.git"
rev = "main"
```

```lean
import HexMvFactor

open Hex Hex.MvFactor Hex.MvPoly

abbrev P := MvPoly 2 Int Mono.lex

def x : P := X 0
def y : P := X 1
def example : P := 1 + x + y + x * y

#eval factor? example
#eval complete? example
```

# Functionality

- Canonical `Decomp` values with scalar content and factor multiplicities.
- Structural factorization of zero, constants, and monomials.
- Complete mixed-radix Kronecker splitting for bounded sparse inputs.
- Deterministic, bounded evaluation-point and modulus searches.
- Leading-coefficient distribution and grouped EEZ recombination.
- Partial results that retain checked work and an explicit stopping reason.
- Complete factorization with replayed irreducibility certificates.

# Verification

`checkDecomp` verifies reassembly and canonical factor shape independently of
all producers. `checkComplete` additionally checks one irreducibility
certificate per factor. The public result types retain the subject polynomial
and the corresponding successful replay equation.

```lean
theorem checkDecomp_sound {f : P} {D : Decomp 2 Mono.lex}
    (h : checkDecomp f D = true) : IsDecompOf f D
```

The executable factorizer is Mathlib-free. The Mathlib companion transports
checked decompositions and irreducibility to `MvPolynomial` and supplies the
user-facing `factor_poly` and `irreducibility` tactics.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
