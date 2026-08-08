# hex-mv-poly-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-mv-poly-mathlib` is the Mathlib bridge for
[`hex-mv-poly`](https://github.com/leanprover/hex-mv-poly). It identifies
the executable sparse representation with `MvPolynomial (Fin n) R` and
transports the proof-facing algebraic API. It depends on Mathlib,
[`hex-mv-poly`](https://github.com/leanprover/hex-mv-poly), and
[`hex-poly-mathlib`](https://github.com/leanprover/hex-poly-mathlib).

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-mv-poly-mathlib"
git = "https://github.com/leanprover/hex-mv-poly-mathlib.git"
rev = "main"
```

```lean
import HexMvPolyMathlib

open Hex Hex.MvPoly HexMvPolyMathlib
open scoped HexMvPolyMathlib

abbrev P := MvPoly 2 Int Mono.lex

#check (equiv : P ≃+* MvPolynomial (Fin 2) Int)

example (p q : P) :
    toMvPolynomial (p * q) =
      toMvPolynomial p * toMvPolynomial q := by
  simp
```

# Functionality

- The exponent-vector equivalence `monoEquiv` and exact polynomial
  conversions `toMvPolynomial` and `ofMvPolynomial`.
- The ring and algebra equivalences `equiv` and `algEquiv`, with transported
  `CommSemiring`, `CommRing`, and `Algebra` structures whose operations remain
  the executable ones.
- The algebra homomorphism `aeval` and its laws for constants, variables,
  addition, multiplication, powers, negation, and subtraction.
- Correspondence theorems for support, total and per-variable degree,
  differentiation, homogeneous components, substitution, partial evaluation,
  renaming, and storage reordering.
- Ring equivalences for the recursive view, the zero-variable case, and the
  one-variable dense-polynomial case.

# Verification

The correspondence is fully proven in both directions:

```lean
def equiv [CommSemiring R] [DecidableEq R] :
    MvPoly n R cmp ≃+* MvPolynomial (Fin n) R
```

It preserves every coefficient:

```lean
theorem coeff_toMvPolynomial [CommSemiring R] [DecidableEq R]
    (m : Mono n) (p : MvPoly n R cmp) :
    MvPolynomial.coeff (monoEquiv m) (toMvPolynomial p) =
      coeff m p
```

Executable evaluation is Mathlib algebra evaluation after conversion:

```lean
theorem aeval_apply [CommSemiring R] [DecidableEq R]
    [CommSemiring S] [Algebra R S]
    (x : Fin n → S) (p : MvPoly n R cmp) :
    aeval x p = MvPolynomial.aeval x (toMvPolynomial p)
```

The Mathlib-free representation and executable algorithms live in
[`hex-mv-poly`](https://github.com/leanprover/hex-mv-poly).

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
