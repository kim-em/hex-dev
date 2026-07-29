# hex-mv-poly

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-mv-poly` provides canonical sparse multivariate polynomials with fixed
arity and an explicit monomial order. It depends on
[`hex-basic`](https://github.com/leanprover/hex-basic) and
[`hex-poly`](https://github.com/leanprover/hex-poly). See
[`hex-mv-poly-mathlib`](https://github.com/leanprover/hex-mv-poly-mathlib)
for the correspondence with Mathlib's `MvPolynomial`.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-mv-poly"
git = "https://github.com/leanprover/hex-mv-poly.git"
rev = "main"
```

```lean
import HexMvPoly

open Hex Hex.MvPoly

abbrev P := MvPoly 2 Int Mono.lex
def x : P := X 0
def y : P := X 1
def p : P := x ^ 2 + C 2 * x * y + C 3

#eval p.termCount
#eval p.coeff #v[1, 1]
#eval p.totalDegree
#eval eval (fun | 0 => 2 | 1 => 5) p
#eval (derivative 0 p).termsList
```

# Functionality

- Monomial arithmetic, divisibility, exact quotients, splits, least common
  multiples, and the named orders `Mono.lex`, `Mono.grlex`, and
  `Mono.grevlex`.
- Canonical construction with `monomial`, `C`, `X`, `addMonomial`, and
  `ofTerms`; ordered iteration with `termsList`, `monomials`, and `foldTerms`.
- Sparse addition, subtraction, negation, multiplication, and repeated-square
  powers.
- Direct and sparse-Horner evaluation, formal derivatives, homogeneous
  components, substitution, partial evaluation, variable renaming, and
  storage reordering.
- The `toUnivariate` / `ofUnivariate` recursive view through
  [`hex-poly`](https://github.com/leanprover/hex-poly).

# Verification

The representation invariant excludes explicit zero coefficients, so each
polynomial has one canonical tree representation. Coefficient extensionality
and constructor laws are complete. Arithmetic has proved additive,
multiplicative, power, evaluation, differentiation, substitution, and
recursive-view laws.

A product coefficient is the convolution over every monomial split:

```lean
theorem coeff_mul [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (p q : MvPoly n R cmp) :
    coeff m (p * q) =
      (Mono.splits m).foldl
        (fun acc ab => acc + coeff ab.1 p * coeff ab.2 q) 0
```

Sparse Horner evaluation agrees with direct evaluation:

```lean
theorem evalHorner_eq [Lean.Grind.CommSemiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) :
    evalHorner x p = eval x p
```

The standard Mathlib algebraic structures and correspondence theorems live in
[`hex-mv-poly-mathlib`](https://github.com/leanprover/hex-mv-poly-mathlib).

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
