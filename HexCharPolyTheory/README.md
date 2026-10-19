# hex-char-poly-theory

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4.

This is the theory companion of
[`hex-char-poly`](https://github.com/leanprover/hex-char-poly).  It proves that
the executable Samuelson--Berkowitz polynomial is Mathlib's
`Matrix.charpoly`, and derives Cayley--Hamilton, determinant and trace
coefficient formulas, evaluation as `det (tI-A)`, and invariance under
transpose and similarity.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-char-poly-theory"
git = "https://github.com/leanprover/hex-char-poly-theory.git"
rev = "main"
```

```lean
import HexCharPolyTheory

#check HexCharPolyTheory.equiv_charPoly
#check HexCharPolyTheory.evalMatrix_charPoly
#check HexCharPolyTheory.charPoly_transpose
#check HexCharPolyTheory.charPoly_conj
```

# Functionality

- `equiv_charPoly` identifies the executable polynomial with
  `Matrix.charpoly`;
- `equiv_evalMatrix` transports executable Horner evaluation to `aeval`;
- `evalMatrix_charPoly` is Cayley--Hamilton for executable matrices;
- `eval_charPoly` and `coeff_zero_charPoly` connect evaluation and the
  constant coefficient to the executable determinant;
- `charPoly_transpose` and `charPoly_conj` prove the standard invariances.

# Verification

All correspondence theorems are proved over arbitrary commutative rings. The
central `equiv_charPoly` proof follows the Berkowitz recursion through a
bordered characteristic-polynomial identity; the remaining results transport
Mathlib theorems across the matrix and polynomial equivalences.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo; this repository is a
published mirror. Contributions should be opened against the monorepo.
