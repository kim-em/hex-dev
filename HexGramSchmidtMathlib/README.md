# hex-gram-schmidt-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-gram-schmidt-mathlib` is the Mathlib bridge for
[`hex-gram-schmidt`](https://github.com/kim-em/hex-gram-schmidt). It
identifies the executable dense-matrix Gram-Schmidt basis with Mathlib's
`InnerProductSpace.gramSchmidt`, and the fraction-free integer
coefficients with Bareiss determinants. It depends on
[`hex-gram-schmidt`](https://github.com/kim-em/hex-gram-schmidt) and on
Mathlib.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-gram-schmidt-mathlib"
git = "https://github.com/kim-em/hex-gram-schmidt-mathlib.git"
rev = "main"
```

```lean
import HexGramSchmidtMathlib

open Hex

-- Each row of the executable integer Gram-Schmidt basis matches Mathlib's
-- `gramSchmidt` after casting the row into Euclidean space.
#check @GramSchmidtMathlib.int_basis_row_eq_gramSchmidt

-- Mathlib's real inner product agrees with the executable rational dot product.
#check @GramSchmidtMathlib.rowToEuclidean_inner

-- The fraction-free integer coefficients are Bareiss determinants.
#check @GramSchmidt.Int.scaledCoeffs_eq_scaledCoeffMatrix_bareiss
```

# Functionality

The proof-facing API splits into two parts.

- The view `GramSchmidtMathlib.rowToEuclidean` from a rational dense row
  into `EuclideanSpace ℝ (Fin m)`, with its additivity, scaling, and
  inner-product transfer lemmas (`rowToEuclidean_add`,
  `rowToEuclidean_smul`, `rowToEuclidean_inner`).
- The rowwise correspondences `rat_basis_row_eq_gramSchmidt` and
  `int_basis_row_eq_gramSchmidt` between the executable basis and Mathlib's
  `InnerProductSpace.gramSchmidt`.
- The integer determinantal layer: `gramDet_eq_prod_normSq`,
  `scaledCoeffs_eq_scaledCoeffMatrix_bareiss`, and `scaledCoeffs_eq`,
  relating the leading Gram determinants and the scaled coefficients to
  Bareiss determinants of the [`hex-matrix`](https://github.com/kim-em/hex-matrix)
  Gram matrices.

# Verification

The rowwise correspondence with Mathlib's orthogonalization is fully
proven. Over the rationals:

```lean
theorem rat_basis_row_eq_gramSchmidt (b : Matrix Rat n m) (i : Fin n) :
    rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row i) =
      InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) i
```

and the integer version, casting the integer rows first:

```lean
theorem int_basis_row_eq_gramSchmidt (b : Matrix Int n m) (i : Fin n) :
    rowToEuclidean ((Hex.GramSchmidt.Int.basis b).row i) =
      InnerProductSpace.gramSchmidt ℝ (intRowFamily b) i
```

The fraction-free integer surface is identified with Bareiss
determinants. Below the diagonal the scaled coefficients are exactly:

```lean
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji)
```

and for an independent matrix the leading Gram determinant is the product
of squared Gram-Schmidt norms:

```lean
theorem gramDet_eq_prod_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk
```

The executable Gram-Schmidt algorithm and its own algebraic API live in
[`hex-gram-schmidt`](https://github.com/kim-em/hex-gram-schmidt).

# Reference manual

The hex reference manual covers this library and its computational base at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-gram-schmidt>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
