# hex-determinant-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-determinant-mathlib` is the Mathlib bridge for
[`hex-determinant`](https://github.com/kim-em/hex-determinant). It identifies
the executable Leibniz determinant with Mathlib's `Matrix.det`, so Mathlib's
determinant theory transfers to the executable matrices. This library depends
on [`hex-determinant`](https://github.com/kim-em/hex-determinant) and on
Mathlib.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-determinant-mathlib"
git = "https://github.com/kim-em/hex-determinant-mathlib.git"
rev = "main"
```

```lean
import HexDeterminantMathlib

open Hex HexMatrixMathlib

-- The executable Leibniz determinant equals Mathlib's `Matrix.det`.
#check @det_eq

-- A leading principal submatrix determinant, restated in Mathlib terms.
#check @det_principalSubmatrix_eq_submatrix_det

-- The Desnanot-Jacobi identity for a Bareiss bordered minor.
#check @desnanot_jacobi_borderedMinor
```

# Functionality

The proof-facing API connects the executable determinant to Mathlib:

- `det_eq`: the executable `Hex.Matrix.det` equals `Matrix.det` of the
  corresponding Mathlib matrix `matrixEquiv M`;
- the permutation-sign bridge: `PermutationVector.toPerm`,
  `PermutationVector.equivs`, and `detSign_eq_permSign`, matching Hex's
  inversion-count sign to `Equiv.Perm.sign`;
- submatrix transport: `matrixEquiv_borderedMinor` and the determinant forms
  `det_principalSubmatrix_eq_submatrix_det` and
  `det_borderedMinor_eq_submatrix_det`;
- the Plücker three-term identity `det_plucker_three_term` and the
  Desnanot-Jacobi identities `desnanot_jacobi` and
  `desnanot_jacobi_borderedMinor` used by the Bareiss correctness proof.

# Verification

The determinant correspondence is fully proven over a `CommRing`. The
headline theorem identifies the two determinants:

```lean
theorem det_eq [CommRing R] (M : Hex.Matrix R n n) :
    Hex.Matrix.det M = Matrix.det (matrixEquiv M)
```

The Plücker three-term identity, assembled for the Bareiss correctness proof:

```lean
theorem det_plucker_three_term
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (v : Vector R (n + 3))
    (p1 p2 p3 : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    Hex.Matrix.mDet B v p1 * Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B v p2 * Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B v p3 * Hex.Matrix.nDet B p1 p2 h12 = 0
```

The Desnanot-Jacobi identity over Mathlib matrices:

```lean
theorem desnanot_jacobi {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det * (M.submatrix (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
      (Fin.succAbove 0 ∘ (Fin.last n).succAbove)).det =
    (M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
      (M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det -
    (M.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).det *
      (M.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)).det
```

The Leibniz determinant and its cofactor, adjugate, and Cauchy-Binet theory
live in [`hex-determinant`](https://github.com/kim-em/hex-determinant); the
`bareiss = det` headline theorems live in
[`hex-bareiss-mathlib`](https://github.com/kim-em/hex-bareiss-mathlib).

# Reference manual

The hex reference manual covers this library and its computational base at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-determinant>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
