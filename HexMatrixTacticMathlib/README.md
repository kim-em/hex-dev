# hex-matrix-tactic-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4.

This is the Mathlib companion of
[`hex-matrix-tactic`](../HexMatrixTactic/README.md). It accepts closed Mathlib
matrices written as `!![…]`, `Matrix.of ![…]`, `fun i j => …` or
`Matrix.ofArray xs h`, reconstructs them as executable Hex matrices with one
kernel-checked entrywise certificate, and transports the Hex results to
`Matrix.det` and `Matrix.charpoly` through the correspondence
theorems of the Mathlib bridges. Rank tactics live with `hex-rank-mathlib`.

The design is
[`SPEC/hex-matrix-tactic-mathlib.md`](SPEC/hex-matrix-tactic-mathlib.md).

# Quickstart

```lean
import HexMatrixTacticMathlib

open Matrix Polynomial

def A : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 3, 4]

example : A.det = -2 := by det
example : A.charpoly = X ^ 2 - 5 * X - 2 := by char_poly

#check det% A       -- Hex.MatrixTactic.Certified Matrix.det A
#check char_poly A  -- Hex.MatrixTactic.Certified Matrix.charpoly A

example : Matrix.det !![(1 : ℤ), 2; 3, 4] = -2 := by simp only [hex_norm_det]
```

Supported carriers are `ℤ` and `ℚ` for `det`, and `ℤ` for `char_poly`. `hex_norm_det` tries the Hex determinant first and falls back to
Mathlib's unmodified `norm_det`, so symbolic entries still normalize.
