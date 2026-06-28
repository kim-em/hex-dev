module

public import HexMatrix.Basic

public section

/-!
Elementary row and column operations.

This module contains the primitive executable row/column operations and their
entrywise access lemmas. Algebraic preservation theorems for multiplication and
inverse tracking live downstream in `HexMatrix.RowEchelon`.
-/

namespace Hex

universe u

namespace Matrix

/-- Swap rows `i` and `j` in a dense matrix. -/
@[expose]
def rowSwap (M : Matrix R n m) (i j : Fin n) : Matrix R n m :=
  (M.set i M[j]).set j M[i]

/-- Read an entry of `rowSwap M i j` by cases on the row index: row `j`
returns the original row `i`, row `i` returns the original row `j`, and any
other row is unchanged. -/
theorem rowSwap_getElem (M : Matrix R n m) (i j r : Fin n) (k : Fin m) :
    (rowSwap M i j)[r][k] =
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] := by
  by_cases hrj : r = j
  · subst r
    simp [rowSwap]
  · by_cases hri : r = i
    · subst r
      simp [rowSwap, hrj]
      have hval : j.val ≠ i.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow : ((M.set i M[j]).set j M[i])[i] = (M.set i M[j])[i] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i])
          j.isLt i.isLt hval
      simpa using congrArg (fun row => row[k]) hrow
    · simp [rowSwap, hrj, hri]
      have hir : i.val ≠ r.val := by
        intro hval
        exact hri (Fin.ext hval.symm)
      have hjr : j.val ≠ r.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow₁ : (M.set i M[j])[r] = M[r] := by
        exact Vector.getElem_set_ne (xs := M) (x := M[j]) i.isLt r.isLt hir
      have hrow₂ : ((M.set i M[j]).set j M[i])[r] = (M.set i M[j])[r] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i])
          j.isLt r.isLt hjr
      exact (congrArg (fun row => row[k]) hrow₂).trans
        (congrArg (fun row => row[k]) hrow₁)

/-- Row `i` of `rowSwap M i j` is the original row `j`. -/
@[simp, grind =] theorem row_rowSwap_left (M : Matrix R n m) (i j : Fin n) :
    row (rowSwap M i j) i = row M j := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowSwap M i j) i)[kk] = (row M j)[kk]
  rw [row_getElem, row_getElem, rowSwap_getElem]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- Row `j` of `rowSwap M i j` is the original row `i`. -/
@[simp, grind =] theorem row_rowSwap_right (M : Matrix R n m) (i j : Fin n) :
    row (rowSwap M i j) j = row M i := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowSwap M i j) j)[kk] = (row M i)[kk]
  rw [row_getElem, row_getElem, rowSwap_getElem]
  simp

/-- Any row other than `i` and `j` is unchanged by `rowSwap M i j`. -/
theorem row_rowSwap_of_ne (M : Matrix R n m) {i j r : Fin n}
    (hri : r ≠ i) (hrj : r ≠ j) :
    row (rowSwap M i j) r = row M r := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowSwap M i j) r)[kk] = (row M r)[kk]
  rw [row_getElem, row_getElem, rowSwap_getElem]
  simp [hri, hrj]

/-- Diagonal-entry corollary of `rowSwap_getElem` for square matrices: when
`pivot ≠ k`, the `(k, k)` entry of `rowSwap M k pivot` is the original
`(pivot, k)` entry. -/
theorem rowSwap_diag_of_ne (M : Matrix R n n) {k pivot : Fin n}
    (h : pivot ≠ k) :
    (rowSwap M k pivot)[k][k] = M[pivot][k] := by
  rw [rowSwap_getElem]
  by_cases hkp : k = pivot
  · exact (h hkp.symm).elim
  · simp [hkp]

/-- Scale row `i` by `c`. -/
@[expose]
def rowScale [Mul R] (M : Matrix R n m) (i : Fin n) (c : R) : Matrix R n m :=
  M.set i <| Vector.ofFn fun k => c * M[i][k]

/-- Read an entry of `rowScale M i c` by cases on the row index: row `i`
returns `c * M[i][k]`, any other row is unchanged. -/
theorem rowScale_getElem [Mul R] (M : Matrix R n m) (i r : Fin n) (c : R) (k : Fin m) :
    (rowScale M i c)[r][k] =
      if r = i then c * M[i][k] else M[r][k] := by
  by_cases h : r = i
  · subst r
    simp [rowScale]
  · simp [rowScale, h]
    have hval : i.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set i (Vector.ofFn fun k => c * M[i][k]))[r] = M[r] := by
      exact
        (Vector.getElem_set_ne (xs := M) (x := Vector.ofFn fun k => c * M[i][k])
          i.isLt r.isLt hval)
    simpa [rowScale] using congrArg (fun row => row[k]) hrow

/-- Row `i` of `rowScale M i c` is the pointwise scalar multiple of row `i`. -/
@[simp, grind =] theorem row_rowScale_self [Mul R] (M : Matrix R n m) (i : Fin n) (c : R) :
    row (rowScale M i c) i = Vector.ofFn (fun k => c * M[i][k]) := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowScale M i c) i)[kk] = (Vector.ofFn (fun k => c * M[i][k]))[kk]
  rw [row_getElem, rowScale_getElem]
  simp

/-- Any row other than `i` is unchanged by `rowScale M i c`. -/
theorem row_rowScale_of_ne [Mul R] (M : Matrix R n m) {i r : Fin n} (c : R)
    (hri : r ≠ i) :
    row (rowScale M i c) r = row M r := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowScale M i c) r)[kk] = (row M r)[kk]
  rw [row_getElem, row_getElem, rowScale_getElem]
  simp [hri]

/-- Replace row `dst` by `row dst + c * row src`. -/
@[expose]
def rowAdd [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin n) (c : R) : Matrix R n m :=
  M.set dst <| Vector.ofFn fun k => M[dst][k] + c * M[src][k]

/-- Read an entry of `rowAdd M src dst c` by cases on the row index: row `dst`
returns `M[dst][k] + c * M[src][k]`, any other row is unchanged. -/
theorem rowAdd_getElem [Mul R] [Add R]
    (M : Matrix R n m) (src dst r : Fin n) (c : R) (k : Fin m) :
    (rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [rowAdd]
  · simp [rowAdd, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]))[r] = M[r] := by
      exact
        (Vector.getElem_set_ne (xs := M)
          (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
          dst.isLt r.isLt hval)
    simpa [rowAdd] using congrArg (fun row => row[k]) hrow

/-- Source-row entries are unchanged by `rowAdd M src dst c` when `src ≠ dst`. -/
theorem rowAdd_getElem_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin n} (c : R) (hsrcdst : src ≠ dst) (k : Fin m) :
    (rowAdd M src dst c)[src][k] = M[src][k] := by
  rw [rowAdd_getElem]
  simp [hsrcdst]

/-- Row `dst` of `rowAdd M src dst c` is the pointwise row combination. -/
@[simp, grind =] theorem row_rowAdd_dst [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin n) (c : R) :
    row (rowAdd M src dst c) dst =
      Vector.ofFn (fun k => M[dst][k] + c * M[src][k]) := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowAdd M src dst c) dst)[kk] =
    (Vector.ofFn (fun k => M[dst][k] + c * M[src][k]))[kk]
  rw [row_getElem, rowAdd_getElem]
  simp

/-- Any row other than `dst` is unchanged by `rowAdd M src dst c`. -/
theorem row_rowAdd_of_ne [Mul R] [Add R]
    (M : Matrix R n m) (src : Fin n) {dst r : Fin n} (c : R)
    (hrdst : r ≠ dst) :
    row (rowAdd M src dst c) r = row M r := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowAdd M src dst c) r)[kk] = (row M r)[kk]
  rw [row_getElem, row_getElem, rowAdd_getElem]
  simp [hrdst]

/-- The source row is unchanged by `rowAdd M src dst c` when `src ≠ dst`. -/
@[simp, grind =] theorem row_rowAdd_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin n} (c : R) (hsrcdst : src ≠ dst) :
    row (rowAdd M src dst c) src = row M src := by
  exact row_rowAdd_of_ne M src c hsrcdst

/-- Replace column `dst` by `col dst + c * col src`. -/
@[expose]
def colAdd [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin m) (c : R) : Matrix R n m :=
  Matrix.ofFn fun i j => if j = dst then M[i][j] + c * M[i][src] else M[i][j]

/-- Replace column `dst` by `col dst + col src * c`.

This is the right-scalar variant of `colAdd`. It is the column-add operation
whose right-multiplication wrapper is valid over a noncommutative ring. -/
@[expose]
def colAddRight [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin m) (c : R) :
    Matrix R n m :=
  Matrix.ofFn fun i j => if j = dst then M[i][j] + M[i][src] * c else M[i][j]

/-- Read an entry of `colAdd M src dst c` by cases on the column index:
column `dst` returns `M[i][dst] + c * M[i][src]`, any other column is
unchanged. -/
theorem colAdd_getElem [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) (i : Fin n) (j : Fin m) :
    (colAdd M src dst c)[i][j] =
      if j = dst then M[i][j] + c * M[i][src] else M[i][j] := by
  rw [colAdd, getElem_ofFn]

/-- Read an entry of `colAddRight M src dst c` by cases on the column index:
column `dst` returns `M[i][dst] + M[i][src] * c`, any other column is
unchanged. -/
theorem colAddRight_getElem [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) (i : Fin n) (j : Fin m) :
    (colAddRight M src dst c)[i][j] =
      if j = dst then M[i][j] + M[i][src] * c else M[i][j] := by
  rw [colAddRight, getElem_ofFn]

/-- Column `dst` of `colAdd M src dst c` is the pointwise column combination. -/
@[simp, grind =] theorem col_colAdd_dst [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) :
    col (colAdd M src dst c) dst =
      Vector.ofFn (fun i => M[i][dst] + c * M[i][src]) := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show (col (colAdd M src dst c) dst)[ii] =
    (Vector.ofFn (fun i => M[i][dst] + c * M[i][src]))[ii]
  rw [col_getElem, colAdd_getElem]
  simp

/-- Column `dst` of `colAddRight M src dst c` is the pointwise column
combination with right scalar multiplication. -/
@[simp, grind =] theorem col_colAddRight_dst [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) :
    col (colAddRight M src dst c) dst =
      Vector.ofFn (fun i => M[i][dst] + M[i][src] * c) := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show (col (colAddRight M src dst c) dst)[ii] =
    (Vector.ofFn (fun i => M[i][dst] + M[i][src] * c))[ii]
  rw [col_getElem, colAddRight_getElem]
  simp

/-- Any column other than `dst` is unchanged by `colAdd M src dst c`. -/
theorem col_colAdd_of_ne [Mul R] [Add R]
    (M : Matrix R n m) (src : Fin m) {dst j : Fin m} (c : R)
    (hjdst : j ≠ dst) :
    col (colAdd M src dst c) j = col M j := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show (col (colAdd M src dst c) j)[ii] = (col M j)[ii]
  rw [col_getElem, col_getElem, colAdd_getElem]
  simp [hjdst]

/-- Any column other than `dst` is unchanged by `colAddRight M src dst c`. -/
theorem col_colAddRight_of_ne [Mul R] [Add R]
    (M : Matrix R n m) (src : Fin m) {dst j : Fin m} (c : R)
    (hjdst : j ≠ dst) :
    col (colAddRight M src dst c) j = col M j := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show (col (colAddRight M src dst c) j)[ii] = (col M j)[ii]
  rw [col_getElem, col_getElem, colAddRight_getElem]
  simp [hjdst]

/-- Source-column entries are unchanged by `colAdd M src dst c` when `src ≠ dst`. -/
theorem colAdd_getElem_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin m} (c : R) (hsrcdst : src ≠ dst) (i : Fin n) :
    (colAdd M src dst c)[i][src] = M[i][src] := by
  rw [colAdd_getElem]
  simp [hsrcdst]

/-- Source-column entries are unchanged by `colAddRight M src dst c` when
`src ≠ dst`. -/
theorem colAddRight_getElem_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin m} (c : R) (hsrcdst : src ≠ dst) (i : Fin n) :
    (colAddRight M src dst c)[i][src] = M[i][src] := by
  rw [colAddRight_getElem]
  simp [hsrcdst]

/-- The source column is unchanged by `colAdd M src dst c` when `src ≠ dst`. -/
@[simp, grind =] theorem col_colAdd_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin m} (c : R) (hsrcdst : src ≠ dst) :
    col (colAdd M src dst c) src = col M src :=
  col_colAdd_of_ne M src c hsrcdst

/-- The source column is unchanged by `colAddRight M src dst c` when
`src ≠ dst`. -/
@[simp, grind =] theorem col_colAddRight_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin m} (c : R) (hsrcdst : src ≠ dst) :
    col (colAddRight M src dst c) src = col M src :=
  col_colAddRight_of_ne M src c hsrcdst

end Matrix

end Hex
