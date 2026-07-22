/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic
public import HexBasic.Vector.Modify

public section

/-!
Elementary row and column operations.

This module contains the primitive executable row/column operations and their
entrywise access lemmas. Algebraic preservation theorems for multiplication and
inverse tracking live downstream in `HexRowReduce.RowEchelon`.
-/

namespace Hex

universe u

namespace Matrix

/-- Reading the `i`-th materialized row of `M.rows` is `getRow M i`. A stable
bridge (independent of the backing representation) used to route the entrywise
elementary-op proofs through the `.rows` characterization lemmas. -/
private theorem getRow_rows (M : Matrix R n m) (i : Fin n) : M.rows[i] = getRow M i := by
  simp [rows]

/-- `getRow` commutes with `mapRows`: row `r` of `M.mapRows f` is `f` applied to
row `r` of `M`. -/
private theorem getRow_mapRows {m' : Nat} (M : Matrix R n m)
    (f : Vector R m → Vector R m') (r : Fin n) :
    getRow (M.mapRows f) r = f (getRow M r) := by
  rw [← getRow_rows, rows_mapRows]
  simp

/-- Swap rows `i` and `j` in a dense matrix.

Implemented with `Vector.swap`, which updates the dense backing store in place
when `M` is uniquely referenced, rather than reading both rows and writing them
back through two `set`s (which forces a copy of the outer vector). -/
@[expose]
def rowSwap (M : Matrix R n m) (i j : Fin n) : Matrix R n m :=
  M.swap i j

/-- Read an entry of `rowSwap M i j` by cases on the row index: row `j`
returns the original row `i`, row `i` returns the original row `j`, and any
other row is unchanged. -/
theorem getElem_rowSwap (M : Matrix R n m) (i j r : Fin n) (k : Fin m) :
    (rowSwap M i j)[r][k] =
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] := by
  rw [rowSwap, getElem_eq_getRow, ← getRow_rows, rows_swap]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    simp_all [getElem_eq_getRow, Fin.ext_iff]

/-- Row `i` of `rowSwap M i j` is the original row `j`. -/
@[simp, grind =] theorem row_rowSwap_left (M : Matrix R n m) (i j : Fin n) :
    row (rowSwap M i j) i = row M j := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowSwap M i j) i)[kk] = (row M j)[kk]
  rw [getElem_row, getElem_row, getElem_rowSwap]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- Row `j` of `rowSwap M i j` is the original row `i`. -/
@[simp, grind =] theorem row_rowSwap_right (M : Matrix R n m) (i j : Fin n) :
    row (rowSwap M i j) j = row M i := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowSwap M i j) j)[kk] = (row M i)[kk]
  rw [getElem_row, getElem_row, getElem_rowSwap]
  simp

/-- Any row other than `i` and `j` is unchanged by `rowSwap M i j`. -/
theorem row_rowSwap_of_ne (M : Matrix R n m) {i j r : Fin n}
    (hri : r ≠ i) (hrj : r ≠ j) :
    row (rowSwap M i j) r = row M r := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowSwap M i j) r)[kk] = (row M r)[kk]
  rw [getElem_row, getElem_row, getElem_rowSwap]
  simp [hri, hrj]

/-- Diagonal-entry corollary of `getElem_rowSwap` for square matrices: when
`pivot ≠ k`, the `(k, k)` entry of `rowSwap M k pivot` is the original
`(pivot, k)` entry. -/
theorem rowSwap_diag_of_ne (M : Matrix R n n) {k pivot : Fin n}
    (h : pivot ≠ k) :
    (rowSwap M k pivot)[k][k] = M[pivot][k] := by
  rw [getElem_rowSwap]
  by_cases hkp : k = pivot
  · exact (h hkp.symm).elim
  · simp [hkp]

/-- Scale row `i` by `c`.

Per-entry in place via `modifyEntries`: each of the row's `m` entries is a
single `Vector.modify` of the flat backing buffer, with no row
materialization, when `M` is uniquely referenced. -/
@[expose]
def rowScale [Mul R] (M : Matrix R n m) (i : Fin n) (c : R) : Matrix R n m :=
  M.modifyEntries i.val fun _ x => c * x

/-- Read an entry of `rowScale M i c` by cases on the row index: row `i`
returns `c * M[i][k]`, any other row is unchanged. -/
theorem getElem_rowScale [Mul R] (M : Matrix R n m) (i r : Fin n) (c : R) (k : Fin m) :
    (rowScale M i c)[r][k] =
      if r = i then c * M[i][k] else M[r][k] := by
  rw [rowScale, getElem_modifyEntries]
  by_cases h : r = i
  · rw [if_pos (congrArg Fin.val h), if_pos h, h]
  · rw [if_neg (fun hv => h (Fin.ext hv)), if_neg h]

/-- Row `i` of `rowScale M i c` is the pointwise scalar multiple of row `i`. -/
@[simp, grind =] theorem row_rowScale_self [Mul R] (M : Matrix R n m) (i : Fin n) (c : R) :
    row (rowScale M i c) i = Vector.ofFn (fun k => c * M[i][k]) := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowScale M i c) i)[kk] = (Vector.ofFn (fun k => c * M[i][k]))[kk]
  rw [getElem_row, getElem_rowScale]
  simp

/-- Any row other than `i` is unchanged by `rowScale M i c`. -/
theorem row_rowScale_of_ne [Mul R] (M : Matrix R n m) {i r : Fin n} (c : R)
    (hri : r ≠ i) :
    row (rowScale M i c) r = row M r := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowScale M i c) r)[kk] = (row M r)[kk]
  rw [getElem_row, getElem_row, getElem_rowScale]
  simp [hri]

/-- Replace row `dst` by `row dst + c * row src`.

The source row is read once into `rsrc` (one contiguous copy, a borrowed read
taken before the write); the subsequent `modifyEntries` then holds the only
live reference to the buffer and updates the `dst` row's entries in place when
the runtime sees it uniquely referenced, with no destination-row
materialization. -/
@[expose]
def rowAdd [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin n) (c : R) : Matrix R n m :=
  let rsrc := getRow M src
  M.modifyEntries dst.val fun k x => x + c * rsrc[k]

/-- Read an entry of `rowAdd M src dst c` by cases on the row index: row `dst`
returns `M[dst][k] + c * M[src][k]`, any other row is unchanged. -/
theorem getElem_rowAdd [Mul R] [Add R]
    (M : Matrix R n m) (src dst r : Fin n) (c : R) (k : Fin m) :
    (rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  rw [rowAdd, getElem_modifyEntries]
  by_cases h : r = dst
  · rw [if_pos (congrArg Fin.val h), if_pos h, h]
    rw [show (getRow M src)[k] = M[src][k] from rfl]
  · rw [if_neg (fun hv => h (Fin.ext hv)), if_neg h]

/-- Source-row entries are unchanged by `rowAdd M src dst c` when `src ≠ dst`. -/
theorem getElem_rowAdd_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin n} (c : R) (hsrcdst : src ≠ dst) (k : Fin m) :
    (rowAdd M src dst c)[src][k] = M[src][k] := by
  rw [getElem_rowAdd]
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
  rw [getElem_row, getElem_rowAdd]
  simp

/-- Any row other than `dst` is unchanged by `rowAdd M src dst c`. -/
theorem row_rowAdd_of_ne [Mul R] [Add R]
    (M : Matrix R n m) (src : Fin n) {dst r : Fin n} (c : R)
    (hrdst : r ≠ dst) :
    row (rowAdd M src dst c) r = row M r := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowAdd M src dst c) r)[kk] = (row M r)[kk]
  rw [getElem_row, getElem_row, getElem_rowAdd]
  simp [hrdst]

/-- The source row is unchanged by `rowAdd M src dst c` when `src ≠ dst`. -/
@[simp, grind =] theorem row_rowAdd_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin n} (c : R) (hsrcdst : src ≠ dst) :
    row (rowAdd M src dst c) src = row M src := by
  exact row_rowAdd_of_ne M src c hsrcdst

/-- `rowScale` as a single `set` of the scaled row. The executable definition
goes through `Vector.modify` for in-place update; this is the value-level
characterization for callers that reason about the result as a `set`. -/
theorem rowScale_eq_set [Mul R] (M : Matrix R n m) (i : Fin n) (c : R) :
    rowScale M i c = setRow M i (Vector.ofFn fun k => c * M[i][k]) := by
  apply ext_getElem
  intro r k
  rw [getElem_rowScale]
  by_cases h : r = i
  · subst h
    rw [setRow_get_self]
    simp [Vector.getElem_ofFn]
  · rw [if_neg h, setRow_row_ne M i r _ h]

/-- `rowAdd` as a single `set` of the combined row. The executable definition
goes through `Vector.modify` for in-place update; this is the value-level
characterization for callers that reason about the result as a `set`. -/
theorem rowAdd_eq_set [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin n) (c : R) :
    rowAdd M src dst c =
      setRow M dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]) := by
  apply ext_getElem
  intro r k
  rw [getElem_rowAdd]
  by_cases h : r = dst
  · subst h
    rw [setRow_get_self]
    simp [Vector.getElem_ofFn]
  · rw [if_neg h, setRow_row_ne M dst r _ h]

/-- Column `k` of `rowSwap M i j` is column `k` of `M` with entries `i` and `j`
exchanged. -/
@[grind =] theorem col_rowSwap (M : Matrix R n m) (i j : Fin n) (k : Fin m) :
    col (rowSwap M i j) k =
      Vector.ofFn fun r => if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] := by
  ext r hr
  show (col (rowSwap M i j) k)[(⟨r, hr⟩ : Fin n)] =
    (Vector.ofFn fun r =>
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k])[(⟨r, hr⟩ : Fin n)]
  rw [getElem_col, getElem_rowSwap]
  simp

/-- Column `k` of `rowScale M i c` is column `k` of `M` with entry `i` scaled
by `c`. -/
@[grind =] theorem col_rowScale [Mul R] (M : Matrix R n m) (i : Fin n) (c : R) (k : Fin m) :
    col (rowScale M i c) k =
      Vector.ofFn fun r => if r = i then c * M[i][k] else M[r][k] := by
  ext r hr
  show (col (rowScale M i c) k)[(⟨r, hr⟩ : Fin n)] =
    (Vector.ofFn fun r => if r = i then c * M[i][k] else M[r][k])[(⟨r, hr⟩ : Fin n)]
  rw [getElem_col, getElem_rowScale]
  simp

/-- Column `k` of `rowAdd M src dst c` is column `k` of `M` with the `dst` entry
replaced by `M[dst][k] + c * M[src][k]`. -/
@[grind =] theorem col_rowAdd [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin n) (c : R) (k : Fin m) :
    col (rowAdd M src dst c) k =
      Vector.ofFn fun r => if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  ext r hr
  show (col (rowAdd M src dst c) k)[(⟨r, hr⟩ : Fin n)] =
    (Vector.ofFn fun r =>
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k])[(⟨r, hr⟩ : Fin n)]
  rw [getElem_col, getElem_rowAdd]
  simp

/-- Replace column `dst` by `col dst + c * col src`.

The source column is read once into `csrc` (one contiguous copy, a borrowed read
taken before the write); the subsequent `modifyCol` then holds the only live
reference to the buffer and updates the `dst` column entry of each row in place —
one single-entry `Vector.modify` of the flat buffer per row (`O(n)` writes
total) — when the runtime sees it uniquely referenced, with no row
materialization; the source column is first snapshotted into one owned `O(n)`
vector via borrowed reads. This replaces the former `mapRows` pass, which
materialized and reflattened every row. -/
@[expose]
def colAdd [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin m) (c : R) : Matrix R n m :=
  let csrc := M.col src
  M.modifyCol dst fun i x => x + c * csrc[i]

/-- Replace column `dst` by `col dst + col src * c`.

This is the right-scalar variant of `colAdd`, valid as a right-multiplication
wrapper over a noncommutative ring. Same flat per-entry column engine as
`colAdd`: read the source column once, then `modifyCol` the `dst` entries in
place. -/
@[expose]
def colAddRight [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin m) (c : R) :
    Matrix R n m :=
  let csrc := M.col src
  M.modifyCol dst fun i x => x + csrc[i] * c

/-- Read an entry of `colAdd M src dst c` by cases on the column index:
column `dst` returns `M[i][dst] + c * M[i][src]`, any other column is
unchanged. -/
theorem getElem_colAdd [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) (i : Fin n) (j : Fin m) :
    (colAdd M src dst c)[i][j] =
      if j = dst then M[i][j] + c * M[i][src] else M[i][j] := by
  rw [colAdd, getElem_modifyCol]
  by_cases hj : j = dst
  · rw [if_pos hj, if_pos hj, hj, getElem_col]
  · rw [if_neg hj, if_neg hj]

/-- Read an entry of `colAddRight M src dst c` by cases on the column index:
column `dst` returns `M[i][dst] + M[i][src] * c`, any other column is
unchanged. -/
theorem getElem_colAddRight [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) (i : Fin n) (j : Fin m) :
    (colAddRight M src dst c)[i][j] =
      if j = dst then M[i][j] + M[i][src] * c else M[i][j] := by
  rw [colAddRight, getElem_modifyCol]
  by_cases hj : j = dst
  · rw [if_pos hj, if_pos hj, hj, getElem_col]
  · rw [if_neg hj, if_neg hj]

/-- Column `dst` of `colAdd M src dst c` is the pointwise column combination. -/
@[simp, grind =] theorem col_colAdd_dst [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) :
    col (colAdd M src dst c) dst =
      Vector.ofFn (fun i => M[i][dst] + c * M[i][src]) := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show (col (colAdd M src dst c) dst)[ii] =
    (Vector.ofFn (fun i => M[i][dst] + c * M[i][src]))[ii]
  rw [getElem_col, getElem_colAdd]
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
  rw [getElem_col, getElem_colAddRight]
  simp

/-- Any column other than `dst` is unchanged by `colAdd M src dst c`. -/
theorem col_colAdd_of_ne [Mul R] [Add R]
    (M : Matrix R n m) (src : Fin m) {dst j : Fin m} (c : R)
    (hjdst : j ≠ dst) :
    col (colAdd M src dst c) j = col M j := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show (col (colAdd M src dst c) j)[ii] = (col M j)[ii]
  rw [getElem_col, getElem_col, getElem_colAdd]
  simp [hjdst]

/-- Any column other than `dst` is unchanged by `colAddRight M src dst c`. -/
theorem col_colAddRight_of_ne [Mul R] [Add R]
    (M : Matrix R n m) (src : Fin m) {dst j : Fin m} (c : R)
    (hjdst : j ≠ dst) :
    col (colAddRight M src dst c) j = col M j := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show (col (colAddRight M src dst c) j)[ii] = (col M j)[ii]
  rw [getElem_col, getElem_col, getElem_colAddRight]
  simp [hjdst]

/-- Source-column entries are unchanged by `colAdd M src dst c` when `src ≠ dst`. -/
theorem getElem_colAdd_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin m} (c : R) (hsrcdst : src ≠ dst) (i : Fin n) :
    (colAdd M src dst c)[i][src] = M[i][src] := by
  rw [getElem_colAdd]
  simp [hsrcdst]

/-- Source-column entries are unchanged by `colAddRight M src dst c` when
`src ≠ dst`. -/
theorem getElem_colAddRight_src_of_ne [Mul R] [Add R]
    (M : Matrix R n m) {src dst : Fin m} (c : R) (hsrcdst : src ≠ dst) (i : Fin n) :
    (colAddRight M src dst c)[i][src] = M[i][src] := by
  rw [getElem_colAddRight]
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

/-- Row `i` of `colAdd M src dst c` is row `i` of `M` with the `dst` entry
replaced by `M[i][dst] + c * M[i][src]`. -/
@[grind =] theorem row_colAdd [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) (i : Fin n) :
    row (colAdd M src dst c) i =
      Vector.ofFn fun j => if j = dst then M[i][j] + c * M[i][src] else M[i][j] := by
  ext j hj
  show (row (colAdd M src dst c) i)[(⟨j, hj⟩ : Fin m)] =
    (Vector.ofFn fun j =>
      if j = dst then M[i][j] + c * M[i][src] else M[i][j])[(⟨j, hj⟩ : Fin m)]
  rw [getElem_row, getElem_colAdd]
  simp

/-- Row `i` of `colAddRight M src dst c` is row `i` of `M` with the `dst` entry
replaced by `M[i][dst] + M[i][src] * c`. -/
@[grind =] theorem row_colAddRight [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) (i : Fin n) :
    row (colAddRight M src dst c) i =
      Vector.ofFn fun j => if j = dst then M[i][j] + M[i][src] * c else M[i][j] := by
  ext j hj
  show (row (colAddRight M src dst c) i)[(⟨j, hj⟩ : Fin m)] =
    (Vector.ofFn fun j =>
      if j = dst then M[i][j] + M[i][src] * c else M[i][j])[(⟨j, hj⟩ : Fin m)]
  rw [getElem_row, getElem_colAddRight]
  simp

/-- Swap columns `i` and `j` in a dense matrix.

Both columns are read once (two borrowed `O(n)` reads taken before the writes),
then written back with two `setCol` passes that update one flat-buffer entry per
row in place, reusing the backing store when `M` is uniquely referenced. This
replaces the former `mapRows` pass, which materialized and reflattened every row.
The column mirror of `rowSwap`. -/
@[expose]
def colSwap (M : Matrix R n m) (i j : Fin m) : Matrix R n m :=
  let ci := M.col i
  let cj := M.col j
  (M.setCol i fun r => cj[r]).setCol j fun r => ci[r]

/-- Read an entry of `colSwap M i j` by cases on the column index: column `j`
returns the original column `i`, column `i` returns the original column `j`, and
any other column is unchanged. -/
@[grind =] theorem getElem_colSwap (M : Matrix R n m) (i j : Fin m) (r : Fin n) (c : Fin m) :
    (colSwap M i j)[r][c] =
      if c = j then M[r][i] else if c = i then M[r][j] else M[r][c] := by
  rw [colSwap, getElem_setCol]
  by_cases hcj : c = j
  · rw [if_pos hcj, if_pos hcj, getElem_col]
  · rw [if_neg hcj, if_neg hcj, getElem_setCol]
    by_cases hci : c = i
    · rw [if_pos hci, if_pos hci, getElem_col]
    · rw [if_neg hci, if_neg hci]

/-- Column `i` of `colSwap M i j` is the original column `j`. -/
@[simp, grind =] theorem col_colSwap_left (M : Matrix R n m) (i j : Fin m) :
    col (colSwap M i j) i = col M j := by
  ext r hr
  show (col (colSwap M i j) i)[(⟨r, hr⟩ : Fin n)] = (col M j)[(⟨r, hr⟩ : Fin n)]
  rw [getElem_col, getElem_col, getElem_colSwap]
  by_cases hij : i = j <;> simp [hij]

/-- Column `j` of `colSwap M i j` is the original column `i`. -/
@[simp, grind =] theorem col_colSwap_right (M : Matrix R n m) (i j : Fin m) :
    col (colSwap M i j) j = col M i := by
  ext r hr
  show (col (colSwap M i j) j)[(⟨r, hr⟩ : Fin n)] = (col M i)[(⟨r, hr⟩ : Fin n)]
  rw [getElem_col, getElem_col, getElem_colSwap]
  simp

/-- Any column other than `i` and `j` is unchanged by `colSwap M i j`. -/
theorem col_colSwap_of_ne (M : Matrix R n m) {i j c : Fin m}
    (hci : c ≠ i) (hcj : c ≠ j) :
    col (colSwap M i j) c = col M c := by
  ext r hr
  show (col (colSwap M i j) c)[(⟨r, hr⟩ : Fin n)] = (col M c)[(⟨r, hr⟩ : Fin n)]
  rw [getElem_col, getElem_col, getElem_colSwap]
  simp [hci, hcj]

/-- Row `r` of `colSwap M i j` is row `r` of `M` with entries `i` and `j`
exchanged. -/
@[grind =] theorem row_colSwap (M : Matrix R n m) (i j : Fin m) (r : Fin n) :
    row (colSwap M i j) r =
      Vector.ofFn fun c => if c = j then M[r][i] else if c = i then M[r][j] else M[r][c] := by
  ext c hc
  show (row (colSwap M i j) r)[(⟨c, hc⟩ : Fin m)] =
    (Vector.ofFn fun c =>
      if c = j then M[r][i] else if c = i then M[r][j] else M[r][c])[(⟨c, hc⟩ : Fin m)]
  rw [getElem_row, getElem_colSwap]
  simp

/-- Transposing a column swap is the corresponding row swap on the transpose.
This is the bridge the determinant column laws route through. -/
theorem transpose_colSwap (M : Matrix R n m) (i j : Fin m) :
    transpose (colSwap M i j) = rowSwap (transpose M) i j := by
  apply ext_getElem
  intro a b
  rw [getElem_transpose, getElem_colSwap, getElem_rowSwap]
  simp only [getElem_transpose]

/-- Scale column `j` by `c`.

In-place per-entry column update via `modifyCol`: each row's single `j` entry is
multiplied by `c`, reusing the freed row slot when `M` is uniquely referenced.
The column mirror of `rowScale`. -/
@[expose]
def colScale [Mul R] (M : Matrix R n m) (j : Fin m) (c : R) : Matrix R n m :=
  M.modifyCol j fun _ x => c * x

/-- Read an entry of `colScale M j c` by cases on the column index: column `j`
returns `c * M[r][j]`, any other column is unchanged. -/
@[grind =] theorem getElem_colScale [Mul R] (M : Matrix R n m) (j : Fin m) (c : R)
    (r : Fin n) (k : Fin m) :
    (colScale M j c)[r][k] = if k = j then c * M[r][j] else M[r][k] := by
  rw [colScale, getElem_modifyCol]

/-- Column `j` of `colScale M j c` is the pointwise scalar multiple of column `j`. -/
@[simp, grind =] theorem col_colScale_self [Mul R] (M : Matrix R n m) (j : Fin m) (c : R) :
    col (colScale M j c) j = Vector.ofFn fun i => c * M[i][j] := by
  ext i hi
  show (col (colScale M j c) j)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn fun i => c * M[i][j])[(⟨i, hi⟩ : Fin n)]
  rw [getElem_col, getElem_colScale]
  simp

/-- Any column other than `j` is unchanged by `colScale M j c`. -/
theorem col_colScale_of_ne [Mul R] (M : Matrix R n m) {j k : Fin m} (c : R) (hkj : k ≠ j) :
    col (colScale M j c) k = col M k := by
  ext i hi
  show (col (colScale M j c) k)[(⟨i, hi⟩ : Fin n)] = (col M k)[(⟨i, hi⟩ : Fin n)]
  rw [getElem_col, getElem_col, getElem_colScale]
  simp [hkj]

/-- Row `r` of `colScale M j c` is row `r` of `M` with entry `j` scaled by `c`. -/
@[grind =] theorem row_colScale [Mul R] (M : Matrix R n m) (j : Fin m) (c : R) (r : Fin n) :
    row (colScale M j c) r =
      Vector.ofFn fun k => if k = j then c * M[r][j] else M[r][k] := by
  ext k hk
  show (row (colScale M j c) r)[(⟨k, hk⟩ : Fin m)] =
    (Vector.ofFn fun k => if k = j then c * M[r][j] else M[r][k])[(⟨k, hk⟩ : Fin m)]
  rw [getElem_row, getElem_colScale]
  simp

/-- Transposing a column scaling is the corresponding row scaling on the
transpose. -/
theorem transpose_colScale [Mul R] (M : Matrix R n m) (j : Fin m) (c : R) :
    transpose (colScale M j c) = rowScale (transpose M) j c := by
  apply ext_getElem
  intro a b
  rw [getElem_transpose, getElem_colScale, getElem_rowScale]
  simp only [getElem_transpose]

end Matrix

end Hex
