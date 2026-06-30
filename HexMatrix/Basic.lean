/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.ListShim

public section

/-!
Core dense matrix definitions for `hex-matrix`.

This module models matrices as `Vector (Vector R m) n` and provides the
basic executable operations needed by later linear-algebra algorithms:
row/column accessors, zero and identity matrices, dot products,
matrix-vector multiplication, matrix-matrix multiplication, and norm-squared
helpers.
-/
namespace Hex

universe u

/-- Dense `n × m` matrices over `R`, represented as vectors of rows.

Opaque one-field structure: consumers must go through the API
(`ofFn`/`ofRows`/`rows`/`getRow`/`M[(i, j)]`) and never read `data` or
pattern-match the representation, which is an internal detail. -/
structure Matrix (R : Type u) (n m : Nat) where
  ofRows ::
  /-- Implementation detail. Use `Matrix.rows`, never this projection. -/
  data : Vector (Vector R m) n
deriving DecidableEq, BEq

/-- Display a matrix through its rows (the same output as the underlying
nested vectors), so the representation flip does not change `#eval`/`Repr`
output and never exposes the `data` projection. -/
instance [Repr R] : Repr (Matrix R n m) where
  reprPrec M prec := reprPrec M.data prec

end Hex

namespace Vector

/-- Dot product of two vectors. -/
@[expose]
def dotProduct [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  (List.finRange n).foldl (fun acc i => acc + u[i] * v[i]) 0

/-- Squared Euclidean norm of a vector. -/
@[expose]
def normSq [Mul R] [Add R] [OfNat R 0] (v : Vector R n) : R :=
  dotProduct v v

/-- The standard basis vector with value `1` at index `i` and `0` elsewhere. -/
@[expose]
def unit (R : Type u) [Zero R] [One R] (i : Fin n) : Vector R n :=
  Vector.ofFn fun j => if i = j then One.one else Zero.zero

/-- Entry formula for a standard basis vector. -/
@[grind =] theorem getElem_unit [Zero R] [One R] (i j : Fin n) :
    (unit R i)[j] = if i = j then One.one else Zero.zero := by
  simp [unit]

end Vector

namespace Hex

namespace Matrix

/-!
## Opaque API boundary

`Matrix` is accessed only through the functions below: entries via
`M[(i, j)]` (the `GetElem` instances), rows via `getRow`/`rows`, and
construction via `ofFn`/`ofRows`. Consumers must not pattern-match the
representation or rely on `Matrix` being defeq to nested `Vector`s; the
representation is an internal detail that will change. -/

/-- The rows of a matrix. The sanctioned row accessor. -/
@[inline, expose] def rows (M : Matrix R n m) : Vector (Vector R m) n := M.data

@[simp, grind =] theorem rows_ofRows (v : Vector (Vector R m) n) : (ofRows v).rows = v := rfl

/-- Two matrices are equal when their rows are equal. -/
@[ext] theorem ext {M N : Matrix R n m} (h : M.rows = N.rows) : M = N := by
  cases M; cases N; exact congrArg ofRows h

/-- Entry access by a `Nat × Nat` index. -/
instance : GetElem (Matrix R n m) (Nat × Nat) R (fun _ p => p.1 < n ∧ p.2 < m) where
  getElem M p h := (M.rows[p.1]'h.1)[p.2]'h.2

/-- Entry access by a `Fin n × Fin m` index. -/
instance : GetElem (Matrix R n m) (Fin n × Fin m) R (fun _ _ => True) where
  getElem M p _ := (M.rows[p.1])[p.2]

/-- The `i`-th row of a matrix. -/
@[inline, expose] def getRow (M : Matrix R n m) (i : Fin n) : Vector R m :=
  M.rows[i]

/-- The `i`-th row of `ofRows v` is `v[i]`. -/
@[simp, grind =] theorem getRow_ofRows (v : Vector (Vector R m) n) (i : Fin n) :
    getRow (ofRows v) i = v[i] := rfl

/-- Entry access (`Fin` index) unfolds to a row lookup. The simp-normal form is
the pair access `M[(i, j)]`, so this is neither a `simp` nor a `grind` lemma
(it would flood `grind` with representation facts). -/
theorem getElem_rows (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    M[(i, j)] = (M.rows[i])[j] := rfl

/-- Entry access for a matrix built from its rows. -/
@[simp, grind =] theorem getElem_ofRows (v : Vector (Vector R m) n) (i : Fin n) (j : Fin m) :
    (ofRows v)[(i, j)] = (v[i])[j] := rfl

/-- `Nat`-pair entry access unfolds to a row lookup. Unlike the `Fin`-pair
`getElem_rows`, the `Nat`-pair form only appears at concrete literal indices, so
normalizing it to `.rows` is safe and lets `grind`/`simp` line it up with the
`Fin`-indexed form. -/
@[simp] theorem getElem_pair_nat (M : Matrix R n m) (p : Nat × Nat)
    (h : p.1 < n ∧ p.2 < m) : M[p]'h = (M.rows[p.1]'h.1)[p.2]'h.2 := rfl

/-- Entry access through a selected row. -/
@[simp, grind =] theorem getRow_getElem (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    (getRow M i)[j] = M[(i, j)] := rfl

/-- Build a matrix from an entry function. -/
@[expose]
def ofFn (f : Fin n → Fin m → R) : Matrix R n m :=
  ofRows <| Vector.ofFn fun i => Vector.ofFn fun j => f i j

/-- The rows of `ofFn f`. -/
@[simp, grind =] theorem rows_ofFn (f : Fin n → Fin m → R) :
    (ofFn f).rows = Vector.ofFn fun i => Vector.ofFn fun j => f i j := rfl

/-- Entry access for a matrix built from an entry function. -/
@[simp, grind =] theorem getElem_ofFn (f : Fin n → Fin m → R) (i : Fin n) (j : Fin m) :
    (ofFn f)[(i, j)] = f i j := by
  rw [getElem_rows]; simp [ofFn]

/-- The `i`-th row of `ofFn f` is the row function `Vector.ofFn (f i)`. -/
@[simp, grind =] theorem getRow_ofFn (f : Fin n → Fin m → R) (i : Fin n) :
    getRow (ofFn f) i = Vector.ofFn (fun j => f i j) := by
  simp [getRow, ofFn]

/-- The `i`-th row of a matrix (alias of `getRow`). -/
@[inline, expose] def row (M : Matrix R n m) (i : Fin n) : Vector R m :=
  getRow M i

/-- Entry access for a selected matrix row. -/
@[grind =] theorem getElem_row (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    (row M i)[j] = M[(i, j)] := by
  rfl

/-- Two matrices are equal when they agree entrywise. -/
theorem ext_getElem {M N : Matrix R n m}
    (h : ∀ (i : Fin n) (j : Fin m), M[(i, j)] = N[(i, j)]) : M = N := by
  apply ext
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  exact h ⟨i, hi⟩ ⟨j, hj⟩

/-- The `j`-th column of a matrix. -/
@[expose]
def col (M : Matrix R n m) (j : Fin m) : Vector R n :=
  Vector.ofFn fun i => M[(i, j)]

/-- Entry access for a selected matrix column. -/
@[simp, grind =] theorem getElem_col (M : Matrix R n m) (j : Fin m) (i : Fin n) :
    (col M j)[i] = M[(i, j)] := by
  simp [col]

/-- Replace row `dst` of `M` with the vector `v`. Linear in `M`: the matrix is
destructured so the backing store is updated in place when `M` is uniquely
referenced. -/
@[expose]
def setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨d.set dst v⟩

@[simp, grind =] theorem rows_setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v).rows = M.rows.set dst v := by cases M; rfl

/-- Reading back the replaced row `dst` of `setRow M dst v` yields `v`. -/
@[grind =] theorem getRow_setRow_self (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    getRow (setRow M dst v) dst = v := by
  simp [getRow]

/-- Replacing row `dst` leaves every other row unchanged. -/
@[grind =] theorem getRow_setRow_ne (M : Matrix R n m) (dst r : Fin n) (v : Vector R m)
    (h : r ≠ dst) :
    getRow (setRow M dst v) r = getRow M r := by
  have hval : dst.val ≠ r.val := fun hval => h (Fin.ext hval.symm)
  simp only [getRow, rows_setRow]
  exact Vector.getElem_set_ne (xs := M.rows) (x := v) dst.isLt r.isLt hval

/-- Row read through `setRow`, by cases on the row index. -/
@[grind =] theorem getRow_setRow (M : Matrix R n m) (dst r : Fin n) (v : Vector R m) :
    getRow (setRow M dst v) r = if r = dst then v else getRow M r := by
  by_cases h : r = dst
  · subst h; simp [getRow_setRow_self]
  · rw [if_neg h, getRow_setRow_ne M dst r v h]

/-- Entry read through `setRow`, by cases on the row index. -/
@[grind =] theorem getElem_setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m)
    (r : Fin n) (c : Fin m) :
    (setRow M dst v)[(r, c)] = if r = dst then v[c] else M[(r, c)] := by
  rw [getElem_rows, ← getRow, getRow_setRow]
  by_cases h : r = dst <;> simp [h, getRow, getElem_rows]

/-- Replace column `dst` of `M` with the entry function `v`. -/
@[expose]
def setCol (M : Matrix R n m) (dst : Fin m) (v : Fin n → R) : Matrix R n m :=
  ofFn fun r c => if c = dst then v r else M[(r, c)]

/-- Entrywise characterization of `setCol`: the destination column is read from
the replacement function and every other column is read from `M`. -/
@[simp, grind =] theorem getElem_setCol (M : Matrix R n m) (dst : Fin m) (v : Fin n → R)
    (r : Fin n) (c : Fin m) :
    (setCol M dst v)[(r, c)] = if c = dst then v r else M[(r, c)] := by
  simp [setCol]

/-- Replacing a column by itself leaves the matrix unchanged. -/
@[simp] theorem setCol_self (M : Matrix R n m) (dst : Fin m) :
    setCol M dst (fun r => M[(r, dst)]) = M := by
  apply ext_getElem
  intro r c
  rw [getElem_setCol]
  by_cases hc' : c = dst
  · rw [if_pos hc', hc']
  · rw [if_neg hc']

/-- The transpose of a dense matrix. -/
@[expose]
def transpose (M : Matrix R n m) : Matrix R m n :=
  ofFn fun i j => M[(j, i)]

/-- Entry access for the transpose of a dense matrix. -/
@[simp, grind =] theorem getElem_transpose (M : Matrix R n m) (i : Fin m) (j : Fin n) :
    (transpose M)[(i, j)] = M[(j, i)] := by
  simp [transpose]

/-- Transposing a dense matrix twice returns the original matrix. -/
@[simp, grind =] theorem transpose_transpose (M : Matrix R n m) :
    transpose (transpose M) = M := by
  apply ext_getElem
  intro i j
  simp

/-- The all-zero matrix. -/
@[expose]
protected def zero (n m : Nat) [OfNat R 0] : Matrix R n m :=
  ofFn fun _ _ => 0

instance [OfNat R 0] : Zero (Matrix R n m) where
  zero := Matrix.zero n m

/-- The identity matrix. -/
@[expose]
protected def identity (n : Nat) [OfNat R 0] [OfNat R 1] : Matrix R n n :=
  ofFn fun i j => if i = j then 1 else 0

/-- Multiply a matrix by a column vector. -/
@[expose]
def mulVec [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (v : Vector R m) :
    Vector R n :=
  Vector.ofFn fun i => (row M i).dotProduct v

/-- Multiply two matrices. -/
@[expose]
def mul [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  ofFn fun i j => (row M i).dotProduct (col N j)

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Vector R m) (Vector R n) where
  hMul := mulVec

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Matrix R m k) (Matrix R n k) where
  hMul := mul

/-- Homogeneous multiplication on square matrices, agreeing with the
heterogeneous `HMul`. This is the `Mul` instance Mathlib's `Semiring`/`Ring`
structures build on; see `HexMatrixMathlib`. -/
instance [Mul R] [Add R] [OfNat R 0] : Mul (Matrix R n n) where
  mul := mul

/-- Entry characterization for matrix-vector multiplication. -/
@[grind =] theorem getElem_mulVec [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (v : Vector R m) (i : Fin n) :
    (M * v)[i] = (row M i).dotProduct v := by
  show (mulVec M v)[i] = (row M i).dotProduct v
  simp [mulVec]

/-- Entry characterization for matrix multiplication. -/
@[grind =] theorem getElem_mul [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (i : Fin n) (j : Fin k) :
    (M * N)[(i, j)] = (row M i).dotProduct (col N j) := by
  show (mul M N)[(i, j)] = (row M i).dotProduct (col N j)
  rw [mul, getElem_ofFn]

/-- The identity matrix entry function: `(identity n)[(i, j)] = 1` if `i = j`, else `0`. -/
@[grind =] theorem getElem_identity [OfNat R 0] [OfNat R 1] {n : Nat} (i j : Fin n) :
    (Matrix.identity (R := R) n)[(i, j)] = if i = j then (1 : R) else 0 := by
  simp [Matrix.identity, ofFn]

/-- The identity matrix is its own transpose. -/
@[simp, grind =] theorem transpose_identity [OfNat R 0] [OfNat R 1] {n : Nat} :
    Matrix.transpose (Matrix.identity (R := R) n) = Matrix.identity n := by
  apply ext_getElem
  intro i j
  rw [getElem_transpose, getElem_identity, getElem_identity]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij.symm]
  · rw [if_neg hij, if_neg (fun h => hij h.symm)]

end Matrix
end Hex
