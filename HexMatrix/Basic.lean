/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic

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

universe u v

/-- Dense `n × m` matrices over `R`. Opaque one-field structure wrapping the row
data; consumers go through `rows`/`getRow`/`ofRows`/`ofFn` and `M[i]` / `M[(i,j)]`,
never the `data` projection, so the representation can change later. -/
structure Matrix (R : Type u) (n m : Nat) where
  ofRows ::
  /-- Implementation detail — use `Matrix.rows`/`getRow`, never this projection. -/
  data : Vector (Vector R m) n
deriving DecidableEq, BEq

end Hex

namespace Vector

/-- Dot product of two vectors.

This `List.finRange` form is the reference definition the entry lemmas reason
about; crucially it kernel-reduces, so `#guard`/`decide` checks over
`dotProduct` (e.g. `memLattice` membership) stay evaluable — core `Fin.foldl`
does not reduce in the kernel. Compiled code runs the allocation-free
`Fin.foldl` loop `dotProductImpl` via the `@[csimp]` below. -/
@[expose]
def dotProduct [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  (List.finRange n).foldl (fun acc i => acc + u[i] * v[i]) 0

/-- Allocation-free implementation of `dotProduct`: a `Fin.foldl` loop that never
materializes the `List.finRange n` index list. Swapped in for compiled code by the
`@[csimp]` lemma; `dotProduct` remains the reference form for proofs. -/
@[expose]
def dotProductImpl [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  Fin.foldl n (fun acc i => acc + u[i] * v[i]) 0

@[csimp] theorem dotProduct_eq_impl : @dotProduct = @dotProductImpl := by
  funext R n iMul iAdd iZero u v
  rw [dotProduct, dotProductImpl, Fin.foldl_eq_finRange_foldl]

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

variable {R : Type u} {n m k : Nat}

/-- The rows of a matrix as a vector of row-vectors. The only sanctioned way to
observe the row data. -/
@[inline, expose] def rows (M : Matrix R n m) : Vector (Vector R m) n := M.data

/-- The `i`-th row of a matrix. -/
@[inline, expose] def getRow (M : Matrix R n m) (i : Fin n) : Vector R m := M.rows[i]

/-- Entry access by a `Nat × Nat` index. -/
instance : GetElem (Matrix R n m) (Nat × Nat) R (fun _ p => p.1 < n ∧ p.2 < m) where
  getElem M p h := (M.rows[p.1]'h.1)[p.2]'h.2

/-- Entry access by a `Fin n × Fin m` index. -/
instance : GetElem (Matrix R n m) (Fin n × Fin m) R (fun _ _ => True) where
  getElem M p _ := (M.rows[p.1])[p.2]

/-- Row access `M[i]` for `i : Fin n`. **Deliberately `noncomputable`**: for a
future flat (`Vector R (n*m)`) representation, materializing a whole row just to
read it — and especially `M[i][j]` to read one entry — is the wrong cost model.
This instance exists only so *proofs* may write `M[i]` / `M[i][j]`; executable
code must use the computable `getRow` for rows and `M[(i, j)]` (O(1)) for single
entries. Any compiled definition that reaches for `M[i]` will fail to compile,
which is the intended guard. -/
noncomputable instance : GetElem (Matrix R n m) (Fin n) (Vector R m) (fun _ _ => True) where
  getElem M i _ := getRow M i

/-- Row access by a `Nat` index. Also `noncomputable`; see the `Fin n` instance. -/
noncomputable instance : GetElem (Matrix R n m) Nat (Vector R m) (fun _ i => i < n) where
  getElem M i h := getRow M ⟨i, h⟩

@[simp, grind =] theorem rows_ofRows (v : Vector (Vector R m) n) : (ofRows v).rows = v := rfl

/-- Row access `M[i]` normalizes to the computable `getRow M i` (so `rows_*`
reduction lemmas fire on it in proofs). -/
@[simp, grind =] theorem getElem_eq_getRow (M : Matrix R n m) (i : Fin n) : M[i] = getRow M i := rfl

/-- `Nat`-indexed row access normalizes to `getRow`. -/
@[simp, grind =] theorem getElem_nat_eq_getRow (M : Matrix R n m) (i : Nat) (h : i < n) :
    M[i]'h = getRow M ⟨i, h⟩ := rfl

/-- `getRow` on `ofRows` reduces to the underlying vector. -/
@[simp, grind =] theorem getRow_ofRows (v : Vector (Vector R m) n) (i : Fin n) :
    getRow (ofRows v) i = v[i] := rfl

/-- The pair entry access (computable, O(1)) agrees with the nested row-then-element
form. The nested form is the simp-normal form the entry lemmas are stated in, so
proofs about the computable `M[(i, j)]` line up with the `M[i][j]` lemmas. -/
@[simp, grind =] theorem getElem_pair_eq_nested (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    M[(i, j)] = M[i][j] := rfl

/-- `Nat`-pair entry access, normalized to the row lookup (concrete-index form). -/
@[simp] theorem getElem_pair_nat (M : Matrix R n m) (p : Nat × Nat)
    (h : p.1 < n ∧ p.2 < m) : M[p]'h = (M.rows[p.1]'h.1)[p.2]'h.2 := rfl

/-- Two matrices are equal when their rows are equal. -/
@[ext] theorem ext {M N : Matrix R n m} (h : M.rows = N.rows) : M = N := by
  cases M; cases N; simp_all [rows]

/-- Two matrices are equal when they agree entrywise. -/
theorem ext_getElem {M N : Matrix R n m}
    (h : ∀ (i : Fin n) (j : Fin m), M[i][j] = N[i][j]) : M = N := by
  apply ext
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  exact h ⟨i, hi⟩ ⟨j, hj⟩

/-- Build a matrix from an entry function. -/
@[expose]
def ofFn (f : Fin n → Fin m → R) : Matrix R n m :=
  ofRows (Vector.ofFn fun i => Vector.ofFn fun j => f i j)

/-- Entry access for a matrix built from an entry function. -/
@[grind =] theorem getElem_ofFn (f : Fin n → Fin m → R) (i : Fin n) (j : Fin m) :
    (ofFn f)[i][j] = f i j := by
  simp [ofFn]

/-- The `i`-th row of a matrix. -/
@[expose]
def row (M : Matrix R n m) (i : Fin n) : Vector R m :=
  getRow M i

/-- Entry access for a selected matrix row. -/
@[grind =] theorem getElem_row (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    (row M i)[j] = M[i][j] := by
  rfl

/-- The `j`-th column of a matrix. -/
@[expose]
def col (M : Matrix R n m) (j : Fin m) : Vector R n :=
  Vector.ofFn fun i => M[(i, j)]

/-- Entry access for a selected matrix column. -/
@[grind =] theorem getElem_col (M : Matrix R n m) (j : Fin m) (i : Fin n) :
    (col M j)[i] = M[i][j] := by
  simp [col]

/-- Replace row `dst` of `M` with the vector `v`. Linear in `M`: destructuring
consumes `M`, so the backing store is updated in place when `M` is unique. -/
@[expose]
def setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨d.set dst v⟩

@[simp, grind =] theorem rows_setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v).rows = M.rows.set dst v := by cases M; rfl

/-- Reading back the replaced row `dst` of `setRow M dst v` yields `v`. -/
@[grind =] theorem setRow_get_self (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v)[dst] = v := by
  show getRow (setRow M dst v) dst = v
  simp [getRow]

/-- Replacing row `dst` leaves every other row unchanged. -/
theorem setRow_row_ne (M : Matrix R n m) (dst r : Fin n) (v : Vector R m)
    (h : r ≠ dst) :
    (setRow M dst v)[r] = M[r] := by
  have hval : dst.val ≠ r.val := fun hval => h (Fin.ext hval.symm)
  show getRow (setRow M dst v) r = getRow M r
  simp only [getRow, rows_setRow]
  exact Vector.getElem_set_ne (xs := M.rows) (x := v) dst.isLt r.isLt hval

/-- The transpose of a dense matrix. -/
@[expose]
def transpose (M : Matrix R n m) : Matrix R m n :=
  ofRows (Vector.ofFn fun j => col M j)

/-- Entry access for the transpose of a dense matrix. -/
@[grind =] theorem getElem_transpose (M : Matrix R n m) (i : Fin m) (j : Fin n) :
    (transpose M)[i][j] = M[j][i] := by
  simp [transpose, col]

/-- Transposing a dense matrix twice returns the original matrix. -/
@[simp, grind =] theorem transpose_transpose (M : Matrix R n m) :
    transpose (transpose M) = M := by
  ext i hi j hj
  show (transpose (transpose M))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin m)] =
    M[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin m)]
  rw [getElem_transpose, getElem_transpose]

/-- The all-zero matrix. -/
@[expose]
protected def zero (n m : Nat) [OfNat R 0] : Matrix R n m :=
  ofFn fun _ _ => 0

instance [OfNat R 0] : Zero (Matrix R n m) where
  zero := Matrix.zero n m

/-- Every entry of the zero matrix is `0`. -/
@[grind =] theorem getElem_zero [OfNat R 0] (i : Fin n) (j : Fin m) :
    (0 : Matrix R n m)[i][j] = 0 := by
  show (Matrix.zero n m)[i][j] = 0
  simp [Matrix.zero, ofFn]

/-- Every row of the zero matrix is the zero vector. -/
@[simp, grind =] theorem row_zero [OfNat R 0] (i : Fin n) :
    row (0 : Matrix R n m) i = Vector.ofFn fun _ => (0 : R) := by
  ext j hj
  show (row (0 : Matrix R n m) i)[(⟨j, hj⟩ : Fin m)] =
    (Vector.ofFn fun _ => (0 : R))[(⟨j, hj⟩ : Fin m)]
  rw [getElem_row, getElem_zero]
  simp

/-- Every column of the zero matrix is the zero vector. -/
@[simp, grind =] theorem col_zero [OfNat R 0] (j : Fin m) :
    col (0 : Matrix R n m) j = Vector.ofFn fun _ => (0 : R) := by
  ext i hi
  show (col (0 : Matrix R n m) j)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn fun _ => (0 : R))[(⟨i, hi⟩ : Fin n)]
  rw [getElem_col, getElem_zero]
  simp

/-- The identity matrix. -/
@[expose]
protected def identity (n : Nat) [OfNat R 0] [OfNat R 1] : Matrix R n n :=
  ofFn fun i j => if i = j then 1 else 0

/-- Entrywise matrix addition. -/
@[expose]
protected def add [Add R] (A B : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => A[(i, j)] + B[(i, j)]

instance [Add R] : Add (Matrix R n m) where
  add := Matrix.add

/-- Entrywise matrix negation. -/
@[expose]
protected def neg [Neg R] (A : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => -A[(i, j)]

instance [Neg R] : Neg (Matrix R n m) where
  neg := Matrix.neg

/-- Entrywise matrix subtraction. -/
@[expose]
protected def sub [Sub R] (A B : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => A[(i, j)] - B[(i, j)]

instance [Sub R] : Sub (Matrix R n m) where
  sub := Matrix.sub

/-- Entry access for matrix addition. -/
@[grind =] theorem getElem_add [Add R] (A B : Matrix R n m) (i : Fin n) (j : Fin m) :
    (A + B)[i][j] = A[i][j] + B[i][j] := by
  simp [show A + B = Matrix.add A B from rfl, Matrix.add, ofFn]

/-- Entry access for matrix negation. -/
@[grind =] theorem getElem_neg [Neg R] (A : Matrix R n m) (i : Fin n) (j : Fin m) :
    (-A)[i][j] = -A[i][j] := by
  simp [show -A = Matrix.neg A from rfl, Matrix.neg, ofFn]

/-- Entry access for matrix subtraction. -/
@[grind =] theorem getElem_sub [Sub R] (A B : Matrix R n m) (i : Fin n) (j : Fin m) :
    (A - B)[i][j] = A[i][j] - B[i][j] := by
  simp [show A - B = Matrix.sub A B from rfl, Matrix.sub, ofFn]

/-- Multiply a matrix by a column vector. -/
@[expose]
def mulVec [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (v : Vector R m) :
    Vector R n :=
  Vector.ofFn fun i => (row M i).dotProduct v

/-- The `j`-th row of `transpose M` is the `j`-th column of `M`. -/
@[simp, grind =] theorem row_transpose (M : Matrix R n m) (j : Fin m) :
    row (transpose M) j = col M j := by
  simp only [row, transpose, getRow_ofRows]
  grind

/-- The `i`-th column of `transpose M` is the `i`-th row of `M`. -/
@[simp, grind =] theorem col_transpose (M : Matrix R n m) (i : Fin n) :
    col (transpose M) i = row M i := by
  ext k hk
  show (col (transpose M) i)[(⟨k, hk⟩ : Fin m)] = (row M i)[(⟨k, hk⟩ : Fin m)]
  rw [getElem_col, getElem_transpose, getElem_row]

/--
Multiply two matrices, using the naive algorithm.

This reads each column `col N j` and is the reference definition the entry lemmas
reason about. Compiled code runs `mulImpl`, which transposes `N` once (via the
`@[csimp]` below) so each column is materialized a single time instead of being
rebuilt for every row of `M`.

We intend to provide Strassen-Winograd with a customizable algorithm for small sizes later.
-/
@[expose]
def mul [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  ofFn fun i j => (row M i).dotProduct (col N j)

/-- Cache-friendly implementation of `mul`: transpose `N` once (turning its columns
into contiguous rows), then take row-by-row dot products, so each column is built a
single time rather than once per row of `M`. Swapped in for compiled code by the
`@[csimp]` lemma; `mul` stays the column-based reference form for proofs. -/
@[expose]
def mulImpl [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  let Nt := N.transpose
  ofFn fun i j => (row M i).dotProduct (row Nt j)

@[csimp] theorem mul_eq_mulImpl : @mul = @mulImpl := by
  funext R n m k iMul iAdd iZero M N
  apply ext_getElem
  intro i j
  simp only [mul, mulImpl, getElem_ofFn, row, transpose, getRow_ofRows]
  grind

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

/-- Multiply a row vector by a matrix, `v * M`. Equal to `transpose M * v`; the
`j`-th entry is `∑ i, M[i][j] * v[i]`, the combination of the rows of `M` with
coefficients `v`. -/
@[expose]
def vecMul [Mul R] [Add R] [OfNat R 0] (v : Vector R n) (M : Matrix R n m) :
    Vector R m :=
  transpose M * v

instance [Mul R] [Add R] [OfNat R 0] : HMul (Vector R n) (Matrix R n m) (Vector R m) where
  hMul := vecMul

/-- Entry characterization for vector-matrix multiplication. -/
@[grind =] theorem getElem_vecMul [Mul R] [Add R] [OfNat R 0]
    (v : Vector R n) (M : Matrix R n m) (j : Fin m) :
    (v * M)[j] = (col M j).dotProduct v := by
  show (transpose M * v)[j] = (col M j).dotProduct v
  rw [getElem_mulVec, row_transpose]

/-- Entry characterization for matrix multiplication. -/
@[grind =] theorem getElem_mul [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (i : Fin n) (j : Fin k) :
    (M * N)[i][j] = (row M i).dotProduct (col N j) := by
  show (mul M N)[i][j] = (row M i).dotProduct (col N j)
  rw [mul, getElem_ofFn]

/-- Row `i` of `M * N` is the row of dot products of `row M i` against the
columns of `N`. -/
@[simp, grind =] theorem row_mul [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (i : Fin n) :
    row (M * N) i = Vector.ofFn fun j => (row M i).dotProduct (col N j) := by
  ext j hj
  show (row (M * N) i)[(⟨j, hj⟩ : Fin k)] =
    (Vector.ofFn fun j => (row M i).dotProduct (col N j))[(⟨j, hj⟩ : Fin k)]
  rw [getElem_row, getElem_mul]
  simp

/-- Column `j` of `M * N` is the column of dot products of the rows of `M`
against `col N j`. -/
@[simp, grind =] theorem col_mul [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (j : Fin k) :
    col (M * N) j = Vector.ofFn fun i => (row M i).dotProduct (col N j) := by
  ext i hi
  show (col (M * N) j)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn fun i => (row M i).dotProduct (col N j))[(⟨i, hi⟩ : Fin n)]
  rw [getElem_col, getElem_mul]
  simp

/-- The identity matrix entry function: `(identity n)[i][j] = 1` if `i = j`, else `0`. -/
@[grind =] theorem getElem_identity [OfNat R 0] [OfNat R 1] {n : Nat} (i j : Fin n) :
    (Matrix.identity (R := R) n)[i][j] = if i = j then (1 : R) else 0 := by
  simp [Matrix.identity, ofFn]

/-- The identity matrix is its own transpose. -/
@[simp, grind =] theorem transpose_identity [OfNat R 0] [OfNat R 1] {n : Nat} :
    Matrix.transpose (Matrix.identity (R := R) n) = Matrix.identity n := by
  ext i hi j hj
  show (Matrix.transpose (Matrix.identity (R := R) n))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)] =
    (Matrix.identity (R := R) n)[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)]
  rw [getElem_transpose, getElem_identity, getElem_identity]
  by_cases hij : (⟨i, hi⟩ : Fin n) = ⟨j, hj⟩
  · have hji : (⟨j, hj⟩ : Fin n) = ⟨i, hi⟩ := hij.symm
    rw [if_pos hij, if_pos hji]
  · have hji : (⟨j, hj⟩ : Fin n) ≠ ⟨i, hi⟩ := fun h => hij h.symm
    rw [if_neg hij, if_neg hji]

/-- Row `i` of the identity matrix has a `1` in position `i` and `0` elsewhere. -/
@[simp, grind =] theorem row_identity [OfNat R 0] [OfNat R 1] {n : Nat} (i : Fin n) :
    row (Matrix.identity (R := R) n) i = Vector.ofFn fun j => if i = j then (1 : R) else 0 := by
  ext j hj
  show (row (Matrix.identity (R := R) n) i)[(⟨j, hj⟩ : Fin n)] =
    (Vector.ofFn fun j => if i = j then (1 : R) else 0)[(⟨j, hj⟩ : Fin n)]
  rw [getElem_row, getElem_identity]
  simp

/-- Column `j` of the identity matrix has a `1` in position `j` and `0` elsewhere. -/
@[simp, grind =] theorem col_identity [OfNat R 0] [OfNat R 1] {n : Nat} (j : Fin n) :
    col (Matrix.identity (R := R) n) j = Vector.ofFn fun i => if i = j then (1 : R) else 0 := by
  ext i hi
  show (col (Matrix.identity (R := R) n) j)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn fun i => if i = j then (1 : R) else 0)[(⟨i, hi⟩ : Fin n)]
  rw [getElem_col, getElem_identity]
  simp

/-- In-place modification of row `i`. Linear in `M`: destructuring consumes `M`,
so when `M` is uniquely referenced the row is owned and `Vector.modify` updates
the backing store without copying. -/
@[expose, inline]
def modifyRow (M : Matrix R n m) (i : Nat) (f : Vector R m → Vector R m) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨d.modify i f⟩

/-- Swap rows `i` and `j`, in place when `M` is uniquely referenced. -/
@[expose, inline]
def swap (M : Matrix R n m) (i j : Nat) (hi : i < n := by get_elem_tactic)
    (hj : j < n := by get_elem_tactic) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨d.swap i j hi hj⟩

/-- Map a function over every row, in place when `M` is uniquely referenced. -/
@[expose, inline]
def mapRows (M : Matrix R n m) (f : Vector R m → Vector R m') : Matrix R n m' :=
  match M with
  | ⟨d⟩ => ⟨d.map f⟩

@[simp, grind =] theorem rows_modifyRow (M : Matrix R n m) (i : Nat)
    (f : Vector R m → Vector R m) : (modifyRow M i f).rows = M.rows.modify i f := by
  cases M; rfl

/-- Row `i` of `modifyRow M i f` is `f` applied to the old row `i`. -/
@[simp, grind =] theorem getRow_modifyRow_self (M : Matrix R n m) (i : Fin n)
    (f : Vector R m → Vector R m) : getRow (modifyRow M i.val f) i = f (getRow M i) := by
  simp only [getRow, rows_modifyRow, Fin.getElem_fin]
  rw [Vector.getElem_modify_self i.isLt]

/-- Rows other than `i` are unchanged by `modifyRow M i f`. -/
@[simp, grind =] theorem getRow_modifyRow_ne (M : Matrix R n m) (i : Nat)
    (f : Vector R m → Vector R m) (j : Fin n) (h : i ≠ j.val) :
    getRow (modifyRow M i f) j = getRow M j := by
  simp only [getRow, rows_modifyRow, Fin.getElem_fin]
  rw [Vector.getElem_modify_of_ne j.isLt h]

@[simp, grind =] theorem rows_swap (M : Matrix R n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    (M.swap i j hi hj).rows = M.rows.swap i j hi hj := by cases M; rfl

@[simp, grind =] theorem rows_mapRows (M : Matrix R n m) (f : Vector R m → Vector R m') :
    (M.mapRows f).rows = M.rows.map f := by cases M; rfl

/-- In-place indexed row map: replace row `i` by `f i (row i)` for every `i`,
threading `M` through a `Fin.foldl` of per-row `modifyRow`s. No intermediate
index list is allocated, and each row update is in place when `M` is uniquely
referenced (`Vector.modify` frees the row slot before applying `f`). This is the
shared engine for the in-place column and diagonal scatters (`setCol`,
`modifyCol`). -/
@[expose, inline]
def mapRowsIdx (M : Matrix R n m) (f : Fin n → Vector R m → Vector R m) : Matrix R n m :=
  Fin.foldl n (fun M i => M.modifyRow i.val (f i)) M

/-- The row data of `mapRowsIdx` is the corresponding `Fin.foldl` of `Vector.modify`s. -/
theorem rows_mapRowsIdx (M : Matrix R n m) (f : Fin n → Vector R m → Vector R m) :
    (mapRowsIdx M f).rows = Fin.foldl n (fun d i => d.modify i.val (f i)) M.rows := by
  unfold mapRowsIdx
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  generalize List.finRange n = xs
  induction xs generalizing M with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (M.modifyRow x.val (f x)), rows_modifyRow]

/-- Row `r` of `mapRowsIdx M f` is `f r` applied to the original row `r`. -/
@[simp, grind =] theorem getRow_mapRowsIdx (M : Matrix R n m)
    (f : Fin n → Vector R m → Vector R m) (r : Fin n) :
    getRow (mapRowsIdx M f) r = f r (getRow M r) := by
  simp only [getRow, rows_mapRowsIdx, Fin.getElem_fin]
  rw [Vector.getElem_finFoldl_modify]

/-- Entry `(r, c)` of `mapRowsIdx M f` reads from the updated row `f r (row r)`. -/
@[grind =] theorem getElem_mapRowsIdx (M : Matrix R n m)
    (f : Fin n → Vector R m → Vector R m) (r : Fin n) (c : Fin m) :
    (mapRowsIdx M f)[r][c] = (f r (getRow M r))[c] := by
  rw [getElem_eq_getRow, getRow_mapRowsIdx]

/-- Replace column `dst` of `M` with the entry function `v`. In-place via
`mapRowsIdx`: each row's single `dst` entry is set, reusing the freed row slot,
rather than rebuilding the whole matrix with `ofFn`. -/
@[expose]
def setCol (M : Matrix R n m) (dst : Fin m) (v : Fin n → R) : Matrix R n m :=
  mapRowsIdx M fun i row => row.set dst.val (v i) dst.isLt

/-- Entrywise characterization of `setCol`: the destination column is read from
the replacement function and every other column is read from `M`. -/
@[grind =] theorem getElem_setCol (M : Matrix R n m) (dst : Fin m) (v : Fin n → R)
    (r : Fin n) (c : Fin m) :
    (setCol M dst v)[r][c] = if c = dst then v r else M[r][c] := by
  rw [setCol, getElem_mapRowsIdx]
  simp only [Vector.getElem_set, getElem_eq_getRow, Fin.getElem_fin, Fin.ext_iff]
  grind

/-- Replacing a column by itself leaves the matrix unchanged. -/
@[simp] theorem setCol_self (M : Matrix R n m) (dst : Fin m) :
    setCol M dst (fun r => M[r][dst]) = M := by
  ext r hr c hc
  change (setCol M dst (fun r => M[r][dst]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin m)] =
    M[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin m)]
  rw [getElem_setCol]
  by_cases hc' : (⟨c, hc⟩ : Fin m) = dst
  · rw [if_pos hc']
    exact congrArg (fun c' : Fin m => M[(⟨r, hr⟩ : Fin n)][c']) hc'.symm
  · rw [if_neg hc']

/-- Transposing a row replacement is a column replacement on the transpose:
`setRow` on `M` corresponds to `setCol` on `Mᵀ`. This is the bridge the
determinant row laws route through to reuse the column laws. -/
theorem transpose_setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    transpose (setRow M dst v) = setCol (transpose M) dst (fun a => v[a]) := by
  apply ext_getElem
  intro a b
  rw [getElem_transpose, getElem_setCol]
  by_cases hb : b = dst
  · subst hb
    rw [show (setRow M b v)[b] = v from setRow_get_self M b v]
    simp
  · rw [if_neg hb, show (setRow M dst v)[b] = M[b] from setRow_row_ne M dst b v hb,
      getElem_transpose]

/-- In-place per-entry column modify: replace each entry `M[i][dst]` by
`g i M[i][dst]`, every other column unchanged. In-place via `mapRowsIdx`,
analogous to `setCol`. -/
@[expose]
def modifyCol (M : Matrix R n m) (dst : Fin m) (g : Fin n → R → R) : Matrix R n m :=
  mapRowsIdx M fun i row => row.modify dst.val (g i)

/-- Entrywise characterization of `modifyCol`. -/
@[grind =] theorem getElem_modifyCol (M : Matrix R n m) (dst : Fin m) (g : Fin n → R → R)
    (r : Fin n) (c : Fin m) :
    (modifyCol M dst g)[r][c] = if c = dst then g r (M[r][dst]) else M[r][c] := by
  rw [modifyCol, getElem_mapRowsIdx]
  simp only [Vector.getElem_modify, getElem_eq_getRow, Fin.getElem_fin, Fin.ext_iff]
  grind

/-- Entries outside column `dst` are unchanged by `modifyCol`. -/
theorem getElem_modifyCol_of_ne (M : Matrix R n m) (dst : Fin m) (g : Fin n → R → R)
    (r : Fin n) {c : Fin m} (h : c ≠ dst) :
    (modifyCol M dst g)[r][c] = M[r][c] := by
  rw [getElem_modifyCol, if_neg h]

/-- Scalar action on a matrix, delegated to the row data. The single sanctioned
`SMul` instance for matrices: the Mathlib bridge layer reuses it rather than
declaring its own, so there is no overlapping instance. Matches the action the
former `abbrev` inherited from `Vector`, so `c • M` keeps its previous meaning. -/
instance {S : Type v} [SMul S R] : SMul S (Matrix R n m) where
  smul c M := ofRows (c • M.data)

@[simp, grind =] theorem rows_smul {S : Type v} [SMul S R] (c : S) (M : Matrix R n m) :
    (c • M).rows = c • M.rows := rfl

/-- Scalar action pushes through a nested entry read. -/
@[simp, grind =] theorem smul_getElem {S : Type v} [SMul S R] (c : S) (M : Matrix R n m)
    (i : Fin n) (j : Fin m) : (c • M)[i][j] = c • M[i][j] := by
  simp only [getElem_eq_getRow, getRow, rows_smul, Fin.getElem_fin,
    Vector.getElem_smul]

end Matrix
end Hex
