module

public import Batteries.Data.List.Lemmas

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

/-- Dense `n × m` matrices over `R`, represented as vectors of rows. -/
@[expose]
abbrev Matrix (R : Type u) (n m : Nat) := Vector (Vector R m) n

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
def unit [Zero R] [One R] (i : Fin n) : Vector R n :=
  Vector.ofFn fun j => if i = j then One.one else Zero.zero

/-- Entry formula for a standard basis vector. -/
@[grind =] theorem unit_getElem [Zero R] [One R] (i j : Fin n) :
    (unit (R := R) i)[j] = if i = j then One.one else Zero.zero := by
  simp [unit]

end Vector

namespace Matrix

/-- Build a matrix from an entry function. -/
@[expose]
def ofFn (f : Fin n → Fin m → R) : Matrix R n m :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

/-- Entry access for a matrix built from an entry function. -/
@[grind =] theorem getElem_ofFn (f : Fin n → Fin m → R) (i : Fin n) (j : Fin m) :
    (ofFn f)[i][j] = f i j := by
  simp [ofFn]

/-- The `i`-th row of a matrix. -/
@[expose]
def row (M : Matrix R n m) (i : Fin n) : Vector R m :=
  M[i]

/-- Entry access for a selected matrix row. -/
@[grind =] theorem row_getElem (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    (row M i)[j] = M[i][j] := by
  rfl

/-- The `j`-th column of a matrix. -/
@[expose]
def col (M : Matrix R n m) (j : Fin m) : Vector R n :=
  Vector.ofFn fun i => M[i][j]

/-- Entry access for a selected matrix column. -/
@[grind =] theorem col_getElem (M : Matrix R n m) (j : Fin m) (i : Fin n) :
    (col M j)[i] = M[i][j] := by
  simp [col]

/-- Replace row `dst` of `M` with the vector `v`. -/
@[expose]
def setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) : Matrix R n m :=
  M.set dst v

/-- Reading back the replaced row `dst` of `setRow M dst v` yields `v`. -/
@[grind =] theorem setRow_get_self (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v)[dst] = v := by
  simp [setRow]

/-- Replacing row `dst` leaves every other row unchanged. -/
theorem setRow_row_ne (M : Matrix R n m) (dst r : Fin n) (v : Vector R m)
    (h : r ≠ dst) :
    (setRow M dst v)[r] = M[r] := by
  have hval : dst.val ≠ r.val := fun hval => h (Fin.ext hval.symm)
  exact Vector.getElem_set_ne (xs := M) (x := v) dst.isLt r.isLt hval

/-- Replace column `dst` of `M` with the entry function `v`. -/
@[expose]
def setCol (M : Matrix R n m) (dst : Fin m) (v : Fin n → R) : Matrix R n m :=
  ofFn fun r c => if c = dst then v r else M[r][c]

/-- Entrywise characterization of `setCol`: the destination column is read from
the replacement function and every other column is read from `M`. -/
@[grind =] theorem setCol_getElem (M : Matrix R n m) (dst : Fin m) (v : Fin n → R)
    (r : Fin n) (c : Fin m) :
    (setCol M dst v)[r][c] = if c = dst then v r else M[r][c] := by
  simp [setCol, ofFn]

/-- Replacing a column by itself leaves the matrix unchanged. -/
@[simp] theorem setCol_self (M : Matrix R n m) (dst : Fin m) :
    setCol M dst (fun r => M[r][dst]) = M := by
  ext r hr c hc
  change (setCol M dst (fun r => M[r][dst]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin m)] =
    M[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin m)]
  rw [setCol_getElem]
  by_cases hc' : (⟨c, hc⟩ : Fin m) = dst
  · rw [if_pos hc']
    exact congrArg (fun c' : Fin m => M[(⟨r, hr⟩ : Fin n)][c']) hc'.symm
  · rw [if_neg hc']

/-- The transpose of a dense matrix. -/
@[expose]
def transpose (M : Matrix R n m) : Matrix R m n :=
  Vector.ofFn fun j => col M j

/-- Entry access for the transpose of a dense matrix. -/
@[grind =] theorem transpose_getElem (M : Matrix R n m) (i : Fin m) (j : Fin n) :
    (transpose M)[i][j] = M[j][i] := by
  simp [transpose, col]

/-- Transposing a dense matrix twice returns the original matrix. -/
@[simp, grind =] theorem transpose_transpose (M : Matrix R n m) :
    transpose (transpose M) = M := by
  ext i hi j hj
  show (transpose (transpose M))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin m)] =
    M[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin m)]
  rw [transpose_getElem, transpose_getElem]

/-- The all-zero matrix. -/
@[expose]
protected def zero [OfNat R 0] : Matrix R n m :=
  ofFn fun _ _ => 0

instance [OfNat R 0] : Zero (Matrix R n m) where
  zero := Matrix.zero

/-- The identity matrix. -/
@[expose]
protected def identity [OfNat R 0] [OfNat R 1] : Matrix R n n :=
  ofFn fun i j => if i = j then 1 else 0

instance [OfNat R 0] [OfNat R 1] : One (Matrix R n n) where
  one := Matrix.identity

/-- Multiply a matrix by a column vector. -/
@[expose]
def mulVec [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (v : Vector R m) :
    Vector R n :=
  Vector.ofFn fun i => Hex.Vector.dotProduct (row M i) v

/-- Multiply two matrices. -/
@[expose]
def mul [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  ofFn fun i j => Hex.Vector.dotProduct (row M i) (col N j)

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Vector R m) (Vector R n) where
  hMul := mulVec

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Matrix R m k) (Matrix R n k) where
  hMul := mul

/-- Entry characterization for matrix-vector multiplication. -/
@[grind =] theorem mulVec_getElem [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (v : Vector R m) (i : Fin n) :
    (M * v)[i] = Hex.Vector.dotProduct (row M i) v := by
  show (mulVec M v)[i] = Hex.Vector.dotProduct (row M i) v
  simp [mulVec]

/-- Entry characterization for matrix multiplication. -/
@[grind =] theorem mul_getElem [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (i : Fin n) (j : Fin k) :
    (M * N)[i][j] = Hex.Vector.dotProduct (row M i) (col N j) := by
  show (mul M N)[i][j] = Hex.Vector.dotProduct (row M i) (col N j)
  rw [mul, getElem_ofFn]

/-- The identity matrix entry function: `1[i][j] = 1` if `i = j`, else `0`. -/
@[grind =] theorem getElem_one [OfNat R 0] [OfNat R 1] {n : Nat} (i j : Fin n) :
    (1 : Matrix R n n)[i][j] = if i = j then (1 : R) else 0 := by
  simp [show (1 : Matrix R n n) = Matrix.identity from rfl, Matrix.identity, ofFn]

/-- The identity matrix is its own transpose. -/
@[simp, grind =] theorem transpose_one [OfNat R 0] [OfNat R 1] {n : Nat} :
    Matrix.transpose (1 : Matrix R n n) = (1 : Matrix R n n) := by
  ext i hi j hj
  show (Matrix.transpose (1 : Matrix R n n))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)] =
    (1 : Matrix R n n)[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)]
  rw [transpose_getElem, getElem_one, getElem_one]
  by_cases hij : (⟨i, hi⟩ : Fin n) = ⟨j, hj⟩
  · have hji : (⟨j, hj⟩ : Fin n) = ⟨i, hi⟩ := hij.symm
    rw [if_pos hij, if_pos hji]
  · have hji : (⟨j, hj⟩ : Fin n) ≠ ⟨i, hi⟩ := fun h => hij h.symm
    rw [if_neg hij, if_neg hji]

end Matrix
end Hex
