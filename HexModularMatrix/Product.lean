/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Row
public import HexMatrix.MatrixAlgebra

public section

namespace Hex.Matrix.Word

variable {p : Nat} [ZMod64.Bounds p]

/-- A monomorphic modular dot product with an unboxed word accumulator. -/
def dot (a b : Vector (ZMod64 p) n) (k : Nat) (s : ZMod64 p) : ZMod64 p :=
  if h : k < n then dot a b (k + 1) (s + a[k] * b[k]) else s
termination_by n - k

theorem dot_loop (a b : Vector (ZMod64 p) n) (k : Nat) (s : ZMod64 p) :
    dot a b k s = Fin.foldl.loop n (fun acc i => acc + a[i] * b[i]) s k := by
  rw [dot, Fin.foldl.loop]
  split
  · exact dot_loop a b (k + 1) _
  · rfl
termination_by n - k

theorem dot_eq (a b : Vector (ZMod64 p) n) : dot a b 0 0 = a.dotProduct b := by
  rw [dot_loop]
  change Fin.foldl n _ _ = _
  rw [Fin.foldl_eq_finRange_foldl]
  rfl

/-- Multiply cached rows by the columns of a right-hand side. -/
def mulRows (rows : Vector (Vector (ZMod64 p) m) n) (B : Matrix (ZMod64 p) m k) :
    Matrix (ZMod64 p) n k :=
  let cols := Vector.ofFn B.col
  Matrix.ofFn fun i j => dot rows[i] cols[j] 0 0

/-- Cache each row and column once, then run specialised dot products. -/
@[expose]
def mul (A : Matrix (ZMod64 p) n m) (B : Matrix (ZMod64 p) m k) : Matrix (ZMod64 p) n k :=
  mulRows (Vector.ofFn A.row) B

theorem mul_eq (A : Matrix (ZMod64 p) n m) (B : Matrix (ZMod64 p) m k) : mul A B = A * B := by
  apply ext_getElem
  intro i j
  unfold mul mulRows
  rw [getElem_ofFn, getElem_mul]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, dot_eq]

end Hex.Matrix.Word

namespace Hex.Matrix.Sparse

/-- Cache nonzero column indices for each integer row. -/
def support (A : Matrix Int n m) : Vector (List (Fin m)) n :=
  Vector.ofFn fun i => (List.finRange m).filter fun j => A[(i, j)] != 0

/-- Multiply using a precomputed support, shared by every lifting digit. -/
def mul (A : Matrix Int n m) (indices : Vector (List (Fin m)) n)
    (B : Matrix Int m k) : Matrix Int n k :=
  Matrix.ofFn fun i j => indices[i].foldl (fun s t => s + A[(i, t)] * B[(t, j)]) 0

theorem mul_eq (A : Matrix Int n m) (B : Matrix Int m k) :
    mul A (support A) B = A * B := by
  apply ext_getElem
  intro i j
  unfold mul
  rw [getElem_ofFn, getElem_mul]
  simp only [support, Vector.dotProduct, getElem_row, getElem_col]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, List.foldl_filter,
    getElem_pair_eq_nested]
  congr 1
  funext s t
  split <;> simp_all

end Hex.Matrix.Sparse
