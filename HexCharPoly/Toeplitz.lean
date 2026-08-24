/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix

public section

/-!
The lower-triangular Toeplitz multiplication used by one
Samuelson--Berkowitz step.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} [Lean.Grind.CommRing R]

/-- Multiply the `(k+2) x (k+1)` lower-triangular Toeplitz matrix whose first
column is `t` by `v`.  The entry in row `i` and column `l` is `t[i-l]` when
`l <= i`, and zero otherwise. -/
@[expose]
def toeplitzMulVec {k : Nat} (t : Vector R (k + 2)) (v : Vector R (k + 1)) :
    Vector R (k + 2) :=
  Hex.Vector.ofFn' fun i =>
    (List.finRange (k + 1)).foldl (fun acc l =>
      if h : l.val ≤ i.val then
        acc + t[(⟨i.val - l.val, by omega⟩ : Fin (k + 2))] * v[l]
      else
        acc) 0

/-- Entry formula for `toeplitzMulVec`. -/
@[simp, grind =]
theorem getElem_toeplitzMulVec {k : Nat} (t : Vector R (k + 2))
    (v : Vector R (k + 1)) (i : Fin (k + 2)) :
    (toeplitzMulVec t v)[i] =
      (List.finRange (k + 1)).foldl (fun acc l =>
        if h : l.val ≤ i.val then
          acc + t[(⟨i.val - l.val, by omega⟩ : Fin (k + 2))] * v[l]
        else
          acc) 0 := by
  simp [toeplitzMulVec]

/-- Row zero of a lower-triangular Toeplitz product contains only its first
column term. -/
@[simp, grind =]
theorem getElem_toeplitzMulVec_zero {k : Nat} (t : Vector R (k + 2))
    (v : Vector R (k + 1)) :
    (toeplitzMulVec t v)[(0 : Fin (k + 2))] =
      t[(0 : Fin (k + 2))] * v[(0 : Fin (k + 1))] := by
  rw [getElem_toeplitzMulVec, List.finRange_succ]
  simp [List.foldl_map, Fin.succ_ne_zero, List.foldl_const_step]
  grind

/-- Row one of the first (`k = 0`) Toeplitz step has only the first-column
term. -/
@[simp, grind =]
theorem getElem_toeplitzMulVec_one_base (t : Vector R 2) (v : Vector R 1) :
    (toeplitzMulVec t v)[(1 : Fin 2)] = t[(1 : Fin 2)] * v[(0 : Fin 1)] := by
  simp [toeplitzMulVec, List.finRange_succ]
  grind

/-- Proof-irrelevance-friendly form of `getElem_toeplitzMulVec_one_base`. -/
theorem getElem_toeplitzMulVec_one_base_of_val (t : Vector R 2) (v : Vector R 1)
    (i : Fin 2) (hi : i.val = 1) :
    (toeplitzMulVec t v)[i] = t[(1 : Fin 2)] * v[(0 : Fin 1)] := by
  have heq : i = (1 : Fin 2) := Fin.ext hi
  subst i
  exact getElem_toeplitzMulVec_one_base t v

/-- From the second Toeplitz step onward, row one has exactly its first two
lower-triangular terms. -/
@[simp, grind =]
theorem getElem_toeplitzMulVec_one_succ {k : Nat} (t : Vector R (k + 3))
    (v : Vector R (k + 2)) :
    (toeplitzMulVec t v)[(1 : Fin (k + 3))] =
      t[(1 : Fin (k + 3))] * v[(0 : Fin (k + 2))] +
        t[(0 : Fin (k + 3))] * v[(1 : Fin (k + 2))] := by
  rw [getElem_toeplitzMulVec, List.finRange_succ, List.foldl_cons,
    List.foldl_map, List.finRange_succ, List.foldl_cons, List.foldl_map]
  simp [List.foldl_const_step]
  grind

/-- Proof-irrelevance-friendly form of `getElem_toeplitzMulVec_one_succ`. -/
theorem getElem_toeplitzMulVec_one_succ_of_val {k : Nat} (t : Vector R (k + 3))
    (v : Vector R (k + 2)) (i : Fin (k + 3)) (hi : i.val = 1) :
    (toeplitzMulVec t v)[i] =
      t[(1 : Fin (k + 3))] * v[(0 : Fin (k + 2))] +
        t[(0 : Fin (k + 3))] * v[(1 : Fin (k + 2))] := by
  have heq : i = (1 : Fin (k + 3)) := Fin.ext hi
  subst i
  exact getElem_toeplitzMulVec_one_succ t v

end Hex.Matrix
