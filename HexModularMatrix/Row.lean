/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ring
public import HexMatrix.ElementaryAlgebra

public section

namespace Hex.Matrix.Word

variable {p : Nat} [ZMod64.Bounds p]

/-- A specialised modular row addition, skipping zero multipliers. -/
@[inline]
def add (M : Matrix (ZMod64 p) n m) (src dst : Fin n) (c : ZMod64 p) :
    Matrix (ZMod64 p) n m :=
  if c = 0 then M else
    let row := M.getRow src
    M.modifyEntries dst.val fun k x => x + c * row[k]

theorem add_eq (M : Matrix (ZMod64 p) n m) (src dst : Fin n) (c : ZMod64 p) :
    add M src dst c = M.rowAdd src dst c := by
  unfold add
  split
  · rename_i h
    subst c
    apply ext_getElem
    intro i j
    rw [getElem_rowAdd]
    by_cases h : i = dst <;> simp_all
  · rfl

/-- A monomorphic row loop; modular arithmetic stays outside higher-order folds. -/
def addVec (src dst : Vector (ZMod64 p) m) (c : ZMod64 p) (k : Nat) :
    Vector (ZMod64 p) m :=
  if hk : k < m then
    let a := src[k]
    let dst := if a = 0 then dst else dst.set k (dst[k] + c * a)
    addVec src dst c (k + 1)
  else dst
termination_by m - k

theorem addVec_get (src dst : Vector (ZMod64 p) m) (c : ZMod64 p) (k : Nat) (i : Fin m) :
    (addVec src dst c k)[i] = if k ≤ i.val then dst[i] + c * src[i] else dst[i] := by
  rw [addVec]
  split
  · rename_i hk
    rw [addVec_get]
    by_cases ha : src[k] = 0
    · simp only [ha, ↓reduceIte]
      by_cases hi : i.val = k
      · have he : src[i] = 0 := by simpa only [Fin.getElem_fin, hi] using ha
        simp only [hi, Nat.le_refl, Nat.not_succ_le_self, ↓reduceIte, he]
        grind only
      · have he : (k + 1 ≤ i.val) = (k ≤ i.val) := propext (by omega)
        simp only [he]
    · simp only [ha, ↓reduceIte, Fin.getElem_fin, Vector.getElem_set]
      by_cases hi : k = i.val <;> by_cases hki : k + 1 ≤ i.val <;>
        by_cases hle : k ≤ i.val <;> simp_all <;> try omega
      split <;> split <;> first | omega | rfl
  · rename_i hk
    rw [ite_eq_right (by omega)]
termination_by m - k

/-- Read two rows once, update the owned destination vector, and write it back. -/
def addFast (M : Matrix (ZMod64 p) n m) (src dst : Fin n) (c : ZMod64 p) :
    Matrix (ZMod64 p) n m :=
  if c = 0 then M else M.setRow dst (addVec (M.getRow src) (M.getRow dst) c 0)

theorem addFast_eq (M : Matrix (ZMod64 p) n m) (src dst : Fin n) (c : ZMod64 p) :
    addFast M src dst c = M.rowAdd src dst c := by
  unfold addFast
  split
  · rename_i h; subst c; simp
  · apply ext_getElem
    intro i j
    rw [getElem_rowAdd]
    by_cases hi : i = dst
    · subst i
      rw [ite_eq_left rfl, setRow_get_self, addVec_get, ite_eq_left (Nat.zero_le _)]
      rfl
    · rw [ite_eq_right hi, setRow_row_ne _ _ _ _ hi]

@[csimp] theorem add_eq_fast : @add = @addFast := by
  funext n m p inst M src dst c
  exact (add_eq _ _ _ _).trans (addFast_eq _ _ _ _).symm

end Hex.Matrix.Word
