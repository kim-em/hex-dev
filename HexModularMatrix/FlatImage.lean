/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Decomp
public import HexDeterminant.Triangular

public section

namespace Hex.Matrix.Dixon

variable {p : Nat} [ZMod64.Bounds p]

/-- Determinant-only elimination omits the inverse transform. -/
structure Echelon (A : Matrix (ZMod64 p) n n) where
  matrix : Matrix (ZMod64 p) n n
  factor : ZMod64 p
  det_eq : det A = factor * det matrix

variable {A : Matrix (ZMod64 p) n n}

def Echelon.swap (S : Echelon A) (i j : Fin n) : Echelon A where
  matrix := S.matrix.rowSwap i j
  factor := if i = j then S.factor else -S.factor
  det_eq := by
    by_cases h : i = j
    · subst j; simpa using S.det_eq
    · rw [ite_eq_right h, det_rowSwap _ _ _ h]
      have hd := S.det_eq
      grind only

def Echelon.clear (S : Echelon A) (j i : Fin n) (b : ZMod64 p) : Echelon A :=
  if h : j < i then
    { matrix := Word.add S.matrix j i (-S.matrix[(i, j)] * b)
      factor := S.factor
      det_eq := by
        rw [Word.add_eq, det_rowAdd _ _ _ _ (by omega)]
        exact S.det_eq }
  else S

def Echelon.forward (S : Echelon A) (k : Nat) : Option (Echelon A) :=
  if hk : k < n then do
    let j : Fin n := ⟨k, hk⟩
    let (i, b) ← pivot? S.matrix j
    let S := S.swap j i
    let S := Fin.foldl n (fun S i => S.clear j i b) S
    S.forward (k + 1)
  else some S
termination_by n - k

/-- A checked upper-triangular candidate gives the determinant image. -/
def flatDet? (A : Matrix (ZMod64 p) n n) : Option (ZMod64 p) := do
  let S ← (Echelon.mk A 1 (by simp) : Echelon A).forward 0
  if ∀ i j : Fin n, j.val < i.val → S.matrix[(i, j)] = 0 then
    return S.factor * Fin.foldl n (fun s i => s * S.matrix[(i, i)]) 1
  else none

theorem flatDet?_eq {A : Matrix (ZMod64 p) n n} {d : ZMod64 p}
    (h : flatDet? A = some d) : det A = d := by
  unfold flatDet? at h
  obtain ⟨S, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> try contradiction
  rename_i htri
  cases h
  rw [S.det_eq, det_upperTriangular_eq_finFoldl_diag S.matrix (by simpa only [getElem_pair_eq_nested] using htri)]
  simp only [getElem_pair_eq_nested]

end Hex.Matrix.Dixon
