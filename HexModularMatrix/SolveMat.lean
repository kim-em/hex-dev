/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Solve

public section

namespace Hex.Matrix
namespace Dixon

/-- Row-major vector for one common-denominator reconstruction. -/
@[expose] def flatten (M : Matrix Int n m) : Vector Int (n * m) :=
  Vector.ofFn fun k : Fin (n * m) =>
    M[((⟨k.val / m, row_of_lt k⟩ : Fin n), (⟨k.val % m, col_of_lt k⟩ : Fin m))]

/-- Restore the rectangular shape of reconstructed numerators. -/
@[expose] def unflatten (v : Vector Int (n * m)) : Matrix Int n m :=
  Matrix.ofFn fun i j => v[i.val * m + j.val]'(flatIdx_lt i.isLt j.isLt)

theorem unflatten_get (v : Vector Int (n * m)) (i : Fin n) (j : Fin m) :
    (unflatten v)[i][j] = v[i.val * m + j.val]'(flatIdx_lt i.isLt j.isLt) := by
  rw [unflatten, getElem_ofFn]

theorem flatten_get (M : Matrix Int n m) (i : Fin n) (j : Fin m) :
    (flatten M)[i.val * m + j.val]'(flatIdx_lt i.isLt j.isLt) = M[i][j] := by
  simp only [flatten, Vector.getElem_ofFn, flatIdx_div j.isLt, flatIdx_mod j.isLt,
    getElem_pair_eq_nested]

theorem unflatten_flatten (M : Matrix Int n m) : unflatten (flatten M) = M := by
  apply ext_getElem
  intro i j
  rw [unflatten_get, flatten_get]

/-- Maximum numerator bound over all right-hand sides. -/
def matrixBound (A : Matrix Int n n) (C : Matrix Int n m) : Nat :=
  Fin.foldl m (fun P j => max P (numeratorBound A (C.col j))) 0

def checkMat (A : Matrix Int n n) (C : Matrix Int n m) (y : Vector Int (n * m))
    (d : Int) : Option (Matrix Int n m × Int) :=
  if 0 < d then
    let (y, d) := normalise y d
    let X := unflatten y
    if A * X = d • C then some (X, d) else none
  else none

theorem checkMat_spec {A : Matrix Int n n} {C X : Matrix Int n m}
    {y : Vector Int (n * m)} {d e : Int} (h : checkMat A C y d = some (X, e)) :
    A * X = e • C ∧ 0 < e := by
  unfold checkMat at h
  split at h <;> try contradiction
  rename_i hd
  dsimp only at h
  split at h <;> try contradiction
  rename_i heq
  cases h
  exact ⟨heq, normalise_pos y d hd⟩

theorem checkMat_reduced {A : Matrix Int n n} {C X : Matrix Int n m}
    {y : Vector Int (n * m)} {d e : Int} (h : checkMat A C y d = some (X, e)) :
    ∀ g : Int, (∀ (i : Fin n) (j : Fin m), g ∣ X[i][j]) → g ∣ e → g ∣ 1 := by
  unfold checkMat at h
  split at h <;> try contradiction
  rename_i hd
  dsimp only at h
  split at h <;> try contradiction
  cases h
  intro g hg he
  apply normalise_reduced y d hd g ?_ he
  intro k
  have h := hg ⟨k.val / m, row_of_lt k⟩ ⟨k.val % m, col_of_lt k⟩
  rw [unflatten_get] at h
  simpa only [Nat.mul_comm (k.val / m) m, Nat.div_add_mod, Fin.getElem_fin] using h

end Dixon

/-- Lift all right-hand sides together and reconstruct one common denominator. -/
def solveMatWith (D : Decomp n) (C : Matrix Int n m) : Option (Matrix Int n m × Int) := do
  let P := Dixon.matrixBound D.A C
  let Q := hadamardBound D.A
  let k := Dixon.digits D P Q
  let (y, d) ← Modular.ratReconVec? (Dixon.flatten (Dixon.liftMat D C k)) (D.p ^ k) P Q
  Dixon.checkMat D.A C y d

def solveMat? (A : Matrix Int n n) (C : Matrix Int n m) (fuel : Nat) :
    Option (Matrix Int n m × Int) := (decomp? A fuel).bind (solveMatWith · C)

theorem solveMatWith_spec {D : Decomp n} {C X : Matrix Int n m} {d : Int}
    (h : solveMatWith D C = some (X, d)) : D.A * X = d • C ∧ 0 < d := by
  obtain ⟨⟨y, e⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact Dixon.checkMat_spec h

theorem solveMatWith_reduced {D : Decomp n} {C X : Matrix Int n m} {d : Int}
    (h : solveMatWith D C = some (X, d)) :
    ∀ g : Int, (∀ (i : Fin n) (j : Fin m), g ∣ X[i][j]) → g ∣ d → g ∣ 1 := by
  obtain ⟨⟨y, e⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact Dixon.checkMat_reduced h

theorem solveMat?_spec {A : Matrix Int n n} {C X : Matrix Int n m} {fuel : Nat} {d : Int}
    (h : solveMat? A C fuel = some (X, d)) : A * X = d • C ∧ 0 < d := by
  obtain ⟨D, hD, hs⟩ := Option.bind_eq_some_iff.mp h
  have h := solveMatWith_spec hs
  rwa [decomp?_A hD] at h

/-- Nonsingularity makes any two rational matrix solutions equal. -/
theorem solveMat?_unique {A : Matrix Int n n} {C X Z : Matrix Int n m}
    {fuel : Nat} {d e : Int} (h : solveMat? A C fuel = some (X, d))
    (hA : det A ≠ 0) (hz : A * Z = e • C) (_he : 0 < e) : e • X = d • Z := by
  have hy := (solveMat?_spec h).1
  apply ext_getElem
  intro i j
  have hcol (c : Int) (M : Matrix Int n m) : (c • M).col j = c • M.col j := by
    apply Vector.ext
    intro k hk
    change ((c • M).col j)[(⟨k, hk⟩ : Fin n)] = (c • M.col j)[(⟨k, hk⟩ : Fin n)]
    rw [getElem_col, smul_getElem]
    simp only [Fin.getElem_fin, Vector.getElem_smul]
    change c • M[(⟨k, hk⟩ : Fin n)][j] = c • (M.col j)[(⟨k, hk⟩ : Fin n)]
    rw [getElem_col]
  have hmul (M : Matrix Int n m) : (A * M).col j = A * M.col j := by
    apply Vector.ext
    intro k hk
    change ((A * M).col j)[(⟨k, hk⟩ : Fin n)] = (A * M.col j)[(⟨k, hk⟩ : Fin n)]
    rw [getElem_col, getElem_mul, getElem_mulVec]
  have hy' := congrArg (fun M : Matrix Int n m => M.col j) hy
  have hz' := congrArg (fun M : Matrix Int n m => M.col j) hz
  rw [hmul, hcol] at hy' hz'
  have heq := Dixon.solution_unique hA hy' hz'
  have heq' := congrArg (fun v : Vector Int n => v[i]) heq
  simp only [Fin.getElem_fin, Vector.getElem_smul] at heq'
  change e • (X.col j)[i] = d • (Z.col j)[i] at heq'
  rw [getElem_col, getElem_col] at heq'
  rw [smul_getElem, smul_getElem]
  exact heq'

end Hex.Matrix
