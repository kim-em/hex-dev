import HexMatrixMathlib.Basic
import HexMatrixMathlib.Determinant.DesnanotJacobi
import HexMatrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Determinant bridge theorems for `hex-matrix-mathlib`.

This module relates the executable Leibniz-formula determinant on `Hex.Matrix`
to Mathlib's determinant on function-based matrices. The supporting lemmas keep
the permutation-indexed product surface in a form that downstream proofs can
rewrite through `matrixEquiv` directly.
-/

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n : Nat}

namespace PermutationVector

private theorem get_injective_of_nodup
    {perm : Vector (Fin n) n} (hnodup : perm.toList.Nodup) :
    Function.Injective fun i : Fin n => perm[i] := by
  intro i j hij
  have hi : i.val < perm.toList.length := by
    simp [Vector.length_toList]
  have hj : j.val < perm.toList.length := by
    simp [Vector.length_toList]
  have hget :
      perm.toList[i.val]'hi = perm.toList[j.val]'hj := by
    simpa [Vector.getElem_toList] using hij
  exact Fin.ext ((hnodup.getElem_inj_iff).mp hget)

/-- Convert a Hex permutation vector into the corresponding Mathlib permutation. -/
noncomputable def toPerm (perm : Vector (Fin n) n)
    (hnodup : perm.toList.Nodup) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i : Fin n => perm[i])
    ⟨get_injective_of_nodup hnodup,
      Finite.surjective_of_injective (get_injective_of_nodup hnodup)⟩

@[simp]
theorem toPerm_apply (perm : Vector (Fin n) n)
    (hnodup : perm.toList.Nodup) (i : Fin n) :
    toPerm perm hnodup i = perm[i] := by
  rfl

theorem toPerm_injective :
    Function.Injective
      (fun p : {perm : Vector (Fin n) n // perm.toList.Nodup} =>
        toPerm p.1 p.2) := by
  intro p q hpq
  apply Subtype.ext
  apply Vector.ext
  intro i hi
  exact congrFun (congrArg Equiv.toFun hpq) ⟨i, hi⟩

private theorem vectorOfPerm_toList (σ : Equiv.Perm (Fin n)) :
    (Vector.ofFn fun i : Fin n => σ i).toList =
      (List.finRange n).map fun i : Fin n => σ i := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro i hi₁ hi₂
    simp [Vector.getElem_toList]

private theorem vectorOfPerm_nodup (σ : Equiv.Perm (Fin n)) :
    (Vector.ofFn fun i : Fin n => σ i).toList.Nodup := by
  rw [vectorOfPerm_toList]
  exact List.Nodup.map σ.injective (List.nodup_finRange n)

theorem toPerm_vectorOfPerm (σ : Equiv.Perm (Fin n)) :
    toPerm (Vector.ofFn fun i : Fin n => σ i) (vectorOfPerm_nodup σ) = σ := by
  ext i
  simp [toPerm]

/-- Hex permutation vectors converted to Mathlib permutations, with proofs attached. -/
noncomputable def equivs (n : Nat) : List (Equiv.Perm (Fin n)) :=
  (Hex.Matrix.permutationVectors n).attach.map fun perm =>
    toPerm perm.1 (Hex.Matrix.permutationVectors_nodup perm.2)

theorem equivs_complete (σ : Equiv.Perm (Fin n)) :
    σ ∈ equivs n := by
  let perm : Vector (Fin n) n := Vector.ofFn fun i : Fin n => σ i
  have hnodup : perm.toList.Nodup := vectorOfPerm_nodup σ
  have hmem : perm ∈ Hex.Matrix.permutationVectors n :=
    Hex.Matrix.permutationVectors_complete hnodup
  rw [equivs, List.mem_map]
  refine ⟨⟨perm, hmem⟩, List.mem_attach _ _, ?_⟩
  exact toPerm_vectorOfPerm σ

theorem equivs_nodup (n : Nat) :
    (equivs n).Nodup := by
  unfold equivs
  refine List.Nodup.map ?_ (List.Nodup.attach Hex.Matrix.permutationVectors_nodup_list)
  intro p q hpq
  apply Subtype.ext
  have hpq' :
      (⟨p.1, Hex.Matrix.permutationVectors_nodup p.2⟩ :
        {perm : Vector (Fin n) n // perm.toList.Nodup}) =
        ⟨q.1, Hex.Matrix.permutationVectors_nodup q.2⟩ := by
    exact toPerm_injective hpq
  exact congrArg (fun x : {perm : Vector (Fin n) n // perm.toList.Nodup} => x.1) hpq'

end PermutationVector

@[simp]
theorem detProduct_eq_matrixEquiv
    [Lean.Grind.Ring R] (M : Hex.Matrix R n n) (perm : Vector (Fin n) n) :
    Hex.Matrix.detProduct M perm =
      (List.finRange n).foldl (fun acc i => acc * matrixEquiv M i (perm[i])) 1 := by
  rfl

@[simp]
theorem detTerm_eq_matrixEquiv
    [Lean.Grind.Ring R] (M : Hex.Matrix R n n) (perm : Vector (Fin n) n) :
    Hex.Matrix.detTerm M perm =
      Hex.Matrix.detSign perm *
        (List.finRange n).foldl (fun acc i => acc * matrixEquiv M i (perm[i])) 1 := by
  rfl

theorem det_eq [CommRing R] (M : Hex.Matrix R n n) :
    Hex.Matrix.det M = Matrix.det (matrixEquiv M) := by
  sorry

/-- `matrixEquiv` sends Hex leading prefixes to Mathlib submatrices. -/
theorem matrixEquiv_leadingPrefix
    (M : Hex.Matrix R n n) (k : Nat) (hk : k ≤ n) :
    matrixEquiv (Hex.Matrix.leadingPrefix M k hk) =
      (matrixEquiv M).submatrix
        (fun r : Fin k => ⟨r.val, Nat.lt_of_lt_of_le r.isLt hk⟩)
        (fun c : Fin k => ⟨c.val, Nat.lt_of_lt_of_le c.isLt hk⟩) := by
  ext r c
  simp [Hex.Matrix.leadingPrefix, Hex.Matrix.ofFn]

/-- `matrixEquiv` sends Hex bordered Bareiss minors to Mathlib submatrices. -/
theorem matrixEquiv_borderedMinor
    (M : Hex.Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    matrixEquiv (Hex.Matrix.borderedMinor M k hk i j) =
      (matrixEquiv M).submatrix
        (fun r : Fin (k + 1) =>
          if hr : r.val < k then ⟨r.val, Nat.lt_trans hr hk⟩ else i)
        (fun c : Fin (k + 1) =>
          if hc : c.val < k then ⟨c.val, Nat.lt_trans hc hk⟩ else j) := by
  ext r c
  simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn]

/-- Determinant form of `matrixEquiv_leadingPrefix`. -/
theorem det_leadingPrefix_eq_submatrix_det [CommRing R]
    (M : Hex.Matrix R n n) (k : Nat) (hk : k ≤ n) :
    Hex.Matrix.det (Hex.Matrix.leadingPrefix M k hk) =
      Matrix.det
        ((matrixEquiv M).submatrix
          (fun r : Fin k => ⟨r.val, Nat.lt_of_lt_of_le r.isLt hk⟩)
          (fun c : Fin k => ⟨c.val, Nat.lt_of_lt_of_le c.isLt hk⟩)) := by
  rw [det_eq, matrixEquiv_leadingPrefix]

/-- Determinant form of `matrixEquiv_borderedMinor`. -/
theorem det_borderedMinor_eq_submatrix_det [CommRing R]
    (M : Hex.Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    Hex.Matrix.det (Hex.Matrix.borderedMinor M k hk i j) =
      Matrix.det
        ((matrixEquiv M).submatrix
          (fun r : Fin (k + 1) =>
            if hr : r.val < k then ⟨r.val, Nat.lt_trans hr hk⟩ else i)
          (fun c : Fin (k + 1) =>
            if hc : c.val < k then ⟨c.val, Nat.lt_trans hc hk⟩ else j)) := by
  rw [det_eq, matrixEquiv_borderedMinor]

end HexMatrixMathlib
