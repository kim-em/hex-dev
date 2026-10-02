/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Kernel
import all HexModularMatrix.Rank
public import HexRankMathlib.Extension
public import Mathlib.LinearAlgebra.Dimension.Constructions

public section

/-! Integer rank and rational kernel correspondence, reusing hex-rank soundness. -/

namespace HexModularMatrixMathlib

open HexMatrixMathlib

variable {n m : Nat} {A : Hex.Matrix Int n m} {c : Hex.Matrix.RankCert Int n m}
    {K : Hex.Matrix.Kernel n m} {fuel : Nat}

/-- A checked integer rank certificate has Mathlib's rank. -/
theorem rank_eq (h : Hex.Matrix.checkRank A c = true) : (matrixEquiv A).rank = c.rank :=
  checkRank_sound h

/-- Both the modular certificate and integer fallback give Mathlib's rank. -/
theorem rankModular_eq (A : Hex.Matrix Int n m) :
    Hex.Matrix.rankModular A = (matrixEquiv A).rank := by
  unfold Hex.Matrix.rankModular
  split
  · exact (rank_eq (Hex.Matrix.rankCert?_check ‹_›)).symm
  · exact Rank.rank_eq A

/-- The rational columns represented by the integer numerator matrix. -/
noncomputable def kernelColumn (K : Hex.Matrix.Kernel n m) (j : Fin (m - K.cert.rank)) (i : Fin m) : ℚ :=
  (K.basis[i][j] : ℚ) / (K.cert.denom : ℚ)

/-- At free coordinates the rational columns form negative identity. -/
theorem kernelColumn_free (h : Hex.Matrix.kernel? A fuel = some K)
    (i j : Fin (m - K.cert.rank)) :
    kernelColumn K j K.freeCols[i] = if i = j then -1 else 0 := by
  have hd : (K.cert.denom : ℚ) ≠ 0 := by
    exact_mod_cast ((Hex.Matrix.checkRank_iff A K.cert).mp (Hex.Matrix.kernel?_check h)).1
  unfold kernelColumn
  rw [Hex.Matrix.kernel?_free h]
  by_cases hij : i = j <;> simp [hij, hd]

/-- Each represented rational column belongs to the kernel. -/
theorem kernelColumn_mem (h : Hex.Matrix.kernel? A fuel = some K)
    (j : Fin (m - K.cert.rank)) :
    kernelColumn K j ∈ LinearMap.ker
      (Matrix.mulVecLin ((matrixEquiv A).map (Int.castRingHom ℚ))) := by
  have hz := Hex.Matrix.kernel?_annihilate h
  have hm := congrArg matrixEquiv hz
  rw [matrixEquiv_mul] at hm
  change ((matrixEquiv A).map (Int.castRingHom ℚ)).mulVec (kernelColumn K j) = 0
  funext i
  have hi := congrFun (congrFun hm i) j
  have hi' : (∑ l, ((matrixEquiv A i l : ℤ) : ℚ) * ((matrixEquiv K.basis l j : ℤ) : ℚ)) = 0 := by
    have hi'' : ∑ l, matrixEquiv A i l * matrixEquiv K.basis l j = 0 := by
      change (matrixEquiv A * matrixEquiv K.basis) i j =
        matrixEquiv (0 : Hex.Matrix Int n (m - K.cert.rank)) i j at hi
      simpa only [Matrix.mul_apply, matrixEquiv_apply, Hex.Matrix.getElem_zero] using hi
    exact_mod_cast hi''
  simpa [Matrix.mulVec, dotProduct, kernelColumn, matrixEquiv_apply,
    ← mul_div_assoc, ← Finset.sum_div] using congrArg (fun x : ℚ => x / (K.cert.denom : ℚ)) hi'

/-- Free coordinates recover every coefficient in a zero linear combination. -/
theorem kernel_independent (h : Hex.Matrix.kernel? A fuel = some K) :
    LinearIndependent ℚ (kernelColumn K) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi := congrFun hg K.freeCols[i]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    kernelColumn_free h] at hi
  simpa using hi

/-- Annihilation and the certified rank account for the whole rational kernel. -/
theorem kernel_span (h : Hex.Matrix.kernel? A fuel = some K) :
    Submodule.span ℚ (Set.range (kernelColumn K)) =
      LinearMap.ker (Matrix.mulVecLin ((matrixEquiv A).map (Int.castRingHom ℚ))) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact kernelColumn_mem h j
  · rw [finrank_span_eq_card (kernel_independent h), Fintype.card_fin]
    have hr := checkRank_sound_map (Int.castRingHom ℚ) Int.cast_injective
      (Hex.Matrix.kernel?_check h)
    have hd := LinearMap.finrank_range_add_finrank_ker
      (Matrix.mulVecLin ((matrixEquiv A).map (Int.castRingHom ℚ)))
    change ((matrixEquiv A).map (Int.castRingHom ℚ)).rank + _ = _ at hd
    rw [hr, Module.finrank_pi, Fintype.card_fin] at hd
    omega

end HexModularMatrixMathlib
