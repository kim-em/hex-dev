/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Extension
public import Mathlib.LinearAlgebra.Matrix.Block

public section

namespace HexMatrixMathlib

/-- The two independent rank bounds: a unitriangular product after any ring
homomorphism, and exact row relations over the original domain. The modular
carrier may have zero divisors. -/
theorem rank_eq_of_modular {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Nontrivial S] {n m r : Nat}
    (φ : R →+* S) (A : Matrix (Fin n) (Fin m) R)
    (rows : Fin r → Fin n) (cols : Fin r → Fin m)
    (V : Matrix (Fin r) (Fin r) S) (d : R) (W : Matrix (Fin n) (Fin r) R)
    (hd : d ≠ 0)
    (htri : ((A.submatrix rows cols).map φ * V).IsLowerTriangular)
    (hdiag : ∀ i, ((A.submatrix rows cols).map φ * V) i i = 1)
    (hrows : d • A = W * A.submatrix rows id) : A.rank = r := by
  classical
  apply le_antisymm
  · calc
      A.rank = (d • A).rank :=
        (Matrix.rank_smul_of_mem_nonZeroDivisors A (mem_nonZeroDivisors_of_ne_zero hd)).symm
      _ = (W * A.submatrix rows id).rank := congrArg Matrix.rank hrows
      _ ≤ (A.submatrix rows id).rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin r) := Matrix.rank_le_card_height _
      _ = r := Fintype.card_fin r
  · have hdet : ((A.submatrix rows cols).map φ * V).det = 1 := by
      rw [Matrix.det_of_isLowerTriangular _ htri]
      simp [hdiag]
    have hB : (A.submatrix rows cols).det ≠ 0 := by
      intro hzero
      have hmap : ((A.submatrix rows cols).map φ).det = φ (A.submatrix rows cols).det :=
        (RingHom.map_det φ _).symm
      rw [Matrix.det_mul, hmap, hzero, map_zero, zero_mul] at hdet
      exact zero_ne_one hdet
    calc
      r = Fintype.card (Fin r) := (Fintype.card_fin r).symm
      _ = (A.submatrix rows cols).rank := (Matrix.rank_of_det_ne_zero hB).symm
      _ ≤ A.rank := Matrix.rank_submatrix_le _ _ _

/-- Extension along any injective ring homomorphism between domains preserves
matrix rank, including embeddings of integral orders in number fields. -/
theorem rank_map_of_injective {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] {n m : Nat} (φ : R →+* S)
    (hφ : Function.Injective φ) (A : Matrix (Fin n) (Fin m) R) :
    (A.map φ).rank = A.rank := by
  classical
  obtain ⟨c, hc⟩ := exists_rankCert (matrixEquiv.symm A)
  have h1 := checkRank_sound hc
  have h2 := checkRank_sound_map φ hφ hc
  simp only [Equiv.apply_symm_apply] at h1 h2
  exact h2.trans h1.symm

end HexMatrixMathlib
