/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmithMathlib.Chain
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms

public section

/-! The quotient decomposition supplied by the executable Smith form. -/

namespace HexSmithMathlib

open Module
open scoped DirectSum

abbrev cyclic (A : Hex.Matrix Int n m)
    (i : Fin (Hex.Matrix.snfRank A)) :=
  ℤ ⧸ Ideal.span ({(Hex.Matrix.invariantFactors A)[i]} : Set ℤ)

noncomputable def freeProjection (A : Hex.Matrix Int n m) :
    (Fin m → ℤ) →ₗ[ℤ] (Fin (m - Hex.Matrix.snfRank A) → ℤ) :=
  LinearMap.pi fun i =>
    (ambientBasis A).coord
      ⟨Hex.Matrix.snfRank A + i, by
        have := Hex.Matrix.snfRank_le_m A
        omega⟩

noncomputable def torsionProjectionFun (A : Hex.Matrix Int n m) :
    (Fin m → ℤ) →ₗ[ℤ] ((i : Fin (Hex.Matrix.snfRank A)) → cyclic A i) :=
  LinearMap.pi fun i =>
    (Ideal.span ({(Hex.Matrix.invariantFactors A)[i]} : Set ℤ)).mkQ.comp
      ((ambientBasis A).coord
        (Fin.castLE (Hex.Matrix.snfRank_le_m A) i))

noncomputable def torsionProjection (A : Hex.Matrix Int n m) :
    (Fin m → ℤ) →ₗ[ℤ] ⨁ i : Fin (Hex.Matrix.snfRank A), cyclic A i :=
  (DirectSum.linearEquivFunOnFintype ℤ _ _).symm.toLinearMap.comp
    (torsionProjectionFun A)

noncomputable def presentationMap (A : Hex.Matrix Int n m) :
    (Fin m → ℤ) →ₗ[ℤ]
      (Fin (m - Hex.Matrix.snfRank A) → ℤ) ×
        ⨁ i : Fin (Hex.Matrix.snfRank A), cyclic A i :=
  (freeProjection A).prod (torsionProjection A)

private theorem coord_relationVector (A : Hex.Matrix Int n m)
    (i j : Fin (Hex.Matrix.snfRank A)) :
    (ambientBasis A).coord (Fin.castLE (Hex.Matrix.snfRank_le_m A) i)
        (relationVector A j : Fin m → ℤ) =
      if i = j then (Hex.Matrix.invariantFactors A)[j] else 0 := by
  rw [relationVector_eq, map_smul, Basis.coord_apply,
    Basis.repr_self_apply]
  simp only [Fin.castLE_inj, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [eq_comm]

private theorem coord_relationVector_tail (A : Hex.Matrix Int n m)
    (i : Fin (m - Hex.Matrix.snfRank A))
    (j : Fin (Hex.Matrix.snfRank A)) :
    (ambientBasis A).coord
        ⟨Hex.Matrix.snfRank A + i, by
          have := Hex.Matrix.snfRank_le_m A
          omega⟩ (relationVector A j : Fin m → ℤ) = 0 := by
  rw [relationVector_eq, map_smul, Basis.coord_apply,
    Basis.repr_self_apply]
  simp only [smul_eq_mul]
  have hne :
      (⟨Hex.Matrix.snfRank A + i, by
          have := Hex.Matrix.snfRank_le_m A
          omega⟩ : Fin m) ≠
        Fin.castLE (Hex.Matrix.snfRank_le_m A) j := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  have hne' :
      Fin.castLE (Hex.Matrix.snfRank_le_m A) j ≠
        (⟨Hex.Matrix.snfRank A + i, by
          have := Hex.Matrix.snfRank_le_m A
          omega⟩ : Fin m) :=
    Ne.symm hne
  simp [hne']

private theorem mem_rowSpan_iff (A : Hex.Matrix Int n m) (x : Fin m → ℤ) :
    x ∈ rowSpan A ↔
      (∀ i : Fin (Hex.Matrix.snfRank A),
        (Hex.Matrix.invariantFactors A)[i] ∣
          (ambientBasis A).coord
            (Fin.castLE (Hex.Matrix.snfRank_le_m A) i) x) ∧
      (∀ i : Fin (m - Hex.Matrix.snfRank A),
        (ambientBasis A).coord
          ⟨Hex.Matrix.snfRank A + i, by
            have := Hex.Matrix.snfRank_le_m A
            omega⟩ x = 0) := by
  classical
  rw [(relationBasis A).mem_submodule_iff']
  constructor
  · rintro ⟨c, rfl⟩
    constructor
    · intro i
      refine ⟨c i, ?_⟩
      rw [map_sum]
      simp only [map_smul, relationBasis_apply, coord_relationVector,
        smul_eq_mul]
      simp [mul_comm]
    · intro i
      rw [map_sum]
      simp only [map_smul, relationBasis_apply, coord_relationVector_tail,
        smul_zero, Finset.sum_const_zero]
  · rintro ⟨hhead, htail⟩
    choose c hc using hhead
    refine ⟨c, ?_⟩
    apply (ambientBasis A).ext_elem
    intro j
    change (ambientBasis A).coord j x =
      (ambientBasis A).coord j
        (∑ i, c i • ((relationBasis A i : rowSpan A) : Fin m → ℤ))
    by_cases hj : j.val < Hex.Matrix.snfRank A
    · let i : Fin (Hex.Matrix.snfRank A) := ⟨j.val, hj⟩
      have hji : j = Fin.castLE (Hex.Matrix.snfRank_le_m A) i := Fin.ext rfl
      rw [hji]
      rw [map_sum]
      simp only [map_smul, relationBasis_apply, coord_relationVector,
        smul_eq_mul]
      simp [hc i, mul_comm]
    · let i : Fin (m - Hex.Matrix.snfRank A) :=
        ⟨j.val - Hex.Matrix.snfRank A, by
          have := j.isLt
          omega⟩
      have hji : j = ⟨Hex.Matrix.snfRank A + i, by
          have := Hex.Matrix.snfRank_le_m A
          omega⟩ := Fin.ext (by simp [i]; omega)
      rw [hji]
      rw [map_sum]
      simp only [map_smul, relationBasis_apply, coord_relationVector_tail,
        smul_zero, Finset.sum_const_zero, htail i]

theorem ker_presentationMap (A : Hex.Matrix Int n m) :
    LinearMap.ker (presentationMap A) = rowSpan A := by
  ext x
  rw [LinearMap.mem_ker, mem_rowSpan_iff]
  constructor
  · intro hx
    have hfree : freeProjection A x = 0 := by
      simpa [presentationMap] using congrArg Prod.fst hx
    have htorsion : torsionProjection A x = 0 := by
      simpa [presentationMap] using congrArg Prod.snd hx
    constructor
    · intro i
      rw [← Ideal.mem_span_singleton]
      rw [← Submodule.Quotient.mk_eq_zero]
      have hfun := congrArg
        (DirectSum.linearEquivFunOnFintype ℤ
          (Fin (Hex.Matrix.snfRank A)) (cyclic A)) htorsion
      exact congrFun hfun i
    · intro i
      exact congrFun hfree i
  · rintro ⟨hhead, htail⟩
    change (freeProjection A x, torsionProjection A x) = 0
    apply Prod.ext
    · funext i
      exact htail i
    · apply (DirectSum.linearEquivFunOnFintype ℤ
        (Fin (Hex.Matrix.snfRank A)) (cyclic A)).injective
      funext i
      change (Ideal.span
        ({(Hex.Matrix.invariantFactors A)[i]} : Set ℤ)).mkQ
          ((ambientBasis A).coord
            (Fin.castLE (Hex.Matrix.snfRank_le_m A) i) x) = 0
      change (Submodule.Quotient.mk
        ((ambientBasis A).coord
          (Fin.castLE (Hex.Matrix.snfRank_le_m A) i) x) :
            ℤ ⧸ Ideal.span
              ({(Hex.Matrix.invariantFactors A)[i]} : Set ℤ)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      rw [Ideal.mem_span_singleton]
      exact hhead i

theorem presentationMap_surjective (A : Hex.Matrix Int n m) :
    Function.Surjective (presentationMap A) := by
  classical
  rintro ⟨f, t⟩
  let e := DirectSum.linearEquivFunOnFintype ℤ
    (Fin (Hex.Matrix.snfRank A)) (cyclic A)
  choose z hz using fun i =>
    Submodule.mkQ_surjective
      (Ideal.span ({(Hex.Matrix.invariantFactors A)[i]} : Set ℤ)) (e t i)
  let y : Fin m → ℤ := fun j =>
    if h : j.val < Hex.Matrix.snfRank A then z ⟨j.val, h⟩
    else f ⟨j.val - Hex.Matrix.snfRank A, by
      have := j.isLt
      omega⟩
  refine ⟨(ambientBasis A).equivFun.symm y, ?_⟩
  apply Prod.ext
  · funext i
    change (ambientBasis A).coord
      ⟨Hex.Matrix.snfRank A + i, by
        have := Hex.Matrix.snfRank_le_m A
        omega⟩ ((ambientBasis A).equivFun.symm y) = f i
    rw [Basis.coord_equivFun_symm]
    simp [y]
  · apply e.injective
    funext i
    change (Ideal.span
      ({(Hex.Matrix.invariantFactors A)[i]} : Set ℤ)).mkQ
        ((ambientBasis A).coord
          (Fin.castLE (Hex.Matrix.snfRank_le_m A) i)
          ((ambientBasis A).equivFun.symm y)) = e t i
    rw [Basis.coord_equivFun_symm]
    simp [y]
    simpa using hz i

/-- The cokernel of an integer matrix is the direct product of its free part
and the cyclic factors computed by the executable Smith algorithm. -/
@[expose]
noncomputable def quotientEquiv (A : Hex.Matrix Int n m) :
    ((Fin m → ℤ) ⧸ (rowSpan A)) ≃ₗ[ℤ]
      (Fin (m - Hex.Matrix.snfRank A) → ℤ) ×
        ⨁ i : Fin (Hex.Matrix.snfRank A),
          ℤ ⧸ Ideal.span ({(Hex.Matrix.invariantFactors A)[i]} : Set ℤ) :=
  (Submodule.quotEquivOfEq _ _ (ker_presentationMap A).symm).trans
    ((presentationMap A).quotKerEquivOfSurjective
      (presentationMap_surjective A))

end HexSmithMathlib
