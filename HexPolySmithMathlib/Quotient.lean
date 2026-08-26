/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmithMathlib.Chain
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Prod

public section

/-! The module decomposition supplied by the executable Smith basis. -/

namespace HexPolySmithMathlib

universe u

open Hex Hex.PolyMatrix Module
open scoped DirectSum

noncomputable section

private def coordinateIdeal {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) (j : Fin m) :
    Submodule (Polynomial F) (Polynomial F) :=
  if h : j.val < snfRank A then
    Ideal.span {(smithNormalForm A).a ⟨j.val, h⟩}
  else ⊥

private theorem mem_rowSpan_iff {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m)
    (x : Fin m → Polynomial F) :
    x ∈ Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A)) ↔
      ∀ j : Fin m, if h : j.val < snfRank A then
        (smithNormalForm A).a ⟨j.val, h⟩ ∣ (smithNormalForm A).bM.repr x j
      else (smithNormalForm A).bM.repr x j = 0 := by
  let S := smithNormalForm A
  constructor
  · intro hx j
    let y : Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A)) := ⟨x, hx⟩
    split
    case isTrue hj =>
      let i : Fin (snfRank A) := ⟨j.val, hj⟩
      have hfi : S.f i = j := by
        apply Fin.ext
        simp [S, i]
      change S.a i ∣ S.bM.repr x j
      refine ⟨S.bN.repr y i, ?_⟩
      simp only [← hfi]
      have he := S.repr_apply_embedding_eq_repr_smul y (i := i)
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at he
      exact he
    case isFalse hj =>
      apply S.repr_eq_zero_of_notMem_range y
      rintro ⟨i, hi⟩
      have hiv : i.val = j.val := by
        simpa [S] using congrArg Fin.val hi
      exact hj (hiv ▸ i.isLt)
  · intro hx
    have hdvd : ∀ i : Fin (snfRank A),
        S.a i ∣ S.bM.repr x (S.f i) := by
      intro i
      have hi : (S.f i).val < snfRank A := by
        simp [S]
      simpa [S] using hx (S.f i)
    choose c hc using hdvd
    let y : Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A)) :=
      ∑ i, c i • S.bN i
    have hxy : x = (y : Fin m → Polynomial F) := by
      apply S.bM.ext_elem
      intro j
      by_cases hj : j.val < snfRank A
      · let i : Fin (snfRank A) := ⟨j.val, hj⟩
        have hfi : S.f i = j := by
          apply Fin.ext
          simp [S, i]
        calc
          S.bM.repr x j = S.a i * c i := by simpa [hfi] using hc i
          _ = S.bN.repr (S.a i • y) i := by
            simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
            rw [show S.bN.repr y i = c i by
              change S.bN.repr (∑ k, c k • S.bN k) i = c i
              rw [S.bN.repr_sum_self]]
          _ = S.bM.repr y (S.f i) :=
            (S.repr_apply_embedding_eq_repr_smul y (i := i)).symm
          _ = S.bM.repr y j := by rw [hfi]
      · have hxj : S.bM.repr x j = 0 := by
          simpa [hj] using hx j
        rw [hxj]
        symm
        apply S.repr_eq_zero_of_notMem_range y
        rintro ⟨i, hi⟩
        have hiv : i.val = j.val := by
          simpa [S] using congrArg Fin.val hi
        exact hj (hiv ▸ i.isLt)
    rw [hxy]
    exact y.property

private theorem coordinateMap {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Submodule.map (smithNormalForm A).bM.equivFun.toLinearMap
        (Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A))) =
      Submodule.pi Set.univ (coordinateIdeal A) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A)) at hx
    have hx' := (mem_rowSpan_iff A x).1 hx
    rw [Submodule.mem_pi]
    intro j _
    change (smithNormalForm A).bM.repr x j ∈ coordinateIdeal A j
    unfold coordinateIdeal
    split
    case isTrue hj =>
      rw [Submodule.mem_span_singleton]
      have h := hx' j
      rw [_root_.dite_eq_left hj] at h
      rcases h with ⟨c, hc⟩
      exact ⟨c, by simpa [smul_eq_mul, mul_comm] using hc.symm⟩
    case isFalse hj =>
      have h := hx' j
      rw [_root_.dite_eq_right hj] at h
      simpa using h
  · intro hz
    refine ⟨(smithNormalForm A).bM.equivFun.symm z, ?_, ?_⟩
    · apply (mem_rowSpan_iff A
          ((smithNormalForm A).bM.equivFun.symm z)).2
      intro j
      have hzj := Submodule.mem_pi.mp hz j (Set.mem_univ j)
      unfold coordinateIdeal at hzj
      by_cases hj : j.val < snfRank A
      · rw [_root_.dite_eq_left hj] at hzj ⊢
        rw [Submodule.mem_span_singleton] at hzj
        rw [show (smithNormalForm A).bM.repr
          ((smithNormalForm A).bM.equivFun.symm z) j = z j from
            (smithNormalForm A).bM.coord_equivFun_symm j z]
        rcases hzj with ⟨c, hc⟩
        exact ⟨c, by simpa [smul_eq_mul, mul_comm] using hc.symm⟩
      · rw [_root_.dite_eq_right hj] at hzj ⊢
        rw [show (smithNormalForm A).bM.repr
          ((smithNormalForm A).bM.equivFun.symm z) j = z j from
            (smithNormalForm A).bM.coord_equivFun_symm j z]
        exact hzj
    · exact (smithNormalForm A).bM.equivFun.apply_symm_apply z

private def coordinateQuotientEquiv {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    ((Fin m → Polynomial F) ⧸
        Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A))) ≃ₗ[Polynomial F]
      ∀ j : Fin m, Polynomial F ⧸ coordinateIdeal A j :=
  (Submodule.Quotient.equiv _ _ (smithNormalForm A).bM.equivFun
      (coordinateMap A)).trans (Submodule.quotientPi (coordinateIdeal A))

private def splitFin {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Fin (snfRank A) ⊕ Fin (m - snfRank A) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (by
    have hm := (snfData_isSNF A).rank_le_m
    rw [← snfRank_eq A] at hm
    omega))

private def sumPiLinearEquiv {R : Type*} [CommRing R]
    {ι κ : Type*} (M : ι ⊕ κ → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    (∀ s, M s) ≃ₗ[R] ((∀ i, M (Sum.inl i)) × (∀ j, M (Sum.inr j))) where
  __ := Equiv.sumPiEquivProdPi M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def splitCoordinateEquiv {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    (∀ j : Fin m, Polynomial F ⧸ coordinateIdeal A j) ≃ₗ[Polynomial F]
      ((∀ i : Fin (snfRank A),
          Polynomial F ⧸ coordinateIdeal A (splitFin A (Sum.inl i))) ×
       (∀ j : Fin (m - snfRank A),
          Polynomial F ⧸ coordinateIdeal A (splitFin A (Sum.inr j)))) :=
  (LinearEquiv.piCongrLeft (Polynomial F)
      (fun j : Fin m => Polynomial F ⧸ coordinateIdeal A j) (splitFin A)).symm |>.trans
    (sumPiLinearEquiv (fun s =>
      Polynomial F ⧸ coordinateIdeal A (splitFin A s)))

private def torsionCoordinates {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    (∀ i : Fin (snfRank A),
        Polynomial F ⧸ coordinateIdeal A (splitFin A (Sum.inl i))) ≃ₗ[Polynomial F]
      (∀ i : Fin (snfRank A), Polynomial F ⧸
        Ideal.span {HexPolyMathlib.toPolynomial ((invariantFactors A)[i])}) :=
  LinearEquiv.piCongrRight fun i =>
    Submodule.quotEquivOfEq _ _ (by
      have hi : (splitFin A (Sum.inl i)).val < snfRank A := by
        simp [splitFin]
      unfold coordinateIdeal
      rw [_root_.dite_eq_left hi]
      rw [smithNormalForm_a]
      apply congrArg (fun p => Ideal.span
        {HexPolyMathlib.toPolynomial p})
      apply congrArg (fun k : Fin (snfRank A) => (invariantFactors A)[k])
      apply Fin.ext
      simp [splitFin])

private def freeCoordinates {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    (∀ j : Fin (m - snfRank A),
        Polynomial F ⧸ coordinateIdeal A (splitFin A (Sum.inr j))) ≃ₗ[Polynomial F]
      (Fin (m - snfRank A) → Polynomial F) :=
  LinearEquiv.piCongrRight fun j =>
    Submodule.quotEquivOfEqBot _ (by
      have hj : ¬ (splitFin A (Sum.inr j)).val < snfRank A := by
        simp [splitFin]
      unfold coordinateIdeal
      rw [_root_.dite_eq_right hj])

/-- The presented module is the product of its free part and its cyclic
torsion summands. -/
noncomputable def quotientEquiv {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    ((Fin m → Polynomial F) ⧸ Submodule.span (Polynomial F)
        (Set.range (polyMatrixEquiv A))) ≃ₗ[Polynomial F]
      (Fin (m - snfRank A) → Polynomial F) ×
        ⨁ i : Fin (snfRank A),
          Polynomial F ⧸ Ideal.span
            {HexPolyMathlib.toPolynomial ((invariantFactors A)[i])} :=
  (coordinateQuotientEquiv A).trans <| (splitCoordinateEquiv A).trans <|
    ((torsionCoordinates A).prodCongr (freeCoordinates A)).trans <|
      (LinearEquiv.prodComm (Polynomial F) _ _).trans <|
        (LinearEquiv.refl _ _).prodCongr
          (DirectSum.linearEquivFunOnFintype (Polynomial F) _ _).symm

end

end HexPolySmithMathlib
