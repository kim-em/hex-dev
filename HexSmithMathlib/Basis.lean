/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith
public import HexHermiteMathlib.Span
public import Mathlib.LinearAlgebra.FreeModule.PID

public section

/-! The executable Smith transforms as an explicit Mathlib Smith basis. -/

namespace HexSmithMathlib

open HexMatrixMathlib
open HexHermiteMathlib
open Module

/-- The Mathlib row-span presentation associated to an executable matrix. -/
abbrev rowSpan (A : Hex.Matrix Int n m) : Submodule ℤ (Fin m → ℤ) :=
  Submodule.span ℤ (Set.range (_root_.Matrix.row (matrixEquiv A)))

/-- Right multiplication by the recorded inverse Smith transform, bundled as
an ambient linear equivalence. -/
@[expose]
noncomputable def rightEquiv (A : Hex.Matrix Int n m) :
    (Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ) := by
  let S := Hex.Matrix.snfData A
  refine LinearEquiv.ofLinearMap
    (_root_.Matrix.vecMulLinear (matrixEquiv S.rightInv))
    (_root_.Matrix.vecMulLinear (matrixEquiv S.right)) ?_ ?_
  · apply LinearMap.ext
    intro x
    change _root_.Matrix.vecMul
      (_root_.Matrix.vecMul x (matrixEquiv S.right))
      (matrixEquiv S.rightInv) = x
    rw [_root_.Matrix.vecMul_vecMul, ← matrixEquiv_mul,
      Hex.Matrix.snfData_right_inv A]
    have hone : matrixEquiv (Hex.Matrix.identity (R := Int) m) = 1 := matrixEquiv_one
    rw [hone, _root_.Matrix.vecMul_one]
  · apply LinearMap.ext
    intro x
    have hrev : S.rightInv * S.right = Hex.Matrix.identity m :=
      Hex.Matrix.mul_eq_one_comm (Hex.Matrix.snfData_right_inv A)
    change _root_.Matrix.vecMul
      (_root_.Matrix.vecMul x (matrixEquiv S.rightInv))
      (matrixEquiv S.right) = x
    rw [_root_.Matrix.vecMul_vecMul, ← matrixEquiv_mul, hrev]
    have hone : matrixEquiv (Hex.Matrix.identity (R := Int) m) = 1 := matrixEquiv_one
    rw [hone, _root_.Matrix.vecMul_one]

/-- Ambient Smith basis: the rows of the recorded right inverse. -/
@[expose]
noncomputable def ambientBasis (A : Hex.Matrix Int n m) :
    Basis (Fin m) ℤ (Fin m → ℤ) :=
  (Pi.basisFun ℤ (Fin m)).map (rightEquiv A)

@[simp]
theorem ambientBasis_apply (A : Hex.Matrix Int n m) (i : Fin m) :
    ambientBasis A i =
      vectorEquiv (Hex.Matrix.row (Hex.Matrix.snfData A).rightInv i) := by
  rw [ambientBasis, Basis.map_apply, Pi.basisFun_apply]
  change _root_.Matrix.vecMul (Pi.single i 1)
    (matrixEquiv (Hex.Matrix.snfData A).rightInv) = _
  rw [_root_.Matrix.single_one_vecMul, matrixEquiv_row]

/-- A relation basis vector, represented by the corresponding independent row
of the left-transformed presentation. -/
@[expose]
def relationVector (A : Hex.Matrix Int n m) (i : Fin (Hex.Matrix.snfRank A)) :
    rowSpan A := by
  let v := Hex.Matrix.row (Hex.Matrix.smithBasis A) i
  refine ⟨vectorEquiv v, ?_⟩
  rw [mem_span_iff]
  exact (Hex.Matrix.smithBasis_memLattice_iff A v).1
    (Hex.Matrix.row_memLattice (Hex.Matrix.smithBasis A) i)

theorem relationVector_eq (A : Hex.Matrix Int n m)
    (i : Fin (Hex.Matrix.snfRank A)) :
    (relationVector A i : Fin m → ℤ) =
      (Hex.Matrix.invariantFactors A)[i] •
        ambientBasis A (Fin.castLE (Hex.Matrix.snfRank_le_m A) i) := by
  let S := Hex.Matrix.snfData A
  let hS := Hex.Matrix.snfData_isSNF A
  let iS : Fin S.rank := Fin.cast (Hex.Matrix.snfRank_eq_data A) i
  let iN : Fin n := Fin.castLE hS.rank_le_n iS
  let iM : Fin m := Fin.castLE hS.rank_le_m iS
  have hiN : iN = Fin.castLE (Hex.Matrix.snfRank_le_n A) i := Fin.ext rfl
  have hiM : iM = Fin.castLE (Hex.Matrix.snfRank_le_m A) i := Fin.ext rfl
  have hdget := congrArg (fun d => d.get iS)
    (Hex.Matrix.invariantFactors_cast_eq_data A)
  have hd : S.diag[iS] = (Hex.Matrix.invariantFactors A)[i] := by
    change (Hex.Matrix.invariantFactors A).get
      (Fin.cast (Hex.Matrix.snfRank_eq_data A).symm iS) = S.diag.get iS at hdget
    have hi : Fin.cast (Hex.Matrix.snfRank_eq_data A).symm iS = i := Fin.ext rfl
    rw [hi] at hdget
    exact hdget.symm
  have hrow : Hex.Matrix.row (Hex.Matrix.smithBasis A) i =
      S.diag[iS] • Hex.Matrix.row S.rightInv iM := by
    calc
      Hex.Matrix.row (Hex.Matrix.smithBasis A) i =
          Hex.Matrix.row (S.left * A) iN := by
        rw [Hex.Matrix.smithBasis, Hex.Matrix.row_takeRows]
        exact congrArg (Hex.Matrix.row (S.left * A)) hiN.symm
      _ = Hex.Matrix.row (Hex.Matrix.diagMatrix S.diag n m * S.rightInv) iN :=
        congrArg (fun M : Hex.Matrix Int n m => Hex.Matrix.row M iN)
          (Hex.Matrix.snfData_left_mul A)
      _ = Hex.Matrix.vecMul
          (Hex.Matrix.row (Hex.Matrix.diagMatrix S.diag n m) iN) S.rightInv :=
        Hex.Matrix.row_mul_eq_vecMul _ _ _
      _ = Hex.Matrix.vecMul (S.diag[iS] • Vector.unit Int iM) S.rightInv := by
        rw [show iN = Fin.castLE hS.rank_le_n iS from rfl,
          Hex.Matrix.row_diagMatrix_cast S.diag hS.rank_le_n hS.rank_le_m iS]
      _ = S.diag[iS] • Hex.Matrix.row S.rightInv iM := by
        rw [Hex.Matrix.vecMul_smul, Hex.Matrix.vecMul_unit]
        rfl
  apply funext
  intro j
  change vectorEquiv (Hex.Matrix.row (Hex.Matrix.smithBasis A) i) j = _
  rw [hrow, hd, hiM, ambientBasis_apply]
  simp only [vectorEquiv_apply, Pi.smul_apply]
  change ((Hex.Matrix.invariantFactors A)[i] •
      Hex.Matrix.row S.rightInv (Fin.castLE (Hex.Matrix.snfRank_le_m A) i))[j.val] =
    (Hex.Matrix.invariantFactors A)[i] *
      (Hex.Matrix.row (Hex.Matrix.snfData A).rightInv
        (Fin.castLE (Hex.Matrix.snfRank_le_m A) i))[j]
  rw [Vector.getElem_smul]
  rfl

theorem relationVector_independent (A : Hex.Matrix Int n m) :
    LinearIndependent ℤ (relationVector A) := by
  apply LinearIndependent.of_comp (rowSpan A).subtype
  have hsub := (ambientBasis A).linearIndependent.comp
    (fun i : Fin (Hex.Matrix.snfRank A) =>
      Fin.castLE (Hex.Matrix.snfRank_le_m A) i)
    (Fin.castLE_injective (Hex.Matrix.snfRank_le_m A))
  rw [Fintype.linearIndependent_iff] at hsub ⊢
  intro g hg i
  have hz : ∀ i : Fin (Hex.Matrix.snfRank A),
      g i * (Hex.Matrix.invariantFactors A)[i] = 0 := by
    apply hsub (fun i => g i * (Hex.Matrix.invariantFactors A)[i])
    have hrel := hg
    change ∑ i, g i • (relationVector A i : Fin m → ℤ) = 0 at hrel
    simp_rw [relationVector_eq] at hrel
    simpa only [Function.comp_apply, mul_smul] using hrel
  exact (mul_eq_zero.mp (hz i)).resolve_right
    (Int.ne_of_gt (Hex.Matrix.invariantFactors_pos A i))

theorem relationVector_spans (A : Hex.Matrix Int n m) :
    ⊤ ≤ Submodule.span ℤ (Set.range (relationVector A)) := by
  rw [top_le_iff, span_range_eq_top_iff_surjective_fintypeLinearCombination]
  intro x
  let v : Vector Int m := vectorEquiv.symm x.1
  have hv : Hex.Matrix.smithBasis A |>.memLattice v := by
    apply (Hex.Matrix.smithBasis_memLattice_iff A v).2
    apply (mem_span_iff A v).1
    have hvx : vectorEquiv v = x.1 := Equiv.apply_symm_apply vectorEquiv x.1
    rw [hvx]
    exact x.2
  rcases hv with ⟨c, hc⟩
  refine ⟨vectorEquiv c, ?_⟩
  apply (rowSpan A).injective_subtype
  rw [Fintype.linearCombination_apply, map_sum]
  simp_rw [map_smul]
  change (∑ i, vectorEquiv c i •
    vectorEquiv (Hex.Matrix.row (Hex.Matrix.smithBasis A) i)) = x.1
  calc
    (∑ i, vectorEquiv c i •
        vectorEquiv (Hex.Matrix.row (Hex.Matrix.smithBasis A) i)) =
        Fintype.linearCombination ℤ
          (_root_.Matrix.row (matrixEquiv (Hex.Matrix.smithBasis A)))
          (vectorEquiv c) := by
      rw [Fintype.linearCombination_apply]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [matrixEquiv_row]
    _ = vectorEquiv (Hex.Matrix.vecMul c (Hex.Matrix.smithBasis A)) :=
      (vectorEquiv_vecMul (Hex.Matrix.smithBasis A) c).symm
    _ = vectorEquiv v := congrArg vectorEquiv hc
    _ = x.1 := Equiv.apply_symm_apply vectorEquiv x.1

/-- The independent Smith relation rows form a basis of the original row
span. -/
@[expose]
noncomputable def relationBasis (A : Hex.Matrix Int n m) :
    Basis (Fin (Hex.Matrix.snfRank A)) ℤ (rowSpan A) :=
  Basis.mk (relationVector_independent A) (relationVector_spans A)

@[simp]
theorem relationBasis_apply (A : Hex.Matrix Int n m)
    (i : Fin (Hex.Matrix.snfRank A)) :
    relationBasis A i = relationVector A i := by
  rw [relationBasis, Basis.mk_apply]

/-- The executable Smith normal form as Mathlib's simultaneous-basis
structure for the submodule spanned by the rows. -/
@[expose]
noncomputable def smithNormalForm (A : Hex.Matrix Int n m) :
    Module.Basis.SmithNormalForm (rowSpan A) (Fin m)
      (Hex.Matrix.snfRank A) where
  bM := ambientBasis A
  bN := relationBasis A
  f := Fin.castLEEmb (Hex.Matrix.snfRank_le_m A)
  a := fun i => (Hex.Matrix.invariantFactors A)[i]
  snf := by
    intro i
    rw [relationBasis_apply, relationVector_eq]
    rfl

@[simp]
theorem smithNormalForm_a (A : Hex.Matrix Int n m)
    (i : Fin (Hex.Matrix.snfRank A)) :
    (smithNormalForm A).a i = (Hex.Matrix.invariantFactors A)[i] :=
  rfl

end HexSmithMathlib
