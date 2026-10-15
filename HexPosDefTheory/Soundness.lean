/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Interpretation
public import HexPosDefTheory.Weighted
public import HexPosDef.Producer

public section

/-! Soundness of arbitrary accepted certificates and successful producer results. -/

open Matrix
open scoped ComplexOrder

namespace Hex.PosDefTheory

open Hex.PosDef Hex.Matrix.Lists

namespace Int

variable (R : Type*) [CommRing R] [PartialOrder R] [StarRing R] [IsStrictOrderedRing R]
variable [StarOrderedRing R] [CharZero R] [PosMulReflectLT R] [NoZeroDivisors R]

omit [StarOrderedRing R] in
/-- The explicitly selected vector method is sound for any accepted vector. -/
theorem vector_sound (n : Nat) (rows : List (List Int)) (v : List Int)
    (hs : PosDef.Lists.shape n n rows = true) (h : PosDef.Int.checkVector n rows v = true)
    (norm_nonneg : ∀ x : R, 0 ≤ star x * x)
    (norm_pos : ∀ x : R, x ≠ 0 → 0 < star x * x) :
    (Lists.matrix (intModel R) n rows).PosDef := by
  let f := intModel R
  simp only [PosDef.Int.checkVector, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨hvlen, hherm⟩, hoff⟩, hv⟩, hbv⟩ := h
  let B := Lists.matrix f n rows
  let z := Lists.vector f n v
  have hB : B.IsHermitian := Lists.hermitian f hs hherm
  rw [Lists.hermitian_spec PosDef.Lists.intArithmetic n rows hs] at hherm
  rw [Lists.offDiagonal_spec n rows hs] at hoff
  have hsym (i j : Fin n) : B i j = B j i := by
    have h := (all_iff _ n).mp ((all_iff _ n).mp hherm i i.isLt) j j.isLt
    have he := congrArg f.map ((f.eq _ _).mp h)
    exact he
  have hstar (i : Fin n) : star (z i) = z i := by simp [z, Lists.vector, f, intModel]
  have hv' (i : Fin n) : 0 < z i := by
    have hm : entry 0 v i ∈ v := by
      rw [entry_eq_getD, HexMatrixTheory.getD_eq_getElem' _ _ _ (by omega)]
      exact List.getElem_mem _
    have hp := of_decide_eq_true (List.all_eq_true.mp hv _ hm)
    exact Int.cast_pos.mpr hp
  have hoff' (i j : Fin n) (hij : i ≠ j) : B i j ≤ 0 := by
    have h := (all_iff _ n).mp ((all_iff _ n).mp hoff i i.isLt) j j.isLt
    simp only [Bool.or_eq_true, Nat.beq_eq, decide_eq_true_eq] at h
    have hle : PosDef.Lists.get PosDef.Lists.intArithmetic rows i j ≤ 0 :=
      h.resolve_left (fun he => hij (Fin.ext he))
    exact Int.cast_nonpos.mpr hle
  have hbv' (i : Fin n) : 0 < (B *ᵥ z) i := by
    rw [← Lists.mulVec_entry f v hs i]
    apply Int.cast_pos.mpr
    have hlen : (PosDef.Lists.mulVec PosDef.Lists.intArithmetic rows v).length = n := by
      simpa [PosDef.Lists.mulVec] using (Lists.shape_iff n n rows).mp hs |>.1
    have hm : entry 0 (PosDef.Lists.mulVec PosDef.Lists.intArithmetic rows v) i ∈
        PosDef.Lists.mulVec PosDef.Lists.intArithmetic rows v := by
      rw [entry_eq_getD, HexMatrixTheory.getD_eq_getElem' _ _ _ (by omega)]
      exact List.getElem_mem _
    exact of_decide_eq_true (List.all_eq_true.mp hbv _ hm)
  have hD := weighted_posDef B z hB hsym hstar hoff' hv' hbv'
    norm_nonneg norm_pos
  exact reflect_diagonal B z hB hstar (fun i => (hv' i).ne') hD norm_pos

/-- Integer positive certificates are interpreted directly in the target carrier. -/
theorem checkPositive_sound (n : Nat) (rows : List (List Int)) (c : PositiveCert Int)
    (h : PosDef.Int.checkPositive n rows c = true) :
    (Lists.matrix (intModel R) n rows).PosDef := by
  cases c with
  | triangular ts =>
    exact Lists.triangular_sound (intModel R) (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2 reflect_conjugate
  | positiveVector v =>
    exact vector_sound R n rows v (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2
      star_mul_self_nonneg (fun _ hx => star_mul_self_pos (IsRegular.of_ne_zero hx))

omit [StarOrderedRing R] [PosMulReflectLT R] [NoZeroDivisors R] in
/-- Integer negative certificates refute positivity independently of production. -/
theorem checkNegative_sound (n : Nat) (rows : List (List Int)) (c : NegativeCert Int)
    (h : PosDef.Int.checkNegative n rows c = true) :
    ¬ (Lists.matrix (intModel R) n rows).PosDef :=
  Lists.negative_sound (intModel R) (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2

/-- Every successful producer return has its stated meaning in the target carrier. -/
theorem certify_spec (B : Hex.Matrix Int n n) (method : Method) (c : Certificate Int)
    (h : PosDef.Int.certify B method = .ok c) :
    match c with
    | .positive _ => (Lists.matrix (intModel R) n B.rowLists).PosDef
    | .negative _ => ¬ (Lists.matrix (intModel R) n B.rowLists).PosDef := by
  have hc := PosDef.Int.certify_check B method c h
  cases c with
  | positive c => exact checkPositive_sound R n _ c hc
  | negative c => exact checkNegative_sound R n _ c hc

end Int

namespace Int

/-- Integer certificates are sound in every linearly ordered commutative ring
with the compatible trivial star; no sum-of-squares characterization of its
entire positive cone is assumed. -/
theorem ordered_sound (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [StarRing R] [TrivialStar R] (n : Nat) (rows : List (List Int)) (c : PositiveCert Int)
    (h : PosDef.Int.checkPositive n rows c = true) :
    (Lists.matrix (intModel R) n rows).PosDef := by
  have hn (x : R) : 0 ≤ star x * x := by simpa only [star_trivial] using mul_self_nonneg x
  have hp (x : R) (hx : x ≠ 0) : 0 < star x * x := by
    simpa only [star_trivial] using mul_self_pos.mpr hx
  cases c with
  | triangular ts =>
    obtain ⟨hB, hdet, d, hd, he⟩ :=
      Lists.triangular_congruence (intModel R) (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2
    apply posDef_of_congruence hB hdet (T := Lists.matrix (intModel R) n ts) _
      (reflect_conjugate_of_norm hp)
    rw [he]
    exact diagonal_posDef d hd (fun _ => star_trivial _) hn hp
  | positiveVector v =>
    exact vector_sound R n rows v (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2 hn hp

end Int

namespace Gaussian

/-- Gaussian congruence certificates imply complex positive definiteness. -/
theorem checkPositive_sound (n : Nat) (rows : List (List PosDef.Gaussian))
    (c : PositiveCert PosDef.Gaussian) (h : PosDef.Gaussian.checkPositive n rows c = true) :
    (Lists.matrix gaussianModel n rows).PosDef := by
  cases c with
  | triangular ts =>
    exact Lists.triangular_sound gaussianModel (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2 reflect_conjugate
  | positiveVector v => simp [PosDef.Gaussian.checkPositive] at h

/-- Non-Hermitian coordinates and Gaussian quadratic witnesses both refute positivity. -/
theorem checkNegative_sound (n : Nat) (rows : List (List PosDef.Gaussian))
    (c : NegativeCert PosDef.Gaussian) (h : PosDef.Gaussian.checkNegative n rows c = true) :
    ¬ (Lists.matrix gaussianModel n rows).PosDef :=
  Lists.negative_sound gaussianModel (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2

/-- Gaussian producer correctness follows from self-validation and checker soundness. -/
theorem certify_spec (B : Hex.Matrix PosDef.Gaussian n n) (c : Certificate PosDef.Gaussian)
    (h : PosDef.Gaussian.certify B = .ok c) :
    match c with
    | .positive _ => (Lists.matrix gaussianModel n B.rowLists).PosDef
    | .negative _ => ¬ (Lists.matrix gaussianModel n B.rowLists).PosDef := by
  have hc := PosDef.Gaussian.certify_check B c h
  cases c with
  | positive c => exact checkPositive_sound n _ c hc
  | negative c => exact checkNegative_sound n _ c hc

end Gaussian

end Hex.PosDefTheory
