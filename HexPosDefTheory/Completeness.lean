/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Check
public import HexPosDefTheory.Soundness
import all HexPosDef.Producer
import all HexPosDefTheory.Check
import all HexPosDefTheory.Producer

public section

/-! Total classification by unrestricted no-swap fraction-free elimination. -/

open Matrix
open scoped ComplexOrder

namespace Hex.PosDefTheory.Producer

open Hex.PosDef
open HexMatrixTheory (matrixEquiv)

variable {R : Type} [CommRing R] [StarRing R] [NoZeroDivisors R] [CharZero R]

/-- The exact Boolean obligations for a result of the general producer. -/
def Accepted (a : PosDef.Producer.Arithmetic R) (B : Hex.Matrix R n n) : Certificate R → Prop
  | .positive (.triangular t) =>
      PosDef.Lists.shape n n B.rowLists = true ∧
      PosDef.Lists.triangular a.toArithmetic n B.rowLists t = true
  | .positive (.positiveVector _) => False
  | .negative c =>
      PosDef.Lists.shape n n B.rowLists = true ∧
      PosDef.Lists.negative a.toArithmetic n B.rowLists c = true

theorem loop_complete (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (hadd : ∀ x y, a.add x y = x + y) (hmul : ∀ x y, a.mul x y = x * y)
    (hsub : ∀ x y, a.sub x y = x - y) (hconj : ∀ x, a.conj x = star x)
    (heq : ∀ x y, a.eq x y = true ↔ x = y)
    (hpos : ∀ z : Int, 0 < z → a.positive (z : R) = true)
    (hneg : ∀ z : Int, z ≤ 0 → a.nonpositive (z : R) = true)
    (hreal : ∀ z p, a.real z = some p ↔ z = (p : R))
    (hself : ∀ z : R, star z = z → ∃ p, a.real z = some p)
    (hdiv : ∀ (q : R) (p : Int), p ≠ 0 → a.div (q * (p : R)) p = q)
    (B : Hex.Matrix R n n) (hB : (matrixEquiv B).IsHermitian)
    (fuel k : Nat) (s : PosDef.Producer.State R n) (h : Invariant B k s)
    (hFuel : n + 1 ≤ k + fuel) :
    ∃ c, PosDef.Producer.loop a fuel k s = .ok c ∧ Accepted a B c := by
  classical
  induction fuel generalizing k s with
  | zero => have he := h.step_le; omega
  | succ fuel ih =>
    by_cases hk : k < n
    · let kk : Fin n := ⟨k, hk⟩
      have hs : star s.left[kk][kk] = s.left[kk][kk] := by
        have he := pivot_selfAdjoint B (Hex.Matrix.identity n) (state k s) h.minors hB hk
        change star (augment s.left s.right)[kk.castAdd n][kk.castAdd n] =
          (augment s.left s.right)[kk.castAdd n][kk.castAdd n] at he
        simpa only [augment_left] using he
      obtain ⟨p, hpivot⟩ := hself s.left[kk][kk] hs
      simp only [kk] at hpivot
      by_cases hp : p ≤ 0
      · refine ⟨.negative (.nonpositive ((s.right.getRow kk).toList.map a.conj)), ?_, ?_⟩
        · simp only [PosDef.Producer.loop, hk, dite_eq_left, Hex.Matrix.getElem_pair_eq_nested, kk, hpivot, ite_eq_left hp]
        · exact ⟨rows_shape B,
            negative_check a hz hadd hmul hconj heq hneg B s kk h p hp ((hreal _ _).mp hpivot)⟩
      · have hn := next_invariant a hmul hsub hreal hdiv B s kk h p (by omega) hpivot
        obtain ⟨c, hc, ha⟩ := ih (k + 1) (PosDef.Producer.step a s kk p) hn (by omega)
        refine ⟨c, ?_, ha⟩
        simpa only [PosDef.Producer.loop, hk, dite_eq_left, Hex.Matrix.getElem_pair_eq_nested, kk, hpivot, ite_eq_right hp] using hc
    · have hkn : k = n := by have he := h.step_le; omega
      subst k
      refine ⟨.positive (.triangular (triangle s)), ?_, ?_⟩
      · simp only [PosDef.Producer.loop, Nat.lt_irrefl, dite_false, triangle]
      · exact ⟨rows_shape B, positive_check a hz hadd hmul hconj heq hpos B s h hB⟩

theorem general_complete (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (ho : a.one = 1)
    (hadd : ∀ x y, a.add x y = x + y) (hmul : ∀ x y, a.mul x y = x * y)
    (hsub : ∀ x y, a.sub x y = x - y) (hconj : ∀ x, a.conj x = star x)
    (heq : ∀ x y, a.eq x y = true ↔ x = y)
    (hpos : ∀ z : Int, 0 < z → a.positive (z : R) = true)
    (hneg : ∀ z : Int, z ≤ 0 → a.nonpositive (z : R) = true)
    (hreal : ∀ z p, a.real z = some p ↔ z = (p : R))
    (hself : ∀ z : R, star z = z → ∃ p, a.real z = some p)
    (hdiv : ∀ (q : R) (p : Int), p ≠ 0 → a.div (q * (p : R)) p = q)
    (B : Hex.Matrix R n n) :
    ∃ c, PosDef.Producer.general a B = .ok c ∧ Accepted a B c := by
  classical
  let pairs := (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)
  let bad : Fin n × Fin n → Bool := fun (i, j) => !(a.eq B[(i, j)] (a.conj B[(j, i)]))
  have mem (i j : Fin n) : (i,j) ∈ pairs := by simp [pairs]
  cases hf : pairs.find? bad with
  | some ij =>
    obtain ⟨i,j⟩ := ij
    refine ⟨.negative (.notHermitian i.val j.val), ?_, rows_shape B, ?_⟩
    · simp only [PosDef.Producer.general, pairs, bad, hf]
    · have hb := List.find?_some hf
      simp only [PosDef.Lists.negative, rows_get a hz B i j, rows_get a hz B j i,
        Bool.and_eq_true_iff]
      exact ⟨⟨by simp, by simp⟩, by
        simpa only [bad, Hex.Matrix.getElem_pair_eq_nested] using hb⟩
  | none =>
    simp only [pairs, bad] at hf
    have good (i j : Fin n) : a.eq B[(i,j)] (a.conj B[(j,i)]) = true := by
      have hn := (List.find?_eq_none.mp (show pairs.find? bad = none from hf)) (i,j) (mem i j)
      simpa [bad] using hn
    have hB : (matrixEquiv B).IsHermitian := by
      ext i j
      have he := (heq _ _).mp (good i j)
      simpa only [Matrix.conjTranspose_apply, entry_eq, hconj,
        Hex.Matrix.getElem_pair_eq_nested] using he.symm
    let diagonal := (List.finRange n).all fun i => (List.finRange n).all fun j =>
      if i = j then a.positive B[(i,i)] else a.eq B[(i,j)] a.zero
    by_cases hd : diagonal = true
    · have flags (i j : Fin n) := List.all_eq_true.mp
          (List.all_eq_true.mp hd i (by simp)) j (by simp)
      have hdiag (i : Fin n) : a.positive B[i][i] = true := by
        simpa only [ite_true, Hex.Matrix.getElem_pair_eq_nested] using flags i i
      have hoff (i j : Fin n) (hij : i ≠ j) : B[i][j] = 0 := by
        have he := flags i j
        simp only [hij, ite_false] at he
        simpa only [hz, Hex.Matrix.getElem_pair_eq_nested] using (heq _ _).mp he
      refine ⟨.positive (.triangular (triangle (PosDef.Producer.initial a B))), ?_,
        rows_shape B, diagonal_check a hz ho hadd hmul hconj heq B hB hdiag hoff⟩
      simp only [diagonal] at hd
      simp only [PosDef.Producer.general, hf, hd, ite_true, triangle]
    · obtain ⟨c,hc,ha⟩ := loop_complete a hz hadd hmul hsub hconj heq hpos hneg
          hreal hself hdiv B hB (n+1) 0 (PosDef.Producer.initial a B)
          (initial_invariant a hz ho B) (by omega)
      refine ⟨c, ?_, ha⟩
      simp only [diagonal] at hd
      simpa only [PosDef.Producer.general, hf, ite_eq_right hd] using hc

end Hex.PosDefTheory.Producer

namespace Hex.PosDefTheory

open Hex.PosDef

private theorem int_total (B : Hex.Matrix Int n n) :
    ∃ c, PosDef.Int.certify B .triangular = .ok c := by
  obtain ⟨c, hc, ha⟩ := Producer.general_complete PosDef.Producer.intArithmetic
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => by simp [PosDef.Producer.intArithmetic, PosDef.Lists.intArithmetic])
    (fun _ _ => by simp [PosDef.Producer.intArithmetic, PosDef.Lists.intArithmetic])
    (fun z h => by simpa [PosDef.Producer.intArithmetic, PosDef.Lists.intArithmetic] using h)
    (fun z h => by simpa [PosDef.Producer.intArithmetic, PosDef.Lists.intArithmetic] using h)
    (fun _ _ => by simp [PosDef.Producer.intArithmetic])
    (fun z _ => ⟨z, rfl⟩)
    (fun q p hp => by simp [PosDef.Producer.intArithmetic, HexArith.Int.exactDiv, hp]) B
  have hcheck : PosDef.Int.check n B.rowLists c = true := by
    cases c with
    | positive c => cases c with
      | triangular t => exact Bool.and_eq_true_iff.mpr ha
      | positiveVector v => exact ha.elim
    | negative c => exact Bool.and_eq_true_iff.mpr ha
  exact ⟨c, by simp [PosDef.Int.certify, PosDef.Producer.validate, hc, hcheck]⟩

private theorem gaussian_total (B : Hex.Matrix PosDef.Gaussian n n) :
    ∃ c, PosDef.Gaussian.certify B = .ok c := by
  obtain ⟨c, hc, ha⟩ := Producer.general_complete PosDef.Producer.gaussianArithmetic
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun x y => by cases x; cases y; simp [PosDef.Producer.gaussianArithmetic,
      PosDef.Lists.gaussianArithmetic, PosDef.Gaussian.eq, PosDef.Gaussian.mk.injEq])
    (fun z h => by
      change (decide ((0 : Int) = 0) && decide (0 < z)) = true
      simp [h])
    (fun z h => by
      change (decide ((0 : Int) = 0) && decide (z ≤ 0)) = true
      simp [h])
    Producer.gaussian_real
    (fun z h => by
      have hi := (Gaussian.selfAdjoint_iff z).mp h
      exact ⟨z.re, by change (if z.im = 0 then some z.re else none) = some z.re; simp [hi]⟩)
    Producer.gaussian_div_mul B
  have hcheck : PosDef.Gaussian.check n B.rowLists c = true := by
    cases c with
    | positive c => cases c with
      | triangular t => exact Bool.and_eq_true_iff.mpr ha
      | positiveVector v => exact ha.elim
    | negative c => exact Bool.and_eq_true_iff.mpr ha
  exact ⟨c, by simp [PosDef.Gaussian.certify, PosDef.Producer.validate, hc, hcheck]⟩

/-- The same integer classification characterizes positivity in each compatible
ordered carrier, including rational, real, and complex scalars. -/
theorem Int.certify_complete_over (R : Type*) [CommRing R] [PartialOrder R]
    [StarRing R] [IsStrictOrderedRing R] [StarOrderedRing R] [CharZero R]
    [PosMulReflectLT R] [NoZeroDivisors R] (B : Hex.Matrix Int n n) :
    ∃ c, PosDef.Int.certify B .triangular = .ok c ∧
      ((∃ p, c = .positive p) ↔ (Lists.matrix (intModel R) n B.rowLists).PosDef) := by
  obtain ⟨c, hc⟩ := int_total B
  refine ⟨c, hc, ?_⟩
  have hs := Int.certify_spec R B .triangular c hc
  cases c with
  | positive p => simp_all
  | negative q => simp_all

/-- The unrestricted integer producer always classifies its input, and returns
positive exactly when its integer interpretation is positive definite. -/
theorem Int.certify_complete (B : Hex.Matrix Int n n) :
    ∃ c, PosDef.Int.certify B .triangular = .ok c ∧
      ((∃ p, c = .positive p) ↔ (Lists.matrix (intModel Int) n B.rowLists).PosDef) := by
  obtain ⟨c, hc⟩ := int_total B
  refine ⟨c, hc, ?_⟩
  have hs := Int.certify_spec Int B .triangular c hc
  cases c with
  | positive p => simp_all
  | negative q => simp_all

/-- The unrestricted Gaussian producer always classifies its input, and returns
positive exactly when its complex interpretation is positive definite. -/
theorem Gaussian.certify_complete (B : Hex.Matrix PosDef.Gaussian n n) :
    ∃ c, PosDef.Gaussian.certify B = .ok c ∧
      ((∃ p, c = .positive p) ↔ (Lists.matrix gaussianModel n B.rowLists).PosDef) := by
  obtain ⟨c, hc⟩ := gaussian_total B
  refine ⟨c, hc, ?_⟩
  have hs := Gaussian.certify_spec B c hc
  cases c with
  | positive p => simp_all
  | negative q => simp_all

end Hex.PosDefTheory
