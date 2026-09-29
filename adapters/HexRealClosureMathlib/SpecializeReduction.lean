/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializeTarski
public import HexSignDet.QueryReduction

public section

namespace Hex.SignDet.ReductionStep
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute the stored remainder and witness, retaining its factor index. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (s : ReductionStep (RationalFn F)) : ReductionStep ℝ := by
  classical
  exact ⟨s.index, polynomial embedding s.next t, s.witness.specialize embedding t⟩

/-- Finite data for one actual positive product reduction. -/
@[expose] noncomputable def fractions (s : ReductionStep (RationalFn F))
    (p prev factor : DensePoly (RationalFn F)) : Finset (RationalFn F) := by
  classical
  exact s.witness.fractions ∪
    (p.toArray.toList ++ prev.toArray.toList ++ factor.toArray.toList ++
      s.next.toArray.toList).toFinset

private theorem subIsZero_eq {K : Type} [Field K] [DecidableEq K]
    (p q : DensePoly K) : SignedRemainderChain.subIsZero p q = true ↔
      HexPolyMathlib.toPolynomial p = HexPolyMathlib.toPolynomial q := by
  rw [SignedRemainderChain.subIsZero, DensePoly.isZero_eq_true_iff,
    DensePoly.size_eq_zero_iff]
  constructor
  · intro zero
    have zero := congrArg (HexPolyMathlib.toPolynomial (R := K)) zero
    rw [HexPolyMathlib.toPolynomial_sub, HexPolyMathlib.toPolynomial_zero] at zero
    exact sub_eq_zero.mp zero
  · intro equal
    apply (HexPolyMathlib.equiv (R := K)).injective
    change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
    rw [HexPolyMathlib.toPolynomial_sub, HexPolyMathlib.toPolynomial_zero, equal, sub_self]

/-- The complete indexed product-reduction check specializes using only the
finite input coefficients and witness scales, including its degree bound. -/
theorem check_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (p prev factor : DensePoly (RationalFn F))
    (index : Nat) (s : ReductionStep (RationalFn F))
    (data : ∀ x ∈ s.fractions p prev factor,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : s.check sign p prev factor index = true) :
    (s.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int))
      (polynomial embedding p t) (polynomial embedding prev t)
      (polynomial embedding factor t) index = true := by
  classical
  have row_data r (hr : r = p ∨ r = prev ∨ r = factor ∨ r = s.next) i (hi : i < r.size) :=
    data (r.coeff i) (by
      have hm := coefficient_mem r i hi
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [fractions, Finset.mem_union, List.mem_toFinset, List.mem_append] <;> tauto)
  have witness_data x (hx : x ∈ s.witness.fractions) :=
    data x (Finset.mem_union_left _ hx)
  have quotient_regular i (hi : i < s.witness.quotient.size) :=
    (witness_data _ (by
      simp only [RemainderStep.fractions, Finset.mem_union]
      exact Or.inl (List.mem_toFinset.mpr (coefficient_mem _ i hi)))).1
  have left_data := witness_data s.witness.leftScale (by simp [RemainderStep.fractions])
  have right_data := witness_data s.witness.rightScale (by simp [RemainderStep.fractions])
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted ⊢
  refine ⟨accepted.1, ?_, ?_, ?_, ?_⟩
  · simpa only [specialize, RemainderStep.specialize, left_data.2.2] using accepted.2.1
  · simpa only [specialize, RemainderStep.specialize, right_data.2.2] using accepted.2.2.1
  · simpa only [specialize,
      polynomial_isZero embedding s.next t (fun i hi => (row_data _ (Or.inr (Or.inr (Or.inr rfl))) i hi).2.1),
      polynomial_degree embedding s.next t (fun i hi => (row_data _ (Or.inr (Or.inr (Or.inr rfl))) i hi).2.1),
      polynomial_degree embedding p t (fun i hi => (row_data _ (Or.inl rfl) i hi).2.1)]
      using accepted.2.2.2.1
  · obtain ⟨P, hP⟩ := polynomial_lift embedding t p (fun i hi => (row_data _ (Or.inl rfl) i hi).1)
    obtain ⟨A, hA⟩ := polynomial_lift embedding t prev (fun i hi => (row_data _ (Or.inr (Or.inl rfl)) i hi).1)
    obtain ⟨B, hB⟩ := polynomial_lift embedding t factor (fun i hi => (row_data _ (Or.inr (Or.inr (Or.inl rfl))) i hi).1)
    obtain ⟨C, hC⟩ := polynomial_lift embedding t s.next (fun i hi => (row_data _ (Or.inr (Or.inr (Or.inr rfl))) i hi).1)
    obtain ⟨Q, hQ⟩ := polynomial_lift embedding t s.witness.quotient quotient_regular
    have native := (subIsZero_eq _ _).mp accepted.2.2.2.2
    have lifted : Polynomial.C (⟨s.witness.leftScale, left_data.1⟩ : regularRing embedding t) * (A * B) =
        Q * P + Polynomial.C (⟨s.witness.rightScale, right_data.1⟩ : regularRing embedding t) * C := by
      apply Polynomial.map_injective (regularRing embedding t).subtype Subtype.val_injective
      simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
        hP, hA, hB, hC, hQ, Subring.subtype_apply]
      simpa only [HexPolyMathlib.toPolynomial_scale, HexPolyMathlib.toPolynomial_mul,
        HexPolyMathlib.toPolynomial_add] using native
    have evaluated := congrArg (Polynomial.map (evaluation embedding t)) lifted
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at evaluated
    have left : evaluation embedding t (⟨s.witness.leftScale, left_data.1⟩ : regularRing embedding t) =
        evalMapped embedding s.witness.leftScale t := rfl
    have right : evaluation embedding t (⟨s.witness.rightScale, right_data.1⟩ : regularRing embedding t) =
        evalMapped embedding s.witness.rightScale t := rfl
    rw [left, right] at evaluated
    apply (subIsZero_eq _ _).mpr
    simpa only [specialize, RemainderStep.specialize, HexPolyMathlib.toPolynomial_scale,
      HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_add,
      polynomial_map embedding t p P hP, polynomial_map embedding t prev A hA,
      polynomial_map embedding t factor B hB, polynomial_map embedding t s.next C hC,
      polynomial_map embedding t s.witness.quotient Q hQ] using evaluated

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- One positive neighborhood preserves the actual indexed product reduction. -/
theorem specialize_near (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (p prev factor : DensePoly (RationalFn F)) (index : Nat)
    (s : ReductionStep (RationalFn F))
    (accepted : s.check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
      p prev factor index = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      (s.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int))
        (polynomial embedding p t) (polynomial embedding prev t)
        (polynomial embedding factor t) index = true := by
  classical
  obtain ⟨η, positive, signs⟩ := finite_fractions_map embedding ordered (s.fractions p prev factor)
  refine ⟨η, positive, fun t ht small => ?_⟩
  apply check_specialize embedding t _ p prev factor index s _ accepted
  intro x hx
  have preserved := signs t ht small x hx
  exact ⟨preserved.1, fraction_zero embedding x t preserved.2, preserved.2⟩

/-- info: 'Hex.SignDet.ReductionStep.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.ReductionStep.check_specialize

/-- info: 'Hex.SignDet.ReductionStep.specialize_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.ReductionStep.specialize_near

end Hex.SignDet.ReductionStep
