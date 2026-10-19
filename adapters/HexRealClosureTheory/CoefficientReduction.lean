/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.CoefficientTarski
public import HexSignDet.QueryReduction

public section

namespace Hex.SignDet.ReductionStep
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- Substitute the stored remainder and witness, retaining its factor index. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (s : ReductionStep F) : ReductionStep G := by
  classical
  exact ⟨s.index, interpretation.polynomial s.next, s.witness.substitute interpretation⟩

/-- Finite data for one actual positive product reduction. -/
@[expose] noncomputable def coefficients (s : ReductionStep F)
    (p prev factor : DensePoly F) : Finset F := by
  classical
  exact s.witness.stored ∪
    (p.toArray.toList ++ prev.toArray.toList ++ factor.toArray.toList ++
      s.next.toArray.toList).toFinset

private theorem subIsZero_eq {K : Type} [Field K] [DecidableEq K]
    (p q : DensePoly K) : SignedRemainderChain.subIsZero p q = true ↔
      HexPolyTheory.toPolynomial p = HexPolyTheory.toPolynomial q := by
  rw [SignedRemainderChain.subIsZero, DensePoly.isZero_eq_true_iff,
    DensePoly.size_eq_zero_iff]
  constructor
  · intro zero
    have zero := congrArg (HexPolyTheory.toPolynomial (R := K)) zero
    rw [HexPolyTheory.toPolynomial_sub, HexPolyTheory.toPolynomial_zero] at zero
    exact sub_eq_zero.mp zero
  · intro equal
    apply (HexPolyTheory.equiv (R := K)).injective
    change HexPolyTheory.toPolynomial _ = HexPolyTheory.toPolynomial _
    rw [HexPolyTheory.toPolynomial_sub, HexPolyTheory.toPolynomial_zero, equal, sub_self]

/-- The complete indexed product-reduction check maps using only the
finite input coefficients and witness scales, including its degree bound. -/
theorem check_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (p prev factor : DensePoly F)
    (index : Nat) (s : ReductionStep F)
    (data : ∀ x ∈ s.coefficients p prev factor,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : s.check sign p prev factor index = true) :
    (s.substitute interpretation).check targetSign
      (interpretation.polynomial p) (interpretation.polynomial prev)
      (interpretation.polynomial factor) index = true := by
  classical
  have row_data r (hr : r = p ∨ r = prev ∨ r = factor ∨ r = s.next) i (hi : i < r.size) :=
    data (r.coeff i) (by
      have hm := coefficient_mem r i hi
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [coefficients, Finset.mem_union, List.mem_toFinset, List.mem_append] <;> tauto)
  have witness_data x (hx : x ∈ s.witness.stored) :=
    data x (Finset.mem_union_left _ hx)
  have quotient_regular i (hi : i < s.witness.quotient.size) :=
    (witness_data _ (by
      simp only [RemainderStep.stored, Finset.mem_union]
      exact Or.inl (List.mem_toFinset.mpr (coefficient_mem _ i hi)))).1
  have left_data := witness_data s.witness.leftScale (by simp [RemainderStep.stored])
  have right_data := witness_data s.witness.rightScale (by simp [RemainderStep.stored])
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted ⊢
  refine ⟨accepted.1, ?_, ?_, ?_, ?_⟩
  · simpa only [substitute, RemainderStep.substitute, left_data.2.2] using accepted.2.1
  · simpa only [substitute, RemainderStep.substitute, right_data.2.2] using accepted.2.2.1
  · simpa only [substitute,
      polynomial_isZero interpretation s.next (fun i hi => (row_data _ (Or.inr (Or.inr (Or.inr rfl))) i hi).2.1),
      polynomial_degree interpretation s.next (fun i hi => (row_data _ (Or.inr (Or.inr (Or.inr rfl))) i hi).2.1),
      polynomial_degree interpretation p (fun i hi => (row_data _ (Or.inl rfl) i hi).2.1)]
      using accepted.2.2.2.1
  · obtain ⟨P, hP⟩ := polynomial_lift interpretation p (fun i hi => (row_data _ (Or.inl rfl) i hi).1)
    obtain ⟨A, hA⟩ := polynomial_lift interpretation prev (fun i hi => (row_data _ (Or.inr (Or.inl rfl)) i hi).1)
    obtain ⟨B, hB⟩ := polynomial_lift interpretation factor (fun i hi => (row_data _ (Or.inr (Or.inr (Or.inl rfl))) i hi).1)
    obtain ⟨C, hC⟩ := polynomial_lift interpretation s.next (fun i hi => (row_data _ (Or.inr (Or.inr (Or.inr rfl))) i hi).1)
    obtain ⟨Q, hQ⟩ := polynomial_lift interpretation s.witness.quotient quotient_regular
    have native := (subIsZero_eq _ _).mp accepted.2.2.2.2
    have lifted : Polynomial.C (⟨s.witness.leftScale, left_data.1⟩ : interpretation.domain) * (A * B) =
        Q * P + Polynomial.C (⟨s.witness.rightScale, right_data.1⟩ : interpretation.domain) * C := by
      apply Polynomial.map_injective (interpretation.domain).subtype Subtype.val_injective
      simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
        hP, hA, hB, hC, hQ, Subring.subtype_apply]
      simpa only [HexPolyTheory.toPolynomial_scale, HexPolyTheory.toPolynomial_mul,
        HexPolyTheory.toPolynomial_add] using native
    have evaluated := congrArg (Polynomial.map (interpretation.value)) lifted
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at evaluated
    have left : interpretation.value (⟨s.witness.leftScale, left_data.1⟩ : interpretation.domain) =
        interpretation.map s.witness.leftScale := (map_mem interpretation _ left_data.1).symm
    have right : interpretation.value (⟨s.witness.rightScale, right_data.1⟩ : interpretation.domain) =
        interpretation.map s.witness.rightScale := (map_mem interpretation _ right_data.1).symm
    rw [left, right] at evaluated
    apply (subIsZero_eq _ _).mpr
    simpa only [substitute, RemainderStep.substitute, HexPolyTheory.toPolynomial_scale,
      HexPolyTheory.toPolynomial_mul, HexPolyTheory.toPolynomial_add,
      polynomial_map interpretation p P hP, polynomial_map interpretation prev A hA,
      polynomial_map interpretation factor B hB, polynomial_map interpretation s.next C hC,
      polynomial_map interpretation s.witness.quotient Q hQ] using evaluated

end Hex.SignDet.ReductionStep



namespace Hex.SignDet.Reduction
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- Substitute the supplied steps and result, preserving the factor order. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (r : Reduction F) : Reduction G := by
  classical
  exact ⟨r.steps.map (ReductionStep.substitute interpretation), interpretation.polynomial r.result⟩

/-- The finite obligations of each actual matched factor/step in a replay.
A final zero-difference equality needs no additional evaluation guard. -/
@[expose] noncomputable def coefficientsFrom (p : DensePoly F) :
    DensePoly F → List (Nat × DensePoly F) →
      List (ReductionStep F) → Finset F
  | prev, (_, q) :: fs, s :: ss =>
      s.coefficients p prev q ∪ coefficientsFrom p s.next fs ss
  | _, _, _ => ∅

/-- Finite guards for the positive-degree head and the complete reduction. -/
@[expose] noncomputable def coefficients (r : Reduction F)
    (p : DensePoly F) (qs : List (DensePoly F))
    (es : List Nat) : Finset F := by
  classical
  exact p.toArray.toList.toFinset ∪ coefficientsFrom p 1 (factors qs es) r.steps

/-- Each matched factor/step and the final actual polynomial equality survive
finite guarded substitution. Missing or reordered steps cannot be accepted. -/
theorem checkFrom_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (p prev : DensePoly F)
    (fs : List (Nat × DensePoly F))
    (ss : List (ReductionStep F)) (result : DensePoly F)
    (data : ∀ x ∈ coefficientsFrom p prev fs ss,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : checkFrom sign p prev fs ss result = true) :
    checkFrom targetSign (interpretation.polynomial p)
      (interpretation.polynomial prev) (fs.map (fun (i, q) => (i, interpretation.polynomial q)))
      (ss.map (ReductionStep.substitute interpretation)) (interpretation.polynomial result) = true := by
  classical
  induction fs generalizing prev ss with
  | nil =>
    cases ss with
    | nil =>
      simp only [checkFrom] at accepted
      have equal : prev = result := (HexPolyTheory.equiv (R := F)).injective
        ((ReductionStep.subIsZero_eq _ _).mp accepted)
      subst result
      exact (ReductionStep.subIsZero_eq _ _).mpr rfl
    | cons s ss => simp [checkFrom] at accepted
  | cons pair fs ih =>
    obtain ⟨i, q⟩ := pair
    cases ss with
    | nil => simp [checkFrom] at accepted
    | cons s ss =>
      simp only [checkFrom, Bool.and_eq_true] at accepted
      simp only [List.map_cons, checkFrom, Bool.and_eq_true]
      constructor
      · exact s.check_map interpretation sign targetSign p prev q i
          (fun x hx => data x (Finset.mem_union_left _ hx)) accepted.1
      · exact ih s.next ss (fun x hx => data x (Finset.mem_union_right _ hx)) accepted.2

/-- Factor substitution retains duplicate positions and exponent repetitions. -/
theorem factors_map (interpretation : RealClosure.CoefficientMap F G)
    (qs : List (DensePoly F)) (es : List Nat) :
    factors (qs.map (fun q => interpretation.polynomial q)) es =
      (factors qs es).map (fun (i, q) => (i, interpretation.polynomial q)) := by
  simp only [factors, List.zip_map_left, List.zipIdx_map, List.flatMap_map,
    List.map_flatMap, List.map_replicate, Prod.map, id_eq]

/-- Preserve the complete reduced-moment checker, including the positive head
and exponent guards and the final declared query polynomial. -/
theorem check_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (p : DensePoly F)
    (qs : List (DensePoly F)) (es : List Nat) (r : Reduction F)
    (data : ∀ x ∈ r.coefficients p qs es,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : r.check sign p qs es = true) :
    (r.substitute interpretation).check targetSign
      (interpretation.polynomial p) (qs.map (fun q => interpretation.polynomial q)) es = true := by
  classical
  have p_data i (hi : i < p.size) := data (p.coeff i)
    (Finset.mem_union_left _ (List.mem_toFinset.mpr (coefficient_mem p i hi)))
  have source := accepted
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at source
  simp only [check, substitute, polynomial_degree interpretation p (fun i hi => (p_data i hi).2.1),
    List.length_map, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨source.1, source.2.1, source.2.2.1, ?_⟩
  rw [factors_map, ← polynomial_one interpretation]
  exact checkFrom_map interpretation sign targetSign p 1 (factors qs es) r.steps r.result
    (fun x hx => data x (Finset.mem_union_right _ hx)) source.2.2.2

end Hex.SignDet.Reduction

namespace Hex.SignDet.QueryReduction
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- Substitute shared query witnesses without changing their positions. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (r : QueryReduction F) : QueryReduction G := by
  classical
  exact ⟨r.steps.map (ReductionStep.substitute interpretation)⟩

/-- Finite input/witness obligations for the actually matched query slots. -/
@[expose] noncomputable def coefficientsFrom (p : DensePoly F) :
    List (DensePoly F) → List (ReductionStep F) → Finset F
  | q :: qs, s :: ss => s.coefficients p 1 q ∪ coefficientsFrom p qs ss
  | _, _ => ∅

/-- Finite data for the positive-degree head and all shared query reductions. -/
@[expose] noncomputable def coefficients (r : QueryReduction F)
    (p : DensePoly F) (qs : List (DensePoly F)) :
    Finset F := by
  classical
  exact p.toArray.toList.toFinset ∪ coefficientsFrom p qs r.steps

/-- Every shared query witness preserves its exact slot and acceptance. -/
theorem checkFrom_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (p : DensePoly F) (i : Nat)
    (qs : List (DensePoly F)) (ss : List (ReductionStep F))
    (data : ∀ x ∈ coefficientsFrom p qs ss,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : checkFrom sign p i qs ss = true) :
    checkFrom targetSign (interpretation.polynomial p) i
      (qs.map (fun q => interpretation.polynomial q))
      (ss.map (ReductionStep.substitute interpretation)) = true := by
  classical
  induction qs generalizing ss i with
  | nil => cases ss <;> simp_all only [checkFrom, List.map_nil, Bool.false_eq_true]
  | cons q qs ih =>
    cases ss with
    | nil => simp [checkFrom] at accepted
    | cons s ss =>
      simp only [checkFrom, Bool.and_eq_true] at accepted
      simp only [List.map_cons, checkFrom, Bool.and_eq_true]
      constructor
      · have step := s.check_map interpretation sign targetSign p 1 q i
          (fun x hx => data x (Finset.mem_union_left _ hx)) accepted.1
        simpa only [polynomial_one] using step
      · exact ih (i + 1) ss (fun x hx => data x (Finset.mem_union_right _ hx)) accepted.2

/-- Preserve the complete preprocessing check on the original ordered list. -/
theorem check_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (p : DensePoly F)
    (qs : List (DensePoly F)) (r : QueryReduction F)
    (data : ∀ x ∈ r.coefficients p qs,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : r.check sign p qs = true) :
    (r.substitute interpretation).check targetSign
      (interpretation.polynomial p) (qs.map (fun q => interpretation.polynomial q)) = true := by
  classical
  have p_data i (hi : i < p.size) := data (p.coeff i)
    (Finset.mem_union_left _ (List.mem_toFinset.mpr (coefficient_mem p i hi)))
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted ⊢
  refine ⟨?_, ?_⟩
  · simpa only [polynomial_degree interpretation p (fun i hi => (p_data i hi).2.1)] using accepted.1
  · exact checkFrom_map interpretation sign targetSign p 0 qs r.steps
      (fun x hx => data x (Finset.mem_union_right _ hx)) accepted.2

/-- The reduced operands stay in their original order. -/
theorem queries_map (interpretation : RealClosure.CoefficientMap F G)
    (r : QueryReduction F) :
    (r.substitute interpretation).queries = r.queries.map (fun q => interpretation.polynomial q) := by
  simp only [queries, substitute, List.map_map, Function.comp_def, ReductionStep.substitute]

/-- Optional preprocessing chooses the corresponding mapped operands. -/
theorem operands_map (interpretation : RealClosure.CoefficientMap F G)
    (qs : List (DensePoly F)) (r : Option (QueryReduction F)) :
    operands (qs.map (fun q => interpretation.polynomial q)) (r.map (substitute interpretation)) =
      (operands qs r).map (fun q => interpretation.polynomial q) := by
  cases r with
  | none => rfl
  | some r => exact queries_map interpretation r

end Hex.SignDet.QueryReduction

/-- info: 'Hex.SignDet.Reduction.check_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Reduction.check_map

/-- info: 'Hex.SignDet.QueryReduction.check_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.QueryReduction.check_map
