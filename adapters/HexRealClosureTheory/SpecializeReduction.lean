/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.SpecializeTarski
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
      simpa only [HexPolyTheory.toPolynomial_scale, HexPolyTheory.toPolynomial_mul,
        HexPolyTheory.toPolynomial_add] using native
    have evaluated := congrArg (Polynomial.map (evaluation embedding t)) lifted
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at evaluated
    have left : evaluation embedding t (⟨s.witness.leftScale, left_data.1⟩ : regularRing embedding t) =
        evalMapped embedding s.witness.leftScale t := rfl
    have right : evaluation embedding t (⟨s.witness.rightScale, right_data.1⟩ : regularRing embedding t) =
        evalMapped embedding s.witness.rightScale t := rfl
    rw [left, right] at evaluated
    apply (subIsZero_eq _ _).mpr
    simpa only [specialize, RemainderStep.specialize, HexPolyTheory.toPolynomial_scale,
      HexPolyTheory.toPolynomial_mul, HexPolyTheory.toPolynomial_add,
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

namespace Hex.RealClosure.Specialize
variable {F : Type} [Field F] [DecidableEq F]
attribute [local instance 2000] Field.toGrindField

/-- Literal polynomial one specializes unconditionally. -/
theorem polynomial_one (embedding : F →+* ℝ) (t : ℝ) :
    polynomial embedding (1 : Hex.DensePoly (Hex.RationalFn F)) t = 1 := by
  classical
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff]
  change evalMapped embedding ((Hex.DensePoly.C (1 : Hex.RationalFn F)).coeff i) t =
    (Hex.DensePoly.C (1 : ℝ)).coeff i
  rw [Hex.DensePoly.coeff_C, Hex.DensePoly.coeff_C]
  split_ifs
  · exact evalMapped_one embedding t
  · change evalMapped embedding (0 : Hex.RationalFn F) t = 0
    exact evalMapped_zero embedding t

end Hex.RealClosure.Specialize

namespace Hex.SignDet.Reduction
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute the supplied steps and result, preserving the factor order. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (r : Reduction (RationalFn F)) : Reduction ℝ := by
  classical
  exact ⟨r.steps.map (ReductionStep.specialize embedding t), polynomial embedding r.result t⟩

/-- The finite obligations of each actual matched factor/step in a replay.
A final zero-difference equality needs no additional evaluation guard. -/
@[expose] noncomputable def fractionsFrom (p : DensePoly (RationalFn F)) :
    DensePoly (RationalFn F) → List (Nat × DensePoly (RationalFn F)) →
      List (ReductionStep (RationalFn F)) → Finset (RationalFn F)
  | prev, (_, q) :: fs, s :: ss =>
      s.fractions p prev q ∪ fractionsFrom p s.next fs ss
  | _, _, _ => ∅

/-- Finite guards for the positive-degree head and the complete reduction. -/
@[expose] noncomputable def fractions (r : Reduction (RationalFn F))
    (p : DensePoly (RationalFn F)) (qs : List (DensePoly (RationalFn F)))
    (es : List Nat) : Finset (RationalFn F) := by
  classical
  exact p.toArray.toList.toFinset ∪ fractionsFrom p 1 (factors qs es) r.steps

/-- Each matched factor/step and the final actual polynomial equality survive
finite guarded substitution. Missing or reordered steps cannot be accepted. -/
theorem checkFrom_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (p prev : DensePoly (RationalFn F))
    (fs : List (Nat × DensePoly (RationalFn F)))
    (ss : List (ReductionStep (RationalFn F))) (result : DensePoly (RationalFn F))
    (data : ∀ x ∈ fractionsFrom p prev fs ss,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : checkFrom sign p prev fs ss result = true) :
    checkFrom (fun x : ℝ => (SignType.sign x : Int)) (polynomial embedding p t)
      (polynomial embedding prev t) (fs.map (fun (i, q) => (i, polynomial embedding q t)))
      (ss.map (ReductionStep.specialize embedding t)) (polynomial embedding result t) = true := by
  classical
  induction fs generalizing prev ss with
  | nil =>
    cases ss with
    | nil =>
      simp only [checkFrom] at accepted
      have equal : prev = result := (HexPolyTheory.equiv (R := RationalFn F)).injective
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
      · exact s.check_specialize embedding t sign p prev q i
          (fun x hx => data x (Finset.mem_union_left _ hx)) accepted.1
      · exact ih s.next ss (fun x hx => data x (Finset.mem_union_right _ hx)) accepted.2

/-- Factor substitution retains duplicate positions and exponent repetitions. -/
theorem factors_specialize (embedding : F →+* ℝ) (t : ℝ)
    (qs : List (DensePoly (RationalFn F))) (es : List Nat) :
    factors (qs.map (fun q => polynomial embedding q t)) es =
      (factors qs es).map (fun (i, q) => (i, polynomial embedding q t)) := by
  simp only [factors, List.zip_map_left, List.zipIdx_map, List.flatMap_map,
    List.map_flatMap, List.map_replicate, Prod.map, id_eq]

/-- Preserve the complete reduced-moment checker, including the positive head
and exponent guards and the final declared query polynomial. -/
theorem check_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (p : DensePoly (RationalFn F))
    (qs : List (DensePoly (RationalFn F))) (es : List Nat) (r : Reduction (RationalFn F))
    (data : ∀ x ∈ r.fractions p qs es,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : r.check sign p qs es = true) :
    (r.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int))
      (polynomial embedding p t) (qs.map (fun q => polynomial embedding q t)) es = true := by
  classical
  have p_data i (hi : i < p.size) := data (p.coeff i)
    (Finset.mem_union_left _ (List.mem_toFinset.mpr (coefficient_mem p i hi)))
  have source := accepted
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at source
  simp only [check, specialize, polynomial_degree embedding p t (fun i hi => (p_data i hi).2.1),
    List.length_map, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨source.1, source.2.1, source.2.2.1, ?_⟩
  rw [factors_specialize, ← polynomial_one embedding t]
  exact checkFrom_specialize embedding t sign p 1 (factors qs es) r.steps r.result
    (fun x hx => data x (Finset.mem_union_right _ hx)) source.2.2.2

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- One common neighborhood preserves the complete supplied reduction. -/
theorem specialize_near (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (p : DensePoly (RationalFn F)) (qs : List (DensePoly (RationalFn F)))
    (es : List Nat) (r : Reduction (RationalFn F))
    (accepted : r.check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) p qs es = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      (r.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int))
        (polynomial embedding p t) (qs.map (fun q => polynomial embedding q t)) es = true := by
  classical
  obtain ⟨η, positive, signs⟩ := finite_fractions_map embedding ordered (r.fractions p qs es)
  refine ⟨η, positive, fun t ht small => ?_⟩
  apply check_specialize embedding t _ p qs es r _ accepted
  intro x hx
  have preserved := signs t ht small x hx
  exact ⟨preserved.1, fraction_zero embedding x t preserved.2, preserved.2⟩

/-- info: 'Hex.SignDet.Reduction.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Reduction.check_specialize

/-- info: 'Hex.SignDet.Reduction.specialize_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Reduction.specialize_near

end Hex.SignDet.Reduction

namespace Hex.SignDet.QueryReduction
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute shared query witnesses without changing their positions. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (r : QueryReduction (RationalFn F)) : QueryReduction ℝ := by
  classical
  exact ⟨r.steps.map (ReductionStep.specialize embedding t)⟩

/-- Finite input/witness obligations for the actually matched query slots. -/
@[expose] noncomputable def fractionsFrom (p : DensePoly (RationalFn F)) :
    List (DensePoly (RationalFn F)) → List (ReductionStep (RationalFn F)) → Finset (RationalFn F)
  | q :: qs, s :: ss => s.fractions p 1 q ∪ fractionsFrom p qs ss
  | _, _ => ∅

/-- Finite data for the positive-degree head and all shared query reductions. -/
@[expose] noncomputable def fractions (r : QueryReduction (RationalFn F))
    (p : DensePoly (RationalFn F)) (qs : List (DensePoly (RationalFn F))) :
    Finset (RationalFn F) := by
  classical
  exact p.toArray.toList.toFinset ∪ fractionsFrom p qs r.steps

/-- Every shared query witness preserves its exact slot and acceptance. -/
theorem checkFrom_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (p : DensePoly (RationalFn F)) (i : Nat)
    (qs : List (DensePoly (RationalFn F))) (ss : List (ReductionStep (RationalFn F)))
    (data : ∀ x ∈ fractionsFrom p qs ss,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : checkFrom sign p i qs ss = true) :
    checkFrom (fun x : ℝ => (SignType.sign x : Int)) (polynomial embedding p t) i
      (qs.map (fun q => polynomial embedding q t))
      (ss.map (ReductionStep.specialize embedding t)) = true := by
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
      · have step := s.check_specialize embedding t sign p 1 q i
          (fun x hx => data x (Finset.mem_union_left _ hx)) accepted.1
        simpa only [polynomial_one] using step
      · exact ih (i + 1) ss (fun x hx => data x (Finset.mem_union_right _ hx)) accepted.2

/-- Preserve the complete preprocessing check on the original ordered list. -/
theorem check_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (p : DensePoly (RationalFn F))
    (qs : List (DensePoly (RationalFn F))) (r : QueryReduction (RationalFn F))
    (data : ∀ x ∈ r.fractions p qs,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : r.check sign p qs = true) :
    (r.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int))
      (polynomial embedding p t) (qs.map (fun q => polynomial embedding q t)) = true := by
  classical
  have p_data i (hi : i < p.size) := data (p.coeff i)
    (Finset.mem_union_left _ (List.mem_toFinset.mpr (coefficient_mem p i hi)))
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted ⊢
  refine ⟨?_, ?_⟩
  · simpa only [polynomial_degree embedding p t (fun i hi => (p_data i hi).2.1)] using accepted.1
  · exact checkFrom_specialize embedding t sign p 0 qs r.steps
      (fun x hx => data x (Finset.mem_union_right _ hx)) accepted.2

/-- The reduced operands stay in their original order. -/
theorem queries_specialize (embedding : F →+* ℝ) (t : ℝ)
    (r : QueryReduction (RationalFn F)) :
    (r.specialize embedding t).queries = r.queries.map (fun q => polynomial embedding q t) := by
  simp only [queries, specialize, List.map_map, Function.comp_def, ReductionStep.specialize]

/-- Optional preprocessing chooses the corresponding specialized operands. -/
theorem operands_specialize (embedding : F →+* ℝ) (t : ℝ)
    (qs : List (DensePoly (RationalFn F))) (r : Option (QueryReduction (RationalFn F))) :
    operands (qs.map (fun q => polynomial embedding q t)) (r.map (specialize embedding t)) =
      (operands qs r).map (fun q => polynomial embedding q t) := by
  cases r with
  | none => rfl
  | some r => exact queries_specialize embedding t r

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- One neighborhood preserves all supplied shared query reductions. -/
theorem specialize_near (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (p : DensePoly (RationalFn F)) (qs : List (DensePoly (RationalFn F)))
    (r : QueryReduction (RationalFn F))
    (accepted : r.check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) p qs = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      (r.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int))
        (polynomial embedding p t) (qs.map (fun q => polynomial embedding q t)) = true := by
  classical
  obtain ⟨η, positive, signs⟩ := finite_fractions_map embedding ordered (r.fractions p qs)
  refine ⟨η, positive, fun t ht small => ?_⟩
  apply check_specialize embedding t _ p qs r _ accepted
  intro x hx
  have preserved := signs t ht small x hx
  exact ⟨preserved.1, fraction_zero embedding x t preserved.2, preserved.2⟩

/-- info: 'Hex.SignDet.QueryReduction.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.QueryReduction.check_specialize

/-- info: 'Hex.SignDet.QueryReduction.specialize_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.QueryReduction.specialize_near

end Hex.SignDet.QueryReduction
