/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.CoefficientMap
public import HexRealRoots.Tarski

public section

namespace Hex.RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField

private theorem subIsZero_eq {K : Type} [Field K] [DecidableEq K]
    (p q : Hex.DensePoly K) :
    Hex.SignedRemainderChain.subIsZero p q = true ↔
      HexPolyTheory.toPolynomial p = HexPolyTheory.toPolynomial q := by
  rw [Hex.SignedRemainderChain.subIsZero, Hex.DensePoly.isZero_eq_true_iff,
    Hex.DensePoly.size_eq_zero_iff]
  constructor
  · intro zero
    have zero := congrArg (HexPolyTheory.toPolynomial (R := K)) zero
    rw [HexPolyTheory.toPolynomial_sub, HexPolyTheory.toPolynomial_zero] at zero
    exact sub_eq_zero.mp zero
  · intro equal
    apply (HexPolyTheory.equiv (R := K)).injective
    change HexPolyTheory.toPolynomial _ = HexPolyTheory.toPolynomial _
    rw [HexPolyTheory.toPolynomial_sub, HexPolyTheory.toPolynomial_zero, equal, sub_self]

variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

private theorem initial_map (interpretation : RealClosure.CoefficientMap F G)
    (p f c : Hex.DensePoly (F)) (step : Hex.RemainderStep (F))
    (hp : ∀ i < p.size, p.coeff i ∈ interpretation.domain)
    (hf : ∀ i < f.size, f.coeff i ∈ interpretation.domain)
    (hc : ∀ i < c.size, c.coeff i ∈ interpretation.domain)
    (hq : ∀ i < step.quotient.size, step.quotient.coeff i ∈ interpretation.domain)
    (hl : step.leftScale ∈ interpretation.domain) (hr : step.rightScale ∈ interpretation.domain)
    (accepted : Hex.SignedRemainderChain.subIsZero
      (Hex.DensePoly.scale step.leftScale (f * p.derivative))
      (step.quotient * p + Hex.DensePoly.scale step.rightScale c) = true) :
    Hex.SignedRemainderChain.subIsZero
      (Hex.DensePoly.scale (interpretation.map step.leftScale)
        (interpretation.polynomial f * (interpretation.polynomial p).derivative))
      (interpretation.polynomial step.quotient * interpretation.polynomial p +
        Hex.DensePoly.scale (interpretation.map step.rightScale) (interpretation.polynomial c)) = true := by
  classical
  obtain ⟨P, hP⟩ := polynomial_lift interpretation p hp
  obtain ⟨G, hG⟩ := polynomial_lift interpretation f hf
  obtain ⟨C, hC⟩ := polynomial_lift interpretation c hc
  obtain ⟨Q, hQ⟩ := polynomial_lift interpretation step.quotient hq
  have native := (subIsZero_eq _ _).mp accepted
  have lifted : Polynomial.C (⟨step.leftScale, hl⟩ : interpretation.domain) * (G * P.derivative) =
      Q * P + Polynomial.C (⟨step.rightScale, hr⟩ : interpretation.domain) * C := by
    apply Polynomial.map_injective (interpretation.domain).subtype Subtype.val_injective
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
      ← Polynomial.derivative_map, hP, hG, hC, hQ, Subring.subtype_apply]
    simpa only [HexPolyTheory.toPolynomial_scale, HexPolyTheory.toPolynomial_mul,
      HexPolyTheory.toPolynomial_add, HexPolyTheory.toPolynomial_derivative] using native
  have evaluated := congrArg (Polynomial.map (interpretation.value)) lifted
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
    ← Polynomial.derivative_map] at evaluated
  have left : interpretation.value (⟨step.leftScale, hl⟩ : interpretation.domain) =
      interpretation.map step.leftScale := (map_mem interpretation _ hl).symm
  have right : interpretation.value (⟨step.rightScale, hr⟩ : interpretation.domain) =
      interpretation.map step.rightScale := (map_mem interpretation _ hr).symm
  rw [left, right] at evaluated
  apply (subIsZero_eq _ _).mpr
  simpa only [HexPolyTheory.toPolynomial_scale, HexPolyTheory.toPolynomial_mul,
    HexPolyTheory.toPolynomial_add, HexPolyTheory.toPolynomial_derivative,
    polynomial_map interpretation p P hP, polynomial_map interpretation f G hG,
    polynomial_map interpretation c C hC, polynomial_map interpretation step.quotient Q hQ] using evaluated

private theorem terminal_map (interpretation : RealClosure.CoefficientMap F G)
    (a b q : Hex.DensePoly (F)) (scale : F)
    (ha : ∀ i < a.size, a.coeff i ∈ interpretation.domain)
    (hb : ∀ i < b.size, b.coeff i ∈ interpretation.domain)
    (hq : ∀ i < q.size, q.coeff i ∈ interpretation.domain)
    (hs : scale ∈ interpretation.domain)
    (accepted : Hex.SignedRemainderChain.subIsZero (Hex.DensePoly.scale scale a) (q * b) = true) :
    Hex.SignedRemainderChain.subIsZero
      (Hex.DensePoly.scale (interpretation.map scale) (interpretation.polynomial a))
      (interpretation.polynomial q * interpretation.polynomial b) = true := by
  classical
  obtain ⟨A, hA⟩ := polynomial_lift interpretation a ha
  obtain ⟨B, hB⟩ := polynomial_lift interpretation b hb
  obtain ⟨Q, hQ⟩ := polynomial_lift interpretation q hq
  have native := (subIsZero_eq _ _).mp accepted
  have lifted : Polynomial.C (⟨scale, hs⟩ : interpretation.domain) * A = Q * B := by
    apply Polynomial.map_injective (interpretation.domain).subtype Subtype.val_injective
    simp only [Polynomial.map_mul, Polynomial.map_C, hA, hB, hQ,
      Subring.subtype_apply]
    simpa only [HexPolyTheory.toPolynomial_scale, HexPolyTheory.toPolynomial_mul] using native
  have evaluated := congrArg (Polynomial.map (interpretation.value)) lifted
  simp only [Polynomial.map_mul, Polynomial.map_C] at evaluated
  have scalar : interpretation.value (⟨scale, hs⟩ : interpretation.domain) =
      interpretation.map scale := (map_mem interpretation _ hs).symm
  rw [scalar] at evaluated
  apply (subIsZero_eq _ _).mpr
  simpa only [HexPolyTheory.toPolynomial_scale, HexPolyTheory.toPolynomial_mul,
    polynomial_map interpretation a A hA, polynomial_map interpretation b B hB,
    polynomial_map interpretation q Q hQ] using evaluated

end Hex.RealClosure.CoefficientMap

namespace Hex.RemainderStep
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField

variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- Substitute the actual stored scalar and quotient data of one remainder
step, retaining its supplied recurrence rather than recomputing division. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (step : RemainderStep (F)) : RemainderStep G := by
  classical
  exact ⟨interpretation.map step.leftScale, interpretation.polynomial step.quotient,
    interpretation.map step.rightScale⟩

/-- An accepted signed recurrence remains accepted after finite regular
coefficient substitution and preservation of its two recorded scale signs. -/
theorem check_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (a b c : DensePoly (F))
    (step : RemainderStep (F))
    (ha : ∀ i < a.size, a.coeff i ∈ interpretation.domain)
    (hb : ∀ i < b.size, b.coeff i ∈ interpretation.domain)
    (hc : ∀ i < c.size, c.coeff i ∈ interpretation.domain)
    (hq : ∀ i < step.quotient.size, step.quotient.coeff i ∈ interpretation.domain)
    (hl : step.leftScale ∈ interpretation.domain) (hr : step.rightScale ∈ interpretation.domain)
    (sl : targetSign (interpretation.map step.leftScale) = sign step.leftScale)
    (sr : targetSign (interpretation.map step.rightScale) = sign step.rightScale)
    (accepted : SignedRemainderChain.checkStep sign a b c step = true) :
    SignedRemainderChain.checkStep targetSign
      (interpretation.polynomial a) (interpretation.polynomial b) (interpretation.polynomial c)
      (step.substitute interpretation) = true := by
  classical
  simp only [SignedRemainderChain.checkStep, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at accepted ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa only [substitute, sl] using accepted.1
  · simpa only [substitute, sr] using accepted.2.1
  · obtain ⟨A, hA⟩ := polynomial_lift interpretation a ha
    obtain ⟨B, hB⟩ := polynomial_lift interpretation b hb
    obtain ⟨C, hC⟩ := polynomial_lift interpretation c hc
    obtain ⟨Q, hQ⟩ := polynomial_lift interpretation step.quotient hq
    have native := (RealClosure.CoefficientMap.subIsZero_eq _ _).mp accepted.2.2
    have lifted : Polynomial.C (⟨step.leftScale, hl⟩ : interpretation.domain) * A =
        Q * B - Polynomial.C (⟨step.rightScale, hr⟩ : interpretation.domain) * C := by
      apply Polynomial.map_injective (interpretation.domain).subtype Subtype.val_injective
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_C, hA, hB, hC, hQ]
      simpa only [Subring.subtype_apply, Subtype.coe_mk, HexPolyTheory.toPolynomial_scale,
        HexPolyTheory.toPolynomial_mul, HexPolyTheory.toPolynomial_sub] using native
    have evaluated := congrArg (Polynomial.map (interpretation.value)) lifted
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C] at evaluated
    have left : interpretation.value (⟨step.leftScale, hl⟩ : interpretation.domain) =
        interpretation.map step.leftScale := (map_mem interpretation _ hl).symm
    have right : interpretation.value (⟨step.rightScale, hr⟩ : interpretation.domain) =
        interpretation.map step.rightScale := (map_mem interpretation _ hr).symm
    rw [left, right] at evaluated
    apply (RealClosure.CoefficientMap.subIsZero_eq _ _).mpr
    simpa only [substitute, HexPolyTheory.toPolynomial_scale, HexPolyTheory.toPolynomial_mul,
      HexPolyTheory.toPolynomial_sub, polynomial_map interpretation a A hA,
      polynomial_map interpretation b B hB, polynomial_map interpretation c C hC,
      polynomial_map interpretation step.quotient Q hQ] using evaluated


/-- The literal stored quotient coefficients and scales of a recurrence. -/
@[expose] noncomputable def stored (step : RemainderStep F) : Finset F := by
  classical
  exact step.quotient.toArray.toList.toFinset ∪ {step.leftScale, step.rightScale}

/-- The actual finite input arrays, supplied quotient and scales needed by
one signed recurrence. No division or new certificate production runs. -/
noncomputable def coefficients (step : RemainderStep F) (a b c : DensePoly F) : Finset F := by
  classical
  exact (a.toArray.toList ++ b.toArray.toList ++ c.toArray.toList ++
    step.quotient.toArray.toList ++ [step.leftScale, step.rightScale]).toFinset

/-- Actual successive-infinitesimal coefficient data give a neighborhood
preserving the complete signed-remainder check while retaining the second
indeterminate. Every membership and sign premise is derived from this finite
certificate inventory. -/
theorem firstMap_near
    (a b c : DensePoly (RationalFn (RationalFn ℝ)))
    (step : RemainderStep (RationalFn (RationalFn ℝ)))
    (accepted : SignedRemainderChain.checkStep
      (OrderedFn.Infinitesimal.sign (OrderedFn.Infinitesimal.sign OrderedFn.orderSign))
      a b c step = true) :
    ∀ᶠ first in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      SignedRemainderChain.checkStep (OrderedFn.Infinitesimal.sign OrderedFn.orderSign)
        ((RealClosure.Specialize.firstMap first).polynomial a)
        ((RealClosure.Specialize.firstMap first).polynomial b)
        ((RealClosure.Specialize.firstMap first).polynomial c)
        (step.substitute (RealClosure.Specialize.firstMap first)) = true := by
  filter_upwards [RealClosure.Specialize.firstMap_near (step.coefficients a b c)] with first data
  have present (p : DensePoly (RationalFn (RationalFn ℝ)))
      (selected : p = a ∨ p = b ∨ p = c ∨ p = step.quotient) (i : Nat) (stored : i < p.size) :
      p.coeff i ∈ step.coefficients a b c := by
    have entry := RealClosure.CoefficientMap.coefficient_mem p i stored
    rcases selected with rfl | rfl | rfl | rfl <;>
      simp only [coefficients, List.mem_toFinset, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] <;> tauto
  have left := data step.leftScale (by simp [coefficients])
  have right := data step.rightScale (by simp [coefficients])
  exact step.check_map (RealClosure.Specialize.firstMap first) _ _ a b c
    (fun i stored => (data _ (present _ (Or.inl rfl) i stored)).1)
    (fun i stored => (data _ (present _ (Or.inr (Or.inl rfl)) i stored)).1)
    (fun i stored => (data _ (present _ (Or.inr (Or.inr (Or.inl rfl))) i stored)).1)
    (fun i stored => (data _ (present _ (Or.inr (Or.inr (Or.inr rfl))) i stored)).1)
    left.1 right.1 left.2.2 right.2.2 accepted

end Hex.RemainderStep

namespace Hex.SignedRemainderChain
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField

variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- Substitute the literal chain entries, quotients and scales, retaining
serialized degrees for subsequent checking. No producer or division runs. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (cert : SignedRemainderChain F) : SignedRemainderChain G := by
  classical
  exact {
    chain := cert.chain.map (fun p => interpretation.polynomial p)
    degrees := cert.degrees
    initial := cert.initial.substitute interpretation
    steps := cert.steps.map (fun step => step.substitute interpretation)
    terminal := cert.terminal.map (fun pair =>
      (interpretation.map pair.1, interpretation.polynomial pair.2)) }

/-- All literal coefficients and scales in the supplied chain.
This finite family supplies regularity and degree/zero preservation for its
stored polynomials; endpoint evaluation signs are separate query obligations. -/
@[expose] noncomputable def coefficients (cert : SignedRemainderChain F) :
    Finset F := by
  classical
  exact (cert.chain.toList.flatMap (fun p => p.toArray.toList)).toFinset ∪
    cert.initial.stored ∪
    (cert.steps.toList.flatMap (fun step => step.stored.toList)).toFinset ∪
    (cert.terminal.toList.flatMap (fun pair => pair.1 :: pair.2.toArray.toList)).toFinset

/-- Default-indexed reads commute with literal chain substitution. -/
theorem entry_map (interpretation : RealClosure.CoefficientMap F G)
    (cert : SignedRemainderChain F) (i : Nat) :
    (cert.substitute interpretation).chain.getD i 0 =
      interpretation.polynomial (cert.chain.getD i 0) := by
  classical
  change (cert.chain.map (fun p => interpretation.polynomial p)).getD i 0 = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getD_eq_getD_getElem?]
  cases h : cert.chain[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact ((polynomial_zero interpretation 0 (by simp)).mpr rfl).symm
  | some p => simp only [Option.map_some, Option.getD_some]

/-- Every accepted literal chain check is preserved when its finite coefficient
and scale family lies in the domain, reflects zero and retains the supplied signs. -/
theorem check_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (p f : DensePoly F)
    (cert : SignedRemainderChain F)
    (data : ∀ x ∈ cert.coefficients ∪ (p.toArray.toList ++ f.toArray.toList).toFinset,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : check sign p f cert = true) :
    check targetSign
      (interpretation.polynomial p) (interpretation.polynomial f) (cert.substitute interpretation) = true := by
  classical
  have from_cert x (hx : x ∈ cert.coefficients) := data x (Finset.mem_union_left _ hx)
  have p_data i (hi : i < p.size) := data (p.coeff i)
    (Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.mem_append.mpr (Or.inl (RealClosure.CoefficientMap.coefficient_mem p i hi)))))
  have f_data i (hi : i < f.size) := data (f.coeff i)
    (Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.mem_append.mpr (Or.inr (RealClosure.CoefficientMap.coefficient_mem f i hi)))))
  have row_data r (hr : r ∈ cert.chain.toList) i (hi : i < r.size) := from_cert (r.coeff i) (by
    simp only [coefficients, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (List.mem_toFinset.mpr
      (List.mem_flatMap.mpr ⟨r, hr, RealClosure.CoefficientMap.coefficient_mem r i hi⟩)))))
  have initial_data x (hx : x ∈ cert.initial.stored) := from_cert x (by
    simp only [coefficients, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr hx)))
  have step_data s (hs : s ∈ cert.steps.toList) x (hx : x ∈ s.stored) := from_cert x (by
    simp only [coefficients, Finset.mem_union]
    exact Or.inl (Or.inr (List.mem_toFinset.mpr
      (List.mem_flatMap.mpr ⟨s, hs, Finset.mem_toList.mpr hx⟩))))
  have entry_regular i : ∀ j < (cert.chain.getD i 0).size,
      (cert.chain.getD i 0).coeff j ∈ interpretation.domain := by
    rw [Array.getD_eq_getD_getElem?]
    cases h : cert.chain[i]? with
    | none => simp only [Option.getD_none]; intro j hj; simp at hj
    | some r =>
      simp only [Option.getD_some]
      exact fun j hj => (row_data r (by simpa using Array.mem_of_getElem? h) j hj).1
  have entry_reflects i : ∀ j < (cert.chain.getD i 0).size,
      interpretation.map ((cert.chain.getD i 0).coeff j) = 0 ↔ (cert.chain.getD i 0).coeff j = 0 := by
    rw [Array.getD_eq_getD_getElem?]
    cases h : cert.chain[i]? with
    | none => simp only [Option.getD_none]; intro j hj; simp at hj
    | some r =>
      simp only [Option.getD_some]
      exact fun j hj => (row_data r (by simpa using Array.mem_of_getElem? h) j hj).2.1
  have source := accepted
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at source
  obtain ⟨hp, hn, hb, hh, hd, hnonzero, hdesc, hl, hr, hi, ht⟩ := source
  have psize := RealClosure.CoefficientMap.polynomial_size interpretation p (fun i hi => (p_data i hi).2.1)
  have rowsize i := RealClosure.CoefficientMap.polynomial_size interpretation (cert.chain.getD i 0) (entry_reflects i)
  have chain_size : (cert.substitute interpretation).chain.size = cert.chain.size := by simp [substitute]
  have degree_map : (cert.chain.map (fun r => interpretation.polynomial r)).map DensePoly.natDegree =
      cert.chain.map DensePoly.natDegree := by
    rw [Array.map_map]
    apply Array.ext (by simp)
    intro i hi hj
    simp only [Array.getElem_map]
    have bound : i < cert.chain.size := by simpa using hi
    have member : cert.chain[i] ∈ cert.chain.toList := by
      simp
    apply polynomial_degree
    intro j hj
    exact (row_data cert.chain[i] member j hj).2.1
  simp only [check, chain_size, psize, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨?_, hn, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [RealClosure.CoefficientMap.polynomial_isZero interpretation p (fun i hi => (p_data i hi).2.1)] using hp
  · simp only [substitute, Array.getElem?_map, hh, Option.map_some]
  · simpa only [substitute, Hex.Array.map'_eq_map, degree_map] using hd
  · rw [← chain_size]
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro r hr
    simp only [substitute, Array.mem_map] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    have zero := RealClosure.CoefficientMap.polynomial_isZero interpretation q (fun i hi => (row_data q (by simpa using hq) i hi).2.1)
    simpa only [zero] using
      Array.all_eq_true_iff_forall_mem.mp hnonzero q hq
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro i hi
    simpa only [entry_map, rowsize, chain_size] using
      Array.all_eq_true_iff_forall_mem.mp hdesc i hi
  · have sign := (initial_data cert.initial.leftScale (by simp [RemainderStep.stored])).2.2
    simpa only [substitute, RemainderStep.substitute, sign] using hl
  · have sign := (initial_data cert.initial.rightScale (by simp [RemainderStep.stored])).2.2
    simpa only [substitute, RemainderStep.substitute, sign] using hr
  · rw [entry_map]
    exact RealClosure.CoefficientMap.initial_map interpretation p f (cert.chain.getD 1 0) cert.initial
      (fun i hi => (p_data i hi).1) (fun i hi => (f_data i hi).1) (entry_regular 1)
      (fun i hi => (initial_data (cert.initial.quotient.coeff i) (by
        simp only [RemainderStep.stored, Finset.mem_union]
        exact Or.inl (List.mem_toFinset.mpr (RealClosure.CoefficientMap.coefficient_mem _ i hi)))).1)
      (initial_data cert.initial.leftScale (by simp [RemainderStep.stored])).1
      (initial_data cert.initial.rightScale (by simp [RemainderStep.stored])).1 hi
  · by_cases single : cert.chain.size = 1
    · simp only [single, ↓reduceIte, Bool.and_eq_true] at ht ⊢
      constructor
      · simpa only [substitute, Array.isEmpty, Array.size_map] using ht.1
      · simpa only [substitute, Option.isNone_map] using ht.2
    · simp only [single, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at ht ⊢
      refine ⟨?_, ?_, ?_⟩
      · simpa only [substitute, Array.size_map] using ht.1
      · apply Array.all_eq_true_iff_forall_mem.mpr
        intro i hi
        have idx : i < cert.steps.size := by simpa only [substitute, Array.size_map] using Array.mem_range.mp hi
        have idx' : i < (cert.substitute interpretation).steps.size := by simpa [substitute] using idx
        have step_mem : cert.steps[i] ∈ cert.steps.toList := by
          simp
        have step_regular j (hj : j < cert.steps[i].quotient.size) :=
          (step_data cert.steps[i] step_mem (cert.steps[i].quotient.coeff j) (by
            simp only [RemainderStep.stored, Finset.mem_union]
            exact Or.inl (List.mem_toFinset.mpr (RealClosure.CoefficientMap.coefficient_mem _ j hj)))).1
        rw [entry_map, entry_map, entry_map,
          ← Array.getElem_eq_getD (h := idx') ⟨0, 0, 0⟩]
        simp only [substitute, Array.getElem_map]
        apply RemainderStep.check_map interpretation sign targetSign _ _ _ cert.steps[i]
          (entry_regular i) (entry_regular (i + 1)) (entry_regular (i + 2)) step_regular
          (step_data _ step_mem _ (by simp [RemainderStep.stored])).1
          (step_data _ step_mem _ (by simp [RemainderStep.stored])).1
          (step_data _ step_mem _ (by simp [RemainderStep.stored])).2.2
          (step_data _ step_mem _ (by simp [RemainderStep.stored])).2.2
        simpa only [← Array.getElem_eq_getD (h := idx) ⟨0, 0, 0⟩] using
          Array.all_eq_true_iff_forall_mem.mp ht.2.1 i (Array.mem_range.mpr idx)
      · cases terminal : cert.terminal with
        | none => simp only [terminal, Bool.false_eq_true] at ht; exact ht.2.2.elim
        | some pair =>
          obtain ⟨scale, q⟩ := pair
          have terminal_data x (hx : x ∈ scale :: q.toArray.toList) := from_cert x (by
            simp only [coefficients, Finset.mem_union, terminal, Option.toList_some]
            exact Or.inr (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨(scale, q), by simp, hx⟩)))
          rw [show (cert.substitute interpretation).terminal =
            some (interpretation.map scale, interpretation.polynomial q) by
              simp only [substitute, terminal, Option.map_some]]
          change (decide (targetSign (interpretation.map scale) = 1) &&
            subIsZero (DensePoly.scale (interpretation.map scale)
              ((cert.substitute interpretation).chain.getD (cert.chain.size - 2) 0))
              (interpretation.polynomial q *
                (cert.substitute interpretation).chain.getD (cert.chain.size - 1) 0)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          simp only [terminal, Bool.and_eq_true, decide_eq_true_eq] at ht
          refine ⟨?_, ?_⟩
          · rw [(terminal_data scale (by simp)).2.2]
            exact ht.2.2.1
          · rw [entry_map, entry_map]
            exact RealClosure.CoefficientMap.terminal_map interpretation _ _ q scale
              (entry_regular _) (entry_regular _)
              (fun i hi => (terminal_data (q.coeff i) (List.mem_cons.mpr
                (Or.inr (RealClosure.CoefficientMap.coefficient_mem q i hi)))).1)
              (terminal_data scale (by simp)).1 ht.2.2.2

/-- The actual first-parameter map preserves a complete accepted chain on
one positive neighborhood. All finite guards come from its literal inventory. -/
theorem firstMap_near
    (p f : DensePoly (RationalFn (RationalFn ℝ)))
    (cert : SignedRemainderChain (RationalFn (RationalFn ℝ)))
    (accepted : check
      (OrderedFn.Infinitesimal.sign (OrderedFn.Infinitesimal.sign OrderedFn.orderSign))
      p f cert = true) :
    ∀ᶠ first in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      check (OrderedFn.Infinitesimal.sign OrderedFn.orderSign)
        ((RealClosure.Specialize.firstMap first).polynomial p)
        ((RealClosure.Specialize.firstMap first).polynomial f)
        (cert.substitute (RealClosure.Specialize.firstMap first)) = true := by
  filter_upwards [RealClosure.Specialize.firstMap_near
    (cert.coefficients ∪ (p.toArray.toList ++ f.toArray.toList).toFinset)] with first data
  exact check_map (RealClosure.Specialize.firstMap first) _ _ p f cert data accepted

/-- info: 'Hex.SignedRemainderChain.check_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignedRemainderChain.check_map

/-- info: 'Hex.SignedRemainderChain.firstMap_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignedRemainderChain.firstMap_near

end Hex.SignedRemainderChain

/-- info: 'Hex.RemainderStep.check_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RemainderStep.check_map

/-- info: 'Hex.RemainderStep.firstMap_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RemainderStep.firstMap_near
