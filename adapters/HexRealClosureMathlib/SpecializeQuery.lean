/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializeRegular
public import HexRealRoots.Tarski

public section

namespace Hex.RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField

private theorem subIsZero_eq {K : Type} [Field K] [DecidableEq K]
    (p q : Hex.DensePoly K) :
    Hex.SignedRemainderChain.subIsZero p q = true ↔
      HexPolyMathlib.toPolynomial p = HexPolyMathlib.toPolynomial q := by
  rw [Hex.SignedRemainderChain.subIsZero, Hex.DensePoly.isZero_eq_true_iff,
    Hex.DensePoly.size_eq_zero_iff]
  constructor
  · intro zero
    have zero := congrArg (HexPolyMathlib.toPolynomial (R := K)) zero
    rw [HexPolyMathlib.toPolynomial_sub, HexPolyMathlib.toPolynomial_zero] at zero
    exact sub_eq_zero.mp zero
  · intro equal
    apply (HexPolyMathlib.equiv (R := K)).injective
    change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
    rw [HexPolyMathlib.toPolynomial_sub, HexPolyMathlib.toPolynomial_zero, equal, sub_self]

variable {F : Type} [Field F] [DecidableEq F]

/-- Finite coefficient zero reflection preserves the actual stored size. -/
theorem polynomial_size (embedding : F →+* ℝ) (p : Hex.DensePoly (Hex.RationalFn F)) (t : ℝ)
    (reflects : ∀ i < p.size, evalMapped embedding (p.coeff i) t = 0 ↔ p.coeff i = 0) :
    (polynomial embedding p t).size = p.size := by
  classical
  by_cases hp : p = 0
  · rw [hp, (polynomial_zero embedding 0 t (by simp)).mpr rfl]
    rfl
  · have source : p.size ≠ 0 := fun h => hp ((Hex.DensePoly.size_eq_zero_iff p).mp h)
    have target : (polynomial embedding p t).size ≠ 0 := by
      intro h
      exact hp ((polynomial_zero embedding p t reflects).mp
        ((Hex.DensePoly.size_eq_zero_iff _).mp h))
    have degree := polynomial_degree embedding p t reflects
    simp only [Hex.DensePoly.natDegree_eq_size_sub_one] at degree
    omega

/-- Finite coefficient zero reflection preserves the executable zero test. -/
theorem polynomial_isZero (embedding : F →+* ℝ) (p : Hex.DensePoly (Hex.RationalFn F)) (t : ℝ)
    (reflects : ∀ i < p.size, evalMapped embedding (p.coeff i) t = 0 ↔ p.coeff i = 0) :
    (polynomial embedding p t).isZero = p.isZero := by
  classical
  change ((polynomial embedding p t).size == 0) = (p.size == 0)
  rw [polynomial_size embedding p t reflects]

/-- Every stored coefficient belongs to the literal finite coefficient array. -/
theorem coefficient_mem (p : Hex.DensePoly (Hex.RationalFn F)) (i : Nat) (hi : i < p.size) :
    p.coeff i ∈ p.toArray.toList := by
  have hi' : i < p.toArray.size := by simpa using hi
  have entry : p.toArray[i]? = some (p.coeff i) := by
    rw [Array.getElem?_eq_getElem hi', ← Hex.DensePoly.toArray_getD]
    congr 1
    exact Array.getElem_eq_getD (h := hi') 0
  simpa using Array.mem_of_getElem? entry

private theorem initial_specialize (embedding : F →+* ℝ) (t : ℝ)
    (p f c : Hex.DensePoly (Hex.RationalFn F)) (step : Hex.RemainderStep (Hex.RationalFn F))
    (hp : ∀ i < p.size, Regular embedding t (p.coeff i))
    (hf : ∀ i < f.size, Regular embedding t (f.coeff i))
    (hc : ∀ i < c.size, Regular embedding t (c.coeff i))
    (hq : ∀ i < step.quotient.size, Regular embedding t (step.quotient.coeff i))
    (hl : Regular embedding t step.leftScale) (hr : Regular embedding t step.rightScale)
    (accepted : Hex.SignedRemainderChain.subIsZero
      (Hex.DensePoly.scale step.leftScale (f * p.derivative))
      (step.quotient * p + Hex.DensePoly.scale step.rightScale c) = true) :
    Hex.SignedRemainderChain.subIsZero
      (Hex.DensePoly.scale (evalMapped embedding step.leftScale t)
        (polynomial embedding f t * (polynomial embedding p t).derivative))
      (polynomial embedding step.quotient t * polynomial embedding p t +
        Hex.DensePoly.scale (evalMapped embedding step.rightScale t) (polynomial embedding c t)) = true := by
  classical
  obtain ⟨P, hP⟩ := polynomial_lift embedding t p hp
  obtain ⟨G, hG⟩ := polynomial_lift embedding t f hf
  obtain ⟨C, hC⟩ := polynomial_lift embedding t c hc
  obtain ⟨Q, hQ⟩ := polynomial_lift embedding t step.quotient hq
  have native := (subIsZero_eq _ _).mp accepted
  have lifted : Polynomial.C (⟨step.leftScale, hl⟩ : regularRing embedding t) * (G * P.derivative) =
      Q * P + Polynomial.C (⟨step.rightScale, hr⟩ : regularRing embedding t) * C := by
    apply Polynomial.map_injective (regularRing embedding t).subtype Subtype.val_injective
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
      ← Polynomial.derivative_map, hP, hG, hC, hQ, Subring.subtype_apply]
    simpa only [HexPolyMathlib.toPolynomial_scale, HexPolyMathlib.toPolynomial_mul,
      HexPolyMathlib.toPolynomial_add, HexPolyMathlib.toPolynomial_derivative] using native
  have evaluated := congrArg (Polynomial.map (evaluation embedding t)) lifted
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
    ← Polynomial.derivative_map] at evaluated
  have left : evaluation embedding t (⟨step.leftScale, hl⟩ : regularRing embedding t) =
      evalMapped embedding step.leftScale t := rfl
  have right : evaluation embedding t (⟨step.rightScale, hr⟩ : regularRing embedding t) =
      evalMapped embedding step.rightScale t := rfl
  rw [left, right] at evaluated
  apply (subIsZero_eq _ _).mpr
  simpa only [HexPolyMathlib.toPolynomial_scale, HexPolyMathlib.toPolynomial_mul,
    HexPolyMathlib.toPolynomial_add, HexPolyMathlib.toPolynomial_derivative,
    polynomial_map embedding t p P hP, polynomial_map embedding t f G hG,
    polynomial_map embedding t c C hC, polynomial_map embedding t step.quotient Q hQ] using evaluated

private theorem terminal_specialize (embedding : F →+* ℝ) (t : ℝ)
    (a b q : Hex.DensePoly (Hex.RationalFn F)) (scale : Hex.RationalFn F)
    (ha : ∀ i < a.size, Regular embedding t (a.coeff i))
    (hb : ∀ i < b.size, Regular embedding t (b.coeff i))
    (hq : ∀ i < q.size, Regular embedding t (q.coeff i))
    (hs : Regular embedding t scale)
    (accepted : Hex.SignedRemainderChain.subIsZero (Hex.DensePoly.scale scale a) (q * b) = true) :
    Hex.SignedRemainderChain.subIsZero
      (Hex.DensePoly.scale (evalMapped embedding scale t) (polynomial embedding a t))
      (polynomial embedding q t * polynomial embedding b t) = true := by
  classical
  obtain ⟨A, hA⟩ := polynomial_lift embedding t a ha
  obtain ⟨B, hB⟩ := polynomial_lift embedding t b hb
  obtain ⟨Q, hQ⟩ := polynomial_lift embedding t q hq
  have native := (subIsZero_eq _ _).mp accepted
  have lifted : Polynomial.C (⟨scale, hs⟩ : regularRing embedding t) * A = Q * B := by
    apply Polynomial.map_injective (regularRing embedding t).subtype Subtype.val_injective
    simp only [Polynomial.map_mul, Polynomial.map_C, hA, hB, hQ,
      Subring.subtype_apply]
    simpa only [HexPolyMathlib.toPolynomial_scale, HexPolyMathlib.toPolynomial_mul] using native
  have evaluated := congrArg (Polynomial.map (evaluation embedding t)) lifted
  simp only [Polynomial.map_mul, Polynomial.map_C] at evaluated
  have scalar : evaluation embedding t (⟨scale, hs⟩ : regularRing embedding t) =
      evalMapped embedding scale t := rfl
  rw [scalar] at evaluated
  apply (subIsZero_eq _ _).mpr
  simpa only [HexPolyMathlib.toPolynomial_scale, HexPolyMathlib.toPolynomial_mul,
    polynomial_map embedding t a A hA, polynomial_map embedding t b B hB,
    polynomial_map embedding t q Q hQ] using evaluated

end Hex.RealClosure.Specialize

namespace Hex.RemainderStep
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute the actual stored scalar and quotient data of one remainder
step, retaining its supplied recurrence rather than recomputing division. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (step : RemainderStep (RationalFn F)) : RemainderStep ℝ := by
  classical
  exact ⟨evalMapped embedding step.leftScale t, polynomial embedding step.quotient t,
    evalMapped embedding step.rightScale t⟩

/-- An accepted signed recurrence remains accepted after finite regular
coefficient substitution and preservation of its two recorded scale signs. -/
theorem check_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (a b c : DensePoly (RationalFn F))
    (step : RemainderStep (RationalFn F))
    (ha : ∀ i < a.size, Regular embedding t (a.coeff i))
    (hb : ∀ i < b.size, Regular embedding t (b.coeff i))
    (hc : ∀ i < c.size, Regular embedding t (c.coeff i))
    (hq : ∀ i < step.quotient.size, Regular embedding t (step.quotient.coeff i))
    (hl : Regular embedding t step.leftScale) (hr : Regular embedding t step.rightScale)
    (sl : (SignType.sign (evalMapped embedding step.leftScale t) : Int) = sign step.leftScale)
    (sr : (SignType.sign (evalMapped embedding step.rightScale t) : Int) = sign step.rightScale)
    (accepted : SignedRemainderChain.checkStep sign a b c step = true) :
    SignedRemainderChain.checkStep (fun x : ℝ => (SignType.sign x : Int))
      (polynomial embedding a t) (polynomial embedding b t) (polynomial embedding c t)
      (step.specialize embedding t) = true := by
  classical
  simp only [SignedRemainderChain.checkStep, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at accepted ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa only [specialize, sl] using accepted.1
  · simpa only [specialize, sr] using accepted.2.1
  · obtain ⟨A, hA⟩ := polynomial_lift embedding t a ha
    obtain ⟨B, hB⟩ := polynomial_lift embedding t b hb
    obtain ⟨C, hC⟩ := polynomial_lift embedding t c hc
    obtain ⟨Q, hQ⟩ := polynomial_lift embedding t step.quotient hq
    have native := (RealClosure.Specialize.subIsZero_eq _ _).mp accepted.2.2
    have lifted : Polynomial.C (⟨step.leftScale, hl⟩ : regularRing embedding t) * A =
        Q * B - Polynomial.C (⟨step.rightScale, hr⟩ : regularRing embedding t) * C := by
      apply Polynomial.map_injective (regularRing embedding t).subtype Subtype.val_injective
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_C, hA, hB, hC, hQ]
      simpa only [Subring.subtype_apply, Subtype.coe_mk, HexPolyMathlib.toPolynomial_scale,
        HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_sub] using native
    have evaluated := congrArg (Polynomial.map (evaluation embedding t)) lifted
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C] at evaluated
    have left : evaluation embedding t (⟨step.leftScale, hl⟩ : regularRing embedding t) =
        evalMapped embedding step.leftScale t := rfl
    have right : evaluation embedding t (⟨step.rightScale, hr⟩ : regularRing embedding t) =
        evalMapped embedding step.rightScale t := rfl
    rw [left, right] at evaluated
    apply (RealClosure.Specialize.subIsZero_eq _ _).mpr
    simpa only [specialize, HexPolyMathlib.toPolynomial_scale, HexPolyMathlib.toPolynomial_mul,
      HexPolyMathlib.toPolynomial_sub, polynomial_map embedding t a A hA,
      polynomial_map embedding t b B hB, polynomial_map embedding t c C hC,
      polynomial_map embedding t step.quotient Q hQ] using evaluated

/-- The finite native fraction data needed by the step's local substitution. -/
@[expose] noncomputable def fractions (step : RemainderStep (RationalFn F)) :
    Finset (RationalFn F) := by
  classical
  exact step.quotient.toArray.toList.toFinset ∪ {step.leftScale, step.rightScale}

/-- info: 'Hex.RemainderStep.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RemainderStep.check_specialize

end Hex.RemainderStep

namespace Hex.SignedRemainderChain
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute the literal chain entries, quotients and scales, retaining
serialized degrees for subsequent checking. No producer or division runs. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (cert : SignedRemainderChain (RationalFn F)) : SignedRemainderChain ℝ := by
  classical
  exact {
    chain := cert.chain.map (fun p => polynomial embedding p t)
    degrees := cert.degrees
    initial := cert.initial.specialize embedding t
    steps := cert.steps.map (fun step => step.specialize embedding t)
    terminal := cert.terminal.map (fun pair =>
      (evalMapped embedding pair.1 t, polynomial embedding pair.2 t)) }

/-- All literal fraction coefficients and scales in the supplied chain.
This finite family supplies regularity and degree/zero preservation for its
stored polynomials; endpoint evaluation signs are separate query obligations. -/
@[expose] noncomputable def fractions (cert : SignedRemainderChain (RationalFn F)) :
    Finset (RationalFn F) := by
  classical
  exact (cert.chain.toList.flatMap (fun p => p.toArray.toList)).toFinset ∪
    cert.initial.fractions ∪
    (cert.steps.toList.flatMap (fun step => step.fractions.toList)).toFinset ∪
    (cert.terminal.toList.flatMap (fun pair => pair.1 :: pair.2.toArray.toList)).toFinset

/-- Default-indexed reads commute with literal chain substitution. -/
theorem entry_specialize (embedding : F →+* ℝ) (t : ℝ)
    (cert : SignedRemainderChain (RationalFn F)) (i : Nat) :
    (cert.specialize embedding t).chain.getD i 0 =
      polynomial embedding (cert.chain.getD i 0) t := by
  classical
  change (cert.chain.map (fun p => polynomial embedding p t)).getD i 0 = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getD_eq_getD_getElem?]
  cases h : cert.chain[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact ((polynomial_zero embedding 0 t (by simp)).mpr rfl).symm
  | some p => simp only [Option.map_some, Option.getD_some]

/-- Every accepted literal chain check is preserved when its finite coefficient
and scale family is regular, reflects zero and retains the supplied signs. -/
theorem check_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (p f : DensePoly (RationalFn F))
    (cert : SignedRemainderChain (RationalFn F))
    (data : ∀ x ∈ cert.fractions ∪ (p.toArray.toList ++ f.toArray.toList).toFinset,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : check sign p f cert = true) :
    check (fun x : ℝ => (SignType.sign x : Int))
      (polynomial embedding p t) (polynomial embedding f t) (cert.specialize embedding t) = true := by
  classical
  have from_cert x (hx : x ∈ cert.fractions) := data x (Finset.mem_union_left _ hx)
  have p_data i (hi : i < p.size) := data (p.coeff i)
    (Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.mem_append.mpr (Or.inl (RealClosure.Specialize.coefficient_mem p i hi)))))
  have f_data i (hi : i < f.size) := data (f.coeff i)
    (Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.mem_append.mpr (Or.inr (RealClosure.Specialize.coefficient_mem f i hi)))))
  have row_data r (hr : r ∈ cert.chain.toList) i (hi : i < r.size) := from_cert (r.coeff i) (by
    simp only [fractions, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (List.mem_toFinset.mpr
      (List.mem_flatMap.mpr ⟨r, hr, RealClosure.Specialize.coefficient_mem r i hi⟩)))))
  have initial_data x (hx : x ∈ cert.initial.fractions) := from_cert x (by
    simp only [fractions, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr hx)))
  have step_data s (hs : s ∈ cert.steps.toList) x (hx : x ∈ s.fractions) := from_cert x (by
    simp only [fractions, Finset.mem_union]
    exact Or.inl (Or.inr (List.mem_toFinset.mpr
      (List.mem_flatMap.mpr ⟨s, hs, Finset.mem_toList.mpr hx⟩))))
  have entry_regular i : ∀ j < (cert.chain.getD i 0).size,
      Regular embedding t ((cert.chain.getD i 0).coeff j) := by
    rw [Array.getD_eq_getD_getElem?]
    cases h : cert.chain[i]? with
    | none => simp only [Option.getD_none]; intro j hj; simp at hj
    | some r =>
      simp only [Option.getD_some]
      exact fun j hj => (row_data r (by simpa using Array.mem_of_getElem? h) j hj).1
  have entry_reflects i : ∀ j < (cert.chain.getD i 0).size,
      evalMapped embedding ((cert.chain.getD i 0).coeff j) t = 0 ↔ (cert.chain.getD i 0).coeff j = 0 := by
    rw [Array.getD_eq_getD_getElem?]
    cases h : cert.chain[i]? with
    | none => simp only [Option.getD_none]; intro j hj; simp at hj
    | some r =>
      simp only [Option.getD_some]
      exact fun j hj => (row_data r (by simpa using Array.mem_of_getElem? h) j hj).2.1
  have source := accepted
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at source
  obtain ⟨hp, hn, hb, hh, hd, hnonzero, hdesc, hl, hr, hi, ht⟩ := source
  have psize := RealClosure.Specialize.polynomial_size embedding p t (fun i hi => (p_data i hi).2.1)
  have rowsize i := RealClosure.Specialize.polynomial_size embedding (cert.chain.getD i 0) t (entry_reflects i)
  have chain_size : (cert.specialize embedding t).chain.size = cert.chain.size := by simp [specialize]
  have degree_map : (cert.chain.map (fun r => polynomial embedding r t)).map DensePoly.natDegree =
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
  · simpa only [RealClosure.Specialize.polynomial_isZero embedding p t (fun i hi => (p_data i hi).2.1)] using hp
  · simp only [specialize, Array.getElem?_map, hh, Option.map_some]
  · simpa only [specialize, Hex.Array.map'_eq_map, degree_map] using hd
  · rw [← chain_size]
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro r hr
    simp only [specialize, Array.mem_map] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    have zero := RealClosure.Specialize.polynomial_isZero embedding q t (fun i hi => (row_data q (by simpa using hq) i hi).2.1)
    simpa only [zero] using
      Array.all_eq_true_iff_forall_mem.mp hnonzero q hq
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro i hi
    simpa only [entry_specialize, rowsize, chain_size] using
      Array.all_eq_true_iff_forall_mem.mp hdesc i hi
  · have sign := (initial_data cert.initial.leftScale (by simp [RemainderStep.fractions])).2.2
    simpa only [specialize, RemainderStep.specialize, sign] using hl
  · have sign := (initial_data cert.initial.rightScale (by simp [RemainderStep.fractions])).2.2
    simpa only [specialize, RemainderStep.specialize, sign] using hr
  · rw [entry_specialize]
    exact RealClosure.Specialize.initial_specialize embedding t p f (cert.chain.getD 1 0) cert.initial
      (fun i hi => (p_data i hi).1) (fun i hi => (f_data i hi).1) (entry_regular 1)
      (fun i hi => (initial_data (cert.initial.quotient.coeff i) (by
        simp only [RemainderStep.fractions, Finset.mem_union]
        exact Or.inl (List.mem_toFinset.mpr (RealClosure.Specialize.coefficient_mem _ i hi)))).1)
      (initial_data cert.initial.leftScale (by simp [RemainderStep.fractions])).1
      (initial_data cert.initial.rightScale (by simp [RemainderStep.fractions])).1 hi
  · by_cases single : cert.chain.size = 1
    · simp only [single, ↓reduceIte, Bool.and_eq_true] at ht ⊢
      constructor
      · simpa only [specialize, Array.isEmpty, Array.size_map] using ht.1
      · simpa only [specialize, Option.isNone_map] using ht.2
    · simp only [single, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at ht ⊢
      refine ⟨?_, ?_, ?_⟩
      · simpa only [specialize, Array.size_map] using ht.1
      · apply Array.all_eq_true_iff_forall_mem.mpr
        intro i hi
        have idx : i < cert.steps.size := by simpa only [specialize, Array.size_map] using Array.mem_range.mp hi
        have idx' : i < (cert.specialize embedding t).steps.size := by simpa [specialize] using idx
        have step_mem : cert.steps[i] ∈ cert.steps.toList := by
          simp
        have step_regular j (hj : j < cert.steps[i].quotient.size) :=
          (step_data cert.steps[i] step_mem (cert.steps[i].quotient.coeff j) (by
            simp only [RemainderStep.fractions, Finset.mem_union]
            exact Or.inl (List.mem_toFinset.mpr (RealClosure.Specialize.coefficient_mem _ j hj)))).1
        rw [entry_specialize, entry_specialize, entry_specialize,
          ← Array.getElem_eq_getD (h := idx') ⟨0, 0, 0⟩]
        simp only [specialize, Array.getElem_map]
        apply RemainderStep.check_specialize embedding t sign _ _ _ cert.steps[i]
          (entry_regular i) (entry_regular (i + 1)) (entry_regular (i + 2)) step_regular
          (step_data _ step_mem _ (by simp [RemainderStep.fractions])).1
          (step_data _ step_mem _ (by simp [RemainderStep.fractions])).1
          (step_data _ step_mem _ (by simp [RemainderStep.fractions])).2.2
          (step_data _ step_mem _ (by simp [RemainderStep.fractions])).2.2
        simpa only [← Array.getElem_eq_getD (h := idx) ⟨0, 0, 0⟩] using
          Array.all_eq_true_iff_forall_mem.mp ht.2.1 i (Array.mem_range.mpr idx)
      · cases terminal : cert.terminal with
        | none => simp only [terminal, Bool.false_eq_true] at ht; exact ht.2.2.elim
        | some pair =>
          obtain ⟨scale, q⟩ := pair
          have terminal_data x (hx : x ∈ scale :: q.toArray.toList) := from_cert x (by
            simp only [fractions, Finset.mem_union, terminal, Option.toList_some]
            exact Or.inr (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨(scale, q), by simp, hx⟩)))
          rw [show (cert.specialize embedding t).terminal =
            some (evalMapped embedding scale t, polynomial embedding q t) by
              simp only [specialize, terminal, Option.map_some]]
          change (decide ((SignType.sign (evalMapped embedding scale t) : Int) = 1) &&
            subIsZero (DensePoly.scale (evalMapped embedding scale t)
              ((cert.specialize embedding t).chain.getD (cert.chain.size - 2) 0))
              (polynomial embedding q t *
                (cert.specialize embedding t).chain.getD (cert.chain.size - 1) 0)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          simp only [terminal, Bool.and_eq_true, decide_eq_true_eq] at ht
          refine ⟨?_, ?_⟩
          · rw [(terminal_data scale (by simp)).2.2]
            exact ht.2.2.1
          · rw [entry_specialize, entry_specialize]
            exact RealClosure.Specialize.terminal_specialize embedding t _ _ q scale
              (entry_regular _) (entry_regular _)
              (fun i hi => (terminal_data (q.coeff i) (List.mem_cons.mpr
                (Or.inr (RealClosure.Specialize.coefficient_mem q i hi)))).1)
              (terminal_data scale (by simp)).1 ht.2.2.2

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- A single positive neighborhood preserves the entire accepted chain replay,
including initial/terminal identities, nonzero entries, degrees and descent. -/
theorem specialize_near (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (p f : DensePoly (RationalFn F)) (cert : SignedRemainderChain (RationalFn F))
    (accepted : check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) p f cert = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      check (fun x : ℝ => (SignType.sign x : Int))
        (polynomial embedding p t) (polynomial embedding f t) (cert.specialize embedding t) = true := by
  classical
  obtain ⟨η, positive, signs⟩ := finite_fractions_map embedding ordered
    (cert.fractions ∪ (p.toArray.toList ++ f.toArray.toList).toFinset)
  refine ⟨η, positive, fun t ht small => ?_⟩
  apply check_specialize embedding t _ p f cert _ accepted
  intro x hx
  have preserved := signs t ht small x hx
  exact ⟨preserved.1, fraction_zero embedding x t preserved.2, preserved.2⟩

/-- info: 'Hex.SignedRemainderChain.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignedRemainderChain.check_specialize

/-- info: 'Hex.SignedRemainderChain.specialize_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignedRemainderChain.specialize_near

end Hex.SignedRemainderChain

