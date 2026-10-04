/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.MonicEvaluation
public import HexRealClosureMathlib.ModelEvaluation
public import HexRealClosureMathlib.TransportSelected
public import HexSignDetMathlib.SelectedProducer

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {context : Context registry}
variable {K G : Type} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [IsRealClosed K] [Field G] [DecidableEq G]

/-- Build a native checked zero query for the original selected generator's
actual minimal polynomial. Both the finite native representative and successful
query production are conclusions. -/
theorem minimal_query (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    ∃ q : DensePoly context.Value,
      model.polynomial q = minpoly model.field
        ((model.adjoin descriptor).value (context.adjoin descriptor).generator) ∧
      ∃ s : SignDet.SelectedSigns descriptor [q],
        descriptor.buildSigns [q] = .ok s ∧ s.values.toList = [0] := by
  classical
  obtain ⟨q, original⟩ := model.polynomial_surjective
    (minpoly model.field ((model.adjoin descriptor).value (context.adjoin descriptor).generator))
  obtain ⟨s, built, values⟩ := descriptor.buildSigns_roots model.value model.zero_iff
    model.one model.add model.sub model.mul model.nat model.sign model.neg model.inv [q]
  refine ⟨q, original, s, built, ?_⟩
  have zero : (HexPolyMathlib.Interpret.interpret model.value model.zero_iff q).eval
      (descriptor.root model.value model.zero_iff model.one model.add model.sub
        model.mul model.nat model.sign) = 0 := by
    rw [← model.adjoin_generator descriptor, ← model.polynomial_eval, original]
    exact minpoly.aeval model.field _
  simp only [SignDet.signsAt, List.map_cons, List.map_nil, zero, sign_zero] at values
  change s.values.toList = [0] at values
  exact values

omit [DecidableEq G] in
/-- The actual native generator's minimal polynomial lifts to the guarded
coefficient subring. Monicity follows from its proved algebraicity. -/
theorem minimal_lift (model : Model context K)
    (interpretation : CoefficientMap model.field G)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (guards : ∀ i ≤ (minpoly model.field
      ((model.adjoin descriptor).value (context.adjoin descriptor).generator)).natDegree,
        (minpoly model.field
          ((model.adjoin descriptor).value (context.adjoin descriptor).generator)).coeff i ∈
            interpretation.domain) :
    ∃ minimal : Polynomial interpretation.domain, minimal.Monic ∧
      minimal.map interpretation.domain.subtype = minpoly model.field
        ((model.adjoin descriptor).value (context.adjoin descriptor).generator) := by
  classical
  let root := (model.adjoin descriptor).value (context.adjoin descriptor).generator
  have lifts : minpoly model.field root ∈ Polynomial.lifts interpretation.domain.subtype := by
    apply Polynomial.lifts_iff_coeff_lifts _ |>.mpr
    intro i
    refine ⟨⟨(minpoly model.field root).coeff i, ?_⟩, rfl⟩
    by_cases bound : i ≤ (minpoly model.field root).natDegree
    · exact guards i bound
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge bound)]
      exact interpretation.domain.zero_mem
  obtain ⟨minimal, original⟩ := (Polynomial.mem_lifts _).mp lifts
  refine ⟨minimal, ?_, original⟩
  apply Polynomial.monic_of_injective (f := interpretation.domain.subtype) Subtype.val_injective
  rw [original]
  exact minpoly.monic (model.generator_algebraic descriptor).isIntegral

/-- Specialization of an actual native algebraic value uses its retained
polynomial at the original descriptor's selected generator. A monic lift of
that generator's minimal polynomial makes the result independent of all
polynomial presentations. -/
theorem adjoin_evaluation (model : Model context K)
    (interpretation : CoefficientMap model.field G)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (selected : G) (minimal : Polynomial interpretation.domain) (monic : minimal.Monic)
    (original : minimal.map interpretation.domain.subtype =
      minpoly model.field ((model.adjoin descriptor).value (context.adjoin descriptor).generator))
    (chosen : minimal.eval₂ interpretation.value selected = 0)
    (a : (context.adjoin descriptor).context.Value)
    (guards : ∀ i < (context.polynomial descriptor a).size,
      model.domain interpretation ((context.polynomial descriptor a).coeff i)) :
    let root := (model.adjoin descriptor).value (context.adjoin descriptor).generator
    let extended := interpretation.algebraic root selected minimal monic original chosen
    (model.adjoin descriptor).value a ∈ extended.domain ∧
      extended.map ((model.adjoin descriptor).value a) =
        (HexPolyMathlib.toPolynomial
          (Transport.polynomial (model.read interpretation)
            (context.polynomial descriptor a))).eval selected := by
  classical
  let root := (model.adjoin descriptor).value (context.adjoin descriptor).generator
  obtain ⟨p, lift⟩ := model.polynomial_lift interpretation
    (context.polynomial descriptor a) guards
  have source : Specialize.Algebraic.source interpretation.domain root p =
      (model.adjoin descriptor).value a := by
    rw [Specialize.Algebraic.source_apply, ← Polynomial.eval₂_map,
      ← Polynomial.aeval_def, lift, model.polynomial_eval]
    exact (model.adjoin_value descriptor a).symm
  have evaluated := interpretation.algebraic_polynomial root selected minimal monic original chosen p
  rw [source] at evaluated
  refine ⟨evaluated.1, ?_⟩
  rw [model.polynomial_specialize interpretation _ p lift, Polynomial.eval_map]
  exact evaluated.2

variable [LinearOrder G] [IsStrictOrderedRing G] [IsRealClosed G]

/-- Interpret every guarded native child value at the one root selected by
the literal transported descriptor. The accepted minimal-polynomial query
derives the root equation required for presentation-independent evaluation. -/
theorem adjoin_checked (model : Model context K)
    (interpretation : CoefficientMap model.field G)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (q : DensePoly context.Value) (qs : List (DensePoly context.Value))
    (query : model.polynomial q = minpoly model.field
      ((model.adjoin descriptor).value (context.adjoin descriptor).generator))
    (s : SignDet.SelectedSigns descriptor (q :: qs))
    (descriptorData : Transport.DescriptorData (model.read interpretation)
      (model.domain interpretation) context.sign (fun a : G => (SignType.sign a : Int))
      descriptor.raw descriptor.evidence)
    (queryData : Transport.ReplayData (model.read interpretation) (model.domain interpretation)
      context.sign (fun a : G => (SignType.sign a : Int)) descriptor.raw.head
      descriptor.raw.lower descriptor.raw.upper (descriptor.raw.queries ++ q :: qs) s.evidence)
    (minimal : Polynomial interpretation.domain) (monic : minimal.Monic)
    (original : minimal.map interpretation.domain.subtype = minpoly model.field
      ((model.adjoin descriptor).value (context.adjoin descriptor).generator)) :
    let selected := (Transport.checkedDescriptor (model.read interpretation)
      (model.domain interpretation) (model.closed interpretation) id context.sign
      (fun a : G => (SignType.sign a : Int)) context.signature descriptor descriptorData).root
        (fun a : G => a) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    ∃ chosen : minimal.eval₂ interpretation.value selected = 0,
      (∀ a : (context.adjoin descriptor).context.Value,
        (∀ i < (context.polynomial descriptor a).size,
          model.domain interpretation ((context.polynomial descriptor a).coeff i)) →
        let root := (model.adjoin descriptor).value (context.adjoin descriptor).generator
        let extended := interpretation.algebraic root selected minimal monic original chosen
        (model.adjoin descriptor).value a ∈ extended.domain ∧
          extended.map ((model.adjoin descriptor).value a) =
            (HexPolyMathlib.toPolynomial
              (Transport.polynomial (model.read interpretation)
                (context.polynomial descriptor a))).eval selected) ∧
      SignDet.signsAt (fun a : G => a) (fun _ => Iff.rfl)
        (qs.map (Transport.polynomial (model.read interpretation))) selected =
      SignDet.signsAt model.value model.zero_iff qs
        ((model.adjoin descriptor).value (context.adjoin descriptor).generator) := by
  classical
  dsimp only
  let selected := (Transport.checkedDescriptor (model.read interpretation)
    (model.domain interpretation) (model.closed interpretation) id context.sign
    (fun a : G => (SignType.sign a : Int)) context.signature descriptor descriptorData).root
      (fun a : G => a) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have source := s.values_at_root model.value model.zero_iff model.one model.add model.sub
    model.mul model.nat model.sign
  have zero : (HexPolyMathlib.Interpret.interpret model.value model.zero_iff q).eval
      (descriptor.root model.value model.zero_iff model.one model.add model.sub
        model.mul model.nat model.sign) = 0 := by
    rw [← model.adjoin_generator descriptor, ← model.polynomial_eval, query]
    exact minpoly.aeval model.field _
  have signs := Transport.selected_signs (model.read interpretation)
    (model.domain interpretation) (model.closed interpretation) id context.sign
    context.signature descriptor descriptorData (q :: qs) s queryData
  have identity (p : DensePoly G) :
      HexPolyMathlib.Interpret.interpret (fun a : G => a) (fun _ => Iff.rfl) p =
        HexPolyMathlib.toPolynomial p := by
    ext i
    rw [HexPolyMathlib.Interpret.coeff_interpret, HexPolyMathlib.coeff_toPolynomial]
  rw [source] at signs
  have family := congrArg List.tail signs
  simp only [SignDet.signsAt, List.map_cons, List.tail_cons] at family
  rw [← model.adjoin_generator descriptor] at family
  have first := congrArg (fun xs : List Int => xs.headD 0) signs
  simp only [SignDet.signsAt, List.map_cons, List.headD_cons, identity, zero, sign_zero] at first
  change (SignType.sign ((HexPolyMathlib.toPolynomial
    (Transport.polynomial (model.read interpretation) q)).eval selected) : Int) = 0 at first
  have castZero (a : G) (h : (SignType.sign a : Int) = 0) : a = 0 := by
    have zero : SignType.sign a = 0 := by
      cases hs : SignType.sign a <;> simp [hs] at h ⊢
    exact sign_eq_zero_iff.mp zero
  have mappedZero : (HexPolyMathlib.toPolynomial
      (Transport.polynomial (model.read interpretation) q)).eval selected = 0 := by
    exact castZero _ first
  have chosen : minimal.eval₂ interpretation.value selected = 0 := by
    rw [Polynomial.eval₂_eq_eval_map,
      ← model.polynomial_specialize interpretation q minimal (original.trans query.symm)]
    exact mappedZero
  refine ⟨chosen, ?_, family⟩
  intro a guards
  exact model.adjoin_evaluation interpretation descriptor selected minimal monic original chosen a guards

/-- One finite family of actual native child values retains its signs under
the algebraic interpretation at the checked target root. The joint query list
uses each value's retained polynomial, preceded by the actual minimal polynomial. -/
theorem adjoin_signs (model : Model context K)
    (interpretation : CoefficientMap model.field G)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (q : DensePoly context.Value)
    (query : model.polynomial q = minpoly model.field
      ((model.adjoin descriptor).value (context.adjoin descriptor).generator))
    (values : List (context.adjoin descriptor).context.Value)
    (s : SignDet.SelectedSigns descriptor (q :: values.map (context.polynomial descriptor)))
    (descriptorData : Transport.DescriptorData (model.read interpretation)
      (model.domain interpretation) context.sign (fun a : G => (SignType.sign a : Int))
      descriptor.raw descriptor.evidence)
    (queryData : Transport.ReplayData (model.read interpretation) (model.domain interpretation)
      context.sign (fun a : G => (SignType.sign a : Int)) descriptor.raw.head
      descriptor.raw.lower descriptor.raw.upper
      (descriptor.raw.queries ++ q :: values.map (context.polynomial descriptor)) s.evidence)
    (minimal : Polynomial interpretation.domain) (monic : minimal.Monic)
    (original : minimal.map interpretation.domain.subtype = minpoly model.field
      ((model.adjoin descriptor).value (context.adjoin descriptor).generator))
    (guards : ∀ a ∈ values, ∀ i < (context.polynomial descriptor a).size,
      model.domain interpretation ((context.polynomial descriptor a).coeff i)) :
    let selected := (Transport.checkedDescriptor (model.read interpretation)
      (model.domain interpretation) (model.closed interpretation) id context.sign
      (fun a : G => (SignType.sign a : Int)) context.signature descriptor descriptorData).root
        (fun a : G => a) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    ∃ chosen : minimal.eval₂ interpretation.value selected = 0,
      ∀ a ∈ values,
        let root := (model.adjoin descriptor).value (context.adjoin descriptor).generator
        let extended := interpretation.algebraic root selected minimal monic original chosen
        (model.adjoin descriptor).value a ∈ extended.domain ∧
          (SignType.sign (extended.map ((model.adjoin descriptor).value a)) : Int) =
            (SignType.sign ((model.adjoin descriptor).value a) : Int) := by
  classical
  obtain ⟨chosen, evaluated, signs⟩ := model.adjoin_checked interpretation descriptor q
    (values.map (context.polynomial descriptor)) query s descriptorData queryData minimal monic original
  refine ⟨chosen, ?_⟩
  intro a member
  obtain ⟨domain, value⟩ := evaluated a (guards a member)
  refine ⟨domain, ?_⟩
  rw [value]
  have identity (p : DensePoly G) :
      HexPolyMathlib.Interpret.interpret (fun a : G => a) (fun _ => Iff.rfl) p =
        HexPolyMathlib.toPolynomial p := by
    ext i
    rw [HexPolyMathlib.Interpret.coeff_interpret, HexPolyMathlib.coeff_toPolynomial]
  simp only [SignDet.signsAt, List.map_map, identity] at signs
  have signValue := List.map_inj_left.mp signs a member
  simp only [Function.comp_apply] at signValue
  rw [← model.adjoin_value descriptor a] at signValue
  exact signValue

/-- info: 'Hex.RealClosure.Tower.Model.adjoin_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.adjoin_signs

/-- info: 'Hex.RealClosure.Tower.Model.adjoin_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.adjoin_checked

/-- info: 'Hex.RealClosure.Tower.Model.minimal_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.minimal_query

/-- info: 'Hex.RealClosure.Tower.Model.adjoin_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.adjoin_evaluation

/-- info: 'Hex.RealClosure.Tower.Model.minimal_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.minimal_lift

end Hex.RealClosure.Tower.Model
