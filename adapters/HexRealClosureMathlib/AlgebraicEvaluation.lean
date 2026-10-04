/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.MonicEvaluation
public import HexRealClosureMathlib.ModelEvaluation

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {context : Context registry}
variable {K G : Type} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [IsRealClosed K] [Field G] [DecidableEq G]

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

/-- info: 'Hex.RealClosure.Tower.Model.adjoin_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.adjoin_evaluation

/-- info: 'Hex.RealClosure.Tower.Model.minimal_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.minimal_lift

end Hex.RealClosure.Tower.Model
