/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.NativeSpecialize
public section

/-! Selected coefficient identities at the same finite ordinary reader as the
source matrix. A shared coefficient-selection formula and its proved uniqueness
relative to inherited identities authenticate algebraic suffix coordinates
without treating them as inherited base values. Native row truth, provider history and supplied guards remain
explicit; these laws do not assemble a frozen certificate or establish coverage. -/

namespace Hex.RCF.RealCoefficients.NativeSources
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula

/-- Realize coefficient selection and the matrix together. A proved unique
selection relative to authenticated inherited identities identifies every
coefficient at that same reader, including selected algebraic suffix coordinates.
This is a point law with an explicit selection proof, not a frozen context checker or cell coverage theorem. -/
theorem true_real (context : Context registry) (following : context.origin.base.Realization)
    (values : Fin n → context.Value) (source : Fin n → ℝ)
    (selection : RealFormula.QF n)
    (unique : ∀ coefficients : Fin n → ℝ,
      (∀ i, context.origin.RealValue following (values i) (source i) →
        coefficients i = source i) → selection.toProp coefficients → coefficients = source)
    (sample : context.Value) (formula : RealFormula.QF (n+1)) (guards : List context.Value)
    (nonzero : ∀ a ∈ guards, context.sign a ≠ 0)
    (truth : Samples.Row.eval (.and selection.lift formula)
      (NativeSpecialize.row context values sample (.and selection.lift formula)) = some true) :
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ a, domain a → domain (-a) ∧ read (-a) = -read a) ∧
      (∀ i, domain (values i) ∧ read (values i) = source i) ∧ domain sample ∧
      (∀ q ∈ formula.polys,
        (RepresentationSpecialize.polynomial source q).size =
          (RepresentationSpecialize.polynomial values q).size) ∧
      formula.toProp (RealFormula.append source (read sample)) ∧
      (∀ a ∈ guards, domain a ∧ read a ≠ 0) ∧
      (∀ a r, context.origin.RealValue following a r → domain a ∧ read a = r) := by
  obtain ⟨read, domain, closed, negative, members, present, guardSigns, sizes, signs, fixed⟩ :=
    NativeSpecialize.row_real context following values sample (.and selection.lift formula) guards
  have meaning := (Samples.Row.eval_true (.and selection.lift formula) _ _ signs).mp truth
  change selection.lift.toProp (RealFormula.append (read ∘ values) (read sample)) ∧
    formula.toProp (RealFormula.append (read ∘ values) (read sample)) at meaning
  have same := unique (read ∘ values)
    (fun i inherited => (fixed (values i) (source i) inherited).2)
    ((selection.lift_correct (read ∘ values) (read sample)).mp meaning.1)
  refine ⟨read, domain, closed, negative, ?_, present, ?_, ?_, ?_, fixed⟩
  · intro i
    exact ⟨members i, congrFun same i⟩
  · intro q hq
    have present := sizes q (by rw [RealFormula.QF.polys_and]; exact List.mem_append_right _ hq)
    simpa only [same] using present
  · simpa only [same] using meaning.2
  · intro a member
    obtain ⟨ha, sign⟩ := guardSigns a member
    refine ⟨ha, ?_⟩
    intro zero
    apply nonzero a member
    simpa only [zero, sign_zero, SignType.coe_zero] using sign.symm

/-- A jointly realized selected coefficient and false matrix give a universal
counterexample, retaining every supplied nonzero guard. The input is a
true row for the selection conjoined with the negated matrix. -/
theorem not_forall (context : Context registry) (following : context.origin.base.Realization)
    (values : Fin n → context.Value) (source : Fin n → ℝ)
    (selection : RealFormula.QF n)
    (unique : ∀ coefficients : Fin n → ℝ,
      (∀ i, context.origin.RealValue following (values i) (source i) →
        coefficients i = source i) → selection.toProp coefficients → coefficients = source)
    (sample : context.Value) (formula : RealFormula.QF (n+1)) (guards : List context.Value)
    (nonzero : ∀ a ∈ guards, context.sign a ≠ 0)
    (truth : Samples.Row.eval (.and selection.lift (.not formula))
      (NativeSpecialize.row context values sample (.and selection.lift (.not formula))) = some true) :
    (¬ ∀ x : ℝ, formula.toProp (RealFormula.append source x)) ∧
      ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
        Transport.Closed read domain ∧
        (∀ i, domain (values i) ∧ read (values i) = source i) ∧ domain sample ∧
        ¬ formula.toProp (RealFormula.append source (read sample)) ∧
        (∀ a ∈ guards, domain a ∧ read a ≠ 0) := by
  obtain ⟨read, domain, closed, negative, fixed, present, sizes, meaning, guarded, base⟩ :=
    true_real context following values source selection unique sample (.not formula) guards nonzero truth
  change ¬ formula.toProp (RealFormula.append source (read sample)) at meaning
  refine ⟨?_, read, domain, closed, fixed, present, meaning, guarded⟩
  intro all
  exact meaning (all (read sample))
end Hex.RCF.RealCoefficients.NativeSources
