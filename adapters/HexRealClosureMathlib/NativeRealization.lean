/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseEvaluation
public import HexRealClosureMathlib.BaseFactory

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {context : Context registry}

/-- A value in a stored origin inherited from the caller's actual real
prefix through the original native base and suffix embeddings. -/
@[expose] def Origin.RealValue (origin : Origin context)
    (following : origin.base.Realization) : context.Value → ℝ → Prop := by
  cases origin with
  | pack base suffix same =>
    cases same
    exact fun a r => ∃ b, a = suffix.embed b ∧ following.RealValue b.stored r

/-- Simultaneous ordinary-real realization of a finite family in an actual
native context. Provider history supplies the fixed real coefficients, and
the origin supplies every stored infinitesimal and selected-root level.
The interpretation retains all inherited real values and the requested signs;
it is partial on the semantic field, with no whole-field embedding into ℝ. -/
theorem Origin.realize {K : Type} [Field K] [LinearOrder K] [DecidableEq K]
    [IsStrictOrderedRing K] [IsRealClosed K]
    (origin : Origin context) (following : origin.base.Realization)
    (model : Model context K) (values : List context.Value) :
    ∃ interpretation : CoefficientMap model.field ℝ,
      (∀ a ∈ values, model.domain interpretation a ∧
        (SignType.sign (model.read interpretation a) : Int) = context.sign a) ∧
      (∀ a r, origin.RealValue following a r →
        model.domain interpretation a ∧ model.read interpretation a = r) := by
  cases origin with
  | pack base suffix same =>
    cases same
    let reference := following.reference
    let original := suffix.restrict reference.model model
    have same : model = original.extend suffix :=
      original.extend_unique suffix model (fun _ => rfl)
    rw [same]
    obtain ⟨interpretation, finite, real⟩ := original.realize_suffix base following suffix values
    refine ⟨interpretation, finite, ?_⟩
    intro a r inherited
    change ∃ b, a = suffix.embed b ∧ following.RealValue b.stored r at inherited
    obtain ⟨b, rfl, inherited⟩ := inherited
    exact real b r inherited

/-- Use the context's extracted actual origin for finite ordinary-real
realization. No descriptor transport guards or sign agreement assumptions
are supplied by the caller. -/
theorem Context.realize {K : Type} [Field K] [LinearOrder K] [DecidableEq K]
    [IsStrictOrderedRing K] [IsRealClosed K]
    (context : Context registry) (following : context.origin.base.Realization)
    (model : Model context K) (values : List context.Value) :
    ∃ interpretation : CoefficientMap model.field ℝ,
      (∀ a ∈ values, model.domain interpretation a ∧
        (SignType.sign (model.read interpretation a) : Int) = context.sign a) ∧
      (∀ a r, context.origin.RealValue following a r →
        model.domain interpretation a ∧ model.read interpretation a = r) :=
  context.origin.realize following model values

/-- Realize native finite sign conditions directly from the stored origin
and caller's provider history. The resulting ordinary reader preserves
arithmetic on its domain; no symbolic ambient model is an input premise. -/
theorem Origin.realize_values (origin : Origin context)
    (following : origin.base.Realization) (values : List context.Value) :
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ a ∈ values, domain a ∧ (SignType.sign (read a) : Int) = context.sign a) ∧
      (∀ a r, origin.RealValue following a r → domain a ∧ read a = r) := by
  cases origin with
  | pack base suffix same =>
    cases same
    let reference := following.reference
    let model := reference.model.extend suffix
    obtain ⟨interpretation, finite, real⟩ :=
      (Origin.pack base suffix rfl).realize following model values
    exact ⟨model.read interpretation, model.domain interpretation,
      model.closed interpretation, finite, real⟩

/-- Ordinary finite-sign realization for the actual context, including fixed
real coefficients and domain closure for reached polynomial arithmetic.
Every infinitesimal and selected root is derived from the stored origin. -/
theorem Context.realize_values (context : Context registry)
    (following : context.origin.base.Realization) (values : List context.Value) :
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ a ∈ values, domain a ∧ (SignType.sign (read a) : Int) = context.sign a) ∧
      (∀ a r, context.origin.RealValue following a r → domain a ∧ read a = r) :=
  context.origin.realize_values following values

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.realize

/-- info: 'Hex.RealClosure.Tower.Context.realize_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.realize_values
