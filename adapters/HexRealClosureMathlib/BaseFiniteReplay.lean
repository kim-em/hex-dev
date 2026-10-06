/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseFinite
public import HexRealClosureMathlib.PackingInventory
public import HexRealRootsMathlib.RealClosed

public section

namespace Hex.RealClosure.BaseContext

variable {registry : Registry} {B : Type} [Lean.Grind.Field B] [DecidableEq B]
variable {sign : B → Int} {base : Context registry B sign}
variable {C : Type u} [DecidableEq C] {binding : C}

local instance : Field B := HexPolyMathlib.fieldOfGrind

/-- Construct the entire first algebraic level's finite premises from its
three actual record inventories and the validated staged provider history.
The predecessor reader and its agreement are conclusions, not caller inputs. -/
theorem Context.finite_data (base : Context registry B sign)
    (following : base.chain.Realization registry)
    (context : Algebraic.Context (Element base) C Element.sign binding)
    (entries : List (Algebraic.Packing context)) (records : List (Algebraic.ValueSign context))
    (facts : List (Algebraic.InverseFact context)) :
    ∃ interpretation : CoefficientMap B ℝ,
      Algebraic.Packing.Inventory.Data context entries records facts (base.partialRead interpretation) ∧
      ∀ a r, following.RealValue a.stored r →
        base.partialDomain interpretation a ∧ base.partialRead interpretation a = r := by
  obtain ⟨interpretation, agreement, fixed⟩ := base.partial_exists following
    (Algebraic.Packing.Inventory.level context entries records facts)
  exact ⟨interpretation, Algebraic.Packing.Inventory.level_data context entries records facts
    (base.partialRead interpretation) (base.partialDomain interpretation)
    (base.partialClosed interpretation) agreement, fixed⟩

/-- Choose one ordinary point for all first-level packing equations, inverse
equations and cached input signs, together with the original root interval
and full derivative-sign word. The actual staged history supplies every finite
predecessor premise; provider coefficients retain their prescribed values. -/
theorem Context.finite_point (base : Context registry B sign)
    (following : base.chain.Realization registry)
    (context : Algebraic.Context (Element base) C Element.sign binding)
    (entries : List (Algebraic.Packing context)) (records : List (Algebraic.ValueSign context))
    (facts : List (Algebraic.InverseFact context)) :
    ∃ interpretation : CoefficientMap B ℝ, ∃ x : ℝ,
      let read := base.partialRead interpretation
      x ∈ HexRealRootsMathlib.Tarski.rootsIn
        (HexPolyMathlib.Interpret.interpret (fun y : ℝ => y) (fun _ => Iff.rfl)
          (Transport.polynomial read context.root.raw.head))
        ((Transport.endpoint read context.root.raw.lower).map (fun y : ℝ => y))
        ((Transport.endpoint read context.root.raw.upper).map (fun y : ℝ => y)) ∧
      Hex.SignDet.signsAt (fun y : ℝ => y) (fun _ => Iff.rfl)
        (context.root.raw.queries.map (Transport.polynomial read)) x = context.root.raw.signs ∧
      (∀ entry ∈ entries,
        Algebraic.Packing.eval read x entry.value.polynomial =
          Algebraic.Packing.eval read x entry.original ∧
        (SignType.sign (Algebraic.Packing.eval read x entry.original) : Int) = entry.value.sign) ∧
      (∀ record ∈ records,
        (SignType.sign (Algebraic.Packing.eval read x record.value.polynomial) : Int) =
          record.value.sign) ∧
      (∀ fact ∈ facts,
        Algebraic.Packing.eval read x fact.entry.value.polynomial =
          Algebraic.Packing.eval read x fact.entry.original ∧
        Algebraic.Packing.eval read x fact.entry.value.polynomial =
          (Algebraic.Packing.eval read x fact.inverse.argument.polynomial)⁻¹ ∧
        (SignType.sign (Algebraic.Packing.eval read x fact.entry.value.polynomial) : Int) =
          fact.entry.value.sign ∧
        (SignType.sign (Algebraic.Packing.eval read x fact.inverse.argument.polynomial) : Int) =
          fact.inverse.argument.sign) ∧
      (∀ a r, following.RealValue a.stored r →
        base.partialDomain interpretation a ∧ read a = r) := by
  obtain ⟨interpretation, data, fixed⟩ := base.finite_data following context entries records facts
  let read := base.partialRead interpretation
  have closed := base.partialClosed interpretation
  let x := context.finitePoint read closed.read_zero closed.read_one data.descriptor
  have selected := context.finitePoint_spec read closed.read_zero closed.read_one data.descriptor
  refine ⟨interpretation, x, selected.1, selected.2, ?_, ?_, ?_, fixed⟩
  · intro entry member
    exact entry.atPoint read closed.read_zero closed.read_one data.descriptor (data.packings entry member)
  · intro record member
    exact record.atPoint read closed.read_zero closed.read_one data.descriptor (data.signs record member)
  · intro fact member
    exact fact.atPoint read closed.read_zero closed.read_one data.descriptor (data.inverses fact member)

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Context.finite_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Context.finite_data

/-- info: 'Hex.RealClosure.BaseContext.Context.finite_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Context.finite_point
