/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.BaseProvider
public import HexRealClosureTheory.TowerModel
public import HexRealClosure.BaseInclusion

public section

namespace Hex.RealClosure.BaseContext

variable {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K]
variable {approx : K → Rat → OrderedFn.Oracle.Bounds} {nativeSign : K → Int}

/-- Use the actual prefix interpretation as a tower base, with all field and
order laws supplied by the canonical native coefficient embedding. -/
noncomputable def RealContext.Interpretation.towerModel
    {parent : RealContext registry K approx nativeSign} (model : parent.Interpretation) :
    Tower.Model (Tower.Context.base (Context.real parent)) ℝ :=
  Tower.Model.base (Context.real parent) model.hom model.sign

/-- The provider model constructs a tower model on its actual native base. -/
noncomputable def RealPrefix.Model.towerModel (model : Model registry) :
    Tower.Model (Tower.Context.ofBase model.context.finish) ℝ := by
  cases model with
  | pack chain interpretation realization => exact interpretation.towerModel

/-- The constructed tower model retains the prefix's original real values. -/
theorem RealPrefix.Model.towerModel_value (model : Model registry)
    (a : (Tower.Context.ofBase model.context.finish).Value) :
    model.towerModel.value a =
      model.interpretation.hom (Tower.Context.baseStored model.context.finish a) := by
  cases model with
  | pack chain interpretation realization =>
    exact Tower.Model.base_value (Context.real (RealContext.ofChain chain))
      interpretation.hom interpretation.sign a

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealContext.Interpretation.towerModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealContext.Interpretation.towerModel

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.towerModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.towerModel
