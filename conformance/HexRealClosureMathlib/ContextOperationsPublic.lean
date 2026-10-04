/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.ContextOperationsConformance

public section

namespace Hex.RealClosure.Algebraic.ContextOperationsPublic

open CoefficientSignsConformance ContextOperationsConformance

/-- A caller can read the retained count through public laws, without
access to any private constructor or operation equality on the data. -/
theorem retained_count :
    let : Add Rat := targetAdd.val
    transported.rootCount = some 1 := by
  let : Add Rat := targetAdd.val
  have data := @Context.changeOps_data Rat Nat _ _ _
    inferInstance targetAdd.val inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance Rat.instAdd inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    rfl targetAdd.property.symm rfl rfl rfl rfl rfl rfl Sturm.orderSign 7 context
  exact (congrArg (fun fields => fields.2.1) data).trans source_count

end Hex.RealClosure.Algebraic.ContextOperationsPublic

/-- info: 'Hex.RealClosure.Algebraic.ContextOperationsPublic.retained_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.ContextOperationsPublic.retained_count
