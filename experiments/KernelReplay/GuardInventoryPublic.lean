/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardInventoryReplay

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardInventoryPublic

/-- The original first owner's entire finite inventory is available at the
same exported finite base interpretation through ordinary public imports. -/
theorem first_data : Packing.Inventory.Data FrameOwners.first
    GuardInventoryReplay.first.entries GuardInventoryReplay.first.records
    GuardInventoryReplay.first.facts
    (FiniteBaseProbe.base.partialRead GuardInventoryReplay.interpretation) :=
  GuardInventoryReplay.firstData

/-- One exported ordinary real point satisfies all original first-level
packing, cached-sign and inverse conditions together. -/
theorem first_conditions : Packing.Inventory.Conditions FrameOwners.first
    GuardInventoryReplay.first.entries GuardInventoryReplay.first.records
    GuardInventoryReplay.first.facts
    (FiniteBaseProbe.base.partialRead GuardInventoryReplay.interpretation)
    GuardInventoryReplay.firstPoint :=
  Packing.Inventory.Data.conditions first_data
    (Transport.Closed.read_zero GuardInventoryReplay.closed)
    (Transport.Closed.read_one GuardInventoryReplay.closed)

end Hex.RealClosure.Algebraic.KernelReplay.GuardInventoryPublic
