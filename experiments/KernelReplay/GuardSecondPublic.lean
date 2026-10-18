/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardSecondData

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardSecondPublic

/-- The complete original second inventory at the same realized predecessor. -/
theorem data : Packing.Inventory.Data FrameOwners.second
    GuardInventoryReplay.second.entries GuardInventoryReplay.second.records
    GuardInventoryReplay.second.facts GuardDescriptorPoint.predecessor :=
  GuardSecondData.data

/-- The inventory uses the same selected point as its complete descriptor. -/
theorem point : GuardSecondData.point = GuardDescriptorPoint.point :=
  GuardSecondData.pointBinding

/-- All original second-level conditions hold together at one exported real
point, including the root selection, full Thom signs and all three packings. -/
theorem conditions : Packing.Inventory.Conditions FrameOwners.second
    GuardInventoryReplay.second.entries GuardInventoryReplay.second.records
    GuardInventoryReplay.second.facts GuardDescriptorPoint.predecessor
    GuardDescriptorPoint.point :=
  Packing.Inventory.Data.conditions data GuardDescriptorPoint.zero GuardDescriptorPoint.unit

end Hex.RealClosure.Algebraic.KernelReplay.GuardSecondPublic
