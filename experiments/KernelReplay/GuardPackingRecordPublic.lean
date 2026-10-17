/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingRecord

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRecordPublic

/-- The retained entry occupies its original first position in the inventory. -/
theorem first_entry : GuardInventoryReplay.second.entries[0]? =
    some GuardPackingShape.entry := rfl

/-- Both finite premises of the original first packing at the same first reader. -/
theorem data : Packing.Data GuardPackingShape.entry GuardDescriptorPoint.predecessor :=
  GuardPackingRecord.data

/-- The original packing equality and stored sign hold together at the same
second selected point used by the complete descriptor. -/
theorem value :
    Packing.eval GuardDescriptorPoint.predecessor GuardDescriptorPoint.point
      GuardPackingShape.entry.value.polynomial =
      Packing.eval GuardDescriptorPoint.predecessor GuardDescriptorPoint.point
        GuardPackingShape.entry.original ∧
    (SignType.sign (Packing.eval GuardDescriptorPoint.predecessor GuardDescriptorPoint.point
      GuardPackingShape.entry.original) : Int) = GuardPackingShape.entry.value.sign :=
  Packing.atPoint GuardPackingShape.entry GuardDescriptorPoint.predecessor
    GuardDescriptorPoint.zero GuardDescriptorPoint.unit GuardDescriptorPoint.descriptorData data

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRecordPublic
