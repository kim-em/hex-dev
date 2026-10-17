/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingRecord2

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRecordsPublic

/-- The retained entry has its original inventory position 1. -/
theorem position1 : GuardInventoryReplay.second.entries[1]? = some GuardRemainingShape.record1.entry := rfl

/-- Both finite premises of original packing record 1 at the same first reader. -/
theorem data1 : Packing.Data GuardRemainingShape.record1.entry GuardDescriptorPoint.predecessor :=
  GuardRemainingRecords.record1.data

/-- Original record 1's value and stored sign at the same second selected point. -/
theorem value1 :
    Packing.eval GuardDescriptorPoint.predecessor GuardDescriptorPoint.point
      GuardRemainingShape.record1.entry.value.polynomial =
      Packing.eval GuardDescriptorPoint.predecessor GuardDescriptorPoint.point
        GuardRemainingShape.record1.entry.original ∧
    (SignType.sign (Packing.eval GuardDescriptorPoint.predecessor GuardDescriptorPoint.point
      GuardRemainingShape.record1.entry.original) : Int) = GuardRemainingShape.record1.entry.value.sign :=
  Packing.atPoint GuardRemainingShape.record1.entry GuardDescriptorPoint.predecessor
    GuardDescriptorPoint.zero GuardDescriptorPoint.unit GuardDescriptorPoint.descriptorData data1

/-- The retained entry has its original inventory position 2. -/
theorem position2 : GuardInventoryReplay.second.entries[2]? = some GuardRemainingShape.record2.entry := rfl

/-- Both finite premises of original packing record 2 at the same first reader. -/
theorem data2 : Packing.Data GuardRemainingShape.record2.entry GuardDescriptorPoint.predecessor :=
  GuardRemainingRecords.record2.data

/-- Original record 2's value and stored sign at the same second selected point. -/
theorem value2 :
    Packing.eval GuardDescriptorPoint.predecessor GuardDescriptorPoint.point
      GuardRemainingShape.record2.entry.value.polynomial =
      Packing.eval GuardDescriptorPoint.predecessor GuardDescriptorPoint.point
        GuardRemainingShape.record2.entry.original ∧
    (SignType.sign (Packing.eval GuardDescriptorPoint.predecessor GuardDescriptorPoint.point
      GuardRemainingShape.record2.entry.original) : Int) = GuardRemainingShape.record2.entry.value.sign :=
  Packing.atPoint GuardRemainingShape.record2.entry GuardDescriptorPoint.predecessor
    GuardDescriptorPoint.zero GuardDescriptorPoint.unit GuardDescriptorPoint.descriptorData data2

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRecordsPublic
