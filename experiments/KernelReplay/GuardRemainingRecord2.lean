/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingRecords
public meta import KernelReplay.GuardRemainingRecords
import all KernelReplay.GuardRemainingRecords
import all KernelReplay.GuardRemainingNodes
import all KernelReplay.GuardRemainingShape
import all KernelReplay.GuardCoefficientFence
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier
import all KernelReplay.GuardInventoryReplay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#remaining_packing_record 2
