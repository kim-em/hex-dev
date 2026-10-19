/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingInput01
public meta import KernelReplay.GuardRemainingInput01
import all KernelReplay.GuardRemainingInput01
import all KernelReplay.GuardRemainingInputs
import all KernelReplay.GuardRemainingShape
import all KernelReplay.GuardCoefficientReduce
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#remaining_packing_inputs 1 2
