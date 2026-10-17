/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardObligations28
public meta import KernelReplay.GuardObligations28
import all KernelReplay.GuardObligations28
import all KernelReplay.GuardObligations
import all KernelReplay.GuardFrontierStore
import all KernelReplay.GuardNativeFrontier
import all KernelReplay.GuardNativeBindings
import all KernelReplay.GuardRecordReplay
import all KernelReplay.GuardSecondData
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay
import all KernelReplay.GuardOperand
import all KernelReplay.GuardRemainingShape
import all KernelReplay.FrameJoint
import all KernelReplay.FrameOperand

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#original_guard_batch 440 448
