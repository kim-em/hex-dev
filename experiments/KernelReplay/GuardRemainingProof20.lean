/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingProof19
public meta import KernelReplay.GuardRemainingProof19
import all KernelReplay.GuardRemainingProof19
import all KernelReplay.GuardRemainingQuery
import all KernelReplay.GuardRemainingInputs
import all KernelReplay.GuardRemainingShape
import all KernelReplay.GuardCoefficientFence
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#remaining_query_chain 2 3 2 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#remaining_query_chain 2 3 2 1

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#remaining_packing_query 2 3 2
