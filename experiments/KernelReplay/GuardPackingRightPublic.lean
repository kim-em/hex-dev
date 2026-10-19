/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingRight

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRightPublic

/-- The original right-hand node in position three, with all three queries. -/
theorem third : GuardPackingShape.node3 := GuardPackingRight.node3.data

/-- The original right-hand node in position four, with all three queries. -/
theorem fourth : GuardPackingShape.node4 := GuardPackingRight.node4.data

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRightPublic
