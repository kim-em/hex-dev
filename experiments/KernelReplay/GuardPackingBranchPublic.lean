/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingBranch

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranchPublic

/-- The complete original branch in position one, including all three queries. -/
theorem branch : GuardPackingShape.node1 := GuardPackingBranch.data

/-- The complete original leaf in position two. -/
theorem leaf : GuardPackingShape.node2 := GuardPackingLeaf.data

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranchPublic
