/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardMomentAll

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAllPublic

/-- Every original moment at the actual finite family target. -/
theorem moments : GuardMomentAll.statement := GuardMomentAll.moments

/-- The complete third moment retains both of its original chain subjects. -/
theorem third : GuardMomentLast.statement := GuardMomentLast.data

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAllPublic
