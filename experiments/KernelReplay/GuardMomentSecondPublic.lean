/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardMomentSecond

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentSecondPublic

/-- All seven fields of the original second moment query. -/
theorem second : GuardMomentSecond.statement := GuardMomentSecond.data

/-- The checked finite family contains exactly three original moments. -/
theorem count : GuardMomentSecond.momentCount = 3 := rfl

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentSecondPublic
