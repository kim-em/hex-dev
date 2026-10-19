/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardObligations

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardFirstPublic

/-- The first actual guard, at its complete original checked proposition. -/
theorem first : GuardObligations.firstStatement := GuardObligations.guard0

end Hex.RealClosure.Algebraic.KernelReplay.GuardFirstPublic
