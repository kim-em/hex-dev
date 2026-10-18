/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardLastRemainderEnd

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderPublic

/-- The complete remainder chain of the original third moment query. -/
theorem chain : GuardLastRemainderStart.statement := GuardLastRemainderEnd.chain

/-- The original bounded recurrence family, with all its indices and guards. -/
theorem recurrences : GuardRecurrenceShape.statement := GuardRecurrenceEnd.recurrences

/-- The original third remainder has exactly one recurrence. -/
theorem count : GuardRecurrenceShape.count = 1 := rfl

end Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderPublic
