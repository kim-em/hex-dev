/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainderEnd

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainderPublic

/-- The complete remainder chain of the original second moment query. -/
theorem chain : GuardRemainderStart.statement := GuardRemainderEnd.chain

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainderPublic
