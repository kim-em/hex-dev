/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardNextChainEnd

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardNextChainPublic

/-- The complete squarefree chain of the original second moment query. -/
theorem chain : GuardNextChainStart.statement := GuardNextChainEnd.chain

end Hex.RealClosure.Algebraic.KernelReplay.GuardNextChainPublic
