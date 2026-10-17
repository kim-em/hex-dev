/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardLastChainEnd

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardLastChainPublic

/-- The complete squarefree chain of the original third moment query. -/
theorem chain : GuardLastChainStart.statement := GuardLastChainEnd.chain

end Hex.RealClosure.Algebraic.KernelReplay.GuardLastChainPublic
