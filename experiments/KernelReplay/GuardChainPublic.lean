/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardChainEnd

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardChainPublic

/-- All ten fields of the original first signed chain are available through
ordinary public imports at the same original owner and predecessor reader. -/
theorem chain : GuardChainStart.statement := GuardChainEnd.chain

end Hex.RealClosure.Algebraic.KernelReplay.GuardChainPublic
