/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardFrontier
open Lean

/-- Unproved discovery syntax only. Every later guard proof must pass its
original ordinary-kernel check; this extension supplies no proof rule. -/
initialize templates : SimplePersistentEnvExtension Expr (Array Expr) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (fun found items => found ++ items) #[]
    addEntryFn := fun found expression => found.push expression
  }

end Hex.RealClosure.Algebraic.KernelReplay.GuardFrontier
