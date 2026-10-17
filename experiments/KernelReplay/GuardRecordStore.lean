/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRecordStore
open Lean

/-- Audit roots are bookkeeping only; every retained record and its public
alias is checked by the ordinary kernel before these names are recorded. -/
initialize roots : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (fun found items => found ++ items) #[]
    addEntryFn := fun found name => found.push name
  }

end Hex.RealClosure.Algebraic.KernelReplay.GuardRecordStore
