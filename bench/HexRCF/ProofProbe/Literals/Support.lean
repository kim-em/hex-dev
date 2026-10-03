/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean
public meta section

namespace Hex.RCF.ProofProbe.Literals
open Lean Meta

/-- Inspect the theorem and its generated local declarations. Imported library
bodies remain leaves; quotation data may live inside opaque local auxiliaries. -/
meta def usesConstructor (theoremName constructor : Name) (arity : Nat) : MetaM Bool := do
  let environment ← getEnv
  let mut pending := #[theoremName]
  let mut seen : NameHashSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if environment.getModuleIdxFor? name |>.isSome then continue
    let info ← getConstInfo name
    let some body := info.value? (allowOpaque := true) | continue
    if (body.find? (fun e => e.isAppOfArity constructor arity)).isSome then return true
    pending := body.foldConsts pending fun name rest => rest.push name
  return false

end Hex.RCF.ProofProbe.Literals
