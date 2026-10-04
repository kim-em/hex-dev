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
private meta def anyLocal (theoremName : Name) (predicate : Expr → Bool) : MetaM Bool := do
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
    if (body.find? predicate).isSome then return true
    pending := body.foldConsts pending fun name rest => rest.push name
  return false

meta def usesConstructor (theoremName constructor : Name) (arity : Nat) : MetaM Bool :=
  anyLocal theoremName (fun e => e.isAppOfArity constructor arity)

/-- Identify the recorded sign evidence in actual quoted entry constructors. -/
meta def usesInterval (theoremName : Name) : MetaM Bool :=
  anyLocal theoremName fun e =>
    if e.isAppOfArity `Hex.RCF.RealCoefficients.LiteralSign.Entry.mk 4 then
      e.getAppArgs[3]!.isAppOfArity ``Option.none 1
    else false

end Hex.RCF.ProofProbe.Literals
