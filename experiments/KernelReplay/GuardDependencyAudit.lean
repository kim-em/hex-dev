/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardDependencyAudit
open Lean Meta

def standard : Array Name := #[`propext, `Classical.choice, `Quot.sound].qsort Name.lt

def fromModule (env : Environment) (moduleName name : Name) : Bool :=
  match env.getModuleIdx? moduleName with
  | none => false
  | some index => env.getModuleIdxFor? name == some index

/-- The parametric constant-polynomial constructor and its proof auxiliaries
are independent of the old fixture's cached operands. -/
def generic (name : Name) (info : ConstantInfo) : Bool :=
  let root := `Hex.RealClosure.Algebraic.KernelReplay.FrameOperand.constant
  name == root || (info.isTheorem && root.isPrefixOf (privateToUserName name).eraseMacroScopes)

structure Result where
  declarations : Nat
  axioms : Array Name

private def bounded (began : Nat) : MetaM Unit := do
  Core.checkSystem "public joint checked dependencies"
  if ((← IO.getNumHeartbeats) - began) / 1000 ≥ 1500000 then
    throwError "public joint dependency budget exhausted"

/-- Traverse the actual checked private and opaque bodies. Module ownership
also catches nested, macro-scoped and private generated declarations. -/
def walk (began : Nat) (roots : Array Expr) : MetaM Result := do
  let env ← getEnv
  let checked := env.checked.get
  let some cachedModule := env.getModuleIdx? `KernelReplay.FrameOperand |
    throwError "cached operand origin module is not loaded"
  let mut queued : NameSet := {}
  let mut queue : Array Name := #[]
  for root in roots do
    for name in root.getUsedConstants do
      unless queued.contains name do
        queued := queued.insert name
        queue := queue.push name
  let forbidden := #[`Hex.RealClosure.BaseContext.PackedContext.Realization.reference,
    `Hex.RealClosure.Ambient.ofField, `Hex.RealClosure.Ambient.exists_ambient,
    `TauCeti.RealClosure.exists_realClosure]
  let mut axioms : NameSet := {}
  let mut cursor := 0
  while cursor < queue.size do
    bounded began
    if queue.size > 150000 then throwError "public joint dependency bound exhausted"
    let name := queue[cursor]!
    cursor := cursor + 1
    let some info := checked.find? name | throwError "public joint checked declaration missing: {name}"
    if env.getModuleIdxFor? name == some cachedModule && !generic name info then
      throwError "cached operand dependency from KernelReplay.FrameOperand: {name}"
    if forbidden.contains name then throwError "public joint retained whole-field construction {name}"
    if info.isUnsafe || info.isPartial then throwError "unsafe public joint dependency {name}"
    if info matches .axiomInfo _ then
      unless standard.contains name do throwError "unexpected public joint assumption {name}"
      axioms := axioms.insert name
    let dependencies := info.type.getUsedConstants ++
      match info with
      | .defnInfo value => value.value.getUsedConstants
      | .thmInfo value => value.value.getUsedConstants
      | .opaqueInfo value => value.value.getUsedConstants
      | .inductInfo value => value.ctors.toArray
      | _ => #[]
    for dependency in dependencies do
      unless queued.contains dependency do
        queued := queued.insert dependency
        queue := queue.push dependency
  return ⟨cursor, axioms.toArray.qsort Name.lt⟩

end Hex.RealClosure.Algebraic.KernelReplay.GuardDependencyAudit
