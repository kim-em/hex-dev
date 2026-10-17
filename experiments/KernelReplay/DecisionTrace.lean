/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.DecisionTrace
open Lean Meta

private initialize decisions : EnvExtension (PHashMap Expr Nat × Nat) ←
  registerEnvExtension (pure ({}, 0)) (asyncMode := .local)

/-- Identify an exact closed decision type without changing its proof search. -/
def begin (type : Expr) : MetaM (Option (Nat × Nat)) := do
  unless (← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE").isSome do return none
  let (known, next) := decisions.getState (← getEnv)
  let id := known.find? type |>.getD next
  unless (known.find? type).isSome do
    modifyEnv fun environment => decisions.modifyState environment
      (fun _ => (known.insert type id, next + 1))
  return some (id, (← IO.getNumHeartbeats) / 1000)

/-- Report the ordinary kernel check, including rejected literal candidates. -/
def finish (trace : Option (Nat × Nat)) (binders : Nat) (accepted : Bool) : MetaM Unit := do
  let some (id, began) := trace | return
  let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" | return
  let cost := (← IO.getNumHeartbeats) / 1000 - began
  let moduleName := (← getEnv).mainModule
  IO.FS.withFile path .append fun handle => do
    handle.putStrLn s!"literal decision: module={moduleName} id={id} binders={binders} accepted={accepted} kernelHeartbeats={cost}"
    handle.flush

end Hex.RealClosure.Algebraic.KernelReplay.DecisionTrace
