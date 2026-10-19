/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardNativeFrontier
public meta import KernelReplay.GuardNativeFrontier
import all KernelReplay.GuardNativeFrontier

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardNativeAudit
open Lean Meta Elab

/-- Recover both original field subjects from their stored checked theorem.
The theorem is comparison metadata, not a premise of the rebuilt record. -/
def origin (root : Name) : MetaM Name := do
  let .thmInfo certificate ← getConstInfo (root.appendAfter "_binding") |
    throwError "missing stored original field bindings for {root}"
  unless certificate.type.getAppFn.isConstOf ``And do throwError "invalid stored binding shape"
  let mut source : Option Name := none
  for (equation, index) in certificate.type.getAppArgs.zipIdx do
    unless equation.getAppFn.isConstOf ``Eq do throwError "stored field binding is not equality"
    let arguments := equation.getAppArgs
    let .proj ``SignFact leftIndex left := arguments[1]! | throwError "missing rebuilt field"
    let .proj ``SignFact rightIndex right := arguments[2]! | throwError "missing original field"
    unless leftIndex == index && rightIndex == index && left.isConstOf root do
      throwError "stored binding changed its rebuilt record or field"
    let some original := right.constName? | throwError "original binding is not a named source"
    if let some previous := source then
      unless previous == original do throwError "stored field bindings have different originals"
    source := some original
  let some original := source | throwError "stored field bindings are empty"
  let recordType := (← getConstInfo root).type
  let originalType := (← getConstInfo original).type
  kernelCheck `__storedOriginalOwner (← mkEq recordType originalType) (← mkEqRefl originalType)
  return original


end Hex.RealClosure.Algebraic.KernelReplay.GuardNativeAudit
