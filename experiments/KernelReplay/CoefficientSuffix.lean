/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.FiniteIndex
import all HexRealClosureTheory.FiniteIndex

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.CoefficientSuffix
open Lean Meta Elab Command FiniteData

private def checkMember (inventory : Expr) (position : Nat) (value : Expr)
    (cache : Option CoefficientCache := none) : MetaM Expr := do
  let proof ← FiniteData.suffixMember inventory position value cache
  let type ← instantiateMVars (← mkAppM ``List.Mem #[value, inventory])
  let _ ← auditProof proof type
  kernelCheck `__tailMembership type proof
  return proof

private def rejects (action : MetaM Expr) : MetaM Unit := do
  let rejected ← try
    let _ ← action
    pure false
  catch error =>
    unless (← error.toMessageData.toString).startsWith "(kernel) declaration type mismatch" do
      throw error
    pure true
  unless rejected do throwError "suffix membership accepted a corrupted position or suffix"

private def positions : MetaM Unit := do
  let inventory ← mkListLit (mkConst ``Nat) [toExpr (1 : Nat), toExpr (2 : Nat), toExpr (3 : Nat)]
  let tail ← mkListLit (mkConst ``Nat) [toExpr (2 : Nat), toExpr (3 : Nat)]
  let wrong ← mkListLit (mkConst ``Nat) [toExpr (9 : Nat)]
  let empty ← mkListLit (mkConst ``Nat) []
  let saved ← Meta.saveState
  try
    let bad : CoefficientWalk := { inventory, rest := empty, cells := #[
      { value := toExpr (1 : Nat), tail := inventory }, { value := toExpr (2 : Nat), tail := wrong }] }
    let cache ← IO.mkRef (some bad)
    rejects (FiniteData.suffixMember inventory 1 (toExpr (2 : Nat)) (some cache))
    unless (FiniteData.suffixes.getState (← getEnv) |>.find? inventory).isNone do
      throwError "an invalid walk tail entered the checked suffix cache"
    cache.set (some { bad with cells := bad.cells.set! 1 { value := toExpr (2 : Nat), tail } })
    let _ ← checkMember inventory 1 (toExpr (2 : Nat)) (some cache)
    let some initial := FiniteData.suffixes.getState (← getEnv) |>.find? inventory |
      throwError "checked suffix was not retained"
    let some first := initial[0]? | throwError "checked suffix array was empty"
    let _ ← checkMember inventory 2 (toExpr (3 : Nat)) (some cache)
    let _ ← checkMember inventory 0 (toExpr (1 : Nat)) (some cache)
    let proof ← checkMember inventory 2 (toExpr (3 : Nat)) (some cache)
    let some retained := FiniteData.suffixes.getState (← getEnv) |>.find? inventory |
      throwError "checked suffixes disappeared"
    unless retained.size == 2 && retained.any (fun entry => entry.start == 0) &&
        retained.any (fun entry => entry.start == 1 && entry.equality == first.equality) &&
        proof.getUsedConstants.contains first.equality.constName! do
      throwError "an earlier request displaced the nearest checked suffix"
    rejects (FiniteData.suffixMember inventory 1 (toExpr (3 : Nat)) (some cache))
    let dropped ← mkAppM ``List.drop #[toExpr (1 : Nat), inventory]
    rejects (FiniteData.retainEntry (← mkEq dropped wrong) (← mkEqRefl wrong))
    let assigned ← mkFreshExprMVar (← inferType inventory)
    assigned.mvarId!.assign inventory
    let _ ← checkMember assigned 1 (toExpr (2 : Nat))
    unless (FiniteData.suffixes.getState (← getEnv) |>.find? assigned).isNone do
      throwError "suffix cache retained an uninstantiated metavariable key"
    saved.restore
    unless (FiniteData.suffixes.getState (← getEnv) |>.find? inventory).isNone do
      throwError "restoring the environment retained a checked suffix from another branch"
    let _ ← checkMember inventory 2 (toExpr (3 : Nat))
  finally saved.restore

private def namedLevel : MetaM Unit := do
  let one := mkAppN (mkConst ``ULift.up [Level.param `u, Level.zero])
    #[mkConst ``Nat, toExpr (1 : Nat)]
  let two := mkAppN (mkConst ``ULift.up [Level.param `u, Level.zero])
    #[mkConst ``Nat, toExpr (2 : Nat)]
  let inventory ← mkListLit (← inferType one) [one, two]
  let proof ← FiniteData.suffixMember inventory 1 two none
  let type ← mkAppM ``List.Mem #[two, inventory]
  let checked ← FiniteData.retainEntry type proof
  let info ← getConstInfo checked.constName!
  unless info.levelParams.contains `u do throwError "coefficient suffix lost its named universe"
  let _ ← auditProof checked type

syntax (name := coefficientSuffix) "#coefficient_suffix" : command
@[command_elab coefficientSuffix]
def elaborate : CommandElab := fun _ => liftTermElabM do
  positions
  namedLevel
  logInfo "checked coefficient suffixes preserve positions and rollback; corrupt position and suffix reject"

end Hex.RealClosure.Algebraic.KernelReplay.CoefficientSuffix

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- info: checked coefficient suffixes preserve positions and rollback; corrupt position and suffix reject -/
#guard_msgs in
#coefficient_suffix
