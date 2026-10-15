/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.FiniteData

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteRange
open Lean Meta Elab Command FiniteData

private def statement (count : Nat) (dependent : Bool) : MetaM Expr := do
  withLocalDeclD `i (mkConst ``Nat) fun i => do
    let bound ← mkAppM ``Nat.lt #[i, toExpr count]
    withLocalDeclD `bound bound fun h => do
      let value := mkAppN (mkConst ``Fin.mk) #[toExpr count, i, h]
      let conclusion ← if dependent then mkEq value value else mkEq i (toExpr (0 : Nat))
      mkForallFVars #[i, h] conclusion

private def computed (count : Expr) (instance? : Option Expr := none) : MetaM Expr := do
  withLocalDeclD `i (mkConst ``Nat) fun i => do
    let bound ← match instance? with
      | none => mkAppM ``Nat.lt #[i, count]
      | some order => pure (mkAppN (mkConst ``LT.lt [Level.zero])
          #[mkConst ``Nat, order, i, count])
    withLocalDeclD `bound bound fun h => do
      let value := mkAppN (mkConst ``Fin.mk) #[count, i, h]
      mkForallFVars #[i, h] (← mkEq value value)

private def discovery (count : Expr) : MetaM Unit := do
  let type ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let bound ← mkAppM ``Nat.lt #[i, count]
    withLocalDeclD `bound bound fun h => do
      let value := mkAppN (mkConst ``Fin.mk) #[count, i, h]
      let index := mkAppN (mkConst ``Fin.val) #[count, value]
      let equal ← mkAppM ``Nat.beq #[index, i]
      mkForallFVars #[i, h] (← mkEq equal (mkConst ``Bool.true))
  let boundary (type : Expr) : MetaM Bool := pure
    (type.getAppFn.isConstOf ``Eq && type.getAppArgs[0]!.isConstOf ``Bool)
  for leaves in #[← FiniteData.leaves type (fun _ => pure none),
      ← frontier type boundary] do
    unless leaves.size == 3 do throwError "finite discovery lost an actual dependent index"
    for i in [:leaves.size] do
      let some leaf := leaves[i]? | throwError "finite discovery lost a reached leaf"
      leaf.withContext do
        let args := leaf.type.getAppArgs[1]!.getAppArgs
        let some actual ← withTransparency .all (getNatValue? args.back!) |
          throwError "finite discovery left a symbolic reached index"
        unless actual == i do throwError "finite discovery changed its index order"
        let used := collectFVars {} leaf.type
        unless leaf.type.hasFVar do throwError "finite discovery lost its bound proof"
        for id in used.fvarIds do
          unless (leaf.context.find? id).isSome do
            throwError "finite discovery lost a dependent local hypothesis"

private def nonstandard : MetaM Unit := do
  let relation ← withLocalDeclD `a (mkConst ``Nat) fun a => do
    withLocalDeclD `b (mkConst ``Nat) fun b => do
      mkLambdaFVars #[a, b] (← mkAppM ``Nat.lt #[b, a])
  let reversed ← mkAppM ``LT.mk #[relation]
  let type ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let bound := mkAppN (mkConst ``LT.lt [Level.zero])
      #[mkConst ``Nat, reversed, i, toExpr (3 : Nat)]
    withLocalDeclD `bound bound fun h => do
      let equal ← mkAppM ``Nat.beq #[i, toExpr (0 : Nat)]
      mkForallFVars #[i, h] (← mkEq equal (mkConst ``Bool.true))
  let leaves ← frontier type (fun type => pure (type.getAppFn.isConstOf ``Eq))
  let some leaf := leaves[0]? | throwError "finite discovery dropped a nonstandard Nat relation"
  let same ← withNewMCtxDepth do withTransparency .all (isDefEq leaf.type type)
  unless leaves.size == 1 && same do
    throwError "finite discovery changed a nonstandard Nat relation: leaves={leaves.size}, actual={leaf.type}, original={type}"

syntax (name := finiteRange) "#finite_range" : command
@[command_elab finiteRange]
def elaborate : CommandElab := fun _ => liftTermElabM do
  for count in #[0, 1, 3] do
    let reached ← IO.mkRef (#[] : Array Nat)
    let supply : Supplier := fun type => do
      let args := type.getAppArgs
      unless type.getAppFn.isConstOf ``Eq && args.size == 3 do return none
      unless args[0]!.getAppFn.isConstOf ``Fin do return none
      let value := args[1]!.getAppArgs
      let some index ← withTransparency .all (getNatValue? value[1]!) |
        throwError "bounded traversal left an unspecified index"
      reached.modify (·.push index)
      return some (← mkEqRefl args[1]!)
    let type ← statement count true
    let _ ← buildClosed type supply
    unless (← reached.get).toList == List.range count do
      throwError "bounded traversal skipped or repeated an actual dependent index"
  let count ← mkAppM ``List.length
    #[← mkListLit (mkConst ``Nat) [toExpr (7 : Nat), toExpr (8 : Nat), toExpr (9 : Nat)]]
  for instance? in #[none, some (mkConst ``instLTNat)] do
    let type ← computed count instance?
    let _ ← buildClosed type fun type => do
      let args := type.getAppArgs
      unless type.getAppFn.isConstOf ``Eq && args.size == 3 do return none
      return some (← mkEqRefl args[1]!)
  discovery count
  nonstandard
  let falseStatement ← statement 3 false
  let rejected ← try
    let _ ← buildClosed falseStatement fun type => do
      let args := type.getAppArgs
      unless type.getAppFn.isConstOf ``Eq && args.size == 3 do return none
      unless ← withTransparency .all (isDefEq args[1]! args[2]!) do return none
      return some (← mkEqRefl args[1]!)
    pure false
  catch error =>
    unless (← error.toMessageData.toString).startsWith "missing finite replay evidence" do
      throw error
    pure true
  unless rejected do throwError "bounded traversal accepted an unsupported index"
  logInfo "empty, singleton and dependent finite ranges kernel checked; unsupported index rejected"

end Hex.RealClosure.Algebraic.KernelReplay.FiniteRange

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- info: empty, singleton and dependent finite ranges kernel checked; unsupported index rejected -/
#guard_msgs in
#finite_range
