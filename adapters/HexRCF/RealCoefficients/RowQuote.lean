/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellOperations
public meta import HexRCF.RealCoefficients.RootQuote
public section

namespace Hex.RCF.RealCoefficients.RowQuote
open Hex Hex.SignDet Hex.RealClosure Hex.RealClosure.Tower
variable {E Ctx : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [DecidableEq Ctx] {sign : E → Int} {binding : Ctx}

/-- A checked query-list transport retains the stored row values. -/
theorem values_cast {root : Descriptor E Ctx sign binding} {before after : List (DensePoly E)}
    (same : before = after) (source : SelectedSigns root before) :
    (same ▸ source).values.toArray = source.values.toArray := by
  cases same
  rfl

/-- Equal root and query subjects retain the stored row values. -/
theorem values_retarget {first second : Descriptor E Ctx sign binding}
    (rootEq : first = second) {before after : List (DensePoly E)} (queryEq : before = after)
    (source : SelectedSigns first before) :
    (RowOperations.retarget sign binding rootEq queryEq source).values.toArray =
      source.values.toArray := rfl

/-- Restoring the canonical operations retains the supplied row values. -/
theorem values_restore {registry : BaseContext.Registry} {parent : Tower.Context registry}
    (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (original : Descriptor parent.Value Signature parent.sign parent.signature)
    (queries : List parent.Poly) (source : CellOperations.Signs operations original queries) :
    (CellOperations.restore operations original queries source).values.toArray =
      (@SelectedSigns.values parent.Value Signature _ _ operations.one operations.add
        operations.sub operations.mul operations.natCast _ parent.sign parent.signature
        (CellOperations.descriptor operations original) queries source).toArray := rfl

private theorem value_array {root : Descriptor E Ctx sign binding} {q : DensePoly E}
    (source : SelectedSigns root [q]) (values : Array Int)
    (same : source.values.toArray = values) :
    source.value = values[0]'(by
      have size := source.values.size_toArray
      rw [same] at size
      simp only [List.length_cons,List.length_nil] at size
      omega) := by
  cases same
  rfl
/-- A checked singleton array determines the selected query value. -/
theorem value_eq {root : Descriptor E Ctx sign binding} {q : DensePoly E}
    (source : SelectedSigns root [q]) (value : Int)
    (same : source.values.toArray = #[value]) : source.value = value := by
  exact value_array source #[value] same

end Hex.RCF.RealCoefficients.RowQuote

public meta section
namespace Hex.RCF.RealCoefficients.RowQuote
open Lean Meta Hex.RealFormula.Reify

private def explicitArguments (expression : Expr) : ReifyM (Array Expr) := do
  let args := expression.getAppArgs
  let info ← getFunInfoNArgs expression.getAppFn args.size
  return args.zipIdx |>.filterMap fun (arg,i) =>
    if info.paramInfo[i]!.binderInfo.isExplicit then some arg else none

private partial def project (source : Expr) : ReifyM (Expr × Expr) := Core.withIncRecDepth do
  charge .proofNodes 1
  Core.checkSystem "selected-sign projection transport"
  let source := source.consumeMData
  let head := source.getAppFn.constName?
  let boundary ← if head == some ``RowOperations.retarget then do
      let args ← explicitArguments source
      unless args.size == 5 do throwError "unexpected retarget arity: {args.size}"
      let parameters := source.getAppArgs
      let parameters := parameters.extract 0 4 ++ parameters.extract 5 10 ++
        #[parameters[4]!] ++ parameters.extract 10 parameters.size
      pure (some (mkAppN (mkConst ``RowQuote.values_retarget)
        parameters,args[4]!))
    else if head == some ``CellOperations.restore then do
      let args ← explicitArguments source
      unless args.size == 4 do throwError "unexpected restore arity: {args.size}"
      pure (some (mkAppN (mkConst ``RowQuote.values_restore)
        source.getAppArgs,args[3]!))
    else if head == some ``Eq.rec then do
      let .recInfo info ← getConstInfo ``Eq.rec | throwError "equality recursor metadata missing"
      let args := source.getAppArgs
      let originalEquality := args[info.getMajorIdx]!
      let target ← if info.numIndices == 1 then
        mkEq args[info.numParams-1]! args[info.getFirstIndexIdx]!
      else if info.numIndices == 2 then
        mkEq args[info.getFirstIndexIdx]! args[info.getFirstIndexIdx+1]!
      else throwError "unsupported equality recursor indices"
      let equality := mkExpectedPropHint originalEquality target
      let before := args[info.getFirstMinorIdx]!
      let selectedType ← withTransparency .reducible (whnf (← inferType before))
      unless selectedType.getAppFn.isConstOf ``Hex.SignDet.SelectedSigns do
        throwError "equality transport does not move a selected-sign record"
      let parameters := selectedType.getAppArgs
      let law := mkAppN (mkConst ``RowQuote.values_cast)
        ((parameters.extract 0 (parameters.size-1)) ++
          #[parameters.back!,args[info.getFirstIndexIdx]!,equality,before])
      pure (some (law,before))
    else pure none
  if let some (law,before) := boundary then
    accountProof law
    let (value,identity) ← project before
    return (value,← mkEqTrans law identity)
  let selectedType ← withTransparency .reducible (whnf (← inferType source))
  unless selectedType.getAppFn.isConstOf ``Hex.SignDet.SelectedSigns do
    throwError "selected projection base has a different record type"
  let stored := mkAppN
    (mkConst ``Hex.SignDet.SelectedSigns.values selectedType.getAppFn.constLevels!)
    (selectedType.getAppArgs.push source)
  let array ← mkAppM ``Vector.toArray #[stored]
  let value ← withTransparency .all (whnf array)
  return (value,mkExpectedPropHint (← mkEqRefl value) (← mkEq array value))

private def valueWith (left : Expr) : ReifyM (Expr × Expr) := do
  let source := left.getAppArgs.back!
  let (values,identity) ← project source
  let mut laws : SimpTheorems := {}
  for name in #[``Array.emptyWithCapacity_eq, ``Array.toList_empty,
      ``List.concat_eq_append, ``List.nil_append, ``List.get_eq_getElem,
      ``List.getElem_cons] do
    laws ← laws.addConst name
  let context ← Simp.mkContext {maxSteps := 10000} #[laws]
  let mut reduced ← withTransparency .all (whnf values)
  let mut conversion := mkExpectedPropHint (← mkEqRefl reduced) (← mkEq values reduced)
  for _ in [:4] do
    charge .proofNodes 1
    let (result,work) ← Meta.simpCore reduced context
    charge .proofNodes work.numSteps
    conversion ← mkEqTrans conversion (← result.getProof' reduced)
    reduced ← withTransparency .all (whnf result.expr)
    conversion ← mkEqTrans conversion
      (mkExpectedPropHint (← mkEqRefl reduced) (← mkEq result.expr reduced))
  let list ← withTransparency .all (whnf (← mkAppM ``Array.toList #[reduced]))
  let some entries ← getListLit? list
    | throwError "selected-sign values did not reduce to a literal array"
  unless entries.size == 1 do throwError "selected-sign singleton has a different length"
  let value ← withTransparency .all (whnf entries[0]!)
  unless (value.isAppOfArity ``Int.ofNat 1 || value.isAppOfArity ``Int.negSucc 1) &&
      (← getNatValue? value.appArg!).isSome do
    throwError "selected-sign singleton does not contain a literal integer"
  let singleton ← mkArrayLit (mkConst ``Int) [value]
  let target ← mkEq values singleton
  let candidate ← mkEqTrans conversion
    (mkExpectedPropHint (← mkEqRefl reduced) (← mkEq reduced singleton))
  accountProof candidate
  let checked ← Hex.RCF.checkProof `RowQuote.array target candidate
  let identity ← mkEqTrans identity checked
  let candidate := mkAppN (mkConst ``RowQuote.value_eq)
    (left.getAppArgs ++ #[value,identity])
  let target ← mkEq left value
  accountProof candidate
  let checked ← Hex.RCF.checkProof `RowQuote.value target
    (mkExpectedPropHint candidate target)
  return (value,checked)

/-- Propose a checked equality for a demanded literal selected-sign value or
its integer comparison. Query, descriptor and operation transports preserve
the original row; no sign or root producer runs. All work consumes the enclosing
reflection budget, including public equation simplification and proof checking.
Unrecognized boundaries decline; malformed literal rows fail terminally. -/
def decoder (expression : Expr) : ReifyM (Option Expr) := do
  charge .proofNodes 1
  if expression.getAppFn.isConstOf ``Hex.SignDet.SelectedSigns.value then
    return some (← valueWith expression).2
  unless expression.isAppOfArity ``Decidable.decide 2 do return none
  let proposition := expression.getAppArgs[0]!
  unless proposition.isAppOfArity ``Eq 3 && proposition.getAppArgs[0]!.isConstOf ``Int do
    return none
  let left := proposition.getAppArgs[1]!
  unless left.getAppFn.isConstOf ``Hex.SignDet.SelectedSigns.value do return none
  let (value,identity) ← valueWith left
  let motive ← withLocalDeclD `sign (mkConst ``Int) fun sign => do
    mkLambdaFVars #[sign] (expression.replace fun part => if part == left then some sign else none)
  let next := motive.bindingBody!.instantiate1 value
  unless next != expression do throwError "selected-sign projection did not change the comparison"
  let candidate ← mkAppM ``congrArg #[motive,identity]
  let target ← mkEq expression next
  accountProof candidate
  return some (← Hex.RCF.checkProof `RowQuote.boolean target
    (mkExpectedPropHint candidate target))
end Hex.RCF.RealCoefficients.RowQuote
