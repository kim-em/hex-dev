/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosure.NumberFieldTower
public meta import HexRCF.RealCoefficients.RootQuote
public meta section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RealCoefficients.RationalQuote

private def number? (expression : Expr) : MetaM (Option Int) := do
  Core.checkSystem "rational literal number"
  let expression ← whnf expression
  unless expression.isAppOfArity ``Codec.Json.Value.number 1 do return none
  let argument := expression.appArg!
  if let some number ← getIntValue? argument then return some number
  let argument ← whnf argument
  if argument.isAppOfArity ``Int.ofNat 1 then
    return (← getNatValue? argument.appArg!).map Int.ofNat
  if argument.isAppOfArity ``Int.negSucc 1 then
    return (← getNatValue? argument.appArg!).map Int.negSucc
  return none

private def payload? (expression : Expr) : MetaM (Option (Int × Int)) := do
  let expression ← whnf expression
  unless expression.isAppOfArity ``Codec.Json.Value.array 1 do return none
  let mut rest := expression.appArg!
  let mut numbers : Array Int := #[]
  for _ in [:3] do
    Core.checkSystem "rational literal payload"
    let list ← whnf rest
    unless list.isAppOfArity ``Codec.Json.Values.cons 2 do return none
    let arguments := list.getAppArgs
    let some number ← number? arguments[0]! | return none
    numbers := numbers.push number
    rest := arguments[1]!
  unless (← whnf rest).isConstOf ``Codec.Json.Values.nil do return none
  unless numbers[0]! == 0 do return none
  return some (numbers[1]!,numbers[2]!)

/-- Propose the public rational-base decoding equation for a canonical
`[0,n,d]` payload. Native rational arithmetic selects a candidate only; ordinary
proofs establish its exact numerator and denominator. Use this callback with
`RootQuote.quote`, which checks its equation against the demanded input and
accounts for the proof. Codec eligibility uses reducible transparency, so a
foreign selected-root context is not unfolded. A different codec or noncanonical
payload declines. An ill-typed registry is a terminal input error.
This does not authenticate a source coefficient, registry or context history. -/
def decoder (registry : Expr) : RootQuote.Decoder := fun expression => do
  if expression.hasMVar || registry.hasMVar then return none
  unless ← withNewMCtxDepth <| withTransparency .reducible <|
      isDefEq (← inferType registry) (mkConst ``BaseContext.Registry) do
    throwError "rcf: rational quotation expects a BaseContext.Registry expression"
  let .proj ``ValueCodec 1 codec := expression.getAppFn | return none
  unless expression.getAppNumArgs == 1 do return none
  let some (numerator,denominator) ← payload? expression.appArg! | return none
  unless denominator > 0 do return none
  let rational := mkRat numerator denominator.toNat
  unless rational.num == numerator && (rational.den : Int) == denominator do return none
  let context ← mkAppM ``Hex.RealClosure.NumberField.base #[registry]
  let expected ← mkAppM ``Tower.Context.codec #[context]
  -- Do not unfold a foreign context's producer while deciding eligibility.
  unless ← withNewMCtxDepth <| withTransparency .reducible <| isDefEq codec expected do return none
  let value ← mkAppM ``mkRat #[mkIntLit numerator,mkNatLit denominator.toNat]
  let numeratorType ← mkEq (← mkAppM ``Rat.num #[value]) (mkIntLit numerator)
  let denominatorType ← mkEq (← mkAppM ``Int.ofNat #[← mkAppM ``Rat.den #[value]])
    (mkIntLit denominator)
  let proof ← mkAppM ``Hex.RealClosure.NumberField.decode_payload
    #[registry,value,mkIntLit numerator,mkIntLit denominator,
      ← mkDecideProof numeratorType,← mkDecideProof denominatorType]
  let type ← inferType proof
  if ← withNewMCtxDepth <| withTransparency .all <| isDefEq expression type.getAppArgs[1]! then
    return some proof
  return none

end Hex.RCF.RealCoefficients.RationalQuote
