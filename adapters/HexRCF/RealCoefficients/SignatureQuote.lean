/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.RootQuote

public meta section

/-! Full-signature reader quotation using checked literal bindings and public codec laws. -/
namespace Hex.RCF.RealCoefficients.SignatureQuote
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RealFormula.Reify

/-- Quote a full signature decoder from its supplied literal binding. Only the
exact signature codec and payload are eligible. A binding must prove
`literal = signature.literal.toJson`; an invalid binding is terminal.
The public owner equation restores the signature without running its parser.
All inputs and proof construction consume the enclosing reflection budget.
Use `RootQuote.runWith` for the transaction. This checks a serialization
identity, not validity of a registry, selected root or context history. -/
def decoder (signature literal binding : Expr) : RootQuote.DecoderM := fun expression => do
  charge .proofNodes 1
  if expression.hasLooseBVars || expression.hasMVar then return none
  let codec? := match expression.getAppFn with
    | .proj ``ValueCodec 1 codec =>
      if expression.getAppNumArgs == 1 then some codec else none
    | .const ``ValueCodec.decode _ =>
      if expression.getAppNumArgs == 3 then some expression.getAppArgs[1]! else none
    | _ => none
  let some codec := codec? | return none
  unless codec.isConstOf ``Tower.Signature.codec do return none
  let payload ← withTransparency .all (whnf expression.getAppArgs.back!)
  unless ← withNewMCtxDepth <| withTransparency .instances <|
      isDefEq payload literal do return none
  let mut inputs := #[]
  for input in #[signature,literal,binding] do
    let input ← instantiateMVars input
    if input.hasFVar || input.hasMVar || input.hasLooseBVars then
      throwError "rcf: signature quotation requires closed retained inputs"
    accountProof input
    inputs := inputs.push (← Hex.RCF.checkExpr `SignatureQuote.input input)
  let signature := inputs[0]!
  let literal := inputs[1]!
  let binding := inputs[2]!
  let encoded ← mkAppM ``Tower.Literal.toJson #[← mkAppM ``Tower.Signature.literal #[signature]]
  let target ← mkEq literal encoded
  accountProof target
  let binding ← Hex.RCF.checkProof `SignatureQuote.binding target binding
  let decode ← withLocalDeclD `literal (mkConst ``Codec.Json.Value) fun literal => do
    mkLambdaFVars #[literal] (← mkAppM ``ValueCodec.decode #[codec,literal])
  let transported ← mkAppM ``congrArg #[decode,binding]
  let canonical ← mkAppM ``Tower.Signature.codec_literal #[signature]
  let candidate ← mkEqTrans transported canonical
  let kind ← inferType candidate
  let target ← mkEq expression kind.getAppArgs[2]!
  accountProof target
  accountProof candidate
  return some (← Hex.RCF.checkProof `SignatureQuote.read target
    (mkExpectedPropHint candidate target))

end Hex.RCF.RealCoefficients.SignatureQuote
