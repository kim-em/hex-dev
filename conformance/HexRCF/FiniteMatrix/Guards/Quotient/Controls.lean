/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Quotient.Quote
open Hex Hex.SignDet Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients.FiniteMatrixTests
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Controls
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
elab "#frozen_inverse_refusals" : command => liftTermElabM do
  let zero ← mkAppOptM ``Zero.zero #[some (← inferType (mkConst ``Reader.argument)), none]
  for (label, argument, entry, packet) in [
      ("otherPair", mkConst ``Reader.argument, mkConst ``Reader.entry, mkConst ``Literals.alternateGraph),
      ("otherOutput", mkConst ``Reader.argument, mkConst ``Reader.alternate, mkConst ``Literals.inverseGraph),
      ("stale", mkConst ``Reader.argument, mkConst ``Reader.entry, mkConst ``Literals.staleGraph),
      ("missing", mkConst ``Reader.argument, mkConst ``Reader.entry, mkConst ``Codec.Json.Value.null),
      ("zero", zero, mkConst ``Reader.entry, mkConst ``Codec.Json.Value.null)] do
    let reader ← mkAppM ``Reader.read #[argument, entry, packet]
    let type ← mkEq (← mkAppM ``Option.isNone #[reader]) (mkConst ``Bool.true)
    let extra := #[``Hex.SignDet.Descriptor.validate, ``Hex.SignDet.Descriptor.ofReplay?] ++
      (if label == "zero" then #[``Codec.readGraph] else #[])
    Hex.RCF.SelectedRootTests.KernelCheck.addChecked
      (Name.str `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Controls label)
      type (← mkDecideProof type) extra #[``Reader.read]
#frozen_inverse_refusals

elab "#frozen_inverse_missing_packing" : command => liftTermElabM do
  let program := mkApp (mkConst ``Source.program) (mkConst ``Packings.facts)
  let goal ← mkEq program (mkConst ``Bool.true)
  let decision ← mkDecide goal
  let result ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) decision)
  if result.isConstOf ``Bool.true || result.isConstOf ``Bool.false then
    throwError "missing quotient packing reached a Boolean"
  let statement ← mkEq decision (mkConst ``Bool.true)
  let options ← getOptions
  let proof ← mkEqRefl (mkConst ``Bool.true)
  let declarationName ← mkFreshUserName `missingQuotientPacking
  let checked := (← getEnv).addDeclCore (Core.getMaxHeartbeats options).toUSize
    (maxRecDepth.get options).toUSize (.thmDecl {
      name := declarationName, levelParams := [], type := statement, value := proof}) none (doCheck := true)
  match checked with
  | .error (.declTypeMismatch ..) => pure ()
  | .error error => throwKernelException error
  | .ok _ => throwError "unrecorded quotient packing accepted"
#frozen_inverse_missing_packing

private def refuse (label : String) (target : Expr) : MetaM Unit := do
  let before ← getMCtx
  let constants := (← getEnv).constants.map₂.toList.length
  let failed ← try
    let _ ← Quote.prove target
    pure false
  catch error =>
    logInfo m!"{label}: {error.toMessageData}"
    pure true
  unless failed do throwError "altered quotient source accepted: {label}"
  let after ← getMCtx
  unless constants == (← getEnv).constants.map₂.toList.length do throwError "failed quotient changed environment"
  unless after.mvarCounter == before.mvarCounter && after.lmvarCounter == before.lmvarCounter &&
      after.depth == before.depth && after.eAssignment.toList == before.eAssignment.toList &&
      after.lAssignment.toList == before.lAssignment.toList do throwError "failed quotient changed metavariable state"

elab "#frozen_quotient_source_refusals" : command => liftTermElabM do
  let changed ← Term.elabType (← `(∃ x : ℝ,
    x ^ 2 + 1 = 2 / (Real.sqrt 2 - 1) + 0 / (-1 : ℝ) ∧ 1 < x ∧ x < 2))
  let zero ← Term.elabType (← `(∃ x : ℝ,
    x ^ 2 + 1 = 1 / (Real.sqrt 2 - Real.sqrt 2) + 0 / (-1 : ℝ) ∧ 1 < x ∧ x < 2))
  Term.synthesizeSyntheticMVarsNoPostponing
  refuse "changed inverse numerator" (← instantiateMVars changed)
  refuse "zero inverse denominator" (← instantiateMVars zero)
/--
info: changed inverse numerator: rcf: handler FiniteQuote.valuationIdentity proposed a proof of a different goal
---
info: zero inverse denominator: rcf: handler FiniteQuote.guardIdentity proposed a proof of a different goal
-/
#guard_msgs (whitespace := lax) in
#frozen_quotient_source_refusals
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Controls
