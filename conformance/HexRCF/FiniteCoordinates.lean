/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.CertificationInputs
public meta import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients.CommonTactic
public meta import Lean.Elab.Command
public section
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option debug.skipKernelTC false
set_option Elab.async false
run_meta do
  let alpha := q(Hex.RCF.CertificationInputs.realAlgebraic.toReal)
  let cases : Array (Name × Expr × Nat) := #[
    (`Hex.RCF.FiniteCoordinates.values,q(∀ x : ℝ, x^2+$alpha+Real.sqrt 2>0),0),
    (`Hex.RCF.FiniteCoordinates.quotient,q(∀ x : ℝ, x^2+1/($alpha+Real.sqrt 2)>0),1),
    (`Hex.RCF.FiniteCoordinates.cancelled,q(∀ x : ℝ, x^2+0/($alpha+Real.sqrt 2)>0),1)]
  for (name,target,guards) in cases do
    let .ok prepared ← CommonTactic.prepareCoordinates target |
      throwError "finite coordinate preparation declined {name}"
    unless prepared.polynomial.natDegree == 8 do throwError "expected degree-eight presentation"
    unless prepared.source.divisors.size == guards && prepared.divisorProofs.size == guards do
      throwError "lost original guards"
    prepared.checkDomains
    let rep ← mkAppM ``Field.literalRep prepared.rootExpr.getAppArgs
    let interpretation ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit prepared.arity)) fun i => do
      mkLambdaFVars #[i] (← mkAppM ``Field.value #[rep,mkApp prepared.valuesExpr i])
    let expected ← mkEq interpretation prepared.source.valuation
    let proof ← Hex.RCF.checkProof name expected prepared.valuationProof
    addDecl (.thmDecl {name,levelParams:=[],type:=expected,value:=proof})
    for i in [:guards] do
      let divisor : Q(ℝ) ← pure prepared.source.divisors[i]!
      let name := name ++ `guard
      let proof ← Hex.RCF.checkProof name q($divisor ≠ 0) prepared.divisorProofs[i]!
      addDecl (.thmDecl {name,levelParams:=[],type:=q($divisor ≠ 0),value:=proof})
    logInfo m!"FINITE_COORDINATES {name}: degree=8; guards={guards}; source proofs checked"
  for target in #[q(∀ x : ℝ, x^2+0/($alpha-$alpha)≥0),
      q(∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 0 → x^2+0/($alpha-$alpha)≥0)] do
    let saved ← saveState
    let rejected ← try
      let _ ← CommonTactic.prepareCoordinates target
      pure false
    catch e => pure (((← e.toMessageData.toString).splitOn "original closed divisor is zero").length > 1)
    saved.restore
    unless rejected do throwError "cancelled zero denominator accepted during preparation"
#print axioms Hex.RCF.FiniteCoordinates.values
#print axioms Hex.RCF.FiniteCoordinates.quotient
#print axioms Hex.RCF.FiniteCoordinates.quotient.guard
#print axioms Hex.RCF.FiniteCoordinates.cancelled
#print axioms Hex.RCF.FiniteCoordinates.cancelled.guard
