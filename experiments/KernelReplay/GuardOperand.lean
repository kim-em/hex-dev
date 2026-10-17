/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardSecondData
public meta import KernelReplay.GuardSecondData
public meta import KernelReplay.GuardNativeBindings
import all KernelReplay.GuardSecondData
import all KernelReplay.GuardNativeBindings
import all KernelReplay.GuardNativeFrontier
import all KernelReplay.FrameOperand
import all KernelReplay.FrameOwners
import all KernelReplay.GuardDescriptorInputs

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardOperand

private theorem constant_eq {E : Type u} [Zero E] [DecidableEq E]
    (c : E) (nonzero : c ≠ 0) : FrameOperand.constant c nonzero = DensePoly.C c := by
  cases same : DensePoly.C c with
  | mk coeffs normalized =>
    have equal : coeffs = #[c] := by
      simpa only [same] using (DensePoly.coeffs_C_of_ne_zero nonzero)
    subst coeffs
    rfl

end Hex.RealClosure.Algebraic.KernelReplay.GuardOperand

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardOperand
open Lean Meta Elab FiniteData GuardDescriptorInputs


private def typed (type value : Expr) : MetaM Expr := withTransparency .all do
  mkAppOptM ``id #[some type, some value]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let environment := (← getEnv).checked.get
  let roots := environment.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.GuardNativeFrontier." &&
        info.type.getAppFn.isConstOf ``SignFact then found.push name else found) (#[] : Array Name)
  unless roots.size == 17 do throwError "missing complete finite scalar inventory"
  let .defnInfo originalBeta ← getConstInfo ``FrameOwners.beta |
    throwError "original native beta is missing"
  unless originalBeta.value.getAppFn.isConstOf ``Element.ofPoly do
    throwError "original native beta changed construction"
  let originalGenerator := originalBeta.value.getAppArgs.back!
  let owner := (← inferType (mkConst ``FrameOwners.beta)).getAppArgs.back!
  let originalReduced ← mkAppM ``Context.reduce #[owner, originalGenerator]
  let mut facts := #[]
  for name in roots do
    let source ← GuardNativeAudit.origin name
    if source.toString.startsWith "_private.KernelReplay.FrameOperand." then
      let polynomial ← mkAppM ``SignFact.polynomial #[mkConst name]
      if ← withTransparency .all (isDefEq polynomial originalReduced) then
        facts := facts.push (mkConst name)
  unless facts.size == 1 do throwError "original operand has no unique finite scalar fact"
  let fact := facts[0]!
  let sign ← mkAppM ``SignFact.sign #[fact]
  let checked ← mkAppM ``SignFact.checked #[fact]
  let reduced ← mkAppM ``SignFact.polynomial #[fact]
  let nonzeroType ← mkAppM ``Ne #[sign, toExpr (0 : Int)]
  let nonzero ← mkAppOptM ``of_decide_eq_true
    #[some nonzeroType, none, some (← mkEqRefl (mkConst ``Bool.true))]
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardOperand
  let nonzero ← retain began (root ++ `signNonzero) (← typed nonzeroType nonzero)
  let original := mkConst ``FrameOwners.beta
  let beta ← mkAppM ``Element.restore #[reduced, sign, checked, nonzero]
  let beta ← retain began (root ++ `beta) (← typed (← inferType original) beta)
  let .defnInfo source ← getConstInfo ``FrameOwners.beta |
    throwError "original native beta is missing"
  unless source.value.getAppFn.isConstOf ``Element.ofPoly do
    throwError "original native beta changed construction"
  let generator := source.value.getAppArgs.back!
  let restored ← withTransparency .all do
    mkAppM ``Element.ofPoly_restore #[generator, sign, checked, nonzero]
  let betaNative ← retain began (root ++ `betaNative)
    (← typed (← mkEq beta original) (← mkAppM ``Eq.symm #[restored]))
  let .defnInfo sourcePolynomial ← getConstInfo ``FrameOwners.requestPoly |
    throwError "original native request polynomial is missing"
  unless sourcePolynomial.value.getAppFn.isConstOf ``DensePoly.C do
    throwError "original native request polynomial changed construction"
  let constructor := sourcePolynomial.value.appFn!
  let parameters := constructor.getAppArgs
  let zero := mkAppN (mkConst ``Zero.zero constructor.getAppFn.constLevels!)
    (parameters.extract 0 2)
  let nonzeroType ← mkAppM ``Ne #[beta, zero]
  let type ← inferType original
  let stored := mkAppN (mkConst ``Element.stored type.getAppFn.constLevels!) type.getAppArgs
  let nonzero ← withLocalDeclD `equal (← mkEq beta zero) fun equal => do
    let same ← mkAppM ``congrArg #[stored, equal]
    let contradiction ← withExporting (isExporting := false) do
      withTransparency .all (mkNoConfusion (mkConst ``False) same)
    mkLambdaFVars #[equal] contradiction
  let nonzero ← retain began (root ++ `betaNonzero) (← typed nonzeroType nonzero)
  let polynomial ← retain began (root ++ `polynomial)
    (← mkAppM ``FrameOperand.constant #[beta, nonzero])
  let literalEq ← mkAppM ``constant_eq #[beta, nonzero]
  let nativeEq ← mkAppM ``congrArg #[constructor, betaNative]
  let native ← retain began (root ++ `polynomialNative)
    (← typed (← mkEq polynomial (mkConst ``FrameOwners.requestPoly))
      (← mkAppM ``Eq.trans #[literalEq, nativeEq]))
  kernelCheck `__sameCapturedOperand (← mkEq polynomial (mkConst ``FrameOperand.requestPoly))
    (← mkEqRefl (mkConst ``FrameOperand.requestPoly))
  logInfo m!"original native operand module export: finiteScalarFacts=1 originalBetaEqualityKernelChecked=true originalNativePolynomialEqualityKernelChecked=true capturedPolynomialEqualityKernelChecked=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardOperand
