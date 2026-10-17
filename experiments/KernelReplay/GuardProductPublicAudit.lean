/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardProductPublic
import KernelReplay.GuardSecondPublicAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardProductPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardOperand.beta, mkConst ``GuardOperand.signNonzero,
    mkConst ``GuardOperand.betaNonzero, mkConst ``GuardOperand.betaNative,
    mkConst ``GuardOperand.polynomial, mkConst ``GuardOperand.polynomialNative,
    mkConst ``GuardProduct.product, mkConst ``GuardProduct.nativeProduct,
    mkConst ``GuardProductPublic.operand, mkConst ``GuardProductPublic.polynomial,
    mkConst ``GuardProductPublic.product, mkConst ``GuardSecondData.pointBinding,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"original native product public consumer audit: originalOperandBothSidesKernelChecked=true originalBetaAndNativePolynomialEqualitiesChecked=true originalSecondReaderExplicit=true sameFirstAndSecondPointsChecked=true ordinaryPublicImports=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardProductPublicAudit
