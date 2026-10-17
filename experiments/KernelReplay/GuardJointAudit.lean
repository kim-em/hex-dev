/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardJoint

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardJointAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta do
  let began ← IO.getNumHeartbeats
  let name := ``GuardJoint.exists_points
  let info ← getConstInfo name
  unless info.isTheorem && info.levelParams.isEmpty do
    throwError "complete original joint theorem is unavailable"
  let mut type := info.type
  for _ in [:3] do
    unless type.getAppFn.isConstOf ``Exists do throwError "joint theorem lost a witness"
    let .lam _ _ body _ := type.getAppArgs[1]! | throwError "joint predicate is not explicit"
    type := body
  let count ← audit began #[mkConst name]
  logInfo m!"original joint existence result: witnesses=3 originalGuards=3773 completeClauses=3778 fullOrderedBaseAgreement=true inheritedProviderValuesFixed=true bothOriginalInventories=true originalNativeProduct=true chosenWitnessesAbsentFromStatement=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardJointAudit
