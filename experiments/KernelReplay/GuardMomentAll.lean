/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardMomentLast
public meta import KernelReplay.GuardMomentLast
import all KernelReplay.GuardMomentLast
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardMomentSecond
import all KernelReplay.GuardDescriptorInputs

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAll

private theorem three {p : Fin 3 → Prop} (zero : p 0) (one : p 1) (two : p 2) : ∀ i, p i :=
  Fin.cases zero (Fin.cases one (Fin.cases two (fun i => i.elim0)))

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAll

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAll
open Lean Meta Elab FiniteData GuardDescriptorInputs


set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let setup ← GuardDescriptorInputs.prepare
  let target := setup.nodeFields[4]!
  let .forallE _ domain body _ := target | throwError "actual moment family lost its finite index"
  unless domain.getAppFn.isConstOf ``Fin do throwError "actual moment family index is not finite"
  kernelCheck `__allActualMomentCount (← mkEq domain.getAppArgs.back! (toExpr (3 : Nat)))
    (mkConst ``GuardMomentSecond.momentCount_eq)
  let indexType ← mkAppM ``Fin #[toExpr (3 : Nat)]
  let predicate ← withLocalDeclD `index indexType fun index =>
    mkLambdaFVars #[index] (body.instantiate1 index)
  let proof ← mkAppOptM ``three #[some predicate,
    some (mkConst ``GuardMomentFirst.data), some (mkConst ``GuardMomentSecond.data),
    some (mkConst ``GuardMomentLast.data)]
  let proof ← withTransparency .all do mkAppOptM ``id #[some target, some proof]
  let _ ← retain began `Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAll.statement target
  let _ ← retain began `Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAll.moments proof
  logInfo m!"actual complete moment family module export: actualFiniteBound=3 allIndices=[0,1,2] originalTargetRetained=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAll
