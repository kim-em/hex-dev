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
set_option maxHeartbeats 40000000
set_option debug.skipKernelTC false
set_option Elab.async false

-- Exercise source preparation and finite replay directly, independently of
-- tactic dispatch. The ordinary `by rcf` entry point is tested in FiniteDefault.
run_meta do
  let alpha : Q(ℝ) := q(Hex.RCF.CertificationInputs.realAlgebraic.toReal)
  let cases : Array (Name × Expr) := #[
    (`Hex.RCF.FiniteSourceTactic.positive,q(∀ x : ℝ, x^2+$alpha+Real.sqrt 2>0)),
    (`Hex.RCF.FiniteSourceTactic.fourthRoot,q(∃ x : ℝ, x^2=Real.sqrt 2 ∧ 1<x ∧ x<2)),
    (`Hex.RCF.FiniteSourceTactic.betweenRoots,
      q(∀ x : ℝ, x^2-($alpha+Real.sqrt 2)*x+$alpha*Real.sqrt 2<0 → 1<x ∧ x<2))]
  for (name,target) in cases do
    let started ← IO.monoMsNow
    let .ok prepared ← CommonTactic.prepareCoordinates target |
      throwError "finite source recognition declined {name}"
    let proof ← prepared.prove
    let proof ← Hex.RCF.checkProof name target proof
    addDecl (.thmDecl {name,levelParams:=[],type:=target,value:=proof})
    logInfo m!"FINITE_SOURCE_TACTIC {name}: original target checked; ms={(← IO.monoMsNow)-started}"
  let .ok prepared ← CommonTactic.prepareCoordinates q(∀ x : ℝ, x^2<$alpha+Real.sqrt 2) |
    throwError "finite false fixture declined"
  let before := (← getEnv).constants.map₂.toList.length
  let failure ← try
    let _ ← prepared.prove
    pure "accepted"
  catch e => e.toMessageData.toString
  unless (failure.splitOn "universal sentence is false").length > 1 do
    throwError "unexpected finite false diagnostic: {failure}"
  unless (← getEnv).constants.map₂.toList.length == before do
    throwError "finite false failure retained temporary declarations"
#print axioms Hex.RCF.FiniteSourceTactic.positive
#print axioms Hex.RCF.FiniteSourceTactic.fourthRoot
#print axioms Hex.RCF.FiniteSourceTactic.betweenRoots
