/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Quote
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Controls
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
private def refuse (label : String) (target : Expr) (identities : Array Expr) : MetaM Unit := do
  let before ← getMCtx
  let constants := (← getEnv).constants.map₂.toList.length
  let failed ← try
    let _ ← Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quote.prove target identities
    pure false
  catch error =>
    logInfo m!"{label}: {error.toMessageData}"
    pure true
  unless failed do throwError "altered original guard accepted: {label}"
  let after ← getMCtx
  unless constants == (← getEnv).constants.map₂.toList.length do throwError "failed quotation changed environment"
  unless after.mvarCounter == before.mvarCounter && after.lmvarCounter == before.lmvarCounter &&
      after.depth == before.depth && after.eAssignment.toList == before.eAssignment.toList &&
      after.lAssignment.toList == before.lAssignment.toList do throwError "failed quotation changed metavariable state"
elab "#frozen_guard_controls" : command => liftTermElabM do
  let valid ← Term.elabType (← `(∃ x : ℝ,
    x ^ 2 = Real.sqrt 2 + 0 / (Real.sqrt 2 - 1) + 0 / (-1 : ℝ) ∧ 1 < x ∧ x < 2))
  let cancelled ← Term.elabType (← `(∃ x : ℝ,
    x ^ 2 = Real.sqrt 2 + 0 / (Real.sqrt 2 - Real.sqrt 2) + 0 / (-1 : ℝ) ∧ 1 < x ∧ x < 2))
  Term.synthesizeSyntheticMVarsNoPostponing
  let valid ← instantiateMVars valid
  let cancelled ← instantiateMVars cancelled
  let first := mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.first
  let second := mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.second
  refuse "reversed original identities" valid #[second, first]
  refuse "omitted negative divisor identity" valid #[first]
  refuse "extra original identity" valid #[first, second, second]
  refuse "cancelled zero divisor" cancelled #[first, second]
/--
info: reversed original identities: rcf: handler FiniteQuote.guardIdentity proposed a proof of a different goal
---
info: omitted negative divisor identity: rcf: finite checker has a different original divisor identity count
---
info: extra original identity: rcf: finite checker has a different original divisor identity count
---
info: cancelled zero divisor: rcf: handler FiniteQuote.guardIdentity proposed a proof of a different goal
-/
#guard_msgs (whitespace := lax) in
#frozen_guard_controls
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Controls
