/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBareissMathlib.Tactic
public meta import HexPolyDetMathlib.Bird.Evaluator
public import HexBareissMathlib.Tactic

public meta section

open Lean Meta Elab

namespace HexPolyDetMathlib

/-- Importing the companion installs its single symbolic extension in the
numeric syntax owner. -/
initialize HexMatrixMathlib.Det.symbolicHandler.set (some {
  compute := Bird.compute
  prove := Bird.prove
})

/-- Close a determinant equality through the shared numeric/Bird operation. -/
@[tactic HexMatrixMathlib.Det.detTac, no_fallback]
def evalDet : Tactic.Tactic := fun stx => Tactic.withMainContext do
  let cfg ← HexMatrixMathlib.Det.elabConfig stx[1]
  match ← Bird.prove cfg (← Tactic.getMainTarget) with
  | .success proof => Tactic.closeMainGoal `det proof
  | .notApplicable msg => throwError "det: not applicable: {msg}"
  | .declined msg =>
    trace[HexMatrix.certificate] "symbolic determinant declined: {msg}"
    throwError "det: symbolic determinant declined: {msg}"

end HexPolyDetMathlib

open Lean Meta in
/-- Opt-in rewriting of a supported symbolic or numeric determinant. -/
simproc_decl Hex.normPolyDet (Matrix.det _) := fun e => do
  match ← HexMatrixMathlib.Det.compute {} e.appArg! with
  | .success p => return .done { expr := p.value, proof? := some p.proof }
  | .notApplicable msg | .declined msg =>
    trace[HexMatrix.certificate] "determinant rewrite declined: {msg}"
    return .continue
