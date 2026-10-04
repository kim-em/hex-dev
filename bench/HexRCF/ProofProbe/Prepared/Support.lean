/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public meta import Lean
public section

namespace Hex.RCF.ProofProbe.Prepared

/-- Build-only probe of the explicit prepared finite replay API. -/
elab "prepared_rcf" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let .ok input ← RealCoefficients.Coefficients.prepare (← goal.getType) |
    throwError "prepared proof probe did not recognize its source"
  goal.assign (← input.proveReplay)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Build-only probe of total production on an authenticated exact field. -/
elab "prepared_total" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let .ok input ← RealCoefficients.Coefficients.prepare (← goal.getType) |
    throwError "total proof probe did not recognize its source"
  goal.assign (← input.proveTotalReplay)
  Lean.Elab.Tactic.replaceMainGoal []

end Hex.RCF.ProofProbe.Prepared
