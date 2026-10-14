/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.FiniteSigns
public meta import HexRCF.Tactic
public section
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.ModuleCheck
/-- Ordinary module consumers can reduce the exported checker bodies. -/
theorem constant : FiniteSigns.Row.check [] (.tt : Hex.RealFormula.QF 1) [] = .ok true := by
  decide +kernel

theorem zero_guard : FiniteSigns.Row.check [0] (.tt : Hex.RealFormula.QF 1) [] = .error .divisor := by
  decide +kernel
open Lean Meta in
run_meta do
  for name in #[``constant, ``zero_guard] do
    let .thmInfo info ← getConstInfo name | throwError "expected module consumer theorem"
    let _ ← Hex.RCF.checkProof name info.type info.value
end Hex.RCF.RealCoefficients.FiniteMatrixTests.ModuleCheck
