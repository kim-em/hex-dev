/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Restore
import HexRCF.RealCoefficients.FiniteSigns
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.KernelControls
open Lean Meta
private meta def probe (forbidden required : Array Name) : MetaM Unit := do
  let goal ← mkEq (← mkAppM ``FiniteSigns.Row.check
    #[← mkListLit (mkConst ``Int) [],
      ← mkAppOptM ``Hex.RealFormula.QF.tt #[some (mkNatLit 1)],
      ← mkListLit (mkConst ``Int) []])
    (mkAppN (mkConst ``Except.ok [.zero, .zero])
      #[mkConst ``Replay.Error, mkConst ``Bool, mkConst ``Bool.true])
  Hex.RCF.SelectedRootTests.KernelCheck.addChecked
    (← mkFreshUserName `kernelTripwire) goal
    (← mkDecideProof goal) forbidden required
/-- error: native production unfolded Hex.RCF.RealCoefficients.FiniteSigns.Row.check: 1 -/
#guard_msgs (whitespace := lax) in
run_meta probe #[``FiniteSigns.Row.check] #[]
/-- error: kernel diagnostics did not observe required reader Hex.RCF.RealCoefficients.FiniteMatrixTests.Read.selected -/
#guard_msgs (whitespace := lax) in
run_meta probe #[] #[``Read.selected]
end Hex.RCF.RealCoefficients.FiniteMatrixTests.KernelControls
