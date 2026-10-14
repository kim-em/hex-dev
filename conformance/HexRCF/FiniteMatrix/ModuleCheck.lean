/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.FiniteSigns
public import HexRCF.RealCoefficients.RootReplay
public meta import HexRCF.Tactic
public section
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.ModuleCheck
/-- Ordinary module consumers can reduce the exported checker bodies. -/
theorem constant : FiniteSigns.Row.check [] (.tt : Hex.RealFormula.QF 1) [] = .ok true := by
  decide +kernel

theorem zero_guard : FiniteSigns.Row.check [0] (.tt : Hex.RealFormula.QF 1) [] = .error .divisor := by
  decide +kernel
open Hex Hex.RealClosure
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- The public interpretation map unfolds through an ordinary module import. -/
theorem roots (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (result : RootReplay.Result p lower upper) (original : Tower.Model parent ℝ) :
    result.values original = result.roots.map (fun d =>
      d.root original.value original.zero_iff original.one original.add original.sub
        original.mul original.nat original.sign) := rfl

/-- Full coverage and mathematical order are available to ordinary consumers. -/
theorem root_laws (p : DensePoly parent.Value) (lower upper : Endpoint parent.Value)
    (result : RootReplay.Result p lower upper) (original : Tower.Model parent ℝ) :
    (result.values original).Nodup ∧ (result.values original).Pairwise (· < ·) :=
  ⟨(result.coverage original).2, result.ordered original⟩

open Lean Meta in
run_meta do
  for name in #[``constant, ``zero_guard, ``roots, ``root_laws] do
    let .thmInfo info ← getConstInfo name | throwError "expected module consumer theorem"
    let _ ← Hex.RCF.checkProof name info.type info.value
end Hex.RCF.RealCoefficients.FiniteMatrixTests.ModuleCheck
