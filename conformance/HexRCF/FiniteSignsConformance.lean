/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.FiniteSigns
import HexRCF.SelectedRoot.KernelCheck
open Hex
namespace Hex.RCF.RealCoefficients.FiniteSignsTests
private def atom (cmp : RealFormula.Cmp) : RealFormula.QF 1 := .atom ⟨MvPoly.X 0, cmp⟩
/-- All comparisons retain their strict and nonstrict boundary behavior. -/
theorem comparisons :
    [RealFormula.Cmp.eq, .ne, .lt, .le, .gt, .ge].map (fun cmp =>
      [-1, 0, 1].map (fun sign => FiniteSigns.Row.check [] (atom cmp) [sign])) =
    [[.ok false, .ok true, .ok false], [.ok true, .ok false, .ok true],
     [.ok true, .ok false, .ok false], [.ok true, .ok true, .ok false],
     [.ok false, .ok false, .ok true], [.ok false, .ok true, .ok true]] := by decide +kernel

/-- Missing right-side atoms reject even when a left disjunct is true. -/
theorem strict_or : FiniteSigns.Row.check [] (.or .tt (atom .gt)) [] = .error .binding := by
  decide +kernel

theorem strict_and : FiniteSigns.Row.check [] (.and .ff (atom .gt)) [] = .error .binding := by
  decide +kernel

/-- Extra signs reject as well as missing signs. -/
theorem extra_atom : FiniteSigns.Row.check [] (atom .gt) [1, 1] = .error .binding := by
  decide +kernel

/-- Guard validation precedes missing atoms and constant formulas. -/
theorem guard_before_row : FiniteSigns.Row.check [1, 0] (atom .gt) [] = .error .divisor := by
  decide +kernel

theorem guard_before_constant : FiniteSigns.Row.check [0] (.tt : RealFormula.QF 1) [] =
    .error .divisor := by decide +kernel

theorem negative_guard : FiniteSigns.Row.check [-1] (atom .eq) [0] = .ok true := by
  decide +kernel

theorem false_point : FiniteSigns.Row.check [1] (.not (atom .eq)) [0] = .ok false := by
  decide +kernel

open Lean Meta in
run_meta do
  for name in #[``comparisons, ``strict_or, ``strict_and, ``extra_atom,
      ``guard_before_row, ``guard_before_constant, ``negative_guard, ``false_point] do
    let .thmInfo info ← getConstInfo name | throwError "expected refusal/control theorem"
    let proof ← mkDecideProof info.type
    Hex.RCF.SelectedRootTests.KernelCheck.addChecked (Name.str name "kernel") info.type proof
    let axioms ← collectAxioms name
    unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected control axiom"
end Hex.RCF.RealCoefficients.FiniteSignsTests
