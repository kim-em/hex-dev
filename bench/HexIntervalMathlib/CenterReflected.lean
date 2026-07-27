/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.Center

public section

/-! Ordinary-kernel replay of a local centered-product certificate. -/

namespace Hex.Interval.Experiment.Center

theorem centerReflected (valuation : Valuation)
    (hprogram : extendedProgram.Holds valuation)
    (hsource : 0 ≤ valuation (node 0) ∧ valuation (node 0) ≤ 1) :
    0 ≤ valuation (node 0) * (1 - valuation (node 0)) ∧
      valuation (node 0) * (1 - valuation (node 0)) ≤ (1 / 4 : ℝ) := by
  let certificate : Certificate :=
    { program := extendedProgram
      center := centerWitness
      edges := [centerEdge]
      facts :=
        [ ⟨⟨node 0, unitRange⟩, .source 0⟩
        , ⟨Row.lit (node 1) 1, .lit⟩
        , ⟨⟨node 2, unitRange⟩, .sub 1 0⟩
        , ⟨⟨node 3, unitRange⟩, .mul 0 2⟩
        , ⟨Row.lit (node 4) half, .lit⟩
        , ⟨⟨node 5, centeredRange⟩, .sub 0 4⟩
        , ⟨⟨node 6, quarterRange⟩, .sq 5⟩
        , ⟨Row.lit (node 7) quarter, .lit⟩
        , ⟨⟨node 8, quarterRange⟩, .sub 7 6⟩
        , ⟨⟨node 3, quarterRange⟩, .transport 0 8⟩ ]
      result := 9 }
  have hchecked : certificate.check fixtureLimit fixtureStructureLimit
      baseProgram.length fixtureSources fixtureTarget = true := by
    decide +kernel
  have hsources : RowsHold valuation fixtureSources :=
    RowsHold.iff_forall.mpr (by
      intro row hmem
      simp only [fixtureSources, List.mem_singleton] at hmem
      subst row
      simpa only [unitRange, Row.holds_closed_iff, dyadic_zero, dyadic_one] using hsource)
  have htarget : fixtureTarget.Holds valuation :=
    Certificate.sound hchecked hprogram hsources
  have hnodeBound :
      0 ≤ valuation (node 3) ∧ valuation (node 3) ≤ (1 / 4 : ℝ) := by
    simpa only [fixtureTarget, quarterRange, Row.holds_closed_iff, dyadic_zero,
      dyadic_quarter] using htarget
  rw [← fixture_product_eq hprogram]
  exact hnodeBound

/-- info: 'Hex.Interval.Experiment.Center.centerReflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms centerReflected

-- The sweep harness parses this unguarded copy from Lake's captured output.
#print axioms centerReflected

end Hex.Interval.Experiment.Center
