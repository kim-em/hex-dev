/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Tactic
public meta import HexRCF.Tactic

public section

namespace Hex.RCF.ProofExamples

theorem quadratic : ∀ x : ℝ, x ^ 2 + 1 > 0 := by rcf
theorem witness : ∃ x : ℝ, x ^ 2 = 2 := by rcf

/-- A supplied literal certificate exercises ordinary checker replay. -/
def input : Sentence :=
  .forallReal (.atom ⟨Hex.DensePoly.ofCoeffs #[(1 : Int), 0, 1], .gt⟩)

def certificate : Certificate :=
  .noRoots {
    carrier := {
      carrier := Hex.DensePoly.ofCoeffs #[1, 0, 1]
      repeated := Hex.DensePoly.ofCoeffs #[1]
      derivPart := Hex.DensePoly.ofCoeffs #[0, 2]
      factorScale := 1
      derivScale := 1
      replay := {
        chain := #[Hex.DensePoly.ofCoeffs #[1, 0, 1],
          Hex.DensePoly.ofCoeffs #[0, 1], Hex.DensePoly.ofCoeffs #[-1]]
        derivScale := 2
        steps := #[{ leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 1 }] } }
    isolations := { intervals := #[] } }

theorem literal : input.toProp :=
  check_sound input certificate (by decide +kernel)

/-- info: 'Hex.RCF.ProofExamples.literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal

/-- info: 'Hex.RCF.ProofExamples.quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadratic

end Hex.RCF.ProofExamples
