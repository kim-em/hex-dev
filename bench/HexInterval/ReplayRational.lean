/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.ReplayRationalDirect
public import HexInterval.ReplayRationalChecked

public section

/-! Ordinary-kernel replay canaries for both Mathlib-free rational encodings. -/

namespace Hex.Interval.Experiment.Rational

theorem directAdd : Rat.divInt 1 3 + Rat.divInt 1 6 = Rat.divInt 1 2 := by
  rw [← add_eq]
  decide +kernel

theorem directSub : Rat.divInt 5 6 - Rat.divInt 1 3 = Rat.divInt 1 2 := by
  rw [← sub_eq]
  decide +kernel

theorem directMul : Rat.divInt 2 3 * Rat.divInt 9 10 = Rat.divInt 3 5 := by
  rw [← mul_eq]
  decide +kernel

theorem directInv : (Rat.divInt (-2) 3)⁻¹ = Rat.divInt (-3) 2 := by
  rw [← inv_eq]
  decide +kernel

theorem checkedAdd :
    Raw.value ⟨1, 3⟩ + Raw.value ⟨1, 6⟩ = Raw.value ⟨1, 2⟩ :=
  Raw.add_sound (by decide +kernel)

theorem checkedSub :
    Raw.value ⟨5, 6⟩ - Raw.value ⟨1, 3⟩ = Raw.value ⟨1, 2⟩ :=
  Raw.sub_sound (by decide +kernel)

theorem checkedMul :
    Raw.value ⟨2, 3⟩ * Raw.value ⟨9, 10⟩ = Raw.value ⟨3, 5⟩ :=
  Raw.mul_sound (by decide +kernel)

theorem checkedInv : (Raw.value ⟨-2, 3⟩)⁻¹ = Raw.value ⟨-3, 2⟩ :=
  Raw.inv_sound (by decide +kernel)

theorem checkedInvZero : (Raw.value ⟨0, 7⟩)⁻¹ = Raw.value ⟨0, 1⟩ :=
  Raw.inv_sound (by decide +kernel)

end Hex.Interval.Experiment.Rational
