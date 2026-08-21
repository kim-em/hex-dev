/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk11

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe

/-- The complete bounded checker state through the pinned PNT+ cutoff. -/
theorem fullState : checkState 11723 = (118671, true) := Chunk11.state

/-- Package-owned natural-number form of the medium-range Chebyshev bound. -/
theorem psi_nat (n : Nat) (hn : n ≤ 11723) :
    Chebyshev.psi (n : Real) ≤ (111 / 100 : Real) * n :=
  psi_nat_of_state fullState n hn

/-- Exact statement of PNT+'s `Chebyshev.psi_num_2`, after the localized
replacement of its LeanCert checker by the package-owned bounded replay. -/
theorem psi_num_2 (x : Real) (hx : x > 0) (hx2 : x ≤ 11723) :
    Chebyshev.psi x ≤ 1.11 * x := by
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  have hnn : (0 : Real) ≤ x := hx.le
  have hfloor_le : ⌊x⌋₊ ≤ 11723 := Nat.floor_le_of_le hx2
  rcases Nat.eq_zero_or_pos ⌊x⌋₊ with hf | hf
  · simp only [hf, Nat.cast_zero]
    rw [Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (0 : Real) < 2)]
    linarith
  · calc
      Chebyshev.psi (⌊x⌋₊ : Real) ≤ (111 / 100 : Real) * ⌊x⌋₊ :=
        psi_nat ⌊x⌋₊ hfloor_le
      _ ≤ (111 / 100 : Real) * x := by
        gcongr
        exact Nat.floor_le hnn
      _ = 1.11 * x := by norm_num

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe

end
