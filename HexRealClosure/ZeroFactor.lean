/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.Interpret

public section

namespace Hex.RealClosure.ZeroFactor

variable {E : Type u} [Zero E] [DecidableEq E]

/-- The number of literal zero coefficients preceding the first nonzero one. -/
@[expose] def order (p : DensePoly E) : Nat := p.coeffs.findIdx (fun a => a != 0)

/-- Remove the complete power of `X` using one coefficient scan and a slice.
No coefficient arithmetic or selected-root query is performed. Zero remains
`(0, 0)`; the complete roots API must retain its separate `all` case. -/
@[expose] def remove (p : DensePoly E) : DensePoly E × Nat :=
  let k := order p
  (DensePoly.ofCoeffs (p.coeffs.extract k p.size), k)

theorem remove_zero : remove (0 : DensePoly E) = (0, 0) := by
  simp [remove, order, DensePoly.size,
    show (0 : DensePoly E).coeffs = #[] from rfl]

/-- The quotient copies the input coefficients at the extracted offset. -/
theorem remove_coeff (p : DensePoly E) (i : Nat) :
    (remove p).1.coeff i = p.coeff (order p + i) := by
  dsimp only [remove]
  rw [DensePoly.coeff_ofCoeffs]
  simp only [DensePoly.coeff, DensePoly.size, Array.getD_eq_getD_getElem?,
    Array.getElem?_extract, Nat.min_self]
  split
  · rfl
  · rename_i h
    have hn : ¬ order p + i < p.coeffs.size := by omega
    rw [Array.getElem?_eq_none (Nat.not_lt.mp hn)]

/-- Every coefficient before the extracted offset is literally zero. -/
theorem coeff_zero (p : DensePoly E) (i : Nat) (hi : i < order p) : p.coeff i = 0 := by
  have h := Array.not_of_lt_findIdx (xs := p.coeffs) (p := fun a => a != 0) hi
  have hb : i < p.coeffs.size := Nat.lt_of_lt_of_le hi Array.findIdx_le_size
  simpa only [bne_eq_false_iff_eq, DensePoly.coeff, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hb, Option.getD_some] using h

end Hex.RealClosure.ZeroFactor
