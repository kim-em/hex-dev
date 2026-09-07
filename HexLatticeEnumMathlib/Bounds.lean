/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Bounds
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

/-- An integer square can be compared with a rational bound using an integer square root. -/
theorem integer_square (x a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    (x : Rat) * x ≤ (a : Rat) / b ↔ x.natAbs ≤ Nat.sqrt (a / b).toNat := by
  have hbq : (0 : Rat) < b := by exact_mod_cast hb
  have hquot : 0 ≤ a / b := Int.ediv_nonneg ha (Int.le_of_lt hb)
  rw [le_div_iff₀ hbq, Nat.le_sqrt]
  have hcast : (x : Rat) * x * b ≤ a ↔ x * x * b ≤ a := by norm_cast
  rw [hcast, ← Int.le_ediv_iff_mul_le hb]
  have hsq : ((x.natAbs * x.natAbs : Nat) : Int) = x * x := Int.natAbs_mul_self
  omega

/-- Mathematical floor and ceiling division give exactly the cleared-denominator interval. -/
theorem interval_iff (u v t z : Int) (hv : 0 < v) :
    (-((-(u - t)) / v) ≤ z ∧ z ≤ (u + t) / v) ↔ |v * z - u| ≤ t := by
  rw [abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' : -z ≤ -(u - t) / v := by omega
    have hl := (Int.le_ediv_iff_mul_le hv).mp hlo'
    have hh := (Int.le_ediv_iff_mul_le hv).mp hhi
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    have hl : (-z) * v ≤ -(u - t) := by nlinarith
    have hh : z * v ≤ u + t := by nlinarith
    have hl' := (Int.le_ediv_iff_mul_le hv).mpr hl
    exact ⟨by omega, (Int.le_ediv_iff_mul_le hv).mpr hh⟩

/-- Exact integer bounds include precisely the coefficients satisfying the quadratic bound. -/
theorem bounds_iff (c d r : Rat) (z : Int) (hd : 0 < d) :
    (bounds c d r).lo ≤ z ∧ z ≤ (bounds c d r).hi ↔
      d * ((z : Rat) - c) ^ 2 ≤ r := by
  by_cases hr : r < 0
  · simp only [bounds, ite_eq_left (Or.inr hr)]
    constructor
    · intro h; omega
    · intro h
      have := mul_nonneg (le_of_lt hd) (sq_nonneg ((z : Rat) - c))
      linarith
  · have hr' : 0 ≤ r := le_of_not_gt hr
    have hv : (0 : Int) < c.den := by exact_mod_cast c.den_pos
    have hb : (0 : Int) < (r / d).den := by exact_mod_cast (r / d).den_pos
    have hq : 0 ≤ (r / d).num := Rat.num_nonneg.mpr (div_nonneg hr' (le_of_lt hd))
    have ha : 0 ≤ (r / d).num * (c.den : Int) * c.den := by positivity
    simp only [bounds, ite_eq_right (not_or.mpr ⟨not_le.mpr hd, hr⟩)]
    rw [interval_iff _ _ _ _ hv]
    have habs : |(c.den : Int) * z - c.num| =
        (((c.den : Int) * z - c.num).natAbs : Int) := Int.natCast_natAbs _ |>.symm
    rw [habs, Int.ofNat_le]
    rw [← integer_square _ _ _ ha hb]
    push_cast
    have hvq : (0 : Rat) < c.den := by exact_mod_cast c.den_pos
    have hc : (c.num : Rat) = c * c.den := (div_eq_iff (ne_of_gt hvq)).mp c.num_div_den
    have hbq : (0 : Rat) < (r / d).den := by exact_mod_cast (r / d).den_pos
    have hqr : ((r / d).num : Rat) = (r / d) * (r / d).den :=
      (div_eq_iff (ne_of_gt hbq)).mp (r / d).num_div_den
    rw [hc, hqr]
    have heq : (r / d) * ((r / d).den : Rat) * c.den * c.den / (r / d).den =
        (r / d) * (c.den : Rat) ^ 2 := by field_simp
    rw [heq]
    have hleft : ((c.den : Rat) * z - c * c.den) * (c.den * z - c * c.den) =
        ((z : Rat) - c) ^ 2 * (c.den : Rat) ^ 2 := by ring
    rw [hleft, mul_le_mul_iff_left₀ (sq_pos_of_pos hvq), le_div_iff₀ hd]
    rw [mul_comm]

end HexLatticeEnumMathlib
