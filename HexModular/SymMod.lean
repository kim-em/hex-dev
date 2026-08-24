/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith

public section

/-!
Symmetric integer representatives for `hex-modular`.
-/
namespace Hex

namespace Modular

/-- The representative of `a` modulo `m` in the interval `(-m/2, m/2]`.
For the degenerate modulus zero, this returns `a`, matching `Int.emod`'s
zero-modulus convention. -/
@[expose]
def symMod (a : Int) (m : Nat) : Int :=
  if m = 0 then
    a
  else
    let r := a % (m : Int)
    if (m : Int) < 2 * r then r - m else r

#guard symMod 3 6 == 3
#guard symMod (-3) 6 == 3
#guard symMod 4 6 == -2

/-- Symmetric reduction preserves the ordinary nonnegative residue at every
positive modulus. -/
theorem symMod_emod {a : Int} {m : Nat} (h : 0 < m) :
    (symMod a m) % (m : Int) = a % (m : Int) := by
  unfold symMod
  rw [if_neg (Nat.ne_of_gt h)]
  simp only
  split
  · rw [Int.sub_emod, Int.emod_self, Int.sub_zero]
    simp only [Int.emod_emod]
  · exact Int.emod_emod _ _

/-- A symmetric representative has absolute value at most half its positive
modulus, with the positive representative selected at an even tie. -/
theorem symMod_le {a : Int} {m : Nat} (h : 0 < m) :
    2 * (symMod a m).natAbs ≤ m := by
  have hm : (0 : Int) < (m : Int) := by omega
  have hr0 : (0 : Int) ≤ a % (m : Int) :=
    Int.emod_nonneg _ (by omega)
  have hrm : a % (m : Int) < (m : Int) :=
    Int.emod_lt_of_pos _ hm
  unfold symMod
  rw [if_neg (Nat.ne_of_gt h)]
  simp only
  split
  · rename_i hlarge
    apply Int.ofNat_le.mp
    rw [Int.natCast_mul, Int.ofNat_natAbs_of_nonpos (by omega)]
    omega
  · rename_i hsmall
    apply Int.ofNat_le.mp
    rw [Int.natCast_mul, Int.ofNat_natAbs_of_nonneg hr0]
    omega

/-- A strictly-half-bounded integer congruent to `a` is the unique symmetric
representative. The strict bound excludes the two representatives at an even
tie. -/
theorem symMod_unique {a x : Int} {m : Nat}
    (h : 2 * x.natAbs < m)
    (hx : x % (m : Int) = a % (m : Int)) :
    symMod a m = x := by
  have hm : 0 < m := by omega
  let s := symMod a m
  have hs : 2 * s.natAbs ≤ m := symMod_le hm
  have hsum : s.natAbs + x.natAbs < m := by omega
  have hdiff : (s - x).natAbs < m :=
    Nat.lt_of_le_of_lt (Int.natAbs_sub_le s x) hsum
  have hsx : s % (m : Int) = x % (m : Int) := by
    exact (symMod_emod hm).trans hx.symm
  have hdvd : (m : Int) ∣ s - x :=
    Int.dvd_of_emod_eq_zero
      (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hsx)
  have hzero : s - x = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    simpa using hdiff
  dsimp only [s] at hzero ⊢
  omega

end Modular

end Hex
