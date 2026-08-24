/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ.ExactDivision

public section
set_option backward.proofsInPublic true

/-!
Decidable divisibility for integer dense polynomials, backed by the shared
checked exact-division primitive in `hex-poly-z`.
-/

namespace Hex.ZPoly

/-- A polynomial is divisible by zero exactly when it is zero. -/
theorem zero_dvd_iff (f : ZPoly) : (0 : ZPoly) ∣ f ↔ f = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    grind
  · intro hf
    subst f
    exact ⟨0, by grind⟩

/-- Integer-polynomial divisibility is decided by checked exact division.
The zero-divisor case is handled separately so `0 ∣ 0` remains true even
though `divExact? f 0` deliberately returns `none`. -/
instance (f g : ZPoly) : Decidable (g ∣ f) :=
  if hg : g = 0 then
    if hf : f = 0 then
      isTrue (by subst g; exact (zero_dvd_iff f).2 hf)
    else
      isFalse (by subst g; exact fun h => hf ((zero_dvd_iff f).1 h))
  else
    match hq : divExact? f g with
    | some q =>
        isTrue ⟨q, by
          rw [DensePoly.mul_comm_poly]
          exact (divExact?_product hq).symm⟩
    | none =>
        isFalse fun hd => by
          have hsome := divExact?_isSome_of_dvd hg hd
          rw [hq] at hsome
          contradiction

end Hex.ZPoly
