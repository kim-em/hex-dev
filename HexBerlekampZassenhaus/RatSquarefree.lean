/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.FactorizationData
public meta import HexBerlekampZassenhaus.FactorizationData
import all HexPolyZ.Rational

public section

namespace Hex.ZPoly

/-- Exact squarefreeness over the rational base field, excluding zero. -/
@[expose]
def ratSquarefree (p : DensePoly Rat) : Bool :=
  !p.isZero && (DensePoly.gcd p (DensePoly.derivative p)).size ≤ 1

/-- Try the verified modular certificate on the integer primitive part before
running the exact rational gcd. Bad reduction is inconclusive and retains the
exact fallback, including primes dividing the leading coefficient. -/
@[expose]
def ratSquarefreeFast (p : DensePoly Rat) : Bool :=
  !p.isZero &&
    (modularSquareFreeCoreFires (ZPoly.ratPolyPrimitivePart p) ||
      (DensePoly.gcd p (DensePoly.derivative p)).size ≤ 1)

/-- The modular trial changes only the compiled computation, preserving the
exact gcd-based predicate used by the correspondence proofs. -/
@[csimp]
theorem ratSquarefree_eq_fast : ratSquarefree = ratSquarefreeFast := by
  funext p
  by_cases hpzero : p.isZero = true
  · simp [ratSquarefree, ratSquarefreeFast, hpzero]
  · have hp : p ≠ 0 := by
      intro h
      apply hpzero
      rw [h]
      rfl
    by_cases hmod : modularSquareFreeCoreFires (ZPoly.ratPolyPrimitivePart p) = true
    · have hparts := hmod
      simp only [modularSquareFreeCoreFires, Bool.and_eq_true,
        Bool.not_eq_true', bne_iff_ne] at hparts
      have hsq := ZPoly.squareFreeRat_of_separableModP _ 499
        prime_499 hparts.1.2 hparts.2
      obtain ⟨u, hu⟩ := ZPoly.ratPolyPrimitivePart_rational_associate p
      have hune : u ≠ 0 := by
        intro h
        apply hp
        rw [hu, h]
        exact DensePoly.scale_zero_left_semiring _
      have hqne : ZPoly.toRatPoly (ZPoly.ratPolyPrimitivePart p) ≠ 0 := by
        intro h
        apply hp
        rw [hu, h]
        exact DensePoly.scale_zero_right _
      have hassoc : ZPoly.toRatPoly (ZPoly.ratPolyPrimitivePart p) =
          DensePoly.scale u⁻¹ p := by
        conv => rhs; rw [hu]
        rw [DensePoly.scale_scale, Rat.inv_mul_cancel u hune]
        exact (ZPoly.rat_scale_one _).symm
      have hcheck := ZPoly.rat_squareFree_of_rational_associate
        (by
          intro h
          have hc := Rat.inv_mul_cancel u hune
          rw [h, Rat.zero_mul] at hc
          exact (by decide : (0 : Rat) ≠ 1) hc) hqne hassoc hsq
      simp [ratSquarefree, ratSquarefreeFast, hmod, hcheck]
    · simp [ratSquarefree, ratSquarefreeFast, hmod]

/-! The trial is sufficient, not necessary: both kinds of bad reduction
below must take the exact fallback and still accept the squarefree input. -/

#guard
  let badDiscriminant : DensePoly Rat := DensePoly.ofList [-499, 0, 1]
  let badLeading : DensePoly Rat := DensePoly.ofList [1, 499]
  #[badDiscriminant, badLeading].all fun p =>
    !modularSquareFreeCoreFires (ZPoly.ratPolyPrimitivePart p) &&
      ratSquarefreeFast p

#guard
  let rational : DensePoly Rat := DensePoly.ofList [-2 / 3, 0, 1 / 3]
  modularSquareFreeCoreFires (ZPoly.ratPolyPrimitivePart rational) &&
    ratSquarefreeFast rational &&
    !ratSquarefreeFast (rational * rational) &&
    !ratSquarefreeFast 0 && ratSquarefreeFast 1

end Hex.ZPoly
