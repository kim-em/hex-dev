/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.RingTheory.HahnSeries.Lex
public import Mathlib.RingTheory.HahnSeries.Summable

/-!
Coefficient embeddings of ordered Hahn fields preserve support, leading
coefficients, order and constant embeddings.
-/

@[expose] public section

noncomputable section

namespace Hex.OrderedFn.Hahn

variable {K L : Type*} [Field K] [Field L]

/-- Apply a coefficient embedding to an ordered Hahn series. -/
def mapHom (ι : K →+* L) : Lex (HahnSeries ℤ K) →+* Lex (HahnSeries ℤ L) where
  toFun x := toLex ((ofLex x).map ι)
  map_zero' := congrArg toLex (HahnSeries.map_zero ι.toZeroHom)
  map_one' := congrArg toLex (HahnSeries.map_one ι.toMonoidWithZeroHom)
  map_add' _ _ := congrArg toLex (HahnSeries.map_add ι.toAddMonoidHom)
  map_mul' _ _ := congrArg toLex (HahnSeries.map_mul ι.toNonUnitalRingHom)

/-- An injective coefficient homomorphism preserves support. -/
theorem map_support (ι : K →+* L) (x : HahnSeries ℤ K) :
    (x.map ι).support = x.support := by
  ext i
  simp

/-- Coefficient embeddings preserve the lowest exponent, including at zero. -/
theorem map_orderTop (ι : K →+* L) (x : HahnSeries ℤ K) :
    (x.map ι).orderTop = x.orderTop := by
  apply le_antisymm
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro j hj
    have h := HahnSeries.coeff_eq_zero_of_lt_orderTop hj
    simpa using h
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro j hj
    simpa using congrArg ι (HahnSeries.coeff_eq_zero_of_lt_orderTop hj)

/-- The leading coefficient maps by the coefficient embedding. -/
theorem map_leadingCoeff (ι : K →+* L) (x : HahnSeries ℤ K) :
    (x.map ι).leadingCoeff = ι x.leadingCoeff := by
  by_cases hx : x = 0
  · subst x
    simp only [HahnSeries.leadingCoeff_zero, map_zero]
    have h : (0 : HahnSeries ℤ K).map ι = 0 := HahnSeries.map_zero ι.toZeroHom
    rw [h, HahnSeries.leadingCoeff_zero]
  have hm : x.map ι ≠ 0 := by
    rw [← HahnSeries.orderTop_ne_top, map_orderTop, HahnSeries.orderTop_ne_top]
    exact hx
  rw [HahnSeries.leadingCoeff_of_ne_zero hm, HahnSeries.leadingCoeff_of_ne_zero hx,
    HahnSeries.map_coeff]
  congr 2
  apply WithTop.coe_injective
  simpa only [WithTop.coe_untop] using map_orderTop ι x

variable [LinearOrder K] [LinearOrder L]

/-- A strictly monotone coefficient embedding preserves and reflects Hahn order. -/
theorem map_lt (ι : K →+* L) (hι : StrictMono ι) (x y : Lex (HahnSeries ℤ K)) :
    mapHom ι x < mapHom ι y ↔ x < y := by
  simp only [HahnSeries.lt_iff]
  constructor
  · rintro ⟨i, h, hi⟩
    exact ⟨i, fun j hj => ι.injective (h j hj), hι.lt_iff_lt.mp hi⟩
  · rintro ⟨i, h, hi⟩
    exact ⟨i, fun j hj => congrArg ι (h j hj), hι hi⟩

/-- Nonstrict Hahn order is also preserved and reflected. -/
theorem map_le (ι : K →+* L) (hι : StrictMono ι) (x y : Lex (HahnSeries ℤ K)) :
    mapHom ι x ≤ mapHom ι y ↔ x ≤ y := by
  simp only [le_iff_lt_or_eq, map_lt ι hι, (mapHom ι).injective.eq_iff]

omit [LinearOrder K] [LinearOrder L] in
/-- Coefficient extension commutes with the embedding of constants. -/
theorem map_C (ι : K →+* L) (a : K) :
    mapHom ι (toLex (HahnSeries.single 0 a)) = toLex (HahnSeries.single 0 (ι a)) :=
  congrArg toLex (HahnSeries.map_single ι.toZeroHom)

end Hex.OrderedFn.Hahn
