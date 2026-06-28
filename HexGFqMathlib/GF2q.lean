/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGFqMathlib.Basic
import HexGF2Mathlib.Field
import Mathlib.Algebra.Ring.Equiv

/-!
Mathlib-side correspondence between the optimized binary Conway field and the
generic canonical Conway field.
-/

namespace Hex

namespace GF2q

variable {n : Nat} [h : Conway.PackedGF2Entry n]

instance : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private theorem cast_symm_cast {α β : Type u} (h : α = β) (x : α) :
    cast h.symm (cast h x) = x := by
  cases h
  rfl

private theorem cast_cast_symm {α β : Type u} (h : α = β) (x : β) :
    cast h (cast h.symm x) = x := by
  cases h
  rfl

/-- Transport of multiplication along an equality of executable finite-field
types induced by an equality of moduli. Sound because the field structure is
defined uniformly in the modulus, so after `subst` the two multiplications
coincide by proof irrelevance on the degree/prime/irreducibility witnesses. -/
private theorem finiteField_cast_mul
    {f₁ f₂ : FpPoly 2}
    {pos₁ : 0 < FpPoly.degree f₁} {prime₁ : Hex.Nat.Prime 2}
    {irr₁ : FpPoly.Irreducible f₁}
    {pos₂ : 0 < FpPoly.degree f₂} {prime₂ : Hex.Nat.Prime 2}
    {irr₂ : FpPoly.Irreducible f₂}
    (hf : f₁ = f₂)
    (hty : GFqField.FiniteField f₁ pos₁ prime₁ irr₁ =
      GFqField.FiniteField f₂ pos₂ prime₂ irr₂)
    (x y : GFqField.FiniteField f₁ pos₁ prime₁ irr₁) :
    cast hty (x * y) = cast hty x * cast hty y := by
  subst hf
  rfl

/-- Transport of addition along an equality of executable finite-field types
induced by an equality of moduli (companion to `finiteField_cast_mul`). -/
private theorem finiteField_cast_add
    {f₁ f₂ : FpPoly 2}
    {pos₁ : 0 < FpPoly.degree f₁} {prime₁ : Hex.Nat.Prime 2}
    {irr₁ : FpPoly.Irreducible f₁}
    {pos₂ : 0 < FpPoly.degree f₂} {prime₂ : Hex.Nat.Prime 2}
    {irr₂ : FpPoly.Irreducible f₂}
    (hf : f₁ = f₂)
    (hty : GFqField.FiniteField f₁ pos₁ prime₁ irr₁ =
      GFqField.FiniteField f₂ pos₂ prime₂ irr₂)
    (x y : GFqField.FiniteField f₁ pos₁ prime₁ irr₁) :
    cast hty (x + y) = cast hty x + cast hty y := by
  subst hf
  rfl

/-- The packed bit test `(w >>> i &&& 1) = 0` agrees with the cleared `ofUInt64`
coefficient at position `i` (for `i < 64`). -/
private theorem bit_and_one_eq_zero_iff (w : UInt64) {i : Nat} (hi : i < 64) :
    (w >>> i.toUInt64 &&& 1) = 0 ↔ (Hex.GF2Poly.ofUInt64 w).coeff i = false := by
  rw [Hex.GF2Poly.coeff_ofUInt64_eq_testBit w hi, ← UInt64.toNat_inj]
  have hshift : (i.toUInt64).toNat % 64 = i := by
    have hi64 : (i.toUInt64).toNat = i := by
      simp only [Nat.toUInt64]
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi (by norm_num))
    rw [hi64]; exact Nat.mod_eq_of_lt hi
  simp only [UInt64.toNat_and, UInt64.toNat_shiftRight, hshift]
  rw [show ((1 : UInt64).toNat) = 1 from rfl, show ((0 : UInt64).toNat) = 0 from rfl]
  rw [Nat.testBit, Nat.and_comm (w.toNat >>> i) 1]
  generalize 1 &&& (w.toNat >>> i) = b
  constructor
  · intro hb; simp [hb]
  · intro hb
    by_contra hne
    rw [bne_iff_ne.mpr hne] at hb
    exact absurd hb (by simp)

/-- Coefficients of the packed binary modulus polynomial: the implicit leading
`x^n` term, with lower degrees reading the bits of `lower`. -/
private theorem coeff_packedGF2FpPoly (lower : UInt64) (n i : Nat) :
    (Conway.packedGF2FpPoly lower n).coeff i =
      if i = n then (1 : Hex.ZMod64 2)
      else if i < n then (if (lower >>> i.toUInt64 &&& 1) = 0 then 0 else 1)
      else 0 := by
  unfold Conway.packedGF2FpPoly
  rw [Hex.FpPoly.ofCoeffs, Hex.DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?,
    Array.getElem?_push]
  have hsz : (((List.range n).map fun j =>
      if (lower >>> j.toUInt64 &&& 1) = 0 then (0 : Hex.ZMod64 2) else 1).toArray).size = n := by
    simp
  rw [hsz]
  by_cases hin : i = n
  · simp [hin]
  · rw [if_neg hin, List.getElem?_toArray, List.getElem?_map, if_neg hin]
    by_cases hlt : i < n
    · rw [List.getElem?_range hlt, if_pos hlt]
      simp
    · rw [List.getElem?_eq_none (by simp; omega), if_neg hlt]
      rfl

/-- The packed `GF2n` modulus, transported to `FpPoly 2`, is the Conway
polynomial selected for the same committed packed entry. -/
@[simp, grind =]
theorem modulusFpPoly_eq_conway :
    HexGF2Mathlib.GF2n.modulusFpPoly (n := n) (irr := h.lower) =
      GFq.modulus h.entry := by
  rw [gfq_modulus_eq_packedFpPoly, lower_eq]
  apply Hex.DensePoly.ext_coeff
  intro i
  show (HexGF2Mathlib.GF2Poly.toFpPoly (Hex.GF2Poly.ofUInt64Monic h.lower n)).coeff i =
      (Conway.packedGF2FpPoly h.lower n).coeff i
  have hn64 : n < 64 := h.degree_lt_word
  rw [HexGF2Mathlib.GF2Poly.coeff_toFpPoly,
    Hex.GF2Poly.coeff_ofUInt64Monic h.lower h.degree_lt_word,
    coeff_packedGF2FpPoly]
  by_cases hin : i = n
  · subst hin; simp
  · rw [if_neg hin]
    by_cases hlt : i < n
    · simp only [hin, decide_false, Bool.false_bne, if_pos hlt]
      by_cases hb : (h.lower >>> i.toUInt64 &&& 1) = 0
      · rw [if_pos hb, (bit_and_one_eq_zero_iff h.lower (by omega)).mp hb]
        simp
      · rw [if_neg hb]
        have hc : (Hex.GF2Poly.ofUInt64 h.lower).coeff i = true := by
          by_contra hcf
          exact hb ((bit_and_one_eq_zero_iff h.lower (by omega)).mpr (by simpa using hcf))
        rw [hc]; simp
    · simp [hin, hlt]

/-- The generic finite-field target of the packed correspondence is
definitionally the same field type as `GFq 2 n` after identifying the
transported packed modulus with the Conway modulus. -/
private theorem genericField_eq_conway :
    HexGF2Mathlib.GF2n.GenericFiniteField
      (n := n) (irr := h.lower)
      (hn := h.degree_pos) (hn64 := h.degree_lt_word) (hirr := h.packed_irreducible) =
      GFq 2 n h.entry := by
  have hmod : HexGF2Mathlib.GF2n.modulusFpPoly (n := n) (irr := h.lower) =
      Conway.conwayPoly 2 n h.entry := modulusFpPoly_eq_conway
  show GFqField.FiniteField (HexGF2Mathlib.GF2n.modulusFpPoly (n := n) (irr := h.lower)) _ _ _ =
      GFqField.FiniteField (Conway.conwayPoly 2 n h.entry) _ _ _
  congr 1

/-- Reindex the generic finite-field target of the packed `GF2n` correspondence
to the canonical Conway-field target used by `GFq 2 n`. -/
private def genericEquivGFq :
    RingEquiv
      (HexGF2Mathlib.GF2n.GenericFiniteField
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word) (hirr := h.packed_irreducible))
      (GFq 2 n h.entry) where
  toFun x := cast (genericField_eq_conway (n := n)) x
  invFun x := cast (genericField_eq_conway (n := n)).symm x
  left_inv := by
    intro x
    exact cast_symm_cast (genericField_eq_conway (n := n)) x
  right_inv := by
    intro x
    exact cast_cast_symm (genericField_eq_conway (n := n)) x
  map_mul' := by
    intro x y
    exact finiteField_cast_mul modulusFpPoly_eq_conway (genericField_eq_conway (n := n)) x y
  map_add' := by
    intro x y
    exact finiteField_cast_add modulusFpPoly_eq_conway (genericField_eq_conway (n := n)) x y

set_option maxHeartbeats 800000

/-- The packed-side equivalence `HexGF2Mathlib.GF2n.equiv`, repackaged with its
domain stated as `GF2q n`. This is the project-local `HexGF2Mathlib.RingEquiv`;
naming it avoids re-elaborating its `whnf`-heavy type inline. -/
private def packedRingEquiv :
    HexGF2Mathlib.RingEquiv
      (GF2n n h.lower h.degree_pos h.degree_lt_word h.packed_irreducible)
      (HexGF2Mathlib.GF2n.GenericFiniteField (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word) (hirr := h.packed_irreducible)) :=
  HexGF2Mathlib.GF2n.equiv
    (n := n) (irr := h.lower)
    (hn := h.degree_pos) (hn64 := h.degree_lt_word)
    (hirr := h.packed_irreducible)

/-- The optimized packed binary Conway field is ring-equivalent to the generic
canonical Conway field over `p = 2`. The packed-side equivalence is the
project-local `HexGF2Mathlib.RingEquiv`, which this composition repackages with
the canonical Conway field on the generic side through `genericEquivGFq`. -/
def equivGFq : RingEquiv (GF2q n) (GFq 2 n h.entry) where
  toFun x := genericEquivGFq (n := n) (packedRingEquiv (n := n) x)
  invFun x := (packedRingEquiv (n := n)).invFun ((genericEquivGFq (n := n)).symm x)
  left_inv x := by
    show (packedRingEquiv (n := n)).invFun
        ((genericEquivGFq (n := n)).symm
          (genericEquivGFq (n := n) (packedRingEquiv (n := n) x))) = x
    rw [RingEquiv.symm_apply_apply]
    exact (packedRingEquiv (n := n)).left_inv x
  right_inv x := by
    show genericEquivGFq (n := n)
        (packedRingEquiv (n := n)
          ((packedRingEquiv (n := n)).invFun ((genericEquivGFq (n := n)).symm x))) = x
    rw [(packedRingEquiv (n := n)).right_inv, RingEquiv.apply_symm_apply]
  map_mul' x y := by
    show genericEquivGFq (n := n) (packedRingEquiv (n := n) (x * y)) =
      genericEquivGFq (n := n) (packedRingEquiv (n := n) x) *
        genericEquivGFq (n := n) (packedRingEquiv (n := n) y)
    rw [(packedRingEquiv (n := n)).map_mul' x y, map_mul (genericEquivGFq (n := n))]
  map_add' x y := by
    show genericEquivGFq (n := n) (packedRingEquiv (n := n) (x + y)) =
      genericEquivGFq (n := n) (packedRingEquiv (n := n) x) +
        genericEquivGFq (n := n) (packedRingEquiv (n := n) y)
    rw [(packedRingEquiv (n := n)).map_add' x y, map_add (genericEquivGFq (n := n))]

end GF2q

end Hex
