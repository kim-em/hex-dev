/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHensel.WordStep

public section

/-!
The polynomial reduction map `toWP : ZPoly → DensePoly (WordMod ctx)` (reduce every
coefficient into the residue ring) and its readback `ofWP`, together with the ring
homomorphism laws modulo the working modulus `M := m.toNat`.

`toWP` commutes with `+`, `-`, `*`, `0`, `1`; it kills the canonical reduction
(`reduceModPow _ _ 2`); and `ofWP ∘ toWP` is that canonical reduction. These are
the transport laws that carry the executable bignum Hensel step, coefficient by
coefficient, into `WordMod` arithmetic.
-/

namespace Hex
namespace ZPoly

open Hex.DensePoly

variable {m : UInt64} (ctx : _root_.MontCtx m)

/-- Reduce an integer polynomial coefficientwise into `WordMod ctx`. -/
def toWP (x : ZPoly) : DensePoly (WordMod ctx) :=
  DensePoly.ofCoeffs (x.toArray.map (fun c => WordMod.ofNat (ZPoly.intModNat c m.toNat)))

/-- Read the canonical `[0, M)` residues of a `WordMod` polynomial back into `ZPoly`. -/
def ofWP (p : DensePoly (WordMod ctx)) : ZPoly :=
  DensePoly.ofCoeffs (p.toArray.map (fun w => (Int.ofNat w.toNat : Int)))

@[simp] theorem coeff_toWP (x : ZPoly) (j : Nat) :
    (toWP ctx x).coeff j = WordMod.ofNat (ctx := ctx) (ZPoly.intModNat (x.coeff j) m.toNat) := by
  have h0 : WordMod.ofNat (ctx := ctx) (ZPoly.intModNat 0 m.toNat) = 0 := by
    have : ZPoly.intModNat 0 m.toNat = 0 := by simp [ZPoly.intModNat]
    rw [this]; rfl
  rw [toWP, DensePoly.coeff_ofCoeffs]
  show (x.toArray.map (fun c => WordMod.ofNat (ctx := ctx) (ZPoly.intModNat c m.toNat))).getD j 0
    = WordMod.ofNat (ctx := ctx) (ZPoly.intModNat (x.coeff j) m.toNat)
  rw [show x.coeff j = x.toArray.getD j 0 from rfl]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases x.toArray[j]? with
  | none => simpa using h0.symm
  | some v => simp

@[simp] theorem coeff_ofWP (p : DensePoly (WordMod ctx)) (j : Nat) :
    (ofWP ctx p).coeff j = Int.ofNat (p.coeff j).toNat := by
  rw [ofWP, DensePoly.coeff_ofCoeffs]
  show (p.toArray.map (fun w => (Int.ofNat w.toNat : Int))).getD j 0 = Int.ofNat (p.coeff j).toNat
  rw [show p.coeff j = p.toArray.getD j 0 from rfl]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases p.toArray[j]? with
  | none => simp [WordMod.toNat_zero]
  | some w => simp

/-- `toWP` is well-defined on congruence classes modulo `M`. -/
theorem toWP_congr {x y : ZPoly} (h : ZPoly.congr x y m.toNat) : toWP ctx x = toWP ctx y := by
  apply DensePoly.ext_coeff
  intro j
  rw [coeff_toWP, coeff_toWP]
  apply WordMod.toNat_injective
  rw [WordMod.toNat_ofNat, WordMod.toNat_ofNat]
  have hc : (x.coeff j - y.coeff j) % (m.toNat : Int) = 0 := h j
  have hxy : x.coeff j % (m.toNat : Int) = y.coeff j % (m.toNat : Int) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hc
  have : ZPoly.intModNat (x.coeff j) m.toNat = ZPoly.intModNat (y.coeff j) m.toNat := by
    simp [ZPoly.intModNat, hxy]
  rw [this]

@[simp] theorem toWP_zero : toWP ctx 0 = 0 := by
  apply DensePoly.ext_coeff
  intro j
  rw [coeff_toWP]
  have : ZPoly.intModNat ((0 : ZPoly).coeff j) m.toNat = 0 := by
    rw [DensePoly.coeff_zero]; simp [ZPoly.intModNat]
  rw [this, DensePoly.coeff_zero]; rfl

theorem toWP_add (x y : ZPoly) : toWP ctx (x + y) = toWP ctx x + toWP ctx y := by
  apply DensePoly.ext_coeff
  intro j
  have hz : (0 : WordMod ctx) + 0 = 0 := by rw [WordMod.eq_iff_toNat]; simp
  rw [DensePoly.coeff_add _ _ j hz, coeff_toWP, coeff_toWP, coeff_toWP]
  apply WordMod.toNat_injective
  rw [WordMod.toNat_add, WordMod.toNat_ofNat, WordMod.toNat_ofNat, WordMod.toNat_ofNat,
    DensePoly.coeff_add x y j (by rfl), ZPoly.intModNat_add _ _ ctx.p_pos,
    Nat.mod_eq_of_lt (ZPoly.intModNat_lt' (x.coeff j) ctx.p_pos),
    Nat.mod_eq_of_lt (ZPoly.intModNat_lt' (y.coeff j) ctx.p_pos), Nat.mod_mod]

theorem toWP_sub (x y : ZPoly) : toWP ctx (x - y) = toWP ctx x - toWP ctx y := by
  apply DensePoly.ext_coeff
  intro j
  have hz : (0 : WordMod ctx) - 0 = 0 := by rw [WordMod.eq_iff_toNat]; simp
  rw [DensePoly.coeff_sub _ _ j hz, coeff_toWP, coeff_toWP, coeff_toWP]
  apply WordMod.toNat_injective
  rw [WordMod.toNat_sub, WordMod.toNat_ofNat, WordMod.toNat_ofNat, WordMod.toNat_ofNat,
    DensePoly.coeff_sub x y j (by rfl), ZPoly.intModNat_sub _ _ ctx.p_pos,
    Nat.mod_eq_of_lt (ZPoly.intModNat_lt' (x.coeff j) ctx.p_pos),
    Nat.mod_eq_of_lt (ZPoly.intModNat_lt' (y.coeff j) ctx.p_pos), Nat.mod_mod]

theorem intModNat_one {M : Nat} (hM : 0 < M) : ZPoly.intModNat 1 M = 1 % M := by
  have h : ((ZPoly.intModNat 1 M : Nat) : Int) = ((1 % M : Nat) : Int) := by
    rw [ZPoly.intModNat_cast 1 hM]; exact_mod_cast rfl
  exact_mod_cast h

@[simp] theorem toWP_one : toWP ctx 1 = 1 := by
  apply DensePoly.ext_coeff
  intro j
  rw [coeff_toWP, WordMod.eq_iff_toNat, WordMod.toNat_ofNat,
    show (1 : ZPoly) = DensePoly.C 1 from rfl,
    show (1 : DensePoly (WordMod ctx)) = DensePoly.C 1 from rfl,
    DensePoly.coeff_C, DensePoly.coeff_C]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [if_pos rfl, if_pos rfl, WordMod.toNat_one, intModNat_one ctx.p_pos, Nat.mod_mod]
  · rw [if_neg (Nat.ne_of_gt hj), if_neg (Nat.ne_of_gt hj),
      show (Zero.zero : WordMod ctx) = 0 from rfl, WordMod.toNat_zero,
      show (Zero.zero : Int) = 0 from rfl, ZPoly.intModNat]
    simp

/-- The canonical reduction `reduceModPow _ p k` vanishes under `toWP` when the
working modulus is exactly `p^k`. -/
theorem toWP_reduceModPow {p k : Nat} (hM : m.toNat = p ^ k) (hpk : 0 < p ^ k) (x : ZPoly) :
    toWP ctx (ZPoly.reduceModPow x p k) = toWP ctx x := by
  apply toWP_congr
  have := ZPoly.congr_reduceModPow x p k hpk
  rwa [← hM] at this

end ZPoly
end Hex
