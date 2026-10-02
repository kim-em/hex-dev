/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMinPoly.Kernel
public import HexPolyMathlib.ScaledLiteral
public import HexMatrixMathlib.ListProducts
public import Mathlib.Tactic.FieldSimp

public section

/-! Soundness of denominator-cleared polynomial certificate identities. -/

namespace HexMinPolyMathlib

open Hex.Matrix.Lists Hex.Matrix.MinPolyLists HexMatrixMathlib HexPolyMathlib Polynomial

/-- Decode a polynomial block only in the soundness proof. -/
@[expose] noncomputable def decodeBlock (s : Scaled) : Hex.DensePoly ℚ :=
  Hex.DensePoly.ofList (decodeList s)

theorem blockPolynomial_eq (s : Scaled) :
    blockPolynomial s = toPolynomial (decodeBlock s) := polynomialOfList_eq _

theorem decodeBlock_coeff (s : Scaled) (i : Nat) :
    (decodeBlock s).coeff i = decodeScalar s.denom (entry 0 s.nums i) := by
  rw [decodeBlock, Hex.DensePoly.coeff_ofList]
  change (decodeList s).getD i 0 = _
  rw [decodeList_getD, entry_eq_getD]

theorem blockPolynomial_coeff (s : Scaled) (i : Nat) :
    (blockPolynomial s).coeff i = decodeScalar s.denom (entry 0 s.nums i) := by
  rw [blockPolynomial_eq, coeff_toPolynomial, decodeBlock_coeff]

theorem eqPoly_sound (a b : Scaled) (ha : 0 < a.denom) (hb : 0 < b.denom)
    (h : eqPoly a b = true) : blockPolynomial a = blockPolynomial b := by
  ext i
  rw [blockPolynomial_coeff, blockPolynomial_coeff]
  by_cases hi : i < max a.nums.length b.nums.length
  · have hc := of_decide_eq_true ((all_iff _ _).mp h i hi)
    have ha' : (a.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
    have hb' : (b.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    apply (div_eq_div_iff ha' hb').mpr
    exact_mod_cast hc
  · have hai : a.nums.length ≤ i := by omega
    have hbi : b.nums.length ≤ i := by omega
    rw [entry_eq_getD, entry_eq_getD, getD_eq_default' _ _ _ hai,
      getD_eq_default' _ _ _ hbi, decodeScalar_zero, decodeScalar_zero]

theorem addPoly_sound (a b : Scaled) (ha : 0 < a.denom) (hb : 0 < b.denom) :
    blockPolynomial (addPoly a b) = blockPolynomial a + blockPolynomial b :=
  blockPolynomial_add a b ha hb

theorem mulPoly_sound (a b : Scaled) :
    blockPolynomial (mulPoly a b) = blockPolynomial a * blockPolynomial b :=
  blockPolynomial_mul a b

theorem valid_pos (s : Scaled) (h : valid s = true) : 0 < s.denom := by
  simp only [valid, Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1

theorem decodeBlock_size (s : Scaled) (h : valid s = true) :
    (decodeBlock s).size = s.nums.length := by
  have hle : (decodeBlock s).size ≤ s.nums.length := by
    simpa [decodeBlock, decodeList] using Hex.DensePoly.size_ofList_le (decodeList s)
  apply Nat.le_antisymm hle
  by_contra hn
  have hpos : 0 < s.nums.length := by omega
  have hlast : entry 0 s.nums (s.nums.length - 1) ≠ 0 := by
    have hv := h
    simp only [valid, Bool.and_eq_true] at hv
    have hv := hv.2
    have hnil : s.nums.isEmpty = false := by
      cases hs : s.nums with
      | nil => simp [hs] at hpos
      | cons x xs => rfl
    simpa [hnil] using hv
  have hz := (decodeBlock s).coeff_eq_zero_of_size_le
    (i := s.nums.length - 1) (by omega)
  rw [decodeBlock_coeff, decodeScalar] at hz
  have ha : ((entry 0 s.nums (s.nums.length - 1) : Int) : ℚ) ≠ 0 := by
    exact_mod_cast hlast
  have hd : (s.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (valid_pos s h))
  exact div_ne_zero ha hd hz

theorem decodeBlock_monic (s : Scaled) (hv : valid s = true) (hm : monic s = true) :
    (decodeBlock s).Monic := by
  have hcoeff : (decodeBlock s).coeff ((decodeBlock s).size - 1) = 1 := by
    rw [decodeBlock_size s hv, decodeBlock_coeff, decodeScalar]
    have h := of_decide_eq_true hm
    change entry 0 s.nums (s.nums.length - 1) = (s.denom : Int) at h
    rw [h, Int.cast_natCast, div_self]
    exact_mod_cast (Nat.ne_of_gt (valid_pos s hv))
  have hpos : 0 < (decodeBlock s).size := by
    by_contra hn
    have hz := (decodeBlock s).coeff_eq_zero_of_size_le
      (i := (decodeBlock s).size - 1) (by omega)
    rw [hcoeff] at hz
    exact one_ne_zero hz
  rw [Hex.DensePoly.monic_iff_leadingCoeff_eq_one,
    Hex.DensePoly.leadingCoeff_eq_coeff_last _ hpos]
  exact hcoeff

/-- An accepted LCM step supplies exactly the reference polynomial identities. -/
theorem stepCheck_sound (running incoming : Scaled) (s : Hex.Matrix.LcmWitness)
    (hr : 0 < running.denom) (hi : 0 < incoming.denom)
    (h : stepCheck running incoming s = true) :
    blockPolynomial running = blockPolynomial s.common * blockPolynomial s.left ∧
    blockPolynomial incoming = blockPolynomial s.common * blockPolynomial s.right ∧
    blockPolynomial s.bezoutLeft * blockPolynomial running +
      blockPolynomial s.bezoutRight * blockPolynomial incoming = blockPolynomial s.common ∧
    blockPolynomial s.result = blockPolynomial s.left * blockPolynomial incoming := by
  simp only [stepCheck, Bool.and_assoc, Bool.and_eq_true] at h
  rcases h with ⟨hc, hl, hri, hb, hbr, hs, h1, h2, h3, h4⟩
  have pos (a b : Scaled) (ha : 0 < a.denom) (hb : 0 < b.denom) :
      0 < (mulPoly a b).denom := Nat.mul_pos ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [mulPoly_sound] using eqPoly_sound _ _ hr
      (pos _ _ (valid_pos _ hc) (valid_pos _ hl)) h1
  · simpa only [mulPoly_sound] using eqPoly_sound _ _ hi
      (pos _ _ (valid_pos _ hc) (valid_pos _ hri)) h2
  · have hp := pos _ _ (valid_pos _ hb) hr
    have hq := pos _ _ (valid_pos _ hbr) hi
    simpa only [addPoly_sound _ _ hp hq, mulPoly_sound] using eqPoly_sound _ _
      (Nat.mul_pos hp hq) (valid_pos _ hc) h3
  · simpa only [mulPoly_sound] using eqPoly_sound _ _ (valid_pos _ hs)
      (pos _ _ (valid_pos _ hl) hi) h4

end HexMinPolyMathlib
