/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Std

/-!
Core packed polynomial definitions for `hex-gf2`.

This module models polynomials over `F_2` as arrays of `UInt64` words in
ascending degree order. It provides normalization, degree/bit accessors,
word-wise XOR addition, and shifts by powers of `x`.
-/
namespace Hex

/-- Packed-word normalization for `GF2Poly`: either the polynomial is zero, or
its highest stored word is nonzero. -/
def GF2PolyNormalized (words : Array UInt64) : Prop :=
  words.size = 0 ∨ words.back? ≠ some (0 : UInt64)

/-- Polynomials over `F_2`, packed into 64-bit words. Bit `j` of `words[i]`
stores the coefficient of `x^(64 * i + j)`. -/
structure GF2Poly where
  /-- The packed coefficient words: bit `j` of `words[i]` is the coefficient of
  `x^(64 * i + j)`. -/
  words : Array UInt64
  normalized : GF2PolyNormalized words

namespace GF2Poly

/-- Packed polynomials are equal when their normalized word arrays are equal. -/
theorem ext_words {p q : GF2Poly} (h : p.words = q.words) : p = q := by
  cases p
  cases q
  simp at h
  subst h
  simp

/-- Remove trailing zero words without disturbing the lower-degree prefix. -/
private def trimTrailingZeroWordsList : List UInt64 → List UInt64
  | [] => []
  | w :: ws =>
      let trimmed := trimTrailingZeroWordsList ws
      if trimmed = [] ∧ w = 0 then [] else w :: trimmed

private theorem trimTrailingZeroWordsList_getLast?_ne_zero :
    ∀ ws : List UInt64,
      let trimmed := trimTrailingZeroWordsList ws
      trimmed = [] ∨ trimmed.getLast? ≠ some (0 : UInt64)
  | [] => by simp [trimTrailingZeroWordsList]
  | w :: ws => by
      dsimp
      have htrim := trimTrailingZeroWordsList_getLast?_ne_zero ws
      by_cases hdrop : trimTrailingZeroWordsList ws = [] ∧ w = 0
      · simp [trimTrailingZeroWordsList, hdrop]
      · by_cases hnil : trimTrailingZeroWordsList ws = []
        · have hw : w ≠ 0 := by
            intro hw0
            apply hdrop
            exact ⟨hnil, hw0⟩
          simp [trimTrailingZeroWordsList, hnil, hw]
        · have hlast : (trimTrailingZeroWordsList ws).getLast? ≠ some (0 : UInt64) := by
            cases htrim with
            | inl h =>
                contradiction
            | inr h =>
                exact h
          cases hrest : trimTrailingZeroWordsList ws with
          | nil =>
              contradiction
          | cons x xs =>
              simpa [trimTrailingZeroWordsList, hdrop, hrest] using hlast

private theorem trimTrailingZeroWordsList_length_le (ws : List UInt64) :
    (trimTrailingZeroWordsList ws).length ≤ ws.length := by
  induction ws with
  | nil =>
      simp [trimTrailingZeroWordsList]
  | cons w ws ih =>
      by_cases hdrop : trimTrailingZeroWordsList ws = [] ∧ w = 0
      · have hnil : trimTrailingZeroWordsList (w :: ws) = [] := by
          simp [trimTrailingZeroWordsList, hdrop]
        rw [hnil]
        exact Nat.zero_le _
      · have hcons : trimTrailingZeroWordsList (w :: ws) = w :: trimTrailingZeroWordsList ws := by
          simp [trimTrailingZeroWordsList, hdrop]
        rw [hcons]
        simp [ih]

private theorem trimTrailingZeroWordsList_getD (ws : List UInt64) (i : Nat) :
    (trimTrailingZeroWordsList ws).getD i 0 = ws.getD i 0 := by
  induction ws generalizing i with
  | nil =>
      simp [trimTrailingZeroWordsList]
  | cons w ws ih =>
      by_cases hdrop : trimTrailingZeroWordsList ws = [] ∧ w = 0
      · cases i with
        | zero =>
            simp [trimTrailingZeroWordsList, hdrop]
        | succ i =>
            have htail : ws.getD i 0 = 0 := by
              rw [← ih i, hdrop.1]
              simp
            simpa [trimTrailingZeroWordsList, hdrop, List.getD] using htail.symm
      · cases i with
        | zero =>
            simp [trimTrailingZeroWordsList, hdrop]
        | succ i =>
            simpa [trimTrailingZeroWordsList, hdrop, List.getD] using ih i

/-- Normalize a word array by discarding trailing zero words. -/
def normalizeWords (words : Array UInt64) : Array UInt64 :=
  (trimTrailingZeroWordsList words.toList).toArray

/-- Packed-word coefficient lookup before wrapping the array as a `GF2Poly`. -/
def coeffWords (words : Array UInt64) (n : Nat) : Bool :=
  let word := words[n / 64]?.getD 0
  (((word >>> (n % 64).toUInt64) &&& 1) != 0)

/-- Trailing-zero normalization preserves every packed coefficient word. -/
@[simp, grind =] theorem normalizeWords_get?_getD (words : Array UInt64) (i : Nat) :
    ((normalizeWords words)[i]?).getD 0 = (words[i]?).getD 0 := by
  simpa [normalizeWords, Array.getD, List.getD] using
    trimTrailingZeroWordsList_getD words.toList i

/-- Trailing-zero normalization preserves packed coefficients. -/
@[simp, grind =] theorem coeffWords_normalizeWords (words : Array UInt64) (n : Nat) :
    coeffWords (normalizeWords words) n = coeffWords words n := by
  rw [coeffWords, coeffWords, normalizeWords_get?_getD]

private def wordBitIsSet (w : UInt64) (i : Nat) : Bool :=
  (((w >>> i.toUInt64) &&& 1) != 0)

private def highestSetBitBelow? (fuel : Nat) (w : UInt64) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      if wordBitIsSet w fuel' then
        some fuel'
      else
        highestSetBitBelow? fuel' w

/-- The index of the highest set bit in a machine word, if any. -/
def highestSetBit? (w : UInt64) : Option Nat :=
  highestSetBitBelow? 64 w

private theorem highestSetBitBelow?_lt {fuel : Nat} {w : UInt64} {i : Nat}
    (h : highestSetBitBelow? fuel w = some i) :
    i < fuel := by
  induction fuel generalizing i with
  | zero =>
      simp [highestSetBitBelow?] at h
  | succ fuel ih =>
      by_cases htop : wordBitIsSet w fuel = true
      · simp [highestSetBitBelow?, htop] at h
        omega
      · have htopFalse : wordBitIsSet w fuel = false := by
          cases hbit : wordBitIsSet w fuel <;> simp [hbit] at htop ⊢
        simp [highestSetBitBelow?, htopFalse] at h
        exact Nat.lt_trans (ih h) (Nat.lt_succ_self fuel)

private theorem highestSetBitBelow?_bit {fuel : Nat} {w : UInt64} {i : Nat}
    (h : highestSetBitBelow? fuel w = some i) :
    wordBitIsSet w i = true := by
  induction fuel generalizing i with
  | zero =>
      simp [highestSetBitBelow?] at h
  | succ fuel ih =>
      by_cases htop : wordBitIsSet w fuel = true
      · simp [highestSetBitBelow?, htop] at h
        subst h
        exact htop
      · have htopFalse : wordBitIsSet w fuel = false := by
          cases hbit : wordBitIsSet w fuel <;> simp [hbit] at htop ⊢
        simp [highestSetBitBelow?, htopFalse] at h
        exact ih h

private theorem highestSetBitBelow?_above_bit {fuel : Nat} {w : UInt64} {i j : Nat}
    (h : highestSetBitBelow? fuel w = some i) (hj : j < fuel) (hij : i < j) :
    wordBitIsSet w j = false := by
  induction fuel generalizing i j with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases htop : wordBitIsSet w fuel = true
      · simp [highestSetBitBelow?, htop] at h
        subst h
        omega
      · have htopFalse : wordBitIsSet w fuel = false := by
          cases hbit : wordBitIsSet w fuel <;> simp [hbit] at htop ⊢
        simp [highestSetBitBelow?, htopFalse] at h
        by_cases hjtop : j = fuel
        · subst hjtop
          exact htopFalse
        · have hjlt : j < fuel := by omega
          exact ih h hjlt hij

private theorem highestSetBitBelow?_eq_none_bit {fuel : Nat} {w : UInt64} {i : Nat}
    (h : highestSetBitBelow? fuel w = none) (hi : i < fuel) :
    wordBitIsSet w i = false := by
  induction fuel generalizing i with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases htop : wordBitIsSet w fuel = true
      · simp [highestSetBitBelow?, htop] at h
      · have htopFalse : wordBitIsSet w fuel = false := by
          cases hbit : wordBitIsSet w fuel <;> simp [hbit] at htop ⊢
        simp [highestSetBitBelow?, htopFalse] at h
        by_cases hitop : i = fuel
        · subst hitop
          exact htopFalse
        · have hilt : i < fuel := by omega
          exact ih h hilt

/-- A returned highest-bit index is one of the 64 word-bit positions. -/
theorem highestSetBit?_lt {w : UInt64} {i : Nat}
    (h : highestSetBit? w = some i) :
    i < 64 := by
  exact highestSetBitBelow?_lt h

/-- A returned highest-bit index has its bit set in the word. -/
theorem highestSetBit?_bit {w : UInt64} {i : Nat}
    (h : highestSetBit? w = some i) :
    (((w >>> i.toUInt64) &&& 1) != 0) = true := by
  exact highestSetBitBelow?_bit h

/-- If no highest bit exists, every queried word bit is clear. -/
theorem highestSetBit?_eq_none_bit {w : UInt64} {i : Nat}
    (h : highestSetBit? w = none) (hi : i < 64) :
    (((w >>> i.toUInt64) &&& 1) != 0) = false := by
  exact highestSetBitBelow?_eq_none_bit h hi

/-- Bits strictly above the reported highest set bit are clear. -/
theorem highestSetBit?_above_bit {w : UInt64} {i j : Nat}
    (h : highestSetBit? w = some i) (hj : j < 64) (hij : i < j) :
    (((w >>> j.toUInt64) &&& 1) != 0) = false := by
  exact highestSetBitBelow?_above_bit h hj hij

/-- The one-hot word used by `monomial` has its highest set bit at the
requested in-word position. -/
theorem highestSetBit?_oneHot {bit : Nat} (hbit : bit < 64) :
    highestSetBit? ((1 : UInt64) <<< bit.toUInt64) = some bit := by
  have hcases : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨ bit = 4 ∨ bit = 5 ∨
      bit = 6 ∨ bit = 7 ∨ bit = 8 ∨ bit = 9 ∨ bit = 10 ∨ bit = 11 ∨
      bit = 12 ∨ bit = 13 ∨ bit = 14 ∨ bit = 15 ∨ bit = 16 ∨ bit = 17 ∨
      bit = 18 ∨ bit = 19 ∨ bit = 20 ∨ bit = 21 ∨ bit = 22 ∨ bit = 23 ∨
      bit = 24 ∨ bit = 25 ∨ bit = 26 ∨ bit = 27 ∨ bit = 28 ∨ bit = 29 ∨
      bit = 30 ∨ bit = 31 ∨ bit = 32 ∨ bit = 33 ∨ bit = 34 ∨ bit = 35 ∨
      bit = 36 ∨ bit = 37 ∨ bit = 38 ∨ bit = 39 ∨ bit = 40 ∨ bit = 41 ∨
      bit = 42 ∨ bit = 43 ∨ bit = 44 ∨ bit = 45 ∨ bit = 46 ∨ bit = 47 ∨
      bit = 48 ∨ bit = 49 ∨ bit = 50 ∨ bit = 51 ∨ bit = 52 ∨ bit = 53 ∨
      bit = 54 ∨ bit = 55 ∨ bit = 56 ∨ bit = 57 ∨ bit = 58 ∨ bit = 59 ∨
      bit = 60 ∨ bit = 61 ∨ bit = 62 ∨ bit = 63 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- A machine word is `!= 0` exactly when its `Nat` value is `!= 0`,
transporting the word-level boolean inequality to the `toNat` image. -/
theorem UInt64.bne_zero_eq_toNat_bne_zero (w : UInt64) :
    (w != 0) = (w.toNat != 0) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hw
    apply bne_iff_ne.mpr
    intro hnat
    have hz : w = 0 := UInt64.toNat_inj.mp (by simpa using hnat)
    exact (bne_iff_ne.mp hw) hz
  · intro hnat
    apply bne_iff_ne.mpr
    intro hw
    subst hw
    exact (bne_iff_ne.mp hnat) rfl

/-- Extracting bit `i` by shifting a natural number right and testing the low
bit agrees with `Nat.testBit`. This is the bridge used by the word-bit
inspection lemmas that compare packed `UInt64` bits with natural-bit facts. -/
private theorem bit_eq_one_eq_testBit (x i : Nat) :
    (x >>> i % 2 == 1) = x.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  apply decide_eq_decide.mpr
  exact Iff.rfl

/-- A natural number below `2 ^ i` has no bit set at position `i`. The
`highestSetBit?` nonzero proof uses this to rule out bits beyond the 64-bit
`UInt64` range. -/
private theorem Nat.testBit_eq_false_of_lt {n i : Nat} (h : n < 2 ^ i) :
    n.testBit i = false := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

/-- The executable `wordBitIsSet` predicate agrees with `Nat.testBit` on the
`toNat` image of a `UInt64` at every valid word position. This is the local
bridge from the `highestSetBit?` scan to natural-number bit reasoning. -/
private theorem UInt64.wordBitIsSet_eq_testBit (w : UInt64) {i : Nat} (hi : i < 64) :
    wordBitIsSet w i = w.toNat.testBit i := by
  simp [wordBitIsSet, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftRight,
    UInt64.toNat_and, Nat.mod_eq_of_lt hi, bit_eq_one_eq_testBit]

/-- A nonzero `UInt64` has some highest set bit reported by `highestSetBit?`.
This prevents the search from returning `none` on nonzero words by combining
the word-bit/testBit bridge with the 64-bit bound. -/
private theorem highestSetBit?_isSome_of_ne_zero {w : UInt64} (hw : w ≠ 0) :
    ∃ bit, highestSetBit? w = some bit := by
  cases hbit : highestSetBit? w with
  | some bit =>
      exact ⟨bit, rfl⟩
  | none =>
      have hzeroNat : w.toNat = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        by_cases hi : i < 64
        · have hwbit : wordBitIsSet w i = false := by
            simpa [wordBitIsSet] using highestSetBit?_eq_none_bit hbit hi
          simpa [UInt64.wordBitIsSet_eq_testBit w hi] using hwbit
        · have hfalse : w.toNat.testBit i = false := by
            apply Nat.testBit_eq_false_of_lt
            have hwlt : w.toNat < 2 ^ 64 := by
              simpa [UInt64.size] using UInt64.toNat_lt_size w
            exact Nat.lt_of_lt_of_le hwlt (Nat.pow_le_pow_right (by decide : 0 < 2)
              (Nat.le_of_not_gt hi))
          simp [hfalse]
      apply False.elim
      apply hw
      exact UInt64.toNat_inj.mp (by simpa using hzeroNat)

/-- Testing one bit of the xor of two words is the boolean xor of the
corresponding tested input bits. This is the bit-level fact behind the
`GF2Poly` xor coefficient bridge. -/
private theorem UInt64.bit_xor_bne (a b : UInt64) (i : Nat) :
    ((((a ^^^ b) >>> i.toUInt64) &&& 1) != 0) =
      ((((a >>> i.toUInt64) &&& 1) != 0) !=
        (((b >>> i.toUInt64) &&& 1) != 0)) := by
  rw [UInt64.bne_zero_eq_toNat_bne_zero, UInt64.bne_zero_eq_toNat_bne_zero,
    UInt64.bne_zero_eq_toNat_bne_zero]
  simp [UInt64.toNat_xor, UInt64.toNat_shiftRight, UInt64.toNat_and]
  rw [bit_eq_one_eq_testBit, bit_eq_one_eq_testBit, bit_eq_one_eq_testBit]
  simp [Nat.testBit_xor]

/-- In the high-bit branch of a shifted word with carry, where `old + shift <
64`, the target bit comes from bit `old` of the current word `w`. This supplies
the in-word half of the `shiftLeft`-or-carry reindexing argument. -/
private theorem UInt64.shiftLeft_or_carry_high_bit
    (w prev : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hold : old < 64) (htarget : old + shift < 64) :
    (((((w <<< shift.toUInt64) ||| (prev >>> (64 - shift).toUInt64)) >>>
          (old + shift).toUInt64) &&& 1) != 0) =
      ((((w >>> old.toUInt64) &&& 1) != 0)) := by
  rw [UInt64.bne_zero_eq_toNat_bne_zero, UInt64.bne_zero_eq_toNat_bne_zero]
  simp [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    UInt64.toNat_and, Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hold,
    Nat.mod_eq_of_lt htarget]
  rw [bit_eq_one_eq_testBit, bit_eq_one_eq_testBit]
  simp [Nat.testBit_or, Nat.testBit_shiftRight]
  have hprev :
      (prev.toNat >>> (64 - shift)).testBit (old + shift) = false := by
    rw [Nat.testBit_shiftRight]
    apply Nat.testBit_eq_false_of_lt
    have hprevlt : prev.toNat < 2 ^ 64 := by
      simpa [UInt64.size] using UInt64.toNat_lt_size prev
    refine Nat.lt_of_lt_of_le hprevlt ?_
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    omega
  have hprev' :
      prev.toNat.testBit ((64 - shift) % 64 + (old + shift)) = false := by
    have h64 : 64 - shift < 64 := by omega
    simpa [Nat.testBit_shiftRight, Nat.mod_eq_of_lt h64] using hprev
  simpa [hprev'] using (show
    ((w.toNat <<< shift) % 18446744073709551616).testBit (old + shift) =
      w.toNat.testBit old by
        change ((w.toNat <<< shift) % 2 ^ 64).testBit (old + shift) =
          w.toNat.testBit old
        rw [Nat.testBit_mod_two_pow]
        have hge : old + shift ≥ shift := by omega
        have hsub : old + shift - shift = old := by omega
        simp [Nat.testBit_shiftLeft, htarget, hge, hsub])

/-- In the low-bit branch of a shifted word with carry, where `64 ≤ old +
shift`, the wrapped target bit comes from bit `old` of the previous carry word
`prev`. This supplies the carried-word half of the `shiftLeft`-or-carry
reindexing argument. -/
private theorem UInt64.shiftLeft_or_carry_low_bit
    (w prev : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hold : old < 64) (htarget : 64 ≤ old + shift) :
    (((((w <<< shift.toUInt64) ||| (prev >>> (64 - shift).toUInt64)) >>>
          (old + shift - 64).toUInt64) &&& 1) != 0) =
      ((((prev >>> old.toUInt64) &&& 1) != 0)) := by
  have htargetLt : old + shift - 64 < 64 := by omega
  have htargetShift : old + shift - 64 < shift := by omega
  rw [UInt64.bne_zero_eq_toNat_bne_zero, UInt64.bne_zero_eq_toNat_bne_zero]
  simp [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    UInt64.toNat_and, Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hold,
    Nat.mod_eq_of_lt htargetLt]
  rw [bit_eq_one_eq_testBit, bit_eq_one_eq_testBit]
  simp [Nat.testBit_or, Nat.testBit_shiftRight]
  have hleft :
      (((w.toNat <<< shift) % 18446744073709551616).testBit (old + shift - 64)) =
        false := by
    change (((w.toNat <<< shift) % 2 ^ 64).testBit (old + shift - 64)) = false
    rw [Nat.testBit_mod_two_pow]
    simp [Nat.testBit_shiftLeft, htargetLt, Nat.not_le.mpr htargetShift]
  have hidx : (64 - shift) % 64 + (old + shift - 64) = old := by
    have hsub : 64 - shift < 64 := by omega
    rw [Nat.mod_eq_of_lt hsub]
    omega
  simp [hleft, hidx]

/-- Reading a bit from the one-hot `UInt64` word `1 <<< hot` matches the
corresponding natural-number bit calculation. The public one-hot lemmas use
this to prove the selected bit is set and all other valid bits are clear. -/
private theorem oneHotWord_bit_toNat {hot bit : Nat} (hhot : hot < 64) (hbit : bit < 64) :
    (((((1 : UInt64) <<< hot.toUInt64) >>> bit.toUInt64) &&& 1).toNat) =
      ((2 ^ hot >>> bit) &&& 1) := by
  have hpow : 2 ^ hot < 2 ^ 64 := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hhot
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_and,
    Nat.one_shiftLeft, Nat.mod_eq_of_lt hhot, Nat.mod_eq_of_lt hbit,
    Nat.mod_eq_of_lt hpow]

/-- Querying the one-hot word `1 <<< bit` at position `bit` returns the bit it
encodes. -/
theorem oneHotWord_bit_self {bit : Nat} (hbit : bit < 64) :
    (((((1 : UInt64) <<< bit.toUInt64) >>> bit.toUInt64) &&& 1) != 0) = true := by
  rw [UInt64.bne_zero_eq_toNat_bne_zero]
  have hnat := oneHotWord_bit_toNat (hot := bit) (bit := bit) hbit hbit
  rw [hnat]
  simpa [Nat.testBit] using Nat.testBit_two_pow_self (n := bit)

/-- Querying the one-hot word `1 <<< hot` at any position other than `hot`
returns a clear bit. -/
theorem oneHotWord_bit_ne {hot bit : Nat} (hhot : hot < 64) (hbit : bit < 64)
    (hne : hot ≠ bit) :
    (((((1 : UInt64) <<< hot.toUInt64) >>> bit.toUInt64) &&& 1) != 0) = false := by
  rw [UInt64.bne_zero_eq_toNat_bne_zero]
  have hnat := oneHotWord_bit_toNat (hot := hot) (bit := bit) hhot hbit
  rw [hnat]
  simpa [Nat.testBit] using Nat.testBit_two_pow_of_ne (n := hot) (m := bit) hne

/-- The one-hot word `1 <<< bit` is nonzero whenever `bit` is a valid in-word
position. -/
theorem oneHotWord_ne_zero {bit : Nat} (hbit : bit < 64) :
    ((1 : UInt64) <<< bit.toUInt64) ≠ 0 := by
  intro h
  have hset := oneHotWord_bit_self hbit
  rw [h] at hset
  simp at hset

/-- Build a normalized packed polynomial from a raw word array. -/
def ofWords (words : Array UInt64) : GF2Poly :=
  let normalizedWords := normalizeWords words
  { words := normalizedWords
    normalized := by
      classical
      simpa [normalizedWords, normalizeWords, GF2PolyNormalized] using
        trimTrailingZeroWordsList_getLast?_ne_zero words.toList }

/-- Wrapping the empty word array gives the empty packed representation. -/
@[simp, grind =] theorem words_ofWords_empty : (ofWords #[]).words = #[] := by
  rfl

/-- The zero polynomial. -/
def zero : GF2Poly :=
  ofWords #[]

instance : Zero GF2Poly where
  zero := zero

/-- The empty word array represents the zero polynomial. -/
@[simp, grind =] theorem ofWords_empty : ofWords #[] = 0 := by
  apply ext_words
  rfl

/-- The constant polynomial `1`. -/
def one : GF2Poly :=
  ofWords #[1]

instance : One GF2Poly where
  one := one

/-- Build a packed polynomial from a single machine word. -/
def ofUInt64 (w : UInt64) : GF2Poly :=
  ofWords #[w]

/-- A single zero word normalizes to the empty packed representation. -/
@[simp, grind =] theorem words_ofWords_single_zero : (ofWords #[(0 : UInt64)]).words = #[] := by
  rfl

/-- A pair of zero words normalizes to the empty packed representation. -/
@[simp, grind =] theorem words_ofWords_pair_zero :
    (ofWords #[(0 : UInt64), (0 : UInt64)]).words = #[] := by
  rfl

/-- A single nonzero word is already normalized and is its own packed
representation. -/
@[simp, grind =] theorem words_ofWords_single_nonzero {w : UInt64} (hw : w ≠ 0) :
    (ofWords #[w]).words = #[w] := by
  simp [ofWords, normalizeWords, trimTrailingZeroWordsList, hw]

/-- The monomial `x^n`. -/
def monomial (n : Nat) : GF2Poly :=
  let wordIdx := n / 64
  let bitIdx := n % 64
  ofWords <| (Array.replicate wordIdx (0 : UInt64)).push ((1 : UInt64) <<< bitIdx.toUInt64)

/-- The stored packed words. -/
def toWords (p : GF2Poly) : Array UInt64 :=
  p.words

/-- Number of stored machine words. -/
def wordCount (p : GF2Poly) : Nat :=
  p.words.size

/-- `true` exactly when the polynomial is zero. -/
def isZero (p : GF2Poly) : Bool :=
  p.words.isEmpty

/-- Proposition-level zero predicate used by the packed quotient wrappers. -/
def IsZero (p : GF2Poly) : Prop :=
  p.isZero = true

/-- The coefficient of `x^n`. -/
def coeff (p : GF2Poly) (n : Nat) : Bool :=
  coeffWords p.words n

/-- Coefficients of a raw word array are unchanged by `ofWords` normalization. -/
@[simp, grind =] theorem coeff_ofWords (words : Array UInt64) (n : Nat) :
    (ofWords words).coeff n = coeffWords words n := by
  simp [ofWords, coeff, coeffWords_normalizeWords]

/-- Coefficients of a single-word polynomial are the corresponding machine-word bits. -/
theorem coeff_ofUInt64_eq_testBit (w : UInt64) {i : Nat} (hi : i < 64) :
    (ofUInt64 w).coeff i = w.toNat.testBit i := by
  unfold ofUInt64
  rw [coeff_ofWords]
  have hiword : i / 64 = 0 := Nat.div_eq_of_lt hi
  simp [coeffWords, hiword, UInt64.bne_zero_eq_toNat_bne_zero,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hi,
    bit_eq_one_eq_testBit]

/-- Coefficients above the low machine word vanish for a single-word polynomial. -/
theorem coeff_ofUInt64_eq_false_of_ge_64 (w : UInt64) {i : Nat} (hi : 64 ≤ i) :
    (ofUInt64 w).coeff i = false := by
  unfold ofUInt64
  rw [coeff_ofWords]
  have hiword_pos : 0 < i / 64 := Nat.div_pos (by omega) (by decide : 0 < 64)
  cases hidx : i / 64 with
  | zero =>
      omega
  | succ _ =>
      simp [coeffWords, hidx]

/-- Input `0` to `ofUInt64` is the zero polynomial. -/
@[simp, grind =] theorem ofUInt64_zero : ofUInt64 0 = (0 : GF2Poly) := by
  change ofWords #[(0 : UInt64)] = ofWords #[]
  apply ext_words
  exact words_ofWords_single_zero

/-- Input `1` to `ofUInt64` is the unit polynomial. -/
@[simp, grind =] theorem ofUInt64_one : ofUInt64 1 = (1 : GF2Poly) := by
  rfl

/-- The packed single-word constructor preserves the underlying machine word. -/
theorem ofUInt64_injective : Function.Injective ofUInt64 := by
  intro a b h
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · have hcoeff := congrArg (fun p : GF2Poly => p.coeff i) h
    simpa [coeff_ofUInt64_eq_testBit _ hi] using hcoeff
  · have hge : 64 ≤ i := Nat.le_of_not_gt hi
    rw [show a.toNat.testBit i = false by
        apply Nat.testBit_eq_false_of_lt
        have ha64 : a.toNat < 2 ^ 64 := by
          simpa [UInt64.size] using a.toNat_lt_size
        exact Nat.lt_of_lt_of_le ha64
          (Nat.pow_le_pow_right (by decide : 0 < 2) hge),
      show b.toNat.testBit i = false by
        apply Nat.testBit_eq_false_of_lt
        have hb64 : b.toNat < 2 ^ 64 := by
          simpa [UInt64.size] using b.toNat_lt_size
        exact Nat.lt_of_lt_of_le hb64
          (Nat.pow_le_pow_right (by decide : 0 < 2) hge)]

/-- The degree of a nonzero polynomial, if any. -/
def degree? (p : GF2Poly) : Option Nat :=
  match p.words.back? with
  | none => none
  | some last =>
      match highestSetBit? last with
      | none => none
      | some bitIdx => some (64 * (p.words.size - 1) + bitIdx)

/-- The degree of a polynomial, defaulting to `0` for the zero polynomial. -/
def degree (p : GF2Poly) : Nat :=
  p.degree?.getD 0

/-- A normalized packed polynomial is `isZero` iff its stored word array is empty. -/
@[simp, grind =] theorem isZero_eq_true_iff_words_eq_empty (p : GF2Poly) :
    p.isZero = true ↔ p.words = #[] := by
  simp [isZero]

/-- A normalized packed polynomial is non-`isZero` iff its stored word array is nonempty. -/
@[simp, grind =] theorem isZero_eq_false_iff_words_ne_empty (p : GF2Poly) :
    p.isZero = false ↔ p.words ≠ #[] := by
  simp [isZero]

/-- `isZero` agrees with propositional equality to the zero polynomial. -/
@[simp, grind =] theorem isZero_iff_eq_zero (p : GF2Poly) :
    p.isZero = true ↔ p = 0 := by
  constructor
  · intro h
    apply ext_words
    simpa using (isZero_eq_true_iff_words_eq_empty p).mp h
  · intro h
    subst h
    rfl

/-- A polynomial that runs the `isZero` Boolean check is propositionally zero. -/
theorem eq_zero_of_isZero {p : GF2Poly} (h : p.isZero = true) :
    p = 0 :=
  (isZero_iff_eq_zero p).mp h

/-- The zero polynomial passes the `isZero` Boolean check. -/
theorem isZero_of_eq_zero {p : GF2Poly} (h : p = 0) :
    p.isZero = true :=
  (isZero_iff_eq_zero p).mpr h

/-- The degree search returns `none` for any polynomial passing `isZero`. -/
theorem degree?_eq_none_of_isZero {p : GF2Poly} (h : p.isZero = true) :
    p.degree? = none := by
  have hp : p = 0 := eq_zero_of_isZero h
  subst hp
  rfl

/-- A successful degree search certifies the polynomial is not `isZero`. -/
theorem isZero_false_of_degree?_eq_some {p : GF2Poly} {d : Nat}
    (h : p.degree? = some d) :
    p.isZero = false := by
  rw [isZero_eq_false_iff_words_ne_empty]
  intro hwords
  have hnone : p.degree? = none := by
    simp [degree?, hwords]
  rw [h] at hnone
  contradiction

/-- A successful degree search certifies the polynomial is not equal to zero. -/
theorem ne_zero_of_degree?_eq_some {p : GF2Poly} {d : Nat}
    (h : p.degree? = some d) :
    p ≠ 0 := by
  intro hp
  have hzero : p.isZero = true := isZero_of_eq_zero hp
  have hfalse : p.isZero = false := isZero_false_of_degree?_eq_some h
  rw [hzero] at hfalse
  contradiction

/-- The default-`0` degree extracts the witness of a successful degree search. -/
@[simp] theorem degree_eq_of_degree?_eq_some {p : GF2Poly} {d : Nat}
    (h : p.degree? = some d) :
    p.degree = d := by
  simp [degree, h]

/-- Unpack a successful `degree?` computation into the normalized high word and
the selected bit inside that word. -/
theorem degree?_eq_some_highestSetBit {p : GF2Poly} {d : Nat}
    (h : p.degree? = some d) :
    ∃ last bit,
      p.words.back? = some last ∧
        highestSetBit? last = some bit ∧
        d = 64 * (p.words.size - 1) + bit := by
  unfold degree? at h
  cases hback : p.words.back? with
  | none =>
      simp [hback] at h
  | some last =>
      cases hbit : highestSetBit? last with
      | none =>
          simp [hback, hbit] at h
      | some bit =>
          have hsome : some (64 * (p.words.size - 1) + bit) = some d := by
            simpa [hback, hbit] using h
          injection hsome with hd
          exact ⟨last, bit, rfl, hbit, hd.symm⟩

/-- The in-word bit recovered from a successful `degree?` computation is a
valid machine-word bit index. -/
theorem degree?_eq_some_bit_lt {p : GF2Poly} {d bit : Nat} {last : UInt64}
    (hparts :
      p.words.back? = some last ∧
        highestSetBit? last = some bit ∧
        d = 64 * (p.words.size - 1) + bit) :
    bit < 64 :=
  highestSetBit?_lt hparts.2.1

/-- A successful `degree?` computation points at a set bit in the high word. -/
theorem degree?_eq_some_high_bit {p : GF2Poly} {d : Nat}
    (h : p.degree? = some d) :
    ∃ last bit,
      p.words.back? = some last ∧
        highestSetBit? last = some bit ∧
        (((last >>> bit.toUInt64) &&& 1) != 0) = true ∧
        d = 64 * (p.words.size - 1) + bit := by
  obtain ⟨last, bit, hback, hbit, hd⟩ := degree?_eq_some_highestSetBit h
  exact ⟨last, bit, hback, hbit, highestSetBit?_bit hbit, hd⟩

/-- A nonzero normalized packed polynomial has a successful degree search. -/
theorem degree?_isSome_of_isZero_false {p : GF2Poly}
    (h : p.isZero = false) :
    ∃ d, p.degree? = some d := by
  have hwords : p.words ≠ #[] := (isZero_eq_false_iff_words_ne_empty p).mp h
  cases hback : p.words.back? with
  | none =>
      exact False.elim (hwords (Array.back?_eq_none_iff.mp hback))
  | some last =>
      have hlast_ne : last ≠ 0 := by
        have hnorm : GF2PolyNormalized p.words := p.normalized
        unfold GF2PolyNormalized at hnorm
        cases hnorm with
        | inl hsize =>
            have hnone : p.words.back? = none := by
              rw [Array.back?_eq_none_iff]
              exact Array.eq_empty_of_size_eq_zero hsize
            rw [hnone] at hback
            contradiction
        | inr hlast =>
            intro hzero
            subst hzero
            exact hlast hback
      obtain ⟨bit, hbit⟩ := highestSetBit?_isSome_of_ne_zero hlast_ne
      exact ⟨64 * (p.words.size - 1) + bit, by simp [degree?, hback, hbit]⟩

/-- A successful `degree?` computation points at a set global coefficient. -/
theorem coeff_eq_true_of_degree?_eq_some {p : GF2Poly} {d : Nat}
    (h : p.degree? = some d) :
    p.coeff d = true := by
  obtain ⟨last, bit, hback, hbit, hwordBit, hd⟩ := degree?_eq_some_high_bit h
  have hbitLt : bit < 64 := highestSetBit?_lt hbit
  have hwordIdx : d / 64 = p.words.size - 1 := by
    rw [hd, Nat.mul_add_div (by decide : 64 > 0), Nat.div_eq_of_lt hbitLt, Nat.add_zero]
  have hbitIdx : d % 64 = bit := by
    rw [hd, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hbitLt
  have hlastAt : p.words[p.words.size - 1]? = some last := by
    simpa [Array.back?_eq_getElem?] using hback
  simp [coeff, coeffWords, hwordIdx, hbitIdx, hlastAt, hwordBit]

/-- Every coefficient strictly above a successful `degree?` computation is clear. -/
theorem coeff_eq_false_of_degree?_lt {p : GF2Poly} {d n : Nat}
    (h : p.degree? = some d) (hdn : d < n) :
    p.coeff n = false := by
  obtain ⟨last, bit, hback, hbit, hd⟩ := degree?_eq_some_highestSetBit h
  have hbitLt : bit < 64 := highestSetBit?_lt hbit
  have hlastAt : p.words[p.words.size - 1]? = some last := by
    simpa [Array.back?_eq_getElem?] using hback
  have hsizePos : 0 < p.words.size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hnone : p.words[p.words.size - 1]? = none := by
      simp [hzero]
    rw [hnone] at hlastAt
    contradiction
  have hwordLe : p.words.size - 1 ≤ n / 64 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 64)]
    omega
  by_cases hsame : n / 64 = p.words.size - 1
  · have hnmodLt : n % 64 < 64 := Nat.mod_lt _ (by decide)
    have hnDecomp := Nat.div_add_mod n 64
    have hbitBelow : bit < n % 64 := by
      omega
    have hclear := highestSetBit?_above_bit hbit hnmodLt hbitBelow
    simp [coeff, coeffWords, hsame, hlastAt, hclear]
  · have hout : ¬ n / 64 < p.words.size := by
      omega
    simp [coeff, coeffWords, hout]

/-- If a coefficient is set and every higher coefficient is clear, the packed
degree search returns exactly that coefficient index. -/
theorem degree?_eq_some_of_coeff_eq_true_of_forall_gt_false {p : GF2Poly} {n : Nat}
    (hset : p.coeff n = true) (hclear : ∀ m, n < m → p.coeff m = false) :
    p.degree? = some n := by
  have hwords : p.words ≠ #[] := by
    intro hzero
    have hcoeff : p.coeff n = false := by
      simp [coeff, coeffWords, hzero]
    rw [hcoeff] at hset
    contradiction
  have hnonzero : p.isZero = false := (isZero_eq_false_iff_words_ne_empty p).mpr hwords
  obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hnonzero
  have hdset : p.coeff d = true := coeff_eq_true_of_degree?_eq_some hd
  have hnot_lt : ¬ d < n := by
    intro hdn
    have hnfalse := coeff_eq_false_of_degree?_lt hd hdn
    rw [hset] at hnfalse
    contradiction
  have hnot_gt : ¬ n < d := by
    intro hnd
    have hdfalse := hclear d hnd
    rw [hdset] at hdfalse
    contradiction
  have hdn : d = n := by omega
  simpa [hdn] using hd

/-- Coefficients outside the stored word range are clear. -/
theorem coeff_eq_false_of_wordCount_le (p : GF2Poly) {n : Nat}
    (h : p.wordCount ≤ n / 64) :
    p.coeff n = false := by
  have hnone : p.words[n / 64]? = none := by
    rw [Array.getElem?_eq_none_iff]
    simpa [wordCount] using h
  simp [coeff, coeffWords, hnone]

/-- Coefficientwise equality of normalized packed polynomials forces equal
stored word counts. -/
theorem wordCount_eq_of_coeff_eq {p q : GF2Poly}
    (hcoeff : ∀ n, p.coeff n = q.coeff n) :
    p.wordCount = q.wordCount := by
  rcases Nat.lt_trichotomy p.wordCount q.wordCount with hpq | hpq | hqp
  · have hqNonzero : q.isZero = false := by
      rw [isZero_eq_false_iff_words_ne_empty]
      intro hwords
      have hqCount : q.wordCount = 0 := by simp [wordCount, hwords]
      omega
    obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hqNonzero
    obtain ⟨_last, bit, _hback, hbit, hdEq⟩ := degree?_eq_some_highestSetBit hd
    have hbitLt : bit < 64 := highestSetBit?_lt hbit
    have hdword : d / 64 = q.words.size - 1 := by
      rw [hdEq, Nat.mul_add_div (by decide : 64 > 0), Nat.div_eq_of_lt hbitLt, Nat.add_zero]
    have hpClear : p.coeff d = false := by
      apply coeff_eq_false_of_wordCount_le
      have hpSize : p.words.size < q.words.size := by
        simpa [wordCount] using hpq
      rw [wordCount, hdword]
      omega
    have hqSet : q.coeff d = true := coeff_eq_true_of_degree?_eq_some hd
    have h := hcoeff d
    rw [hpClear, hqSet] at h
    contradiction
  · exact hpq
  · have hpNonzero : p.isZero = false := by
      rw [isZero_eq_false_iff_words_ne_empty]
      intro hwords
      have hpCount : p.wordCount = 0 := by simp [wordCount, hwords]
      omega
    obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hpNonzero
    obtain ⟨_last, bit, _hback, hbit, hdEq⟩ := degree?_eq_some_highestSetBit hd
    have hbitLt : bit < 64 := highestSetBit?_lt hbit
    have hdword : d / 64 = p.words.size - 1 := by
      rw [hdEq, Nat.mul_add_div (by decide : 64 > 0), Nat.div_eq_of_lt hbitLt, Nat.add_zero]
    have hqClear : q.coeff d = false := by
      apply coeff_eq_false_of_wordCount_le
      have hqSize : q.words.size < p.words.size := by
        simpa [wordCount] using hqp
      rw [wordCount, hdword]
      omega
    have hpSet : p.coeff d = true := coeff_eq_true_of_degree?_eq_some hd
    have h := hcoeff d
    rw [hpSet, hqClear] at h
    contradiction

/-- Extensionality for normalized packed polynomials when stored word counts
agree and every packed coefficient agrees. -/
@[ext] theorem ext_of_wordCount_eq {p q : GF2Poly}
    (hsize : p.wordCount = q.wordCount)
    (hcoeff : ∀ n, p.coeff n = q.coeff n) :
    p = q := by
  apply ext_words
  apply Array.ext
  · simpa [wordCount] using hsize
  · intro i hi₁ hi₂
    apply UInt64.toNat_inj.mp
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 64
    · have hdiv : (64 * i + j) / 64 = i := by
        rw [Nat.mul_add_div (by decide : 64 > 0), Nat.div_eq_of_lt hj, Nat.add_zero]
      have hmod : (64 * i + j) % 64 = j := by
        rw [Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt hj
      have hpget : p.words[i]? = some p.words[i] := by simp [hi₁]
      have hqget : q.words[i]? = some q.words[i] := by simp [hi₂]
      have hbit :
          wordBitIsSet p.words[i] j = wordBitIsSet q.words[i] j := by
        simpa [coeff, coeffWords, wordBitIsSet, hdiv, hmod, hpget, hqget] using
          hcoeff (64 * i + j)
      simpa [UInt64.wordBitIsSet_eq_testBit _ hj] using hbit
    · have hpFalse : p.words[i].toNat.testBit j = false := by
        apply Nat.testBit_eq_false_of_lt
        have hlt : p.words[i].toNat < 2 ^ 64 := by
          simpa [UInt64.size] using UInt64.toNat_lt_size p.words[i]
        exact Nat.lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hj))
      have hqFalse : q.words[i].toNat.testBit j = false := by
        apply Nat.testBit_eq_false_of_lt
        have hlt : q.words[i].toNat < 2 ^ 64 := by
          simpa [UInt64.size] using UInt64.toNat_lt_size q.words[i]
        exact Nat.lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hj))
      simp [hpFalse, hqFalse]

/-- Extensionality for normalized packed polynomials by their coefficient
functions. -/
theorem ext_coeff {p q : GF2Poly}
    (hcoeff : ∀ n, p.coeff n = q.coeff n) :
    p = q := by
  apply ext_of_wordCount_eq (wordCount_eq_of_coeff_eq hcoeff)
  exact hcoeff

/-- The zero polynomial is canonically represented by the empty word array. -/
@[simp, grind =] theorem words_zero : (0 : GF2Poly).words = #[] := by
  rfl

/-- The zero polynomial stores no machine words. -/
@[simp, grind =] theorem wordCount_zero : (0 : GF2Poly).wordCount = 0 := by
  rfl

/-- The zero polynomial passes the `isZero` Boolean check. -/
@[simp, grind =] theorem isZero_zero : (0 : GF2Poly).isZero = true := by
  rfl

/-- Every coefficient of the zero polynomial is clear. -/
@[simp, grind =] theorem coeff_zero (n : Nat) : (0 : GF2Poly).coeff n = false := by
  simp [coeff, coeffWords]

/-- The zero polynomial has no degree witness. -/
@[simp, grind =] theorem degree?_zero : (0 : GF2Poly).degree? = none := by
  rfl

/-- The default-`0` degree of the zero polynomial is `0`. -/
@[simp, grind =] theorem degree_zero : (0 : GF2Poly).degree = 0 := by
  rfl

/-- Word-wise XOR of packed coefficient arrays. -/
def xorWords (xs ys : Array UInt64) : Array UInt64 :=
  Array.ofFn fun i : Fin (max xs.size ys.size) => xs.getD i.1 0 ^^^ ys.getD i.1 0

/-- Raw XOR output has one word for every word position present in either
input. -/
@[simp, grind =] theorem xorWords_size (xs ys : Array UInt64) :
    (xorWords xs ys).size = max xs.size ys.size := by
  simp [xorWords]

/-- In-bounds `getD` from an `Array.ofFn` recovers the function value. -/
theorem Array.getD_ofFn_lt {α : Type u} [Inhabited α] {n : Nat}
    (f : Fin n → α) {i : Nat} (hi : i < n) :
    (Array.ofFn f).getD i default = f ⟨i, hi⟩ := by
  simp [Array.getD, hi]

/-- Out-of-bounds `getD` from an `Array.ofFn` returns the default value. -/
theorem Array.getD_ofFn_ge {α : Type u} [Inhabited α] {n : Nat}
    (f : Fin n → α) {i : Nat} (hi : n ≤ i) :
    (Array.ofFn f).getD i default = default := by
  simp [Array.getD, Nat.not_lt.mpr hi]

/-- Raw XOR word lookup agrees with defaulted lookup from the two inputs. -/
theorem xorWords_getD (xs ys : Array UInt64) (i : Nat) :
    (xorWords xs ys).getD i 0 = xs.getD i 0 ^^^ ys.getD i 0 := by
  by_cases hi : i < max xs.size ys.size
  · simpa [xorWords] using
      (Array.getD_ofFn_lt
        (fun i : Fin (max xs.size ys.size) => xs.getD i.1 0 ^^^ ys.getD i.1 0)
        hi)
  · have hge : max xs.size ys.size ≤ i := Nat.le_of_not_gt hi
    have hxs : xs.size ≤ i := Nat.le_trans (Nat.le_max_left xs.size ys.size) hge
    have hys : ys.size ≤ i := Nat.le_trans (Nat.le_max_right xs.size ys.size) hge
    simp [xorWords, Array.getD, Nat.not_lt.mpr hxs, Nat.not_lt.mpr hys]

/-- Optional raw XOR word lookup agrees with optional lookup from the two
inputs. -/
theorem xorWords_get?_getD (xs ys : Array UInt64) (i : Nat) :
    ((xorWords xs ys)[i]?).getD 0 = (xs[i]?).getD 0 ^^^ (ys[i]?).getD 0 := by
  by_cases hi : i < max xs.size ys.size
  · by_cases hxs : i < xs.size <;> by_cases hys : i < ys.size <;>
      simp [xorWords, hi, hxs, hys, Array.getD]
  · have hge : max xs.size ys.size ≤ i := Nat.le_of_not_gt hi
    have hxs : xs.size ≤ i := Nat.le_trans (Nat.le_max_left xs.size ys.size) hge
    have hys : ys.size ≤ i := Nat.le_trans (Nat.le_max_right xs.size ys.size) hge
    simp [xorWords, hi, Nat.not_lt.mpr hxs, Nat.not_lt.mpr hys]

/-- Addition in `F_2[x]` is coefficientwise XOR. -/
def add (p q : GF2Poly) : GF2Poly :=
  ofWords (xorWords p.words q.words)

instance : Add GF2Poly where
  add := add

/-- Addition coefficients are the normalized packed XOR of the input words. -/
theorem coeff_add (p q : GF2Poly) (n : Nat) :
    (p + q).coeff n = coeffWords (xorWords p.words q.words) n := by
  change (add p q).coeff n = coeffWords (xorWords p.words q.words) n
  simp [add]

/-- Addition over packed `GF(2)` polynomials is coefficientwise XOR. -/
theorem coeff_add_eq_bne (p q : GF2Poly) (n : Nat) :
    (p + q).coeff n = (p.coeff n != q.coeff n) := by
  rw [coeff_add]
  simp [coeffWords, xorWords_get?_getD, coeff, UInt64.bit_xor_bne]

/-- The single-word constructor maps machine-word XOR to polynomial addition. -/
theorem ofUInt64_xor (a b : UInt64) :
    ofUInt64 (a ^^^ b) = ofUInt64 a + ofUInt64 b := by
  apply ext_coeff
  intro i
  by_cases hi : i < 64
  · rw [coeff_ofUInt64_eq_testBit _ hi, coeff_add_eq_bne,
      coeff_ofUInt64_eq_testBit _ hi, coeff_ofUInt64_eq_testBit _ hi]
    simp [UInt64.toNat_xor, Nat.testBit_xor]
  · have hge : 64 ≤ i := Nat.le_of_not_gt hi
    rw [coeff_ofUInt64_eq_false_of_ge_64 _ hge, coeff_add_eq_bne,
      coeff_ofUInt64_eq_false_of_ge_64 _ hge, coeff_ofUInt64_eq_false_of_ge_64 _ hge]
    rfl

/-- Simp-facing packed addition law for single-word constructors. -/
@[simp, grind =] theorem ofUInt64_add (a b : UInt64) :
    ofUInt64 a + ofUInt64 b = ofUInt64 (a ^^^ b) :=
  (ofUInt64_xor a b).symm

/-- Simp-facing form of coefficientwise addition over packed `GF(2)` polynomials. -/
@[simp, grind =] theorem coeff_add_bne (p q : GF2Poly) (n : Nat) :
    (p + q).coeff n = (p.coeff n != q.coeff n) :=
  coeff_add_eq_bne p q n

/-- Equal set coefficients cancel under `GF(2)` addition. -/
theorem coeff_add_of_true_true {p q : GF2Poly} {n : Nat}
    (hp : p.coeff n = true) (hq : q.coeff n = true) :
    (p + q).coeff n = false := by
  rw [coeff_add_bne, hp, hq]
  rfl

/-- A set left coefficient and clear right coefficient remain set under
`GF(2)` addition. -/
theorem coeff_add_of_true_false {p q : GF2Poly} {n : Nat}
    (hp : p.coeff n = true) (hq : q.coeff n = false) :
    (p + q).coeff n = true := by
  rw [coeff_add_bne, hp, hq]
  rfl

/-- A clear left coefficient and set right coefficient remain set under
`GF(2)` addition. -/
theorem coeff_add_of_false_true {p q : GF2Poly} {n : Nat}
    (hp : p.coeff n = false) (hq : q.coeff n = true) :
    (p + q).coeff n = true := by
  rw [coeff_add_bne, hp, hq]
  rfl

/-- Clear coefficients remain clear under `GF(2)` addition. -/
theorem coeff_add_of_false_false {p q : GF2Poly} {n : Nat}
    (hp : p.coeff n = false) (hq : q.coeff n = false) :
    (p + q).coeff n = false := by
  rw [coeff_add_bne, hp, hq]
  rfl

/-- Raw packed addition cancels each word against itself. -/
theorem xorWords_self_getD (xs : Array UInt64) (i : Nat) :
    (xorWords xs xs).getD i 0 = 0 := by
  rw [xorWords_getD]
  simp

/-- Coefficient lookup sees the raw packed sum of an array with itself as
zero. -/
theorem coeffWords_xorWords_self (xs : Array UInt64) (n : Nat) :
    coeffWords (xorWords xs xs) n = false := by
  simp [coeffWords, xorWords_get?_getD]

/-- Every packed coefficient of `p + p` is zero in characteristic two. -/
theorem coeff_add_self (p : GF2Poly) (n : Nat) :
    (p + p).coeff n = false := by
  rw [coeff_add, coeffWords_xorWords_self]

/-- Simp-facing coefficient form of characteristic-two self-cancellation. -/
@[simp, grind =] theorem coeff_add_self_false (p : GF2Poly) (n : Nat) :
    (p + p).coeff n = false :=
  coeff_add_self p n

private theorem trimTrailingZeroWordsList_replicate_zero (n : Nat) :
    trimTrailingZeroWordsList (List.replicate n (0 : UInt64)) = [] := by
  induction n with
  | zero =>
      simp [trimTrailingZeroWordsList]
  | succ n ih =>
      change trimTrailingZeroWordsList ((0 : UInt64) :: List.replicate n 0) = []
      simp [trimTrailingZeroWordsList, ih]

private theorem trimTrailingZeroWordsList_replicate_zero_append_nonzero
    (n : Nat) {w : UInt64} (hw : w ≠ 0) :
    trimTrailingZeroWordsList (List.replicate n (0 : UInt64) ++ [w]) =
      List.replicate n (0 : UInt64) ++ [w] := by
  induction n with
  | zero =>
      simp [trimTrailingZeroWordsList, hw]
  | succ n ih =>
      change
        trimTrailingZeroWordsList
            ((0 : UInt64) :: (List.replicate n (0 : UInt64) ++ [w])) =
          (0 : UInt64) :: (List.replicate n (0 : UInt64) ++ [w])
      simp [trimTrailingZeroWordsList, ih]

/-- Normalization wipes an all-zero packed word array down to the canonical empty array. -/
theorem normalizeWords_replicate_zero (n : Nat) :
    normalizeWords (Array.replicate n (0 : UInt64)) = #[] := by
  simp [normalizeWords, trimTrailingZeroWordsList_replicate_zero]

/-- Raw packed XOR of a word array with itself produces the all-zero array of the same size. -/
theorem xorWords_self (xs : Array UInt64) :
    xorWords xs xs = Array.replicate xs.size (0 : UInt64) := by
  apply Array.ext
  · simp [xorWords]
  · intro i _ _
    simp [xorWords]

/-- Every element of `F_2[x]` is its own additive inverse: `p + p = 0`. -/
@[simp, grind =] theorem add_self (p : GF2Poly) :
    p + p = 0 := by
  apply ext_words
  change (ofWords (xorWords p.words p.words)).words = #[]
  calc
    (ofWords (xorWords p.words p.words)).words
        = (ofWords (Array.replicate p.words.size (0 : UInt64))).words := by
          exact congrArg (fun words => (ofWords words).words) (xorWords_self p.words)
    _ = #[] := by
          simp [ofWords, normalizeWords_replicate_zero]

/-- Zero is the left identity for `F_2[x]` addition. -/
@[simp, grind =] theorem zero_add (p : GF2Poly) :
    0 + p = p := by
  apply ext_coeff
  intro n
  simp

/-- Adding zero on the left leaves packed `GF(2)` coefficients unchanged. -/
@[simp, grind =] theorem coeff_add_zero_left_bool (p : GF2Poly) (n : Nat) :
    (0 + p).coeff n = p.coeff n := by
  simp

/-- Adding zero on the right leaves packed `GF(2)` coefficients unchanged. -/
@[simp, grind =] theorem coeff_add_zero_right_bool (p : GF2Poly) (n : Nat) :
    (p + 0).coeff n = p.coeff n := by
  simp

/-- Zero is the right identity for `F_2[x]` addition. -/
@[simp, grind =] theorem add_zero (p : GF2Poly) :
    p + 0 = p := by
  apply ext_coeff
  intro n
  simp

/-- Packed `F_2[x]` addition is commutative. -/
theorem add_comm (p q : GF2Poly) :
    p + q = q + p := by
  apply ext_coeff
  intro n
  rw [coeff_add_bne, coeff_add_bne]
  cases p.coeff n <;> cases q.coeff n <;> rfl

/-- Packed `F_2[x]` addition is associative. -/
theorem add_assoc (p q r : GF2Poly) :
    (p + q) + r = p + (q + r) := by
  apply ext_coeff
  intro n
  rw [coeff_add_bne, coeff_add_bne, coeff_add_bne, coeff_add_bne]
  cases p.coeff n <;> cases q.coeff n <;> cases r.coeff n <;> rfl

/-- Adding `p` twice on the left cancels: `p + (p + q) = q`. -/
@[simp, grind =] theorem add_add_cancel_left (p q : GF2Poly) :
    p + (p + q) = q := by
  apply ext_coeff
  intro n
  rw [coeff_add_bne, coeff_add_bne]
  cases p.coeff n <;> cases q.coeff n <;> rfl

/-- Adding `q` twice on the right cancels: `(p + q) + q = p`. -/
@[simp, grind =] theorem add_add_cancel_right (p q : GF2Poly) :
    (p + q) + q = p := by
  apply ext_coeff
  intro n
  rw [coeff_add_bne, coeff_add_bne]
  cases p.coeff n <;> cases q.coeff n <;> rfl

/-- Shift a normalized word list left by `bitShift ∈ [1, 63]`. -/
def shiftLeftBitsList (bitShift : Nat) (carry : UInt64) : List UInt64 → List UInt64
  | [] =>
      if carry = 0 then [] else [carry]
  | w :: ws =>
      let out := (w <<< bitShift.toUInt64) ||| carry
      let nextCarry := w >>> (64 - bitShift).toUInt64
      out :: shiftLeftBitsList bitShift nextCarry ws

/-- A bit that stays inside the same machine word after the sub-word shift
(`old + shift < 64`) reads the same as the source bit, for any previous-word
carry threaded into the head. The carry-parametrised core behind the public
`coeffWords_shiftLeftBitsList_same_word` assembly theorem. -/
private theorem shiftLeftBitsList_getD_high_bit_with_prev
    (ws : List UInt64) (prev : UInt64) {shift i old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hi : i < ws.length) (hold : old < 64) (htarget : old + shift < 64) :
    (((((shiftLeftBitsList shift (prev >>> (64 - shift).toUInt64) ws).getD i 0) >>>
          (old + shift).toUInt64) &&& 1) != 0) =
      (((((ws.getD i 0) >>> old.toUInt64) &&& 1) != 0)) := by
  induction ws generalizing i prev with
  | nil =>
      simp at hi
  | cons w ws ih =>
      cases i with
      | zero =>
          simpa [shiftLeftBitsList, List.getD] using
            UInt64.shiftLeft_or_carry_high_bit
              w prev hshiftPos hshift hold htarget
      | succ i =>
          have hi' : i < ws.length := by simpa using hi
          simpa [shiftLeftBitsList, List.getD] using
            ih (prev := w) hi'

/-- Zero-carry specialisation of `shiftLeftBitsList_getD_high_bit_with_prev`: a
bit that stays inside the same machine word (`old + shift < 64`) reads the same
as the source bit. -/
private theorem shiftLeftBitsList_getD_high_bit
    (ws : List UInt64) {shift i old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hi : i < ws.length) (hold : old < 64) (htarget : old + shift < 64) :
    (((((shiftLeftBitsList shift 0 ws).getD i 0) >>>
          (old + shift).toUInt64) &&& 1) != 0) =
      (((((ws.getD i 0) >>> old.toUInt64) &&& 1) != 0)) := by
  simpa using
    (shiftLeftBitsList_getD_high_bit_with_prev
      (ws := ws) (prev := 0) hshiftPos hshift hi hold htarget)

/-- A bit pushed past the word boundary (`64 ≤ old + shift`) reads from the
previous word's high bits at index `0` of the shifted list. -/
private theorem shiftLeftBitsList_getD_carry_bit
    (ws : List UInt64) (prev : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hold : old < 64) (htarget : 64 ≤ old + shift) :
    (((((shiftLeftBitsList shift (prev >>> (64 - shift).toUInt64) ws).getD 0 0) >>>
          (old + shift - 64).toUInt64) &&& 1) != 0) =
      (((prev >>> old.toUInt64) &&& 1) != 0) := by
  cases ws with
  | nil =>
      have hget :
          (shiftLeftBitsList shift (prev >>> (64 - shift).toUInt64) []).getD 0 0 =
            prev >>> (64 - shift).toUInt64 := by
        by_cases hcarry : prev >>> (64 - shift).toUInt64 = 0 <;>
          simp [shiftLeftBitsList, hcarry]
      rw [hget]
      simpa using
        UInt64.shiftLeft_or_carry_low_bit
          (0 : UInt64) prev hshiftPos hshift hold htarget
  | cons w ws =>
      simpa [shiftLeftBitsList, List.getD] using
        UInt64.shiftLeft_or_carry_low_bit
          w prev hshiftPos hshift hold htarget

/-- The carried-out low bits land in the next word (index `i + 1`) and match the
source bit, for any previous-word carry threaded into the head. -/
private theorem shiftLeftBitsList_getD_low_bit_with_prev
    (ws : List UInt64) (prev : UInt64) {shift i old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hi : i < ws.length) (hold : old < 64) (htarget : 64 ≤ old + shift) :
    (((((shiftLeftBitsList shift (prev >>> (64 - shift).toUInt64) ws).getD (i + 1) 0) >>>
          (old + shift - 64).toUInt64) &&& 1) != 0) =
      (((((ws.getD i 0) >>> old.toUInt64) &&& 1) != 0)) := by
  induction ws generalizing i prev with
  | nil =>
      simp at hi
  | cons w ws ih =>
      cases i with
      | zero =>
          simpa [shiftLeftBitsList, List.getD] using
            shiftLeftBitsList_getD_carry_bit
              (ws := ws) (prev := w) hshiftPos hshift hold htarget
      | succ i =>
          have hi' : i < ws.length := by simpa using hi
          simpa [shiftLeftBitsList, List.getD, Nat.add_assoc] using
            ih (prev := w) hi'

/-- Zero-carry specialisation of `shiftLeftBitsList_getD_low_bit_with_prev`: a
carried-out bit (`64 ≤ old + shift`) reads from index `i + 1` and matches the
source bit. -/
private theorem shiftLeftBitsList_getD_low_bit
    (ws : List UInt64) {shift i old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hi : i < ws.length) (hold : old < 64) (htarget : 64 ≤ old + shift) :
    (((((shiftLeftBitsList shift 0 ws).getD (i + 1) 0) >>>
          (old + shift - 64).toUInt64) &&& 1) != 0) =
      (((((ws.getD i 0) >>> old.toUInt64) &&& 1) != 0)) := by
  simpa using
    (shiftLeftBitsList_getD_low_bit_with_prev
      (ws := ws) (prev := 0) hshiftPos hshift hi hold htarget)

/-- Sub-word `shiftLeftBitsList` preserves the source coefficient when the
shifted bit stays inside the same machine word. -/
theorem coeffWords_shiftLeftBitsList_same_word
    (words : Array UInt64) {shift n : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hword : n / 64 < words.size) (hbit : n % 64 + shift < 64) :
    coeffWords (shiftLeftBitsList shift 0 words.toList).toArray (n + shift) =
      coeffWords words n := by
  have hnbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have hdiv : (n + shift) / 64 = n / 64 := by
    have hn := Nat.div_add_mod n 64
    omega
  have hmod : (n + shift) % 64 = n % 64 + shift := by
    have hn := Nat.div_add_mod n 64
    omega
  have hgetShift :
      (((shiftLeftBitsList shift 0 words.toList).toArray)[n / 64]?).getD 0 =
        (shiftLeftBitsList shift 0 words.toList).getD (n / 64) 0 := by
    simp
  have hgetWords :
      (words.toList.getD (n / 64) 0) = (words[n / 64]?).getD 0 := by
    simp
  rw [coeffWords, coeffWords, hdiv, hmod, hgetShift, ← hgetWords]
  exact shiftLeftBitsList_getD_high_bit
    (ws := words.toList) hshiftPos hshift (by simpa using hword) hnbit hbit

/-- Sub-word `shiftLeftBitsList` preserves the source coefficient when the
shifted bit crosses into the next machine word. -/
theorem coeffWords_shiftLeftBitsList_carry_word
    (words : Array UInt64) {shift n : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hword : n / 64 < words.size) (hbit : 64 ≤ n % 64 + shift) :
    coeffWords (shiftLeftBitsList shift 0 words.toList).toArray (n + shift) =
      coeffWords words n := by
  have hnbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have htargetLt : n % 64 + shift - 64 < 64 := by omega
  have hdiv : (n + shift) / 64 = n / 64 + 1 := by
    have hn := Nat.div_add_mod n 64
    omega
  have hmod : (n + shift) % 64 = n % 64 + shift - 64 := by
    have hn := Nat.div_add_mod n 64
    omega
  have hgetShift :
      (((shiftLeftBitsList shift 0 words.toList).toArray)[n / 64 + 1]?).getD 0 =
        (shiftLeftBitsList shift 0 words.toList).getD (n / 64 + 1) 0 := by
    simp
  have hgetWords :
      (words.toList.getD (n / 64) 0) = (words[n / 64]?).getD 0 := by
    simp
  rw [coeffWords, coeffWords, hdiv, hmod, hgetShift, ← hgetWords]
  exact shiftLeftBitsList_getD_low_bit
    (ws := words.toList) hshiftPos hshift (by simpa using hword) hnbit hbit

/-- Sub-word `shiftLeftBitsList` preserves every source coefficient stored in
the input words. -/
theorem coeffWords_shiftLeftBitsList_add
    (words : Array UInt64) {shift n : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hword : n / 64 < words.size) :
    coeffWords (shiftLeftBitsList shift 0 words.toList).toArray (n + shift) =
      coeffWords words n := by
  by_cases hbit : n % 64 + shift < 64
  · exact coeffWords_shiftLeftBitsList_same_word words hshiftPos hshift hword hbit
  · exact coeffWords_shiftLeftBitsList_carry_word words hshiftPos hshift hword
      (Nat.le_of_not_gt hbit)

/-- The full shift-left assembly preserves the source coefficient at every
in-bounds index when the bit-shift component is nonzero. -/
theorem coeffWords_replicate_append_shiftLeftBitsList_add
    (words : Array UInt64) {k n : Nat}
    (hbitShift : k % 64 ≠ 0) (hword : n / 64 < words.size) :
    coeffWords
        ((Array.replicate (k / 64) (0 : UInt64)) ++
          (shiftLeftBitsList (k % 64) 0 words.toList).toArray)
        (n + k) =
      coeffWords words n := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  by_cases hbit : n % 64 + k % 64 < 64
  · have hdiv : (n + k) / 64 = k / 64 + n / 64 := by
      have hn := Nat.div_add_mod n 64
      have hk := Nat.div_add_mod k 64
      omega
    have hmod : (n + k) % 64 = n % 64 + k % 64 := by
      have hn := Nat.div_add_mod n 64
      have hk := Nat.div_add_mod k 64
      omega
    have hlocalDiv : (n + k % 64) / 64 = n / 64 := by
      have hn := Nat.div_add_mod n 64
      omega
    have hget :
        (((Array.replicate (k / 64) (0 : UInt64)) ++
              (shiftLeftBitsList (k % 64) 0 words.toList).toArray)[k / 64 + n / 64]?).getD 0 =
          (((shiftLeftBitsList (k % 64) 0 words.toList).toArray)[n / 64]?).getD 0 := by
      rw [Array.getElem?_append_right]
      · simp
      · simp
    simpa [coeffWords, hdiv, hmod, hlocalDiv, hget] using
      coeffWords_shiftLeftBitsList_same_word
        words hshiftPos hshift hword hbit
  · have hcarry : 64 ≤ n % 64 + k % 64 := Nat.le_of_not_gt hbit
    have hdiv : (n + k) / 64 = k / 64 + (n / 64 + 1) := by
      have hn := Nat.div_add_mod n 64
      have hk := Nat.div_add_mod k 64
      omega
    have hmod : (n + k) % 64 = n % 64 + k % 64 - 64 := by
      have hn := Nat.div_add_mod n 64
      have hk := Nat.div_add_mod k 64
      omega
    have hlocalDiv : (n + k % 64) / 64 = n / 64 + 1 := by
      have hn := Nat.div_add_mod n 64
      omega
    have hget :
        (((Array.replicate (k / 64) (0 : UInt64)) ++
              (shiftLeftBitsList (k % 64) 0 words.toList).toArray)[k / 64 + (n / 64 + 1)]?).getD 0 =
          (((shiftLeftBitsList (k % 64) 0 words.toList).toArray)[n / 64 + 1]?).getD 0 := by
      rw [Array.getElem?_append_right]
      · simp
      · simp
    simpa [coeffWords, hdiv, hmod, hlocalDiv, hget] using
      coeffWords_shiftLeftBitsList_carry_word
        words hshiftPos hshift hword hcarry

/-- A word-aligned shift-left assembly preserves every source coefficient
(no in-word bit shift is needed). -/
theorem coeffWords_replicate_append_add_of_mod_eq_zero
    (words : Array UInt64) {k n : Nat} (hbitShift : k % 64 = 0) :
    coeffWords ((Array.replicate (k / 64) (0 : UInt64)) ++ words) (n + k) =
      coeffWords words n := by
  have hdiv : (n + k) / 64 = k / 64 + n / 64 := by
    have hn := Nat.div_add_mod n 64
    have hk := Nat.div_add_mod k 64
    omega
  have hmod : (n + k) % 64 = n % 64 := by
    have hn := Nat.div_add_mod n 64
    have hk := Nat.div_add_mod k 64
    omega
  have hget :
      (((Array.replicate (k / 64) (0 : UInt64)) ++ words)[k / 64 + n / 64]?).getD 0 =
        (words[n / 64]?).getD 0 := by
    rw [Array.getElem?_append_right]
    · simp
    · simp
  simp [coeffWords, hdiv, hmod, hget]

/-- The shifted list grows by at most one word, the trailing carry word. -/
private theorem shiftLeftBitsList_length_le_succ
    (shift : Nat) (carry : UInt64) (ws : List UInt64) :
    (shiftLeftBitsList shift carry ws).length ≤ ws.length + 1 := by
  induction ws generalizing carry with
  | nil =>
      by_cases hcarry : carry = 0 <;> simp [shiftLeftBitsList, hcarry]
  | cons w ws ih =>
      simp [shiftLeftBitsList]
      exact ih (w >>> (64 - shift).toUInt64)

/-- Shifting a word right by `64 - shift` clears every bit at index `≥ shift`,
since those positions read beyond the word's high end. -/
private theorem UInt64.shiftRight_high_bit_false
    (w : UInt64) {shift bit : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hbit : bit < 64) (hle : shift ≤ bit) :
    (((((w >>> (64 - shift).toUInt64) >>> bit.toUInt64) &&& 1) != 0) = false) := by
  apply Bool.eq_false_iff.mpr
  intro hb
  have hne :
      (((w >>> (64 - shift).toUInt64) >>> bit.toUInt64) &&& 1) ≠ 0 :=
    bne_iff_ne.mp hb
  apply hne
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hbit]
  rw [← Nat.shiftRight_add, Nat.shiftRight_eq_div_pow]
  have hzero :
      w.toNat / 2 ^ ((64 - shift) % 64 + bit) = 0 := by
    apply Nat.div_eq_of_lt
    have hwlt : w.toNat < 2 ^ 64 := by
      simpa [UInt64.size] using UInt64.toNat_lt_size w
    refine Nat.lt_of_lt_of_le hwlt ?_
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    have hsub : (64 - shift) % 64 = 64 - shift := by
      apply Nat.mod_eq_of_lt
      omega
    omega
  simp [hzero]

/-- At the one-past-the-end carry word (index `ws.length`), every bit at index
`≥ shift` reads false, for any previous-word carry threaded into the head. -/
private theorem shiftLeftBitsList_getD_length_high_bit_false_with_prev
    (ws : List UInt64) (prev : UInt64) {shift bit : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hbit : bit < 64) (hle : shift ≤ bit) :
    (((((shiftLeftBitsList shift (prev >>> (64 - shift).toUInt64) ws).getD ws.length 0) >>>
          bit.toUInt64) &&& 1) != 0) = false := by
  induction ws generalizing prev with
  | nil =>
      by_cases hcarry : prev >>> (64 - shift).toUInt64 = 0
      · simp [shiftLeftBitsList, hcarry]
      · simpa [shiftLeftBitsList, hcarry] using
          UInt64.shiftRight_high_bit_false prev hshiftPos hshift hbit hle
  | cons w ws ih =>
      simpa [shiftLeftBitsList, List.getD] using
        ih w

/-- Zero-carry specialisation of
`shiftLeftBitsList_getD_length_high_bit_false_with_prev`: at the trailing carry
word every bit at index `≥ shift` reads false. -/
private theorem shiftLeftBitsList_getD_length_high_bit_false
    (ws : List UInt64) {shift bit : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hbit : bit < 64) (hle : shift ≤ bit) :
    (((((shiftLeftBitsList shift 0 ws).getD ws.length 0) >>>
          bit.toUInt64) &&& 1) != 0) = false := by
  cases ws with
  | nil =>
      simp [shiftLeftBitsList]
  | cons w ws =>
      simpa [shiftLeftBitsList, List.getD] using
        shiftLeftBitsList_getD_length_high_bit_false_with_prev
          ws w hshiftPos hshift hbit hle

/-- The full shift-left assembly returns a clear coefficient at any index whose
source word lies above the stored input. -/
theorem coeffWords_replicate_append_shiftLeftBitsList_add_of_not_word
    (words : Array UInt64) {k n : Nat}
    (hbitShift : k % 64 ≠ 0) (hword : ¬ n / 64 < words.size) :
    coeffWords
        ((Array.replicate (k / 64) (0 : UInt64)) ++
          (shiftLeftBitsList (k % 64) 0 words.toList).toArray)
        (n + k) =
      false := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  by_cases hbit : n % 64 + k % 64 < 64
  · have hdiv : (n + k) / 64 = k / 64 + n / 64 := by
      have hn := Nat.div_add_mod n 64
      have hk := Nat.div_add_mod k 64
      omega
    have hmod : (n + k) % 64 = n % 64 + k % 64 := by
      have hn := Nat.div_add_mod n 64
      have hk := Nat.div_add_mod k 64
      omega
    have hgetAppend :
        (((Array.replicate (k / 64) (0 : UInt64)) ++
              (shiftLeftBitsList (k % 64) 0 words.toList).toArray)[k / 64 + n / 64]?).getD 0 =
          (((shiftLeftBitsList (k % 64) 0 words.toList).toArray)[n / 64]?).getD 0 := by
      rw [Array.getElem?_append_right]
      · simp
      · simp
    by_cases hgt : words.size < n / 64
    · have hlen :=
        shiftLeftBitsList_length_le_succ (k % 64) 0 words.toList
      have hwordsLen : words.toList.length = words.size := by simp
      have hout :
          (shiftLeftBitsList (k % 64) 0 words.toList).length ≤ n / 64 := by
        exact Nat.le_trans hlen (by omega)
      have hnone :
          ((shiftLeftBitsList (k % 64) 0 words.toList).toArray)[n / 64]? = none := by
        rw [Array.getElem?_eq_none_iff]
        simpa using hout
      simp [coeffWords, hdiv, hmod, hgetAppend, hnone]
    · have hnsize : n / 64 = words.size := by omega
      have hgetList :
          (((shiftLeftBitsList (k % 64) 0 words.toList).toArray)[n / 64]?).getD 0 =
            (shiftLeftBitsList (k % 64) 0 words.toList).getD (n / 64) 0 := by
        simp [List.getD]
      have hclear :
          (((((shiftLeftBitsList (k % 64) 0 words.toList).getD (n / 64) 0) >>>
              (n % 64 + k % 64).toUInt64) &&& 1) != 0) = false := by
        rw [hnsize]
        simpa using
          shiftLeftBitsList_getD_length_high_bit_false
            words.toList hshiftPos hshift hbit (by omega)
      rw [coeffWords, hdiv, hmod, hgetAppend, hgetList]
      exact hclear
  · have hcarry : 64 ≤ n % 64 + k % 64 := Nat.le_of_not_gt hbit
    have hdiv : (n + k) / 64 = k / 64 + (n / 64 + 1) := by
      have hn := Nat.div_add_mod n 64
      have hk := Nat.div_add_mod k 64
      omega
    have hmod : (n + k) % 64 = n % 64 + k % 64 - 64 := by
      have hn := Nat.div_add_mod n 64
      have hk := Nat.div_add_mod k 64
      omega
    have hgetAppend :
        (((Array.replicate (k / 64) (0 : UInt64)) ++
              (shiftLeftBitsList (k % 64) 0 words.toList).toArray)[k / 64 + (n / 64 + 1)]?).getD 0 =
          (((shiftLeftBitsList (k % 64) 0 words.toList).toArray)[n / 64 + 1]?).getD 0 := by
      rw [Array.getElem?_append_right]
      · simp
      · simp
    have hlen :=
      shiftLeftBitsList_length_le_succ (k % 64) 0 words.toList
    have hwordsLen : words.toList.length = words.size := by simp
    have hout :
        (shiftLeftBitsList (k % 64) 0 words.toList).length ≤ n / 64 + 1 := by
      exact Nat.le_trans hlen (by omega)
    have hnone :
        ((shiftLeftBitsList (k % 64) 0 words.toList).toArray)[n / 64 + 1]? = none := by
      rw [Array.getElem?_eq_none_iff]
      simpa using hout
    simp [coeffWords, hdiv, hmod, hgetAppend, hnone]

/-- The full shift-left assembly returns a clear coefficient strictly below the
shift amount: indices below `k` are zero-padded. -/
theorem coeffWords_replicate_append_shiftLeftBitsList_lt
    (words : Array UInt64) {k n : Nat}
    (_hbitShift : k % 64 ≠ 0) (hn : n < k) :
    coeffWords
        ((Array.replicate (k / 64) (0 : UInt64)) ++
          (shiftLeftBitsList (k % 64) 0 words.toList).toArray)
        n =
      false := by
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  by_cases hword : n / 64 < k / 64
  · rw [coeffWords]
    have hget :
        (((Array.replicate (k / 64) (0 : UInt64)) ++
            (shiftLeftBitsList (k % 64) 0 words.toList).toArray)[n / 64]?).getD 0 = 0 := by
      rw [Array.getElem?_append_left]
      · simp [hword]
      · simp [hword]
    rw [hget, UInt64.bne_zero_eq_toNat_bne_zero]
    simp
  · have hdiv : n / 64 = k / 64 := by
      have hnSplit := Nat.div_add_mod n 64
      have hkSplit := Nat.div_add_mod k 64
      have hnBit := Nat.mod_lt n (by decide : 0 < 64)
      have hkBit := Nat.mod_lt k (by decide : 0 < 64)
      omega
    have hbit : n % 64 < k % 64 := by
      have hnSplit := Nat.div_add_mod n 64
      have hkSplit := Nat.div_add_mod k 64
      have hnBit := Nat.mod_lt n (by decide : 0 < 64)
      have hkBit := Nat.mod_lt k (by decide : 0 < 64)
      omega
    have hnBit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
    rw [coeffWords, hdiv]
    have hgetAppend :
        (((Array.replicate (k / 64) (0 : UInt64)) ++
            (shiftLeftBitsList (k % 64) 0 words.toList).toArray)[k / 64]?).getD 0 =
          (((shiftLeftBitsList (k % 64) 0 words.toList).toArray)[0]?).getD 0 := by
      rw [Array.getElem?_append_right]
      · simp
      · simp
    rw [hgetAppend]
    cases hws : words.toList with
    | nil =>
        simp [shiftLeftBitsList]
    | cons w ws =>
        have hbitClear :
            (((((w <<< (k % 64).toUInt64) ||| (0 : UInt64)) >>>
                (n % 64).toUInt64) &&& 1) != 0) = false := by
          rw [UInt64.bne_zero_eq_toNat_bne_zero]
          simp [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
            UInt64.toNat_and, Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hnBit,
            bit_eq_one_eq_testBit]
          change (((w.toNat <<< (k % 64)) % 18446744073709551616).testBit (n % 64)) =
            false
          rw [show 18446744073709551616 = 2 ^ 64 by rfl, Nat.testBit_mod_two_pow,
            Nat.testBit_shiftLeft]
          simp [hnBit, Nat.not_le.mpr hbit]
        simpa [shiftLeftBitsList, hws] using hbitClear

/-- Shift packed words right by `bitShift ∈ [1, 63]`, reading the input from
high degree to low degree. -/
private def shiftRightBitsRevList (bitShift : Nat) (carry : UInt64) :
    List UInt64 → List UInt64
  | [] => []
  | w :: ws =>
      let out := (w >>> bitShift.toUInt64) ||| carry
      let nextCarry := w <<< (64 - bitShift).toUInt64
      out :: shiftRightBitsRevList bitShift nextCarry ws

/-- Multiply by `x^k`. -/
def shiftLeft (p : GF2Poly) (k : Nat) : GF2Poly :=
  let wordShift := k / 64
  let bitShift := k % 64
  let shiftedBits :=
    if bitShift = 0 then
      p.words
    else
      (shiftLeftBitsList bitShift 0 p.words.toList).toArray
  ofWords <| (Array.replicate wordShift (0 : UInt64)) ++ shiftedBits

/-- Divide by `x^k`, discarding the remainder. -/
def shiftRight (p : GF2Poly) (k : Nat) : GF2Poly :=
  let wordShift := k / 64
  let bitShift := k % 64
  let dropped := (p.words.toList.drop wordShift).toArray
  let shiftedBits :=
    if bitShift = 0 then
      dropped
    else
      ((shiftRightBitsRevList bitShift 0 dropped.toList.reverse).reverse).toArray
  ofWords shiftedBits

/-- Alias for multiplication by a power of `x`. -/
def mulXk (p : GF2Poly) (k : Nat) : GF2Poly :=
  shiftLeft p k

/-- Monomial coefficients reduce to the coefficient lookup on its packed word array. -/
theorem coeff_monomial (n m : Nat) :
    (monomial n).coeff m =
      coeffWords
        ((Array.replicate (n / 64) (0 : UInt64)).push ((1 : UInt64) <<< (n % 64).toUInt64))
        m := by
  simp [monomial]

/-- The coefficient of the defining degree of a monomial is set. -/
@[simp, grind =] theorem coeff_monomial_self (n : Nat) :
    (monomial n).coeff n = true := by
  rw [coeff_monomial]
  have hbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have hget :
      (((Array.replicate (n / 64) (0 : UInt64)).push
          ((1 : UInt64) <<< (n % 64).toUInt64))[n / 64]?).getD 0 =
        ((1 : UInt64) <<< (n % 64).toUInt64) := by
    simpa using
      (Array.getElem?_push_size
        (xs := Array.replicate (n / 64) (0 : UInt64))
        (x := ((1 : UInt64) <<< (n % 64).toUInt64)))
  rw [coeffWords, hget]
  exact oneHotWord_bit_self hbit

/-- The normalized storage of a monomial is its zero prefix plus one nonzero
one-hot word. -/
theorem words_monomial (n : Nat) :
    (monomial n).words =
      (Array.replicate (n / 64) (0 : UInt64)).push
        ((1 : UInt64) <<< (n % 64).toUInt64) := by
  have hbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have hne : ((1 : UInt64) <<< (n % 64).toUInt64) ≠ 0 :=
    oneHotWord_ne_zero hbit
  unfold monomial ofWords normalizeWords
  apply Array.toList_inj.mp
  simp [trimTrailingZeroWordsList_replicate_zero_append_nonzero (n / 64) hne]

/-- Coefficients away from the defining degree of a monomial are clear. -/
theorem coeff_monomial_ne {n m : Nat} (h : m ≠ n) :
    (monomial n).coeff m = false := by
  rw [coeff_monomial]
  by_cases hword : m / 64 = n / 64
  · have hbit_ne : m % 64 ≠ n % 64 := by
      intro hbit
      apply h
      exact Nat.div_add_mod m 64 ▸ Nat.div_add_mod n 64 ▸ by omega
    have hm_bit : m % 64 < 64 := Nat.mod_lt m (by decide : 0 < 64)
    have hn_bit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
    have hget :
        (((Array.replicate (n / 64) (0 : UInt64)).push
            ((1 : UInt64) <<< (n % 64).toUInt64))[m / 64]?).getD 0 =
          ((1 : UInt64) <<< (n % 64).toUInt64) := by
      rw [hword]
      simpa using
        (Array.getElem?_push_size
          (xs := Array.replicate (n / 64) (0 : UInt64))
          (x := ((1 : UInt64) <<< (n % 64).toUInt64)))
    rw [coeffWords, hget]
    exact oneHotWord_bit_ne hn_bit hm_bit hbit_ne.symm
  · have hm_word_ne : m / 64 ≠ n / 64 := hword
    have hget :
        (((Array.replicate (n / 64) (0 : UInt64)).push
            ((1 : UInt64) <<< (n % 64).toUInt64))[m / 64]?).getD 0 = 0 := by
      by_cases hlt : m / 64 < n / 64
      · rw [Array.getElem?_push]
        have hne : m / 64 ≠ n / 64 := by omega
        simp [hne, hlt]
      · have hgt : n / 64 < m / 64 := by omega
        have hsize :
            ((Array.replicate (n / 64) (0 : UInt64)).push
              ((1 : UInt64) <<< (n % 64).toUInt64)).size ≤ m / 64 := by
          simp
          omega
        rw [Array.getElem?_push]
        have hne : m / 64 ≠ n / 64 := by omega
        have hnlt : ¬m / 64 < n / 64 := by omega
        simp [hne, hnlt]
    rw [coeffWords, hget]
    simp

/-- The packed degree search recovers the degree of a monomial. -/
@[simp, grind =] theorem degree?_monomial (n : Nat) :
    (monomial n).degree? = some n := by
  have hbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have hne : ((1 : UInt64) <<< (n % 64).toUInt64) ≠ 0 :=
    oneHotWord_ne_zero hbit
  unfold monomial degree?
  simp [ofWords, normalizeWords,
    trimTrailingZeroWordsList_replicate_zero_append_nonzero (n / 64) hne,
    highestSetBit?_oneHot hbit]
  omega

/-- The default-`0` degree of the monomial `x^n` is `n`. -/
@[simp, grind =] theorem degree_monomial (n : Nat) : (monomial n).degree = n :=
  degree_eq_of_degree?_eq_some (degree?_monomial n)

/-- The monomial `x^n` is never the zero polynomial. -/
@[simp, grind =] theorem isZero_monomial_eq_false (n : Nat) :
    (monomial n).isZero = false :=
  isZero_false_of_degree?_eq_some (degree?_monomial n)

/-- The monomial `x^n` is distinct from the zero polynomial. -/
@[simp] theorem monomial_ne_zero (n : Nat) : monomial n ≠ 0 :=
  ne_zero_of_degree?_eq_some (degree?_monomial n)

/-- Shift-left coefficients reduce to the coefficient lookup on the shifted packed words. -/
@[simp, grind =]
theorem coeff_shiftLeft (p : GF2Poly) (k n : Nat) :
    (p.shiftLeft k).coeff n =
      coeffWords
        ((Array.replicate (k / 64) (0 : UInt64)) ++
          if k % 64 = 0 then
            p.words
          else
            (shiftLeftBitsList (k % 64) 0 p.words.toList).toArray)
        n := by
  simp [shiftLeft]

/-- Shifting left by `k` moves every source coefficient at `n` to `n + k`
when the source coefficient lies in a stored word. -/
theorem coeff_shiftLeft_add_of_word_lt (p : GF2Poly) {k n : Nat}
    (hword : n / 64 < p.words.size) :
    (p.shiftLeft k).coeff (n + k) = p.coeff n := by
  rw [coeff_shiftLeft]
  by_cases hbitShift : k % 64 = 0
  · simp [hbitShift, coeff, coeffWords_replicate_append_add_of_mod_eq_zero]
  · simp [hbitShift, coeff,
      coeffWords_replicate_append_shiftLeftBitsList_add p.words hbitShift hword]

/-- `mulXk` is coefficientwise the same as `shiftLeft`. -/
@[simp, grind =]
theorem coeff_mulXk (p : GF2Poly) (k n : Nat) :
    (p.mulXk k).coeff n = (p.shiftLeft k).coeff n := by
  rfl

example (p : GF2Poly) (k n : Nat) :
    (p.mulXk k).coeff n =
      coeffWords
        ((Array.replicate (k / 64) (0 : UInt64)) ++
          if k % 64 = 0 then
            p.words
          else
            (shiftLeftBitsList (k % 64) 0 p.words.toList).toArray)
        n := by
  simp

/-- Multiplication by `x^k` shifts the degree of a nonzero packed polynomial. -/
theorem degree?_mulXk_of_degree?_eq_some {p : GF2Poly} {d k : Nat}
    (h : p.degree? = some d) :
    (p.mulXk k).degree? = some (d + k) := by
  apply degree?_eq_some_of_coeff_eq_true_of_forall_gt_false
  · rw [coeff_mulXk]
    have hdword : d / 64 < p.words.size := by
      have hdcoeff := coeff_eq_true_of_degree?_eq_some h
      by_cases hlt : d / 64 < p.words.size
      · exact hlt
      have hdcoeffFalse : p.coeff d = false := by
        simp [coeff, coeffWords, hlt]
      rw [hdcoeffFalse] at hdcoeff
      contradiction
    have hshift := coeff_shiftLeft_add_of_word_lt (p := p) (k := k) (n := d) hdword
    have hdcoeff := coeff_eq_true_of_degree?_eq_some h
    rw [hshift, hdcoeff]
  · intro m hm
    rw [coeff_mulXk]
    have hk_le_m : k ≤ m := by omega
    let n := m - k
    have hm_eq : m = n + k := by
      dsimp [n]
      omega
    have hd_lt_n : d < n := by
      dsimp [n]
      omega
    by_cases hnword : n / 64 < p.words.size
    · have hshift :=
        coeff_shiftLeft_add_of_word_lt (p := p) (k := k) (n := n) hnword
      have hnfalse : p.coeff n = false := coeff_eq_false_of_degree?_lt h hd_lt_n
      rw [hm_eq, hshift, hnfalse]
    · rw [hm_eq, coeff_shiftLeft]
      by_cases hbitShift : k % 64 = 0
      · have hnfalse : p.coeff n = false := coeff_eq_false_of_degree?_lt h hd_lt_n
        simp [hbitShift, coeffWords_replicate_append_add_of_mod_eq_zero,
          coeff] at hnfalse ⊢
        exact hnfalse
      · simp [hbitShift,
          coeffWords_replicate_append_shiftLeftBitsList_add_of_not_word
            p.words hbitShift hnword]

/-- The shifted leading coefficient of `p.mulXk k` is set. -/
theorem coeff_mulXk_degree_add {p : GF2Poly} {d k : Nat}
    (h : p.degree? = some d) :
    (p.mulXk k).coeff (d + k) = true := by
  exact coeff_eq_true_of_degree?_eq_some (degree?_mulXk_of_degree?_eq_some h)

/-- In a long-division step, shifting the divisor by `rd - qd` aligns its
leading coefficient with the current remainder degree. -/
theorem coeff_mulXk_division_step {q : GF2Poly} {rd qd : Nat}
    (hq : q.degree? = some qd) (hrd : ¬ rd < qd) :
    (q.mulXk (rd - qd)).coeff rd = true := by
  have hshift := coeff_mulXk_degree_add (p := q) (d := qd) (k := rd - qd) hq
  have hrd_eq : qd + (rd - qd) = rd := by
    omega
  simpa [hrd_eq] using hshift

/-- The leading coefficient cancels after the characteristic-two subtraction
step used by long division. -/
theorem coeff_division_step_cancel {rem q : GF2Poly} {rd qd : Nat}
    (hrem : rem.degree? = some rd) (hq : q.degree? = some qd) (hrd : ¬ rd < qd) :
    (rem + q.mulXk (rd - qd)).coeff rd = false := by
  rw [coeff_add_bne, coeff_eq_true_of_degree?_eq_some hrem, coeff_mulXk_division_step hq hrd]
  rfl

/-- A non-terminal long-division subtraction step strictly lowers the
remainder degree. -/
theorem division_step_degree_lt {rem q : GF2Poly} {rd qd : Nat}
    (hrem : rem.degree? = some rd) (hq : q.degree? = some qd) (hrd : ¬ rd < qd) :
    (rem + q.mulXk (rd - qd)).isZero = true ∨
      (rem + q.mulXk (rd - qd)).degree < rd := by
  let next := rem + q.mulXk (rd - qd)
  by_cases hzero : next.isZero = true
  · exact Or.inl hzero
  · right
    have hnonzero : next.isZero = false := by
      cases h : next.isZero <;> simp [h] at hzero ⊢
    obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hnonzero
    have hdegree : next.degree = d := degree_eq_of_degree?_eq_some hd
    rw [hdegree]
    by_cases hlt : d < rd
    · exact hlt
    · have hrd_le_d : rd ≤ d := Nat.le_of_not_gt hlt
      have hdcoeff : next.coeff d = true := coeff_eq_true_of_degree?_eq_some hd
      by_cases hd_eq_rd : d = rd
      · have hnextfalse : next.coeff d = false := by
          rw [hd_eq_rd]
          dsimp [next]
          exact coeff_division_step_cancel hrem hq hrd
        rw [hnextfalse] at hdcoeff
        contradiction
      · have hrd_lt_d : rd < d := Nat.lt_of_le_of_ne hrd_le_d (Ne.symm hd_eq_rd)
        have hremfalse : rem.coeff d = false :=
          coeff_eq_false_of_degree?_lt hrem hrd_lt_d
        have hshiftDegree :
            (q.mulXk (rd - qd)).degree? = some rd := by
          have h := degree?_mulXk_of_degree?_eq_some
            (p := q) (d := qd) (k := rd - qd) hq
          have hrd_eq : qd + (rd - qd) = rd := by
            omega
          simpa [hrd_eq] using h
        have hshiftfalse : (q.mulXk (rd - qd)).coeff d = false :=
          coeff_eq_false_of_degree?_lt hshiftDegree hrd_lt_d
        have hnextfalse : next.coeff d = false := by
          dsimp [next]
          rw [coeff_add_bne, hremfalse, hshiftfalse]
          rfl
        rw [hnextfalse] at hdcoeff
        contradiction

/-- Alias for exact division by a power of `x` when the low coefficients vanish;
otherwise this drops the discarded remainder. -/
def divXk (p : GF2Poly) (k : Nat) : GF2Poly :=
  shiftRight p k

/-- Normalization never increases the number of stored machine words. -/
theorem normalizeWords_size_le (words : Array UInt64) :
    (normalizeWords words).size ≤ words.size := by
  simpa [normalizeWords] using trimTrailingZeroWordsList_length_le words.toList

/-- Wrapping raw words never increases the stored word count. -/
theorem wordCount_ofWords_le (words : Array UInt64) :
    (ofWords words).wordCount ≤ words.size := by
  exact normalizeWords_size_le words

/-- Addition stores no more words than the larger input. -/
theorem wordCount_add_le (p q : GF2Poly) :
    (p + q).wordCount ≤ max p.wordCount q.wordCount := by
  calc
    (p + q).wordCount = (ofWords (xorWords p.words q.words)).wordCount := by
      rfl
    _ ≤ (xorWords p.words q.words).size := wordCount_ofWords_le _
    _ = max p.wordCount q.wordCount := by
      simp [xorWords, wordCount]

/-- The monomial `x^n` stores at most the one word containing its bit. -/
theorem wordCount_monomial_le (n : Nat) :
    (monomial n).wordCount ≤ n / 64 + 1 := by
  calc
    (monomial n).wordCount
        ≤ ((Array.replicate (n / 64) (0 : UInt64)).push
            ((1 : UInt64) <<< (n % 64).toUInt64)).size := by
          exact wordCount_ofWords_le _
    _ = n / 64 + 1 := by
      simp

end GF2Poly
end Hex
