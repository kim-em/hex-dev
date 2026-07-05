/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Basic
public import HexGF2.Clmul

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Bit-level carry-less multiplication over packed `UInt64` words:
`xorClmulAt` and the `coeffWords`/`clmul`/monomial coefficient lemmas.
-/
namespace Hex
namespace GF2Poly

/-- XOR a 128-bit carry-less product into adjacent result words. -/
@[expose]
def xorClmulAt (acc : Array UInt64) (idx : Nat) (x y : UInt64) : Array UInt64 :=
  let (hi, lo) := clmul x y
  let acc := acc.set! idx (acc[idx]! ^^^ lo)
  acc.set! (idx + 1) (acc[idx + 1]! ^^^ hi)

/-- `xorClmulAt_size` says accumulating one carry-less product preserves the result array size. -/
private theorem xorClmulAt_size (acc : Array UInt64) (idx : Nat) (x y : UInt64) :
    (xorClmulAt acc idx x y).size = acc.size := by
  simp [xorClmulAt]

/-- `foldl_xorClmulAt_size` says folding `xorClmulAt` over word indices preserves the accumulator size. -/
private theorem foldl_xorClmulAt_size (js : List Nat) (acc : Array UInt64)
    (idx : Nat) (x : UInt64) (ys : Array UInt64) :
    (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc).size = acc.size := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, xorClmulAt_size]

/-- `foldl_mulWords_size` says the nested word-multiplication fold preserves the accumulator size. -/
private theorem foldl_mulWords_size (is : List Nat) (acc : Array UInt64)
    (xs ys : Array UInt64) :
    (is.foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range ys.size).foldl
            (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
            acc)
        acc).size = acc.size := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      simp only [List.foldl_cons]
      have hinner := foldl_xorClmulAt_size (List.range ys.size) acc i xs[i]! ys
      rw [ih, hinner]

/-- `bit_eq_one_eq_testBit` identifies the shifted low-bit test with `Nat.testBit`. -/
private theorem bit_eq_one_eq_testBit (x i : Nat) :
    (x >>> i % 2 == 1) = x.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  apply decide_eq_decide.mpr
  exact Iff.rfl

/-- `UInt64.bit_xor_bne` rewrites a bit of a word XOR as Boolean inequality of the input bits. -/
private theorem UInt64.bit_xor_bne (a b : UInt64) (i : Nat) :
    ((((a ^^^ b) >>> i.toUInt64) &&& 1) != 0) =
      ((((a >>> i.toUInt64) &&& 1) != 0) !=
        (((b >>> i.toUInt64) &&& 1) != 0)) := by
  rw [UInt64.bne_zero_eq_toNat_bne_zero, UInt64.bne_zero_eq_toNat_bne_zero,
    UInt64.bne_zero_eq_toNat_bne_zero]
  simp [UInt64.toNat_xor, UInt64.toNat_shiftRight, UInt64.toNat_and]
  rw [bit_eq_one_eq_testBit, bit_eq_one_eq_testBit, bit_eq_one_eq_testBit]
  simp [Nat.testBit_xor]

/-- `clmul_xor_left_snd_bit` gives bitwise linearity in the left input for the low word of `clmul`. -/
private theorem clmul_xor_left_snd_bit (x y z : UInt64) (i : Nat) :
    ((((clmul (x ^^^ y) z).2 >>> i.toUInt64) &&& 1) != 0) =
      (((((clmul x z).2 >>> i.toUInt64) &&& 1) != 0) !=
        ((((clmul y z).2 >>> i.toUInt64) &&& 1) != 0)) := by
  rw [clmul_xor_left]
  exact UInt64.bit_xor_bne (clmul x z).2 (clmul y z).2 i

/-- `clmul_xor_left_fst_bit` gives bitwise linearity in the left input for the high word of `clmul`. -/
private theorem clmul_xor_left_fst_bit (x y z : UInt64) (i : Nat) :
    ((((clmul (x ^^^ y) z).1 >>> i.toUInt64) &&& 1) != 0) =
      (((((clmul x z).1 >>> i.toUInt64) &&& 1) != 0) !=
        ((((clmul y z).1 >>> i.toUInt64) &&& 1) != 0)) := by
  rw [clmul_xor_left]
  exact UInt64.bit_xor_bne (clmul x z).1 (clmul y z).1 i

/-- `clmul_xor_right_snd_bit` gives bitwise linearity in the right input for the low word of `clmul`. -/
private theorem clmul_xor_right_snd_bit (x y z : UInt64) (i : Nat) :
    ((((clmul x (y ^^^ z)).2 >>> i.toUInt64) &&& 1) != 0) =
      (((((clmul x y).2 >>> i.toUInt64) &&& 1) != 0) !=
        ((((clmul x z).2 >>> i.toUInt64) &&& 1) != 0)) := by
  rw [clmul_comm x (y ^^^ z), clmul_xor_left, clmul_comm y x, clmul_comm z x]
  exact UInt64.bit_xor_bne (clmul x y).2 (clmul x z).2 i

/-- `clmul_xor_right_fst_bit` gives bitwise linearity in the right input for the high word of `clmul`. -/
private theorem clmul_xor_right_fst_bit (x y z : UInt64) (i : Nat) :
    ((((clmul x (y ^^^ z)).1 >>> i.toUInt64) &&& 1) != 0) =
      (((((clmul x y).1 >>> i.toUInt64) &&& 1) != 0) !=
        ((((clmul x z).1 >>> i.toUInt64) &&& 1) != 0)) := by
  rw [clmul_comm x (y ^^^ z), clmul_xor_left, clmul_comm y x, clmul_comm z x]
  exact UInt64.bit_xor_bne (clmul x y).1 (clmul x z).1 i

/-- `coeffWords_xorClmulAt_low` describes the low-word contribution of one `xorClmulAt` update. -/
private theorem coeffWords_xorClmulAt_low (acc : Array UInt64) {idx n : Nat}
    (x y : UInt64) (hidx : idx < acc.size) (hn : n / 64 = idx) :
    coeffWords (xorClmulAt acc idx x y) n =
      (coeffWords acc n !=
        ((((clmul x y).2 >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  simp [xorClmulAt, coeffWords, hn, hidx, UInt64.bit_xor_bne]

/-- `coeffWords_xorClmulAt_high` describes the high-word contribution of one `xorClmulAt` update. -/
private theorem coeffWords_xorClmulAt_high (acc : Array UInt64) {idx n : Nat}
    (x y : UInt64) (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hn : n / 64 = idx + 1) :
    coeffWords (xorClmulAt acc idx x y) n =
      (coeffWords acc n !=
        ((((clmul x y).1 >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  simp [xorClmulAt, coeffWords, hn, hidx, hidxNext, UInt64.bit_xor_bne]

/-- `coeffWords_xorClmulAt_ne` says unrelated word positions are unchanged by `xorClmulAt`. -/
private theorem coeffWords_xorClmulAt_ne (acc : Array UInt64) {idx n : Nat}
    (x y : UInt64) (hnLow : n / 64 ≠ idx) (hnHigh : n / 64 ≠ idx + 1) :
    coeffWords (xorClmulAt acc idx x y) n = coeffWords acc n := by
  have hLow : idx ≠ n / 64 := Ne.symm hnLow
  have hHigh : idx + 1 ≠ n / 64 := Ne.symm hnHigh
  simp [xorClmulAt, coeffWords, hLow, hHigh]

/-- `coeffWords_xorClmulAt_low_xor_left` isolates the extra low-word bit from XORing the left factor. -/
private theorem coeffWords_xorClmulAt_low_xor_left (acc : Array UInt64) {idx n : Nat}
    (x y z : UInt64) (hidx : idx < acc.size) (hn : n / 64 = idx) :
    coeffWords (xorClmulAt acc idx (x ^^^ y) z) n =
      (coeffWords (xorClmulAt acc idx x z) n !=
        ((((clmul y z).2 >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [coeffWords_xorClmulAt_low acc (x ^^^ y) z hidx hn, coeffWords_xorClmulAt_low acc x z hidx hn,
    clmul_xor_left_snd_bit]
  cases coeffWords acc n <;>
    cases ((((clmul x z).2 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    cases ((((clmul y z).2 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    rfl

/-- `coeffWords_xorClmulAt_high_xor_left` isolates the extra high-word bit from XORing the left factor. -/
private theorem coeffWords_xorClmulAt_high_xor_left (acc : Array UInt64) {idx n : Nat}
    (x y z : UInt64) (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hn : n / 64 = idx + 1) :
    coeffWords (xorClmulAt acc idx (x ^^^ y) z) n =
      (coeffWords (xorClmulAt acc idx x z) n !=
        ((((clmul y z).1 >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [coeffWords_xorClmulAt_high acc (x ^^^ y) z hidx hidxNext hn,
    coeffWords_xorClmulAt_high acc x z hidx hidxNext hn, clmul_xor_left_fst_bit]
  cases coeffWords acc n <;>
    cases ((((clmul x z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    cases ((((clmul y z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    rfl

/-- Unchecked word lookup is the optional lookup defaulted to `0`. -/
private theorem getElem!_eq_getD (a : Array UInt64) (i : Nat) :
    a[i]! = a[i]?.getD 0 := by
  rw [getElem!_def]; cases a[i]? <;> rfl

/-- `xorWords_getElem!` unfolds unchecked access to `xorWords` into wordwise XOR. -/
private theorem xorWords_getElem! (xs ys : Array UInt64) (i : Nat) :
    (xorWords xs ys)[i]! = xs[i]! ^^^ ys[i]! := by
  simp only [getElem!_eq_getD]
  exact xorWords_get?_getD xs ys i

/-- `normalizeWords_getElem!` shows normalization leaves unchecked word lookup unchanged. -/
private theorem normalizeWords_getElem! (words : Array UInt64) (i : Nat) :
    (normalizeWords words)[i]! = words[i]! := by
  simp only [getElem!_eq_getD]
  exact normalizeWords_get?_getD words i

/-- `Array.setIfInBounds_getElem!` says setting an index to its current unchecked value is a no-op. -/
private theorem Array.setIfInBounds_getElem! (xs : Array UInt64) (idx : Nat) :
    xs.setIfInBounds idx xs[idx]! = xs := by
  unfold Array.setIfInBounds
  by_cases h : idx < xs.size
  · simp [h]
  · simp [h]

/-- `xorClmulAt_zero_right` says a carry-less product by the zero word contributes nothing. -/
private theorem xorClmulAt_zero_right (acc : Array UInt64) (idx : Nat) (x : UInt64) :
    xorClmulAt acc idx x 0 = acc := by
  simp [xorClmulAt, Array.setIfInBounds_getElem!]

/-- `coeffWords_xorClmulAt_zero_right` says multiplying by the zero word preserves every coefficient bit. -/
private theorem coeffWords_xorClmulAt_zero_right (acc : Array UInt64) (idx n : Nat)
    (x : UInt64) :
    coeffWords (xorClmulAt acc idx x 0) n = coeffWords acc n := by
  rw [xorClmulAt_zero_right]

/-- `clmul_oneHot_low_bit_same_word` locates a shifted source bit in the low word of a one-hot product. -/
private theorem clmul_oneHot_low_bit_same_word (x : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hold : old < 64)
    (hbit : old + shift < 64) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).2 >>>
        (old + shift).toUInt64) &&& 1) != 0) =
      (((x >>> old.toUInt64) &&& 1) != 0) := by
  rw [clmul_oneHot_snd x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hshift,
    Nat.mod_eq_of_lt hold, Nat.mod_eq_of_lt hbit, bit_eq_one_eq_testBit]
  change (((x.toNat <<< shift) % 18446744073709551616).testBit (old + shift)) =
    x.toNat.testBit old
  rw [show 18446744073709551616 = 2 ^ 64 by rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  simp [hbit]

/-- `clmul_oneHot_low_bit_before_shift_false` shows low-word bits before the one-hot shift are zero. -/
private theorem clmul_oneHot_low_bit_before_shift_false (x : UInt64) {shift bit : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hbit : bit < shift) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).2 >>>
        bit.toUInt64) &&& 1) != 0) = false := by
  rw [clmul_oneHot_snd x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  have hbit64 : bit < 64 := by omega
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hshift,
    Nat.mod_eq_of_lt hbit64, bit_eq_one_eq_testBit]
  change (((x.toNat <<< shift) % 18446744073709551616).testBit bit) = false
  rw [show 18446744073709551616 = 2 ^ 64 by rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  simp
  intro _ hle
  omega

/-- `clmul_oneHot_low_bit_shifted` rewrites a reachable low-word bit as the corresponding source bit. -/
private theorem clmul_oneHot_low_bit_shifted (x : UInt64) {shift bit : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hbit : bit < 64)
    (hle : shift ≤ bit) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).2 >>>
        bit.toUInt64) &&& 1) != 0) =
      (((x >>> (bit - shift).toUInt64) &&& 1) != 0) := by
  have hsource : bit - shift < 64 := by omega
  have hsourceShift : bit - shift + shift < 64 := by omega
  have hsum : bit - shift + shift = bit := by omega
  simpa [hsum] using
    clmul_oneHot_low_bit_same_word x hshiftPos hshift hsource hsourceShift

/-- `clmul_oneHot_high_bit_carry_word` locates a shifted source bit that carries into the high word. -/
private theorem clmul_oneHot_high_bit_carry_word (x : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hold : old < 64)
    (hbit : 64 ≤ old + shift) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).1 >>>
        (old + shift - 64).toUInt64) &&& 1) != 0) =
      (((x >>> old.toUInt64) &&& 1) != 0) := by
  have htargetLt : old + shift - 64 < 64 := by omega
  have hshiftCompl : 64 - shift < 64 := by omega
  rw [clmul_oneHot_fst x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  have hold_eq : 64 - shift + (old + shift - 64) = old := by omega
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftRight,
    UInt64.toNat_and, Nat.mod_eq_of_lt hshiftCompl, Nat.mod_eq_of_lt hold,
    Nat.mod_eq_of_lt htargetLt, bit_eq_one_eq_testBit, Nat.testBit_shiftRight,
    hold_eq]

/-- `clmul_oneHot_high_bit_after_carry_false` shows high-word bits at or beyond the shift window are zero. -/
private theorem clmul_oneHot_high_bit_after_carry_false (x : UInt64) {shift bit : Nat}
    (hshift : shift < 64) (hbit : bit < 64) (hle : shift ≤ bit) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).1 >>>
        bit.toUInt64) &&& 1) != 0) = false := by
  rw [clmul_oneHot_fst x hshift]
  by_cases hshiftZero : shift = 0
  · simp [hshiftZero]
  · simp [hshiftZero, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftRight,
      UInt64.toNat_and, Nat.mod_eq_of_lt (by omega : 64 - shift < 64),
      Nat.mod_eq_of_lt hbit,
      bit_eq_one_eq_testBit, Nat.testBit_shiftRight]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hxlt : x.toNat < 2 ^ 64 := by
      simpa [UInt64.size, show (18446744073709551616 : Nat) = 2 ^ 64 by rfl]
        using UInt64.toNat_lt_size x
    have hexp : 64 ≤ 64 - shift + bit := by omega
    rw [Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hxlt
        (Nat.pow_le_pow_right (by decide : 0 < 2) hexp))]
    simp

/-- `coeffWords_xorClmulAt_oneHot_low_same_word` says a one-hot right factor XORs the shifted source bit into the target coefficient when the shift keeps it in the low word. -/
private theorem coeffWords_xorClmulAt_oneHot_low_same_word
    (acc : Array UInt64) {idx n shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : n / 64 = idx) (hbit : n % 64 + shift < 64) :
    coeffWords (xorClmulAt acc idx x ((1 : UInt64) <<< shift.toUInt64)) (n + shift) =
      (coeffWords acc (n + shift) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hold : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have htargetDiv : (n + shift) / 64 = idx := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  have htargetMod : (n + shift) % 64 = n % 64 + shift := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [coeffWords_xorClmulAt_low acc x ((1 : UInt64) <<< shift.toUInt64) hidx
    htargetDiv]
  rw [htargetMod, clmul_oneHot_low_bit_same_word x hshiftPos hshift hold hbit]

/-- `coeffWords_xorClmulAt_oneHot_low_before_shift` says coefficients below the one-hot shift are left unchanged. -/
private theorem coeffWords_xorClmulAt_oneHot_low_before_shift
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : target / 64 = idx) (hbit : target % 64 < shift) :
    coeffWords (xorClmulAt acc idx x ((1 : UInt64) <<< shift.toUInt64)) target =
      coeffWords acc target := by
  rw [coeffWords_xorClmulAt_low acc x ((1 : UInt64) <<< shift.toUInt64) hidx hn,
    clmul_oneHot_low_bit_before_shift_false x hshiftPos hshift hbit]
  simp

/-- `coeffWords_xorClmulAt_oneHot_high_carry_word` says a one-hot right factor XORs the shifted source bit into the target coefficient when the shift carries it into the high word. -/
private theorem coeffWords_xorClmulAt_oneHot_high_carry_word
    (acc : Array UInt64) {idx n shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : n / 64 = idx) (hbit : 64 ≤ n % 64 + shift) :
    coeffWords (xorClmulAt acc idx x ((1 : UInt64) <<< shift.toUInt64)) (n + shift) =
      (coeffWords acc (n + shift) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hold : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have htargetDiv : (n + shift) / 64 = idx + 1 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  have htargetMod : (n + shift) % 64 = n % 64 + shift - 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [coeffWords_xorClmulAt_high acc x ((1 : UInt64) <<< shift.toUInt64) hidx
    hidxNext htargetDiv]
  rw [htargetMod, clmul_oneHot_high_bit_carry_word x hshiftPos hshift hold hbit]

/-- `coeffWords_xorClmulAt_oneHot_high_after_carry` says high-word coefficients at or beyond the shift window are left unchanged. -/
private theorem coeffWords_xorClmulAt_oneHot_high_after_carry
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hshift : shift < 64) (hn : target / 64 = idx + 1)
    (hbit : shift ≤ target % 64) :
    coeffWords (xorClmulAt acc idx x ((1 : UInt64) <<< shift.toUInt64)) target =
      coeffWords acc target := by
  have htargetBit : target % 64 < 64 := Nat.mod_lt target (by decide : 0 < 64)
  rw [coeffWords_xorClmulAt_high acc x ((1 : UInt64) <<< shift.toUInt64) hidx
    hidxNext hn]
  rw [clmul_oneHot_high_bit_after_carry_false x hshift htargetBit hbit]
  simp

/-- `clmul_oneHot_left_low_bit_same_word` locates a shifted source bit in the low word of a product with the one-hot on the left. -/
private theorem clmul_oneHot_left_low_bit_same_word (x : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hold : old < 64)
    (hbit : old + shift < 64) :
    ((((clmul ((1 : UInt64) <<< shift.toUInt64) x).2 >>>
        (old + shift).toUInt64) &&& 1) != 0) =
      (((x >>> old.toUInt64) &&& 1) != 0) := by
  rw [clmul_oneHot_left_snd x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hshift,
    Nat.mod_eq_of_lt hold, Nat.mod_eq_of_lt hbit, bit_eq_one_eq_testBit]
  change (((x.toNat <<< shift) % 18446744073709551616).testBit (old + shift)) =
    x.toNat.testBit old
  rw [show 18446744073709551616 = 2 ^ 64 by rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  simp [hbit]

/-- `clmul_oneHot_left_low_bit_before_shift_false` shows low-word bits before the shift are zero for a left one-hot factor. -/
private theorem clmul_oneHot_left_low_bit_before_shift_false (x : UInt64) {shift bit : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hbit : bit < shift) :
    ((((clmul ((1 : UInt64) <<< shift.toUInt64) x).2 >>>
        bit.toUInt64) &&& 1) != 0) = false := by
  rw [clmul_oneHot_left_snd x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  have hbit64 : bit < 64 := by omega
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hshift,
    Nat.mod_eq_of_lt hbit64, bit_eq_one_eq_testBit]
  change (((x.toNat <<< shift) % 18446744073709551616).testBit bit) = false
  rw [show 18446744073709551616 = 2 ^ 64 by rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  simp
  intro _ hle
  omega

/-- `clmul_oneHot_left_high_bit_carry_word` locates a shifted source bit that carries into the high word of a left one-hot product. -/
private theorem clmul_oneHot_left_high_bit_carry_word (x : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hold : old < 64)
    (hbit : 64 ≤ old + shift) :
    ((((clmul ((1 : UInt64) <<< shift.toUInt64) x).1 >>>
        (old + shift - 64).toUInt64) &&& 1) != 0) =
      (((x >>> old.toUInt64) &&& 1) != 0) := by
  have htargetLt : old + shift - 64 < 64 := by omega
  have hshiftCompl : 64 - shift < 64 := by omega
  rw [clmul_oneHot_left_fst x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  have hold_eq : 64 - shift + (old + shift - 64) = old := by omega
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftRight,
    UInt64.toNat_and, Nat.mod_eq_of_lt hshiftCompl, Nat.mod_eq_of_lt hold,
    Nat.mod_eq_of_lt htargetLt, bit_eq_one_eq_testBit, Nat.testBit_shiftRight,
    hold_eq]

/-- `clmul_oneHot_left_high_bit_after_carry_false` shows high-word bits at or beyond the shift window are zero for a left one-hot factor. -/
private theorem clmul_oneHot_left_high_bit_after_carry_false
    (x : UInt64) {shift bit : Nat} (hshift : shift < 64) (hbit : bit < 64)
    (hle : shift ≤ bit) :
    ((((clmul ((1 : UInt64) <<< shift.toUInt64) x).1 >>>
        bit.toUInt64) &&& 1) != 0) = false := by
  rw [clmul_oneHot_left_fst x hshift]
  by_cases hshiftZero : shift = 0
  · simp [hshiftZero]
  · simp [hshiftZero, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftRight,
      UInt64.toNat_and, Nat.mod_eq_of_lt (by omega : 64 - shift < 64),
      Nat.mod_eq_of_lt hbit,
      bit_eq_one_eq_testBit, Nat.testBit_shiftRight]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hxlt : x.toNat < 2 ^ 64 := by
      simpa [UInt64.size, show (18446744073709551616 : Nat) = 2 ^ 64 by rfl]
        using UInt64.toNat_lt_size x
    have hexp : 64 ≤ 64 - shift + bit := by omega
    rw [Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hxlt
        (Nat.pow_le_pow_right (by decide : 0 < 2) hexp))]
    simp

/-- `coeffWords_xorClmulAt_oneHot_left_low_same_word` says a one-hot left factor XORs the shifted source bit into the target coefficient when the shift keeps it in the low word. -/
private theorem coeffWords_xorClmulAt_oneHot_left_low_same_word
    (acc : Array UInt64) {idx n shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : n / 64 = idx) (hbit : n % 64 + shift < 64) :
    coeffWords (xorClmulAt acc idx ((1 : UInt64) <<< shift.toUInt64) x) (n + shift) =
      (coeffWords acc (n + shift) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hold : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have htargetDiv : (n + shift) / 64 = idx := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  have htargetMod : (n + shift) % 64 = n % 64 + shift := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [coeffWords_xorClmulAt_low acc ((1 : UInt64) <<< shift.toUInt64) x hidx
    htargetDiv]
  rw [htargetMod, clmul_oneHot_left_low_bit_same_word x hshiftPos hshift hold hbit]

/-- `coeffWords_xorClmulAt_oneHot_left_low_before_shift` says coefficients below the one-hot shift are left unchanged for a left one-hot factor. -/
private theorem coeffWords_xorClmulAt_oneHot_left_low_before_shift
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : target / 64 = idx) (hbit : target % 64 < shift) :
    coeffWords (xorClmulAt acc idx ((1 : UInt64) <<< shift.toUInt64) x) target =
      coeffWords acc target := by
  rw [coeffWords_xorClmulAt_low acc ((1 : UInt64) <<< shift.toUInt64) x hidx hn,
    clmul_oneHot_left_low_bit_before_shift_false x hshiftPos hshift hbit]
  simp

/-- `coeffWords_xorClmulAt_oneHot_left_high_carry_word` says a one-hot left factor XORs the shifted source bit into the target coefficient when the shift carries it into the high word. -/
private theorem coeffWords_xorClmulAt_oneHot_left_high_carry_word
    (acc : Array UInt64) {idx n shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : n / 64 = idx) (hbit : 64 ≤ n % 64 + shift) :
    coeffWords (xorClmulAt acc idx ((1 : UInt64) <<< shift.toUInt64) x) (n + shift) =
      (coeffWords acc (n + shift) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hold : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have htargetDiv : (n + shift) / 64 = idx + 1 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  have htargetMod : (n + shift) % 64 = n % 64 + shift - 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [coeffWords_xorClmulAt_high acc ((1 : UInt64) <<< shift.toUInt64) x hidx
    hidxNext htargetDiv]
  rw [htargetMod, clmul_oneHot_left_high_bit_carry_word x hshiftPos hshift hold hbit]

/-- `coeffWords_xorClmulAt_oneHot_left_high_after_carry` says high-word coefficients at or beyond the shift window are left unchanged for a left one-hot factor. -/
private theorem coeffWords_xorClmulAt_oneHot_left_high_after_carry
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hshift : shift < 64) (hn : target / 64 = idx + 1)
    (hbit : shift ≤ target % 64) :
    coeffWords (xorClmulAt acc idx ((1 : UInt64) <<< shift.toUInt64) x) target =
      coeffWords acc target := by
  have htargetBit : target % 64 < 64 := Nat.mod_lt target (by decide : 0 < 64)
  rw [coeffWords_xorClmulAt_high acc ((1 : UInt64) <<< shift.toUInt64) x hidx
    hidxNext hn]
  rw [clmul_oneHot_left_high_bit_after_carry_false x hshift htargetBit hbit]
  simp

/-- `words_monomial_getElem!_active` says the word of `monomial k` at the active index `k / 64` is the one-hot `1 <<< (k % 64)`. -/
private theorem words_monomial_getElem!_active (k : Nat) :
    (monomial k).words[k / 64]! =
      ((1 : UInt64) <<< (k % 64).toUInt64) := by
  rw [words_monomial, Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos (by simp)]
  change ((Array.replicate (k / 64) (0 : UInt64)).push
    ((1 : UInt64) <<< (k % 64).toUInt64))[k / 64] =
      ((1 : UInt64) <<< (k % 64).toUInt64)
  rw [Array.getElem_push]
  simp

/-- `words_monomial_getElem!_zero_lt` says every word of `monomial k` below the active index `k / 64` is zero. -/
private theorem words_monomial_getElem!_zero_lt {j k : Nat} (hj : j < k / 64) :
    (monomial k).words[j]! = 0 := by
  rw [words_monomial, Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos]
  · simp [Array.getElem_push, hj]
  · simp
    omega

/-- `words_monomial_size` says the word array of `monomial k` has length `k / 64 + 1`. -/
private theorem words_monomial_size (k : Nat) :
    (monomial k).words.size = k / 64 + 1 := by
  rw [words_monomial]
  simp

/-- `coeffWords_xorClmulAt_monomial_active_low` specialises the low-word one-hot coefficient law to the active word of `monomial k`. -/
private theorem coeffWords_xorClmulAt_monomial_active_low
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  have htarget : n + k = (n + k / 64 * 64) + k % 64 := by
    have hk := Nat.div_add_mod k 64
    omega
  have hsourceMod : (n + k / 64 * 64) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [words_monomial_getElem!_active k, htarget]
  simpa [hsourceMod] using
    coeffWords_xorClmulAt_oneHot_low_same_word
      (acc := acc) (idx := i + k / 64) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

/-- `coeffWords_xorClmulAt_monomial_active_zero` handles the active word of `monomial k` when `k` is word-aligned, so the one-hot shift is zero. -/
private theorem coeffWords_xorClmulAt_monomial_active_zero
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 = 0) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have htargetDiv : (n + k) / 64 = i + k / 64 := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  have htargetMod : (n + k) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  rw [words_monomial_getElem!_active k]
  rw [coeffWords_xorClmulAt_low acc x ((1 : UInt64) <<< (k % 64).toUInt64) hidx
    htargetDiv]
  rw [clmul_oneHot_snd x (Nat.mod_lt k (by decide : 0 < 64))]
  simp [hbitShift, htargetMod]

/-- `coeffWords_xorClmulAt_monomial_active_low_before_shift` says active-word coefficients below the monomial's shift are left unchanged. -/
private theorem coeffWords_xorClmulAt_monomial_active_low_before_shift
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hword : target / 64 = i + k / 64)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        target =
      coeffWords acc target := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_low_before_shift
    (acc := acc) (idx := i + k / 64) (target := target)
    (shift := k % 64) x hidx hshiftPos hshift hword hbit

/-- `coeffWords_xorClmulAt_monomial_active_high` specialises the carry-into-high-word one-hot coefficient law to the active word of `monomial k`. -/
private theorem coeffWords_xorClmulAt_monomial_active_high
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hn : n / 64 = i) (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hshiftPos : 0 < k % 64 := by
    have hnbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
    omega
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  have htarget : n + k = (n + k / 64 * 64) + k % 64 := by
    have hk := Nat.div_add_mod k 64
    omega
  have hsourceMod : (n + k / 64 * 64) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [words_monomial_getElem!_active k, htarget]
  simpa [hsourceMod] using
    coeffWords_xorClmulAt_oneHot_high_carry_word
      (acc := acc) (idx := i + k / 64) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hidxNext hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

/-- `coeffWords_xorClmulAt_monomial_active_high_after_carry` says high-word coefficients past the monomial's carry window are left unchanged. -/
private theorem coeffWords_xorClmulAt_monomial_active_high_after_carry
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hword : target / 64 = i + k / 64 + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        target =
      coeffWords acc target := by
  have htargetBit : target % 64 < 64 := Nat.mod_lt target (by decide : 0 < 64)
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_high_after_carry
    (acc := acc) (idx := i + k / 64) (target := target)
    (shift := k % 64) x hidx hidxNext hshift hword hbit

/-- `foldl_xorClmulAt_zero_right_coeff` says folding `xorClmulAt` over indices whose words are all zero preserves every coefficient. -/
private theorem foldl_xorClmulAt_zero_right_coeff (js : List Nat) (acc : Array UInt64)
    (idx n : Nat) (x : UInt64) (ys : Array UInt64)
    (hzero : ∀ j ∈ js, ys[j]! = 0) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc)
        n =
      coeffWords acc n := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      have hjzero : ys[j]! = 0 := hzero j (by simp)
      have htail : ∀ j' ∈ js, ys[j']! = 0 := by
        intro j' hj'
        exact hzero j' (by simp [hj'])
      simp only [List.foldl_cons]
      rw [hjzero, ih (acc := xorClmulAt acc (idx + j) x 0) htail,
        coeffWords_xorClmulAt_zero_right]

/-- `foldl_xorClmulAt_monomial_zero_prefix_coeff` says the below-active prefix words of `monomial k` contribute nothing to any coefficient across the fold. -/
private theorem foldl_xorClmulAt_monomial_zero_prefix_coeff
    (acc : Array UInt64) (idx n : Nat) (x : UInt64) (k : Nat) :
    coeffWords
        ((List.range (k / 64)).foldl
          (fun acc j => xorClmulAt acc (idx + j) x (monomial k).words[j]!)
          acc)
        n =
      coeffWords acc n := by
  exact foldl_xorClmulAt_zero_right_coeff
    (List.range (k / 64)) acc idx n x (monomial k).words
    (by
      intro j hj
      exact words_monomial_getElem!_zero_lt (List.mem_range.mp hj))

/-- `foldl_xorClmulAt_monomial_active_low` lifts the active-word low-case coefficient law across the full fold over `monomial k`'s words. -/
private theorem foldl_xorClmulAt_monomial_active_low
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show k / 64 + 1 = (k / 64).succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_monomial_active_low
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hn := hn) (hbitShift := hbitShift) (hbit := hbit)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

/-- `foldl_xorClmulAt_monomial_active_zero` lifts the word-aligned active-word coefficient law across the full fold over `monomial k`'s words. -/
private theorem foldl_xorClmulAt_monomial_active_zero
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 = 0) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show k / 64 + 1 = (k / 64).succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_monomial_active_zero
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hn := hn) (hbitShift := hbitShift)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

/-- `foldl_xorClmulAt_monomial_active_low_before_shift` lifts the below-shift unchanged-coefficient law across the full fold over `monomial k`'s words. -/
private theorem foldl_xorClmulAt_monomial_active_low_before_shift
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hword : target / 64 = i + k / 64)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        target =
      coeffWords acc target := by
  rw [show k / 64 + 1 = (k / 64).succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_monomial_active_low_before_shift
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hword := hword) (hbitShift := hbitShift) (hbit := hbit)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

/-- `foldl_xorClmulAt_monomial_active_high` lifts the carry-into-high-word coefficient law across the full fold over `monomial k`'s words. -/
private theorem foldl_xorClmulAt_monomial_active_high
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hn : n / 64 = i) (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show k / 64 + 1 = (k / 64).succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_monomial_active_high
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hidxNext := by simpa [foldl_xorClmulAt_size] using hidxNext)
    (hn := hn) (hbit := hbit)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

/-- `foldl_xorClmulAt_monomial_active_high_after_carry` lifts the past-carry-window unchanged-coefficient law across the full fold over `monomial k`'s words. -/
private theorem foldl_xorClmulAt_monomial_active_high_after_carry
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hword : target / 64 = i + k / 64 + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        target =
      coeffWords acc target := by
  rw [show k / 64 + 1 = (k / 64).succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_monomial_active_high_after_carry
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hidxNext := by simpa [foldl_xorClmulAt_size] using hidxNext)
    (hword := hword) (hbit := hbit)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

/-- `foldl_xorClmulAt_monomial_ne` says coefficients in words other than the monomial's active and carry words are left unchanged by the full fold. -/
private theorem foldl_xorClmulAt_monomial_ne
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hLow : target / 64 ≠ i + k / 64)
    (hHigh : target / 64 ≠ i + k / 64 + 1) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        target =
      coeffWords acc target := by
  rw [show k / 64 + 1 = (k / 64).succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_ne
    (hnLow := hLow) (hnHigh := hHigh)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

/-- `xorClmulAt_zero_left` says accumulating the carry-less product of a zero left factor leaves the accumulator untouched. -/
private theorem xorClmulAt_zero_left (acc : Array UInt64) (idx : Nat) (x : UInt64) :
    xorClmulAt acc idx 0 x = acc := by
  simp [xorClmulAt, Array.setIfInBounds_getElem!]

/-- `coeffWords_xorClmulAt_zero_left` says a zero left factor leaves every output coefficient unchanged. -/
private theorem coeffWords_xorClmulAt_zero_left (acc : Array UInt64) (idx n : Nat)
    (x : UInt64) :
    coeffWords (xorClmulAt acc idx 0 x) n = coeffWords acc n := by
  rw [xorClmulAt_zero_left]

/-- `coeffWords_xorClmulAt_xor_left` distributes one `xorClmulAt` step over an xor of left factors, given the three accumulators already agree by xor. -/
private theorem coeffWords_xorClmulAt_xor_left
    (accXY accX accY : Array UInt64) {idx n : Nat} (x y z : UInt64)
    (hsizeX : accX.size = accXY.size) (hsizeY : accY.size = accXY.size)
    (hidx : idx < accXY.size) (hidxNext : idx + 1 < accXY.size)
    (hacc : coeffWords accXY n = (coeffWords accX n != coeffWords accY n)) :
    coeffWords (xorClmulAt accXY idx (x ^^^ y) z) n =
      (coeffWords (xorClmulAt accX idx x z) n !=
        coeffWords (xorClmulAt accY idx y z) n) := by
  by_cases hLow : n / 64 = idx
  · rw [coeffWords_xorClmulAt_low accXY (x ^^^ y) z hidx hLow]
    rw [coeffWords_xorClmulAt_low accX x z (by simpa [hsizeX]) hLow,
      coeffWords_xorClmulAt_low accY y z (by simpa [hsizeY]) hLow, clmul_xor_left_snd_bit, hacc]
    cases coeffWords accX n <;>
      cases coeffWords accY n <;>
      cases ((((clmul x z).2 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
      cases ((((clmul y z).2 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
      rfl
  · by_cases hHigh : n / 64 = idx + 1
    · rw [coeffWords_xorClmulAt_high accXY (x ^^^ y) z hidx hidxNext hHigh]
      rw [coeffWords_xorClmulAt_high accX x z (by simpa [hsizeX])
        (by simpa [hsizeX]) hHigh]
      rw [coeffWords_xorClmulAt_high accY y z (by simpa [hsizeY])
        (by simpa [hsizeY]) hHigh]
      rw [clmul_xor_left_fst_bit, hacc]
      cases coeffWords accX n <;>
        cases coeffWords accY n <;>
        cases ((((clmul x z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
        cases ((((clmul y z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
        rfl
    · rw [coeffWords_xorClmulAt_ne accXY (x ^^^ y) z hLow hHigh]
      rw [coeffWords_xorClmulAt_ne accX x z hLow hHigh,
        coeffWords_xorClmulAt_ne accY y z hLow hHigh]
      exact hacc

/-- `foldl_xorClmulAt_xor_left_coeff` lifts left-factor xor-distributivity across the inner `xorClmulAt` fold over a list of word indices. -/
private theorem foldl_xorClmulAt_xor_left_coeff
    (js : List Nat) (accXY accX accY : Array UInt64) {idx n : Nat}
    (x y : UInt64) (zs : Array UInt64)
    (hsizeX : accX.size = accXY.size) (hsizeY : accY.size = accXY.size)
    (hidx : ∀ j ∈ js, idx + j + 1 < accXY.size)
    (hacc : coeffWords accXY n = (coeffWords accX n != coeffWords accY n)) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) (x ^^^ y) zs[j]!) accXY)
        n =
      (coeffWords
          (js.foldl (fun acc j => xorClmulAt acc (idx + j) x zs[j]!) accX)
          n !=
        coeffWords
          (js.foldl (fun acc j => xorClmulAt acc (idx + j) y zs[j]!) accY)
          n) := by
  induction js generalizing accXY accX accY with
  | nil =>
      simpa using hacc
  | cons j js ih =>
      simp only [List.foldl_cons]
      have hj : idx + j + 1 < accXY.size := hidx j (by simp)
      have htail : ∀ j' ∈ js,
          idx + j' + 1 < (xorClmulAt accXY (idx + j) (x ^^^ y) zs[j]!).size := by
        intro j' hj'
        rw [xorClmulAt_size]
        exact hidx j' (by simp [hj'])
      have hstep :=
        coeffWords_xorClmulAt_xor_left accXY accX accY x y zs[j]!
          (idx := idx + j) (n := n)
          hsizeX hsizeY (by omega) hj hacc
      exact ih
        (accXY := xorClmulAt accXY (idx + j) (x ^^^ y) zs[j]!)
        (accX := xorClmulAt accX (idx + j) x zs[j]!)
        (accY := xorClmulAt accY (idx + j) y zs[j]!)
        (by simp [xorClmulAt_size, hsizeX])
        (by simp [xorClmulAt_size, hsizeY])
        htail hstep

/-- `foldl_mulWords_xor_left_coeff` lifts left-factor xor-distributivity across the full `mulWords` double fold, so coefficients of `(xs ^^^ ys) * zs` split as the xor of the two separate products. -/
private theorem foldl_mulWords_xor_left_coeff
    (is : List Nat) (accXY accX accY : Array UInt64) {n : Nat}
    (xs ys zs : Array UInt64)
    (hsizeX : accX.size = accXY.size) (hsizeY : accY.size = accXY.size)
    (hidx : ∀ i ∈ is, ∀ j, j < zs.size → i + j + 1 < accXY.size)
    (hacc : coeffWords accXY n = (coeffWords accX n != coeffWords accY n)) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            let y := ys[i]!
            (List.range zs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) (x ^^^ y) zs[j]!)
              acc)
          accXY)
        n =
      (coeffWords
          (is.foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range zs.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x zs[j]!)
                acc)
            accX)
          n !=
        coeffWords
          (is.foldl
            (fun acc i =>
              let y := ys[i]!
              (List.range zs.size).foldl
                (fun acc j => xorClmulAt acc (i + j) y zs[j]!)
                acc)
            accY)
          n) := by
  induction is generalizing accXY accX accY with
  | nil =>
      simpa using hacc
  | cons i is ih =>
      simp only [List.foldl_cons]
      have hinner :=
        foldl_xorClmulAt_xor_left_coeff (List.range zs.size)
          accXY accX accY (idx := i) (n := n) xs[i]! ys[i]! zs
          hsizeX hsizeY
          (by
            intro j hj
            exact hidx i (by simp) j (List.mem_range.mp hj))
          hacc
      have htail : ∀ i' ∈ is, ∀ j, j < zs.size →
          i' + j + 1 <
            ((List.range zs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) (xs[i]! ^^^ ys[i]!) zs[j]!)
              accXY).size := by
        intro i' hi' j hj
        rw [foldl_xorClmulAt_size]
        exact hidx i' (by simp [hi']) j hj
      exact ih
        (accXY :=
          (List.range zs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) (xs[i]! ^^^ ys[i]!) zs[j]!)
            accXY)
        (accX :=
          (List.range zs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! zs[j]!)
            accX)
        (accY :=
          (List.range zs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) ys[i]! zs[j]!)
            accY)
        (by simp [foldl_xorClmulAt_size, hsizeX])
        (by simp [foldl_xorClmulAt_size, hsizeY])
        htail hinner

/-- `coeffWords_xorClmulAt_congr` says one `xorClmulAt` step preserves coefficient-level equality of two accumulators. -/
private theorem coeffWords_xorClmulAt_congr
    (accA accB : Array UInt64) {idx n : Nat} (x y : UInt64)
    (hidxA : idx + 1 < accA.size) (hidxB : idx + 1 < accB.size)
    (hacc : coeffWords accA n = coeffWords accB n) :
    coeffWords (xorClmulAt accA idx x y) n =
      coeffWords (xorClmulAt accB idx x y) n := by
  by_cases hLow : n / 64 = idx
  · rw [coeffWords_xorClmulAt_low accA x y (by omega) hLow]
    rw [coeffWords_xorClmulAt_low accB x y (by omega) hLow, hacc]
  · by_cases hHigh : n / 64 = idx + 1
    · rw [coeffWords_xorClmulAt_high accA x y (by omega) hidxA hHigh]
      rw [coeffWords_xorClmulAt_high accB x y (by omega) hidxB hHigh, hacc]
    · rw [coeffWords_xorClmulAt_ne accA x y hLow hHigh]
      rw [coeffWords_xorClmulAt_ne accB x y hLow hHigh]
      exact hacc

/-- `foldl_xorClmulAt_congr_coeff` lifts coefficient-level accumulator congruence across the inner `xorClmulAt` fold. -/
private theorem foldl_xorClmulAt_congr_coeff
    (js : List Nat) (accA accB : Array UInt64) {idx n : Nat}
    (x : UInt64) (ys : Array UInt64)
    (hidxA : ∀ j ∈ js, idx + j + 1 < accA.size)
    (hidxB : ∀ j ∈ js, idx + j + 1 < accB.size)
    (hacc : coeffWords accA n = coeffWords accB n) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) accA)
        n =
      coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) accB)
        n := by
  induction js generalizing accA accB with
  | nil =>
      simpa using hacc
  | cons j js ih =>
      simp only [List.foldl_cons]
      have hjA : idx + j + 1 < accA.size := hidxA j (by simp)
      have hjB : idx + j + 1 < accB.size := hidxB j (by simp)
      have htailA : ∀ j' ∈ js,
          idx + j' + 1 < (xorClmulAt accA (idx + j) x ys[j]!).size := by
        intro j' hj'
        rw [xorClmulAt_size]
        exact hidxA j' (by simp [hj'])
      have htailB : ∀ j' ∈ js,
          idx + j' + 1 < (xorClmulAt accB (idx + j) x ys[j]!).size := by
        intro j' hj'
        rw [xorClmulAt_size]
        exact hidxB j' (by simp [hj'])
      exact ih
        (accA := xorClmulAt accA (idx + j) x ys[j]!)
        (accB := xorClmulAt accB (idx + j) x ys[j]!)
        htailA htailB
        (coeffWords_xorClmulAt_congr accA accB x ys[j]!
          (idx := idx + j) (n := n) hjA hjB hacc)


end GF2Poly
end Hex
