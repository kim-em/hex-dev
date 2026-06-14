import HexGF2.Basic
import HexGF2.Clmul

/-!
Packed `GF2Poly` multiplication.

This module lifts the carry-less `UInt64` primitive to polynomial
multiplication on packed `GF(2)` coefficients. Each word pair contributes a
128-bit carry-less product, which is XOR-accumulated into the result words and
then normalized back into the `GF2Poly` invariant.
-/
namespace Hex
namespace GF2Poly

/-- XOR a 128-bit carry-less product into adjacent result words. -/
private def xorClmulAt (acc : Array UInt64) (idx : Nat) (x y : UInt64) : Array UInt64 :=
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
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.shiftRight_eq_div_pow]
  apply decide_eq_decide.mpr
  exact Iff.rfl

/-- `UInt64.bit_xor_bne` rewrites a bit of a word XOR as Boolean inequality of the input bits. -/
private theorem UInt64.bit_xor_bne (a b : UInt64) (i : Nat) :
    ((((a ^^^ b) >>> i.toUInt64) &&& 1) != 0) =
      ((((a >>> i.toUInt64) &&& 1) != 0) !=
        (((b >>> i.toUInt64) &&& 1) != 0)) := by
  rw [UInt64.bne_zero_eq_toNat_bne_zero]
  rw [UInt64.bne_zero_eq_toNat_bne_zero]
  rw [UInt64.bne_zero_eq_toNat_bne_zero]
  simp [UInt64.toNat_xor, UInt64.toNat_shiftRight, UInt64.toNat_and]
  rw [bit_eq_one_eq_testBit]
  rw [bit_eq_one_eq_testBit]
  rw [bit_eq_one_eq_testBit]
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
  rw [clmul_comm x (y ^^^ z)]
  rw [clmul_xor_left]
  rw [clmul_comm y x, clmul_comm z x]
  exact UInt64.bit_xor_bne (clmul x y).2 (clmul x z).2 i

/-- `clmul_xor_right_fst_bit` gives bitwise linearity in the right input for the high word of `clmul`. -/
private theorem clmul_xor_right_fst_bit (x y z : UInt64) (i : Nat) :
    ((((clmul x (y ^^^ z)).1 >>> i.toUInt64) &&& 1) != 0) =
      (((((clmul x y).1 >>> i.toUInt64) &&& 1) != 0) !=
        ((((clmul x z).1 >>> i.toUInt64) &&& 1) != 0)) := by
  rw [clmul_comm x (y ^^^ z)]
  rw [clmul_xor_left]
  rw [clmul_comm y x, clmul_comm z x]
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
  rw [coeffWords_xorClmulAt_low acc (x ^^^ y) z hidx hn]
  rw [coeffWords_xorClmulAt_low acc x z hidx hn]
  rw [clmul_xor_left_snd_bit]
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
  rw [coeffWords_xorClmulAt_high acc (x ^^^ y) z hidx hidxNext hn]
  rw [coeffWords_xorClmulAt_high acc x z hidx hidxNext hn]
  rw [clmul_xor_left_fst_bit]
  cases coeffWords acc n <;>
    cases ((((clmul x z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    cases ((((clmul y z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    rfl

/-- `xorWords_getElem!` unfolds unchecked access to `xorWords` into wordwise XOR. -/
private theorem xorWords_getElem! (xs ys : Array UInt64) (i : Nat) :
    (xorWords xs ys)[i]! = xs[i]! ^^^ ys[i]! := by
  simpa only [getElem!_def] using xorWords_get?_getD xs ys i

/-- `normalizeWords_getElem!` shows normalization leaves unchecked word lookup unchanged. -/
private theorem normalizeWords_getElem! (words : Array UInt64) (i : Nat) :
    (normalizeWords words)[i]! = words[i]! := by
  simpa only [getElem!_def] using normalizeWords_get?_getD words i

/-- `foldl_keep` collapses a fold whose step ignores every input element. -/
private theorem foldl_keep {α β : Type} (xs : List β) (acc : α) :
    xs.foldl (fun acc _ => acc) acc = acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons _ xs ih => simp [ih]

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
  rw [htargetMod]
  rw [clmul_oneHot_low_bit_same_word x hshiftPos hshift hold hbit]

/-- `coeffWords_xorClmulAt_oneHot_low_before_shift` says coefficients below the one-hot shift are left unchanged. -/
private theorem coeffWords_xorClmulAt_oneHot_low_before_shift
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : target / 64 = idx) (hbit : target % 64 < shift) :
    coeffWords (xorClmulAt acc idx x ((1 : UInt64) <<< shift.toUInt64)) target =
      coeffWords acc target := by
  rw [coeffWords_xorClmulAt_low acc x ((1 : UInt64) <<< shift.toUInt64) hidx hn]
  rw [clmul_oneHot_low_bit_before_shift_false x hshiftPos hshift hbit]
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
  rw [htargetMod]
  rw [clmul_oneHot_high_bit_carry_word x hshiftPos hshift hold hbit]

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
  rw [htargetMod]
  rw [clmul_oneHot_left_low_bit_same_word x hshiftPos hshift hold hbit]

/-- `coeffWords_xorClmulAt_oneHot_left_low_before_shift` says coefficients below the one-hot shift are left unchanged for a left one-hot factor. -/
private theorem coeffWords_xorClmulAt_oneHot_left_low_before_shift
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : target / 64 = idx) (hbit : target % 64 < shift) :
    coeffWords (xorClmulAt acc idx ((1 : UInt64) <<< shift.toUInt64) x) target =
      coeffWords acc target := by
  rw [coeffWords_xorClmulAt_low acc ((1 : UInt64) <<< shift.toUInt64) x hidx hn]
  rw [clmul_oneHot_left_low_bit_before_shift_false x hshiftPos hshift hbit]
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
  rw [htargetMod]
  rw [clmul_oneHot_left_high_bit_carry_word x hshiftPos hshift hold hbit]

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
  rw [words_monomial]
  rw [Array.getElem!_eq_getD]
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
  rw [words_monomial]
  rw [Array.getElem!_eq_getD]
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
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
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
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
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
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
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
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
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
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
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
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_ne
    (hnLow := hLow) (hnHigh := hHigh)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

/-- `xorClmulAt_zero_left` says accumulating a carry-less product whose left word is `0` leaves the accumulator unchanged. -/
private theorem xorClmulAt_zero_left (acc : Array UInt64) (idx : Nat) (x : UInt64) :
    xorClmulAt acc idx 0 x = acc := by
  simp [xorClmulAt, Array.setIfInBounds_getElem!]

/-- `coeffWords_xorClmulAt_zero_left` says a zero left word leaves every coefficient of the accumulator unchanged. -/
private theorem coeffWords_xorClmulAt_zero_left (acc : Array UInt64) (idx n : Nat)
    (x : UInt64) :
    coeffWords (xorClmulAt acc idx 0 x) n = coeffWords acc n := by
  rw [xorClmulAt_zero_left]

/-- `coeffWords_xorClmulAt_xor_left` proves left-linearity over `^^^`: accumulating with left word `x ^^^ y` matches the XOR of the two separate accumulations with `x` and `y`, given accumulators related the same way. -/
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
    rw [coeffWords_xorClmulAt_low accX x z (by simpa [hsizeX]) hLow]
    rw [coeffWords_xorClmulAt_low accY y z (by simpa [hsizeY]) hLow]
    rw [clmul_xor_left_snd_bit, hacc]
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
      rw [coeffWords_xorClmulAt_ne accX x z hLow hHigh]
      rw [coeffWords_xorClmulAt_ne accY y z hLow hHigh]
      exact hacc

/-- `foldl_xorClmulAt_xor_left_coeff` lifts left-linearity over `^^^` across a fold over column indices `js`. -/
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

/-- `foldl_mulWords_xor_left_coeff` lifts left-linearity over `^^^` across the full doubly-nested `mulWords` fold: the product with left input `xs ^^^ ys` matches the XOR of the products with `xs` and `ys`. -/
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

/-- `coeffWords_xorClmulAt_congr` says two accumulators agreeing at coefficient `n` still agree there after the same `xorClmulAt` step. -/
private theorem coeffWords_xorClmulAt_congr
    (accA accB : Array UInt64) {idx n : Nat} (x y : UInt64)
    (hidxA : idx + 1 < accA.size) (hidxB : idx + 1 < accB.size)
    (hacc : coeffWords accA n = coeffWords accB n) :
    coeffWords (xorClmulAt accA idx x y) n =
      coeffWords (xorClmulAt accB idx x y) n := by
  by_cases hLow : n / 64 = idx
  · rw [coeffWords_xorClmulAt_low accA x y (by omega) hLow]
    rw [coeffWords_xorClmulAt_low accB x y (by omega) hLow]
    rw [hacc]
  · by_cases hHigh : n / 64 = idx + 1
    · rw [coeffWords_xorClmulAt_high accA x y (by omega) hidxA hHigh]
      rw [coeffWords_xorClmulAt_high accB x y (by omega) hidxB hHigh]
      rw [hacc]
    · rw [coeffWords_xorClmulAt_ne accA x y hLow hHigh]
      rw [coeffWords_xorClmulAt_ne accB x y hLow hHigh]
      exact hacc

/-- `foldl_xorClmulAt_congr_coeff` lifts the coefficient congruence across a fold over column indices `js`. -/
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

/-- `foldl_mulWords_congr_coeff` lifts the coefficient congruence across the full doubly-nested `mulWords` fold. -/
private theorem foldl_mulWords_congr_coeff
    (is : List Nat) (accA accB : Array UInt64) {n : Nat}
    (xs ys : Array UInt64)
    (hidxA : ∀ i ∈ is, ∀ j, j < ys.size → i + j + 1 < accA.size)
    (hidxB : ∀ i ∈ is, ∀ j, j < ys.size → i + j + 1 < accB.size)
    (hacc : coeffWords accA n = coeffWords accB n) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          accA)
        n =
      coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          accB)
        n := by
  induction is generalizing accA accB with
  | nil =>
      simpa using hacc
  | cons i is ih =>
      simp only [List.foldl_cons]
      have hinner :=
        foldl_xorClmulAt_congr_coeff (List.range ys.size)
          accA accB (idx := i) (n := n) xs[i]! ys
          (by
            intro j hj
            exact hidxA i (by simp) j (List.mem_range.mp hj))
          (by
            intro j hj
            exact hidxB i (by simp) j (List.mem_range.mp hj))
          hacc
      have htailA : ∀ i' ∈ is, ∀ j, j < ys.size →
          i' + j + 1 <
            ((List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
              accA).size := by
        intro i' hi' j hj
        rw [foldl_xorClmulAt_size]
        exact hidxA i' (by simp [hi']) j hj
      have htailB : ∀ i' ∈ is, ∀ j, j < ys.size →
          i' + j + 1 <
            ((List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
              accB).size := by
        intro i' hi' j hj
        rw [foldl_xorClmulAt_size]
        exact hidxB i' (by simp [hi']) j hj
      exact ih
        (accA :=
          (List.range ys.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
            accA)
        (accB :=
          (List.range ys.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
            accB)
        htailA htailB hinner

/-- `foldl_xorClmulAt_zero_left` says folding `xorClmulAt` with a zero left word over any index list leaves the accumulator array unchanged. -/
private theorem foldl_xorClmulAt_zero_left (js : List Nat) (acc : Array UInt64)
    (idx : Nat) (ys : Array UInt64) :
    js.foldl (fun acc j => xorClmulAt acc (idx + j) 0 ys[j]!) acc = acc := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [xorClmulAt_zero_left, ih]

/-- `foldl_xorClmulAt_zero_left_coeff` is the coefficient-level form: a zero left word across the fold preserves every coefficient. -/
private theorem foldl_xorClmulAt_zero_left_coeff (js : List Nat) (acc : Array UInt64)
    (idx n : Nat) (ys : Array UInt64) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) 0 ys[j]!) acc)
        n =
      coeffWords acc n := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, coeffWords_xorClmulAt_zero_left]

/-- `getElem!_eq_zero_of_size_le` says an out-of-bounds `getElem!` on a `UInt64` array returns the default `0`. -/
private theorem getElem!_eq_zero_of_size_le (xs : Array UInt64) {i : Nat}
    (hi : xs.size ≤ i) :
    xs[i]! = 0 := by
  rw [getElem!_def]
  rw [Array.getElem?_eq_none]
  · rfl
  · exact hi

/-- `foldl_mulWords_range_add_zero_left_coeff` says extending the outer index range by `k` past `xs.size` adds only zero left words, so every coefficient is unchanged. -/
private theorem foldl_mulWords_range_add_zero_left_coeff
    (xs ys acc : Array UInt64) (n k : Nat) :
    coeffWords
        ((List.range (xs.size + k)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n =
      coeffWords
        ((List.range xs.size).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show xs.size + Nat.succ k = xs.size + k + 1 by omega]
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [getElem!_eq_zero_of_size_le xs (by omega)]
      rw [foldl_xorClmulAt_zero_left_coeff]
      exact ih

/-- `foldl_mulWords_range_extend_left_coeff` generalises that to any outer range length `m ≥ xs.size`: the extra indices contribute zero left words and leave every coefficient unchanged. -/
private theorem foldl_mulWords_range_extend_left_coeff
    (xs ys acc : Array UInt64) (n m : Nat) (hsize : xs.size ≤ m) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n =
      coeffWords
        ((List.range xs.size).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n := by
  have hm : m = xs.size + (m - xs.size) := by omega
  rw [hm]
  exact foldl_mulWords_range_add_zero_left_coeff xs ys acc n (m - xs.size)

/-- `foldl_mulWords_left_monomial_zero_prefix_coeff_aux` is the list-general step: when `monomial k` is the left input, its below-active prefix words contribute nothing to any coefficient across the fold. -/
private theorem foldl_mulWords_left_monomial_zero_prefix_coeff_aux
    (is : List Nat) (acc xs : Array UInt64) (k n : Nat)
    (hmem : ∀ i ∈ is, i < k / 64) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := (monomial k).words[i]!
            (List.range xs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
              acc)
          acc)
        n =
      coeffWords acc n := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < k / 64 := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < k / 64 := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      have hzero : (monomial k).words[i]! = 0 :=
        words_monomial_getElem!_zero_lt (k := k) hi
      rw [hzero]
      rw [ih (acc :=
        (List.range xs.size).foldl (fun acc j => xorClmulAt acc (i + j) 0 xs[j]!) acc)
        htail]
      exact foldl_xorClmulAt_zero_left_coeff (List.range xs.size) acc i n xs

/-- `foldl_mulWords_left_monomial_zero_prefix_coeff` specialises the aux to the prefix range `List.range (k / 64)`: the words below the active word of `monomial k` leave every coefficient unchanged. -/
private theorem foldl_mulWords_left_monomial_zero_prefix_coeff
    (acc xs : Array UInt64) (k n : Nat) :
    coeffWords
        ((List.range (k / 64)).foldl
          (fun acc i =>
            let x := (monomial k).words[i]!
            (List.range xs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
              acc)
          acc)
        n =
      coeffWords acc n := by
  exact foldl_mulWords_left_monomial_zero_prefix_coeff_aux
    (List.range (k / 64)) acc xs k n (by
      intro i hi
      exact List.mem_range.mp hi)

/-- `foldl_mulWords_left_monomial_zero_prefix_aux` is the array-level list-general form: the below-active prefix words of `monomial k` as left input leave the accumulator array unchanged across the fold. -/
private theorem foldl_mulWords_left_monomial_zero_prefix_aux
    (is : List Nat) (acc xs : Array UInt64) (k : Nat)
    (hmem : ∀ i ∈ is, i < k / 64) :
    is.foldl
        (fun acc i =>
          let x := (monomial k).words[i]!
          (List.range xs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
            acc)
        acc =
      acc := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < k / 64 := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < k / 64 := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      have hzero : (monomial k).words[i]! = 0 :=
        words_monomial_getElem!_zero_lt (k := k) hi
      rw [hzero, foldl_xorClmulAt_zero_left, ih (hmem := htail)]

/-- `foldl_mulWords_left_monomial_zero_prefix` specialises the array-level aux to `List.range (k / 64)`: the words below the active word of `monomial k` leave the accumulator array unchanged. -/
private theorem foldl_mulWords_left_monomial_zero_prefix
    (acc xs : Array UInt64) (k : Nat) :
    (List.range (k / 64)).foldl
        (fun acc i =>
          let x := (monomial k).words[i]!
          (List.range xs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
            acc)
        acc =
      acc := by
  exact foldl_mulWords_left_monomial_zero_prefix_aux
    (List.range (k / 64)) acc xs k (by
      intro i hi
      exact List.mem_range.mp hi)

private theorem coeffWords_xorClmulAt_monomial_left_active_low
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
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
  simpa [hsourceMod, Nat.add_comm] using
    coeffWords_xorClmulAt_oneHot_left_low_same_word
      (acc := acc) (idx := k / 64 + i) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

private theorem coeffWords_xorClmulAt_monomial_left_active_zero
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 = 0) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have htargetDiv : (n + k) / 64 = k / 64 + i := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  have htargetMod : (n + k) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  rw [words_monomial_getElem!_active k]
  rw [coeffWords_xorClmulAt_low acc ((1 : UInt64) <<< (k % 64).toUInt64) x hidx
    htargetDiv]
  rw [clmul_oneHot_left_snd x (Nat.mod_lt k (by decide : 0 < 64))]
  simp [hbitShift, htargetMod]

private theorem coeffWords_xorClmulAt_monomial_left_active_low_before_shift
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hword : target / 64 = k / 64 + i)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        target =
      coeffWords acc target := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_left_low_before_shift
    (acc := acc) (idx := k / 64 + i) (target := target)
    (shift := k % 64) x hidx hshiftPos hshift hword hbit

private theorem coeffWords_xorClmulAt_monomial_left_active_high
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hidxNext : k / 64 + i + 1 < acc.size)
    (hn : n / 64 = i) (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
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
  simpa [hsourceMod, Nat.add_comm] using
    coeffWords_xorClmulAt_oneHot_left_high_carry_word
      (acc := acc) (idx := k / 64 + i) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hidxNext hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

private theorem coeffWords_xorClmulAt_monomial_left_active_high_after_carry
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hidxNext : k / 64 + i + 1 < acc.size)
    (hword : target / 64 = k / 64 + i + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        target =
      coeffWords acc target := by
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_left_high_after_carry
    (acc := acc) (idx := k / 64 + i) (target := target)
    (shift := k % 64) x hidx hidxNext hshift hword hbit

private theorem foldl_xorClmulAt_monomial_left_ne
    (acc xs : Array UInt64) {k i target : Nat}
    (hLow : target / 64 ≠ k / 64 + i)
    (hHigh : target / 64 ≠ k / 64 + i + 1) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! xs[i]!)
        target =
      coeffWords acc target := by
  exact coeffWords_xorClmulAt_ne
    (acc := acc) (idx := k / 64 + i) (n := target)
    ((monomial k).words[k / 64]!) xs[i]! hLow hHigh

private theorem foldl_xorClmulAt_monomial_left_target_lt
    (js : List Nat) (acc xs : Array UInt64) {k target : Nat}
    (hmem : ∀ j ∈ js, j < xs.size) (hacc : k / 64 + xs.size + 1 ≤ acc.size)
    (htarget : target < k) :
    coeffWords
        (js.foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          acc)
        target =
      coeffWords acc target := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      have hj : j < xs.size := hmem j (by simp)
      have htail : ∀ j' ∈ js, j' < xs.size := by
        intro j' hj'
        exact hmem j' (by simp [hj'])
      simp only [List.foldl_cons]
      rw [ih
        (acc := xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
        htail]
      · by_cases hLow : target / 64 = k / 64 + j
        · have hbitShift : k % 64 ≠ 0 := by
            intro hzero
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            omega
          have hbit : target % 64 < k % 64 := by
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact coeffWords_xorClmulAt_monomial_left_active_low_before_shift
            (acc := acc) (i := j) (k := k) (target := target) (x := xs[j]!)
            (hidx := by omega) hLow hbitShift hbit
        · have hHigh : target / 64 ≠ k / 64 + j + 1 := by
            intro hHigh
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact foldl_xorClmulAt_monomial_left_ne
            (acc := acc) (xs := xs) (k := k) (i := j) (target := target)
            hLow hHigh
      · simpa [xorClmulAt_size] using hacc

private theorem foldl_xorClmulAt_monomial_left_source_oob
    (js : List Nat) (acc xs : Array UInt64) {k source : Nat}
    (hmem : ∀ j ∈ js, j < xs.size) (hacc : k / 64 + xs.size + 1 ≤ acc.size)
    (hsource : xs.size ≤ source / 64) :
    coeffWords
        (js.foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          acc)
        (source + k) =
      coeffWords acc (source + k) := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      have hj : j < xs.size := hmem j (by simp)
      have htail : ∀ j' ∈ js, j' < xs.size := by
        intro j' hj'
        exact hmem j' (by simp [hj'])
      simp only [List.foldl_cons]
      rw [ih
        (acc := xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
        htail]
      · by_cases hLow : (source + k) / 64 = k / 64 + j
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            exact coeffWords_xorClmulAt_monomial_left_active_low_before_shift
              (acc := acc) (i := j) (k := k) (target := source + k)
              (x := xs[j]!) (hidx := by omega) hLow hbitShift hbit
          · have hsourceWord : source / 64 = j := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = k / 64 + j + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · exact coeffWords_xorClmulAt_monomial_left_active_high_after_carry
                (acc := acc) (i := j) (k := k) (target := source + k)
                (x := xs[j]!) (hidx := by omega) (hidxNext := by omega)
                hHigh hbit
            · have hsourceWord : source / 64 = j := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · exact foldl_xorClmulAt_monomial_left_ne
              (acc := acc) (xs := xs) (k := k) (i := j) (target := source + k)
              hLow hHigh
      · simpa [xorClmulAt_size] using hacc

private theorem foldl_xorClmulAt_monomial_left_prefix_before_source
    (xs : Array UInt64) {k source m : Nat} (hm : m ≤ source / 64)
    (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          (Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64)))
        (source + k) =
      false := by
  induction m with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      rw [coeffWords]
      have hword :
          ((Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64))[
              (source + k) / 64]?).getD 0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
  | succ m ih =>
      have hm_le : m ≤ source / 64 := by omega
      have hm_lt : m < source / 64 := by omega
      rw [show m + 1 = m.succ by omega]
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [words_monomial_size]
      by_cases hLow : (source + k) / 64 = k / 64 + m
      · by_cases hbit : (source + k) % 64 < k % 64
        · have hbitShift : k % 64 ≠ 0 := by omega
          rw [coeffWords_xorClmulAt_monomial_left_active_low_before_shift
            (acc :=
              (List.range m).foldl
                (fun acc j => xorClmulAt acc (k / 64 + j)
                  (monomial k).words[k / 64]! xs[j]!)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
            (i := m) (k := k) (target := source + k) (x := xs[m]!)
            (hidx := by
              have hsize := foldl_xorClmulAt_size (List.range m)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                (k / 64) (monomial k).words[k / 64]! xs
              have hcap : k / 64 + m <
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                simp
                omega
              simpa [hsize] using hcap)
            hLow hbitShift hbit]
          simpa [words_monomial_size] using ih hm_le
        · have hsourceWord : source / 64 = m := by
            have hsourceSplit := Nat.div_add_mod source 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetSplit := Nat.div_add_mod (source + k) 64
            have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
            omega
          omega
      · by_cases hHigh : (source + k) / 64 = k / 64 + m + 1
        · by_cases hbit : k % 64 ≤ (source + k) % 64
          · rw [coeffWords_xorClmulAt_monomial_left_active_high_after_carry
              (acc :=
                (List.range m).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range m)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + m <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hidxNext := by
                have hsize := foldl_xorClmulAt_size (List.range m)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + m + 1 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              hHigh hbit]
            simpa [words_monomial_size] using ih hm_le
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · rw [foldl_xorClmulAt_monomial_left_ne
            (acc :=
              (List.range m).foldl
                (fun acc j => xorClmulAt acc (k / 64 + j)
                  (monomial k).words[k / 64]! xs[j]!)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
            (xs := xs) (k := k) (i := m) (target := source + k) hLow hHigh]
          simpa [words_monomial_size] using ih hm_le

private theorem foldl_xorClmulAt_monomial_left_prefix_after_source
    (xs : Array UInt64) {k source m : Nat} (hm : source / 64 + 1 ≤ m)
    (hmSize : m ≤ xs.size) (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          (Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64)))
        (source + k) =
      coeffWords xs source := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_active : m = source / 64
      · subst hm_active
        rw [show source / 64 + 1 = (source / 64).succ by omega]
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [words_monomial_size]
        have hprefix := foldl_xorClmulAt_monomial_left_prefix_before_source xs
          (m := source / 64) (k := k) (source := source) (by omega) hsource
        have hprefix' :
            coeffWords
                ((List.range (source / 64)).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
                (source + k) =
              false := by
          simpa [words_monomial_size] using hprefix
        by_cases hbitShift : k % 64 = 0
        · rw [coeffWords_xorClmulAt_monomial_left_active_zero
            (acc :=
              (List.range (source / 64)).foldl
                (fun acc j => xorClmulAt acc (k / 64 + j)
                  (monomial k).words[k / 64]! xs[j]!)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
            (i := source / 64) (k := k) (n := source) (x := xs[source / 64]!)
            (hidx := by
              have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                (k / 64) (monomial k).words[k / 64]! xs
              have hcap : k / 64 + source / 64 <
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                simp
                omega
              simpa [hsize] using hcap) (hn := rfl) hbitShift]
          rw [hprefix']
          have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
            exact (getElem!_def xs (source / 64)).symm
          simp [coeffWords, hget]
        · by_cases hbit : source % 64 + k % 64 < 64
          · rw [coeffWords_xorClmulAt_monomial_left_active_low
              (acc :=
                (List.range (source / 64)).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := source / 64) (k := k) (n := source) (x := xs[source / 64]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + source / 64 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap) (hn := rfl)
              hbitShift hbit]
            rw [hprefix']
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
          · rw [coeffWords_xorClmulAt_monomial_left_active_high
              (acc :=
                (List.range (source / 64)).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := source / 64) (k := k) (n := source) (x := xs[source / 64]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + source / 64 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hidxNext := by
                have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + source / 64 + 1 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hn := rfl) (hbit := by omega)]
            rw [hprefix']
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
      · have hm_tail : source / 64 + 1 ≤ m := by omega
        have hm_gt : source / 64 < m := by omega
        rw [show m + 1 = m.succ by omega]
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [words_monomial_size]
        by_cases hLow : (source + k) / 64 = k / 64 + m
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            rw [coeffWords_xorClmulAt_monomial_left_active_low_before_shift
              (acc :=
                (List.range m).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range m)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + m <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              hLow hbitShift hbit]
            simpa [words_monomial_size] using ih hm_tail (by omega)
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = k / 64 + m + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · rw [coeffWords_xorClmulAt_monomial_left_active_high_after_carry
                (acc :=
                  (List.range m).foldl
                    (fun acc j => xorClmulAt acc (k / 64 + j)
                      (monomial k).words[k / 64]! xs[j]!)
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
                (i := m) (k := k) (target := source + k) (x := xs[m]!)
                (hidx := by
                  have hsize := foldl_xorClmulAt_size (List.range m)
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                    (k / 64) (monomial k).words[k / 64]! xs
                  have hcap : k / 64 + m <
                      (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                (hidxNext := by
                  have hsize := foldl_xorClmulAt_size (List.range m)
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                    (k / 64) (monomial k).words[k / 64]! xs
                  have hcap : k / 64 + m + 1 <
                      (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                hHigh hbit]
              simpa [words_monomial_size] using ih hm_tail (by omega)
            · have hsourceWord : source / 64 = m := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · rw [foldl_xorClmulAt_monomial_left_ne
              (acc :=
                (List.range m).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (xs := xs) (k := k) (i := m) (target := source + k) hLow hHigh]
            simpa [words_monomial_size] using ih hm_tail (by omega)

private theorem foldl_mulWords_monomial_active_zero
    (acc xs : Array UInt64) {k n : Nat}
    (hidx : n / 64 + k / 64 < acc.size) (hbitShift : k % 64 = 0) :
    coeffWords
        ((List.range (n / 64 + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (n + k) =
      (coeffWords
          ((List.range (n / 64)).foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range (monomial k).words.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
                acc)
            acc)
          (n + k) !=
        (((xs[n / 64]! >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show n / 64 + 1 = (n / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_zero
    (acc :=
      (List.range (n / 64)).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[n / 64]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hn := rfl) (hbitShift := hbitShift)

private theorem foldl_mulWords_monomial_active_low
    (acc xs : Array UInt64) {k n : Nat}
    (hidx : n / 64 + k / 64 < acc.size)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        ((List.range (n / 64 + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (n + k) =
      (coeffWords
          ((List.range (n / 64)).foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range (monomial k).words.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
                acc)
            acc)
          (n + k) !=
        (((xs[n / 64]! >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show n / 64 + 1 = (n / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_low
    (acc :=
      (List.range (n / 64)).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[n / 64]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hn := rfl) (hbitShift := hbitShift) (hbit := hbit)

private theorem foldl_mulWords_monomial_active_high
    (acc xs : Array UInt64) {k n : Nat}
    (hidx : n / 64 + k / 64 < acc.size)
    (hidxNext : n / 64 + k / 64 + 1 < acc.size)
    (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        ((List.range (n / 64 + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (n + k) =
      (coeffWords
          ((List.range (n / 64)).foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range (monomial k).words.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
                acc)
            acc)
          (n + k) !=
        (((xs[n / 64]! >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show n / 64 + 1 = (n / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_high
    (acc :=
      (List.range (n / 64)).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[n / 64]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hidxNext := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidxNext)
    (hn := rfl) (hbit := hbit)

private theorem foldl_mulWords_monomial_active_low_before_shift
    (acc xs : Array UInt64) {i k target : Nat}
    (hidx : i + k / 64 < acc.size) (hword : target / 64 = i + k / 64)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        ((List.range (i + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords
        ((List.range i).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target := by
  rw [show i + 1 = i.succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_low_before_shift
    (acc :=
      (List.range i).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[i]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range i) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hword := hword) (hbitShift := hbitShift) (hbit := hbit)

private theorem foldl_mulWords_monomial_active_high_after_carry
    (acc xs : Array UInt64) {i k target : Nat}
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hword : target / 64 = i + k / 64 + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        ((List.range (i + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords
        ((List.range i).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target := by
  rw [show i + 1 = i.succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_high_after_carry
    (acc :=
      (List.range i).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[i]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range i) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hidxNext := by
      have hsize := foldl_mulWords_size (List.range i) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidxNext)
    (hword := hword) (hbit := hbit)

private theorem foldl_mulWords_monomial_ne
    (acc xs : Array UInt64) {i k target : Nat}
    (hLow : target / 64 ≠ i + k / 64)
    (hHigh : target / 64 ≠ i + k / 64 + 1) :
    coeffWords
        ((List.range (i + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords
        ((List.range i).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target := by
  rw [show i + 1 = i.succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_ne
    (acc :=
      (List.range i).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[i]!) (hLow := hLow) (hHigh := hHigh)

private theorem foldl_mulWords_monomial_target_lt
    (is : List Nat) (acc xs : Array UInt64) {k target : Nat}
    (hmem : ∀ i ∈ is, i < xs.size)
    (hacc : xs.size + (k / 64 + 1) ≤ acc.size) (htarget : target < k) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords acc target := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < xs.size := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < xs.size := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      rw [ih
        (acc :=
          (List.range (monomial k).words.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
            acc)
        htail]
      · rw [words_monomial_size]
        by_cases hLow : target / 64 = i + k / 64
        · have hbitShift : k % 64 ≠ 0 := by
            intro hzero
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            omega
          have hbit : target % 64 < k % 64 := by
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact foldl_xorClmulAt_monomial_active_low_before_shift
            (acc := acc) (i := i) (k := k) (target := target) (x := xs[i]!)
            (hidx := by omega) hLow hbitShift hbit
        · have hHigh : target / 64 ≠ i + k / 64 + 1 := by
            intro hHigh
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact foldl_xorClmulAt_monomial_ne
            (acc := acc) (i := i) (k := k) (target := target) (x := xs[i]!)
            hLow hHigh
      · simpa [foldl_xorClmulAt_size] using hacc

private theorem foldl_mulWords_monomial_source_oob
    (is : List Nat) (acc xs : Array UInt64) {k source : Nat}
    (hmem : ∀ i ∈ is, i < xs.size)
    (hacc : xs.size + (k / 64 + 1) ≤ acc.size)
    (hsource : xs.size ≤ source / 64) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (source + k) =
      coeffWords acc (source + k) := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < xs.size := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < xs.size := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      rw [ih
        (acc :=
          (List.range (monomial k).words.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
            acc)
        htail]
      · rw [words_monomial_size]
        by_cases hLow : (source + k) / 64 = i + k / 64
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            exact foldl_xorClmulAt_monomial_active_low_before_shift
              (acc := acc) (i := i) (k := k) (target := source + k) (x := xs[i]!)
              (hidx := by omega) hLow hbitShift hbit
          · have hsourceWord : source / 64 = i := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = i + k / 64 + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · exact foldl_xorClmulAt_monomial_active_high_after_carry
                (acc := acc) (i := i) (k := k) (target := source + k)
                (x := xs[i]!) (hidx := by omega) (hidxNext := by omega)
                hHigh hbit
            · have hsourceWord : source / 64 = i := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · exact foldl_xorClmulAt_monomial_ne
              (acc := acc) (i := i) (k := k) (target := source + k) (x := xs[i]!)
              hLow hHigh
      · simpa [foldl_xorClmulAt_size] using hacc

/-- Raw packed-word multiplication before trailing zero normalization. -/
private def mulWords (xs ys : Array UInt64) : Array UInt64 :=
  if xs.isEmpty || ys.isEmpty then
    #[]
  else
    (List.range xs.size).foldl
      (fun acc i =>
        let x := xs[i]!
        (List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
          acc)
      (Array.replicate (xs.size + ys.size) (0 : UInt64))

private theorem coeffWords_replicate_zero (size n : Nat) :
    coeffWords (Array.replicate size (0 : UInt64)) n = false := by
  rw [coeffWords]
  by_cases h : n / 64 < (Array.replicate size (0 : UInt64)).size
  · rw [Array.getElem?_eq_getElem h]
    simp
  · rw [Array.getElem?_eq_none]
    · simp
    · exact Nat.le_of_not_gt h

private theorem coeffWords_empty (n : Nat) :
    coeffWords #[] n = false := by
  rw [coeffWords]
  simp

private theorem coeffWords_mulWords_common_left
    (xs zs : Array UInt64) (n m : Nat) (hm : xs.size ≤ m) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range zs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x zs[j]!)
              acc)
          (Array.replicate (m + zs.size) (0 : UInt64)))
        n =
      coeffWords (mulWords xs zs) n := by
  unfold mulWords
  by_cases hzs : zs.isEmpty
  · have hcommon :=
      foldl_mulWords_range_extend_left_coeff xs zs
        (Array.replicate (m + zs.size) (0 : UInt64)) n m hm
    rw [hcommon]
    have hzsize : zs.size = 0 := by
      simpa [Array.isEmpty] using hzs
    simp only [hzs, hzsize, List.range_zero, List.foldl_nil, Bool.or_true, ↓reduceIte]
    rw [foldl_keep, coeffWords_replicate_zero, coeffWords_empty]
  · by_cases hxs : xs.isEmpty
    · have hcommon :=
        foldl_mulWords_range_extend_left_coeff xs zs
          (Array.replicate (m + zs.size) (0 : UInt64)) n m hm
      rw [hcommon]
      have hxsize : xs.size = 0 := by
        simpa [Array.isEmpty] using hxs
      simp [hxs, hzs, hxsize, coeffWords_replicate_zero, coeffWords_empty]
    · have hcommon :=
        foldl_mulWords_range_extend_left_coeff xs zs
          (Array.replicate (m + zs.size) (0 : UInt64)) n m hm
      rw [hcommon]
      have hcongr :=
        foldl_mulWords_congr_coeff (List.range xs.size)
          (Array.replicate (m + zs.size) (0 : UInt64))
          (Array.replicate (xs.size + zs.size) (0 : UInt64))
          (n := n) xs zs
          (by
            intro i hi j hj
            have hi' : i < xs.size := List.mem_range.mp hi
            simpa using (by omega : i + j + 1 < m + zs.size))
          (by
            intro i hi j hj
            have hi' : i < xs.size := List.mem_range.mp hi
            simpa using (by omega : i + j + 1 < xs.size + zs.size))
          (by
            rw [coeffWords_replicate_zero, coeffWords_replicate_zero])
      rw [hcongr]
      simp [hxs, hzs]

private theorem coeffWords_mulWords_xor_left_same_size
    (xs ys zs : Array UInt64) (n : Nat) (hsize : xs.size = ys.size) :
    coeffWords (mulWords (xorWords xs ys) zs) n =
      (coeffWords (mulWords xs zs) n != coeffWords (mulWords ys zs) n) := by
  unfold mulWords
  by_cases hzs : zs.isEmpty
  · simp [hzs]
    exact coeffWords_empty n
  · by_cases hxs : xs.isEmpty
    · have hxempty : xs = #[] := by
        apply Array.eq_empty_of_size_eq_zero
        simpa [Array.isEmpty] using hxs
      have hyempty : ys = #[] := by
        apply Array.eq_empty_of_size_eq_zero
        have hxsize : xs.size = 0 := by
          simp [hxempty]
        omega
      simp [hxempty, hyempty, xorWords, coeffWords_empty]
    · have hys : ys.isEmpty = false := by
        have hxsize : xs.size ≠ 0 := by
          intro hz
          apply hxs
          simpa [Array.isEmpty] using hz
        have hysize : ys.size ≠ 0 := by omega
        rw [Array.isEmpty]
        simp [hysize]
      have hxor : (xorWords xs ys).isEmpty = false := by
        rw [Array.isEmpty]
        have hxsize : xs.size ≠ 0 := by
          intro hz
          apply hxs
          simpa [Array.isEmpty] using hz
        have hmax : max xs.size ys.size ≠ 0 := by omega
        simp [xorWords_size, hmax]
      have hzarr : zs ≠ #[] := by
        intro hz
        apply hzs
        simp [hz]
      simp [hxs, hys, hxor, xorWords_size, hsize, xorWords_getElem!, hzarr]
      exact foldl_mulWords_xor_left_coeff (List.range ys.size)
        (Array.replicate (ys.size + zs.size) (0 : UInt64))
        (Array.replicate (ys.size + zs.size) (0 : UInt64))
        (Array.replicate (ys.size + zs.size) (0 : UInt64))
        (n := n) xs ys zs rfl rfl
        (by
          intro i hi j hj
          have hi' : i < ys.size := List.mem_range.mp hi
          simp
          omega)
        (by
          rw [coeffWords_replicate_zero]
          rfl)

private theorem coeffWords_mulWords_xor_left
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (xorWords xs ys) zs) n =
      (coeffWords (mulWords xs zs) n != coeffWords (mulWords ys zs) n) := by
  let m := max xs.size ys.size
  rw [← coeffWords_mulWords_common_left (xorWords xs ys) zs n m (by simp [m])]
  rw [← coeffWords_mulWords_common_left xs zs n m
    (by simpa [m] using Nat.le_max_left xs.size ys.size)]
  rw [← coeffWords_mulWords_common_left ys zs n m
    (by simpa [m] using Nat.le_max_right xs.size ys.size)]
  simp only [xorWords_getElem!]
  exact foldl_mulWords_xor_left_coeff (List.range m)
    (Array.replicate (m + zs.size) (0 : UInt64))
    (Array.replicate (m + zs.size) (0 : UInt64))
    (Array.replicate (m + zs.size) (0 : UInt64))
    (n := n) xs ys zs rfl rfl
    (by
      intro i hi j hj
      have hi' : i < m := List.mem_range.mp hi
      simpa using (by omega : i + j + 1 < m + zs.size))
    (by
      rw [coeffWords_replicate_zero]
      rfl)

private theorem coeffWords_mulWords_monomial_lt
    (xs : Array UInt64) {k target : Nat} (htarget : target < k) :
    coeffWords (mulWords xs (monomial k).words) target = false := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · simp [hxs, coeffWords]
  · have hys : ¬ (monomial k).words.isEmpty := by
      rw [words_monomial]
      simp
    simp [hxs, hys]
    rw [foldl_mulWords_monomial_target_lt]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))[target / 64]?).getD
              0 = 0 := by
        by_cases h : target / 64 < (Array.replicate (xs.size + (monomial k).words.size)
            (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword]
      rw [UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro i hi
      exact List.mem_range.mp hi
    · simp [words_monomial_size]
    · exact htarget

private theorem coeffWords_mulWords_monomial_source_oob
    (xs : Array UInt64) {k source : Nat} (hsource : xs.size ≤ source / 64) :
    coeffWords (mulWords xs (monomial k).words) (source + k) = false := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · simp [hxs, coeffWords]
  · have hys : ¬ (monomial k).words.isEmpty := by
      rw [words_monomial]
      simp
    simp [hxs, hys]
    rw [foldl_mulWords_monomial_source_oob]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))[(source + k) / 64]?).getD
              0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword]
      rw [UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro i hi
      exact List.mem_range.mp hi
    · simp [words_monomial_size]
    · exact hsource

private theorem foldl_mulWords_monomial_prefix_before_source
    (xs : Array UInt64) {k source m : Nat} (hm : m ≤ source / 64)
    (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)))
        (source + k) =
      false := by
  induction m with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      rw [coeffWords]
      have hword :
          ((Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))[
              (source + k) / 64]?).getD 0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
  | succ m ih =>
      have hm_le : m ≤ source / 64 := by omega
      have hm_lt : m < source / 64 := by omega
      rw [show m + 1 = m.succ by omega]
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [words_monomial_size]
      by_cases hLow : (source + k) / 64 = m + k / 64
      · by_cases hbit : (source + k) % 64 < k % 64
        · have hbitShift : k % 64 ≠ 0 := by omega
          rw [foldl_xorClmulAt_monomial_active_low_before_shift
            (acc :=
              (List.range m).foldl
                (fun acc i =>
                  let x := xs[i]!
                  (List.range (k / 64 + 1)).foldl
                    (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                    acc)
                (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
            (i := m) (k := k) (target := source + k) (x := xs[m]!)
            (hidx := by
              have hsize := foldl_mulWords_size (List.range m)
                (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                xs (monomial k).words
              rw [words_monomial_size] at hsize
              have hcap : m + k / 64 <
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                simp
                omega
              simpa [hsize] using hcap)
            hLow hbitShift hbit]
          simpa [words_monomial_size] using ih hm_le
        · have hsourceWord : source / 64 = m := by
            have hsourceSplit := Nat.div_add_mod source 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetSplit := Nat.div_add_mod (source + k) 64
            have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
            omega
          omega
      · by_cases hHigh : (source + k) / 64 = m + k / 64 + 1
        · by_cases hbit : k % 64 ≤ (source + k) % 64
          · rw [foldl_xorClmulAt_monomial_active_high_after_carry
              (acc :=
                (List.range m).foldl
                  (fun acc i =>
                    let x := xs[i]!
                    (List.range (k / 64 + 1)).foldl
                      (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                      acc)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_mulWords_size (List.range m)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                  xs (monomial k).words
                rw [words_monomial_size] at hsize
                have hcap : m + k / 64 <
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hidxNext := by
                have hsize := foldl_mulWords_size (List.range m)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                  xs (monomial k).words
                rw [words_monomial_size] at hsize
                have hcap : m + k / 64 + 1 <
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              hHigh hbit]
            simpa [words_monomial_size] using ih hm_le
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · rw [foldl_xorClmulAt_monomial_ne
            (acc :=
              (List.range m).foldl
                (fun acc i =>
                  let x := xs[i]!
                  (List.range (k / 64 + 1)).foldl
                    (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                    acc)
                (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
            (i := m) (k := k) (target := source + k) (x := xs[m]!) hLow hHigh]
          simpa [words_monomial_size] using ih hm_le

private theorem foldl_mulWords_monomial_prefix_after_source
    (xs : Array UInt64) {k source m : Nat} (hm : source / 64 + 1 ≤ m)
    (hmSize : m ≤ xs.size)
    (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)))
        (source + k) =
      coeffWords xs source := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_active : m = source / 64
      · subst hm_active
        by_cases hbitShift : k % 64 = 0
        · rw [foldl_mulWords_monomial_active_zero
            (acc := Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))
            (xs := xs) (k := k) (n := source)
            (hidx := by simp [words_monomial_size]; omega) hbitShift]
          have hprefix := foldl_mulWords_monomial_prefix_before_source xs
            (m := source / 64) (k := k) (source := source) (by omega) hsource
          rw [hprefix]
          have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
            exact (getElem!_def xs (source / 64)).symm
          simp [coeffWords, hget]
        · by_cases hbit : source % 64 + k % 64 < 64
          · rw [foldl_mulWords_monomial_active_low
              (acc := Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))
              (xs := xs) (k := k) (n := source)
              (hidx := by simp [words_monomial_size]; omega) hbitShift hbit]
            have hprefix := foldl_mulWords_monomial_prefix_before_source xs
              (m := source / 64) (k := k) (source := source) (by omega) hsource
            rw [hprefix]
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
          · rw [foldl_mulWords_monomial_active_high
              (acc := Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))
              (xs := xs) (k := k) (n := source)
              (hidx := by simp [words_monomial_size]; omega)
              (hidxNext := by simp [words_monomial_size]; omega)
              (hbit := by omega)]
            have hprefix := foldl_mulWords_monomial_prefix_before_source xs
              (m := source / 64) (k := k) (source := source) (by omega) hsource
            rw [hprefix]
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
      · have hm_tail : source / 64 + 1 ≤ m := by omega
        have hm_gt : source / 64 < m := by omega
        rw [show m + 1 = m.succ by omega]
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [words_monomial_size]
        by_cases hLow : (source + k) / 64 = m + k / 64
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            rw [foldl_xorClmulAt_monomial_active_low_before_shift
              (acc :=
                (List.range m).foldl
                  (fun acc i =>
                    let x := xs[i]!
                    (List.range (k / 64 + 1)).foldl
                      (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                      acc)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_mulWords_size (List.range m)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                  xs (monomial k).words
                rw [words_monomial_size] at hsize
                have hcap : m + k / 64 <
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
            hLow hbitShift hbit]
            simpa [words_monomial_size] using ih hm_tail (by omega)
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = m + k / 64 + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · rw [foldl_xorClmulAt_monomial_active_high_after_carry
                (acc :=
                  (List.range m).foldl
                    (fun acc i =>
                      let x := xs[i]!
                      (List.range (k / 64 + 1)).foldl
                        (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                        acc)
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
                (i := m) (k := k) (target := source + k) (x := xs[m]!)
                (hidx := by
                  have hsize := foldl_mulWords_size (List.range m)
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                    xs (monomial k).words
                  rw [words_monomial_size] at hsize
                  have hcap : m + k / 64 <
                      (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                (hidxNext := by
                  have hsize := foldl_mulWords_size (List.range m)
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                    xs (monomial k).words
                  rw [words_monomial_size] at hsize
                  have hcap : m + k / 64 + 1 <
                      (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                hHigh hbit]
              simpa [words_monomial_size] using ih hm_tail (by omega)
            · have hsourceWord : source / 64 = m := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · rw [foldl_xorClmulAt_monomial_ne
              (acc :=
                (List.range m).foldl
                  (fun acc i =>
                    let x := xs[i]!
                    (List.range (k / 64 + 1)).foldl
                      (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                      acc)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!) hLow hHigh]
            simpa [words_monomial_size] using ih hm_tail (by omega)

private theorem coeffWords_mulWords_monomial_source
    (xs : Array UInt64) {k source : Nat} (hsource : source / 64 < xs.size) :
    coeffWords (mulWords xs (monomial k).words) (source + k) =
      coeffWords xs source := by
  unfold mulWords
  have hxs : ¬xs.isEmpty := by
    intro hempty
    have hsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hempty
    omega
  have hys : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  simp [hxs, hys]
  exact foldl_mulWords_monomial_prefix_after_source xs
    (m := xs.size) (k := k) (source := source) (by omega) (by omega) hsource

private theorem coeffWords_monomial_mulWords_lt
    (xs : Array UInt64) {k target : Nat} (htarget : target < k) :
    coeffWords (mulWords (monomial k).words xs) target = false := by
  unfold mulWords
  have hmon : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  by_cases hxs : xs.isEmpty
  · simp [hmon, hxs, coeffWords]
  · simp [hmon, hxs]
    rw [words_monomial_size]
    rw [show k / 64 + 1 = (k / 64).succ by omega]
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [foldl_mulWords_left_monomial_zero_prefix]
    rw [foldl_xorClmulAt_monomial_left_target_lt]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))[target / 64]?).getD
              0 = 0 := by
        by_cases h : target / 64 <
            (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro j hj
      exact List.mem_range.mp hj
    · simp
      omega
    · exact htarget

private theorem coeffWords_monomial_mulWords_source_oob
    (xs : Array UInt64) {k source : Nat} (hsource : xs.size ≤ source / 64) :
    coeffWords (mulWords (monomial k).words xs) (source + k) = false := by
  unfold mulWords
  have hmon : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  by_cases hxs : xs.isEmpty
  · simp [hmon, hxs, coeffWords]
  · simp [hmon, hxs]
    rw [words_monomial_size]
    rw [show k / 64 + 1 = (k / 64).succ by omega]
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [foldl_mulWords_left_monomial_zero_prefix]
    rw [foldl_xorClmulAt_monomial_left_source_oob]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))[(source + k) / 64]?).getD
              0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro j hj
      exact List.mem_range.mp hj
    · simp
      omega
    · exact hsource

private theorem coeffWords_monomial_mulWords_source
    (xs : Array UInt64) {k source : Nat} (hsource : source / 64 < xs.size) :
    coeffWords (mulWords (monomial k).words xs) (source + k) =
      coeffWords xs source := by
  unfold mulWords
  have hmon : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  have hxs : ¬ xs.isEmpty := by
    intro hempty
    have hsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hempty
    omega
  simp [hmon, hxs]
  rw [words_monomial_size]
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [foldl_mulWords_left_monomial_zero_prefix]
  simpa [words_monomial_size] using
    foldl_xorClmulAt_monomial_left_prefix_after_source xs
      (m := xs.size) (k := k) (source := source) (by omega) (by omega) hsource

private def clmulCoeffAt (idx : Nat) (x y : UInt64) (n : Nat) : Bool :=
  if n / 64 = idx then
    (((clmul x y).2 >>> (n % 64).toUInt64) &&& 1) != 0
  else if n / 64 = idx + 1 then
    (((clmul x y).1 >>> (n % 64).toUInt64) &&& 1) != 0
  else
    false

private def xorBoolList (bits : List Bool) : Bool :=
  bits.foldl (fun acc bit => acc != bit) false

private theorem Bool.bne_assoc (a b c : Bool) :
    ((a != b) != c) = (a != (b != c)) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem foldl_bne_start (bits : List Bool) (acc : Bool) :
    bits.foldl (fun acc bit => acc != bit) acc =
      (acc != xorBoolList bits) := by
  unfold xorBoolList
  induction bits generalizing acc with
  | nil =>
      cases acc <;> rfl
  | cons bit bits ih =>
      simp only [List.foldl_cons]
      rw [ih (acc != bit), ih (false != bit)]
      generalize htail : List.foldl (fun acc bit => acc != bit) false bits = tail
      cases acc <;> cases bit <;> cases tail <;> rfl

private theorem xorBoolList_cons (bit : Bool) (bits : List Bool) :
    xorBoolList (bit :: bits) = (bit != xorBoolList bits) := by
  unfold xorBoolList
  simp only [List.foldl_cons]
  rw [foldl_bne_start]
  cases bit <;> rfl

private theorem xorBoolList_append (xs ys : List Bool) :
    xorBoolList (xs ++ ys) = (xorBoolList xs != xorBoolList ys) := by
  unfold xorBoolList
  rw [List.foldl_append, foldl_bne_start]
  simp [xorBoolList]

private theorem Bool.bne_medial (a b c d : Bool) :
    ((a != b) != (c != d)) = ((a != c) != (b != d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem List.flatMap_const_nil {α β : Type} (xs : List α) :
    xs.flatMap (fun _ => ([] : List β)) = [] := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [ih]

private theorem List.flatMap_empty_input {α β : Type} (f : α → List β) :
    ([] : List α).flatMap f = [] := by
  rfl

private theorem List.flatMap_singleton {α β : Type} (xs : List α) (f : α → β) :
    xs.flatMap (fun x => [f x]) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [ih]

private theorem List.flatMap_congr_left {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [h x (by simp)]
      rw [ih]
      intro y hy
      exact h y (by simp [hy])

private theorem xorBoolList_flatMap_append {α : Type}
    (xs : List α) (left right : α → List Bool) :
    xorBoolList (xs.flatMap fun x => left x ++ right x) =
      (xorBoolList (xs.flatMap left) != xorBoolList (xs.flatMap right)) := by
  induction xs with
  | nil =>
      simp [xorBoolList]
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, xorBoolList_append, xorBoolList_append, ih]
      rw [xorBoolList_append]
      generalize xorBoolList (left x) = a
      generalize xorBoolList (List.flatMap left xs) = b
      generalize xorBoolList (right x) = c
      generalize xorBoolList (List.flatMap right xs) = d
      cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem xorBoolList_wordPairs_swap
    (m n : Nat) (term : Nat → Nat → Bool) :
    xorBoolList
        (List.flatMap
          (fun i => (List.range n).map (fun j => term i j))
          (List.range m)) =
      xorBoolList
        (List.flatMap
          (fun j => (List.range m).map (fun i => term i j))
          (List.range n)) := by
  induction m with
  | zero =>
      simp [xorBoolList, List.flatMap_const_nil]
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, ih]
      rw [List.flatMap_empty_input]
      simp only [List.append_nil]
      have hcols :
          xorBoolList
              (List.flatMap
                (fun j => (List.range m ++ [m]).map (fun i => term i j))
                (List.range n)) =
            (xorBoolList
                (List.flatMap
                  (fun j => (List.range m).map (fun i => term i j))
                  (List.range n)) !=
              xorBoolList ((List.range n).map (fun j => term m j))) := by
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [xorBoolList_flatMap_append]
        rw [List.flatMap_singleton]
      rw [hcols]

private theorem xorBoolList_flatMap_congr_xor {α : Type}
    {xs : List α} {left right : α → List Bool}
    (h : ∀ x, x ∈ xs → xorBoolList (left x) = xorBoolList (right x)) :
    xorBoolList (xs.flatMap left) = xorBoolList (xs.flatMap right) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, xorBoolList_append]
      rw [h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

private theorem xorBoolList_map_xorBoolList {α : Type}
    (xs : List α) (terms : α → List Bool) :
    xorBoolList (xs.map (fun x => xorBoolList (terms x))) =
      xorBoolList (xs.flatMap terms) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [xorBoolList_cons, xorBoolList_append, ih]

private theorem xorBoolList_map_bne_congr {α : Type}
    {xs : List α} {left right both : α → Bool}
    (h : ∀ x, x ∈ xs → (left x != right x) = both x) :
    (xorBoolList (xs.map left) != xorBoolList (xs.map right)) =
      xorBoolList (xs.map both) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [xorBoolList_cons, xorBoolList_cons, xorBoolList_cons]
      rw [Bool.bne_medial, h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

private theorem xorBoolList_flatMap_bne_congr {α : Type}
    {xs : List α} {left right both : α → List Bool}
    (h : ∀ x, x ∈ xs →
      (xorBoolList (left x) != xorBoolList (right x)) = xorBoolList (both x)) :
    (xorBoolList (xs.flatMap left) != xorBoolList (xs.flatMap right)) =
      xorBoolList (xs.flatMap both) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, xorBoolList_append, xorBoolList_append]
      rw [Bool.bne_medial, h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

private theorem xorBoolList_flatMap_ranges_swap_list
    (m n : Nat) (term : Nat → Nat → List Bool) :
    xorBoolList
        (List.flatMap
          (fun i => (List.range n).flatMap (fun j => term i j))
          (List.range m)) =
      xorBoolList
        (List.flatMap
          (fun j => (List.range m).flatMap (fun i => term i j))
          (List.range n)) := by
  calc
    xorBoolList
        (List.flatMap
          (fun i => (List.range n).flatMap (fun j => term i j))
          (List.range m))
        = xorBoolList
            ((List.range m).map
              (fun i => xorBoolList
                ((List.range n).flatMap (fun j => term i j)))) := by
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
            ((List.range m).map
              (fun i => xorBoolList
                ((List.range n).map (fun j => xorBoolList (term i j))))) := by
            congr 1
            apply List.map_congr_left
            intro i _hi
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
            (List.flatMap
              (fun i => (List.range n).map (fun j => xorBoolList (term i j)))
              (List.range m)) := by
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
            (List.flatMap
              (fun j => (List.range m).map (fun i => xorBoolList (term i j)))
              (List.range n)) := by
            exact xorBoolList_wordPairs_swap m n (fun i j => xorBoolList (term i j))
    _ = xorBoolList
            ((List.range n).map
              (fun j => xorBoolList
                ((List.range m).map (fun i => xorBoolList (term i j))))) := by
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
            ((List.range n).map
              (fun j => xorBoolList
                ((List.range m).flatMap (fun i => term i j)))) := by
            congr 1
            apply List.map_congr_left
            intro j _hj
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
        (List.flatMap
          (fun j => (List.range m).flatMap (fun i => term i j))
          (List.range n)) := by
            rw [xorBoolList_map_xorBoolList]

/-- Reindex a triple XOR from the left-associated word-pair grouping
`(i,j),k` to the right-associated grouping `i,(j,k)`, keeping the outer
source word `i` fixed and swapping the two inner finite ranges. -/
private theorem xorBoolList_wordTriples_assoc
    (m n o : Nat) (term : Nat → Nat → Nat → Bool) :
    xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j => (List.range o).map (fun k => term i j k))
              (List.range n))
          (List.range m)) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun k => (List.range n).map (fun j => term i j k))
              (List.range o))
          (List.range m)) := by
  apply xorBoolList_flatMap_congr_xor
  intro i _hi
  exact xorBoolList_wordPairs_swap n o (fun j k => term i j k)

/-- Array-specialized triple reindexing theorem for raw multiplication
associativity proof terms.  Later coefficient lemmas instantiate `term` with
the source-word contribution predicate built from `xs[i]!`, `ys[j]!`, and
`zs[k]!`. -/
private theorem xorBoolList_sourceTriples_assoc
    (xs ys zs : Array UInt64) (term : Nat → Nat → Nat → Bool) :
    xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j => (List.range zs.size).map (fun k => term i j k))
              (List.range ys.size))
          (List.range xs.size)) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun k => (List.range ys.size).map (fun j => term i j k))
              (List.range zs.size))
          (List.range xs.size)) := by
  exact xorBoolList_wordTriples_assoc xs.size ys.size zs.size term

/-- XOR a list of machine words as the word-level analogue of `xorBoolList`. -/
private def xorWordList : List UInt64 → UInt64
  | [] => 0
  | word :: words => word ^^^ xorWordList words

/-- The raw word contribution of a single `clmul x y` placed at word offset
`idx`, projected to result word slot `slot`. -/
private def clmulWordAt (idx : Nat) (x y : UInt64) (slot : Nat) : UInt64 :=
  if slot = idx then
    (clmul x y).2
  else if slot = idx + 1 then
    (clmul x y).1
  else
    0

private theorem UInt64.xor_assoc (a b c : UInt64) :
    (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_xor, Nat.xor_assoc]

private theorem UInt64.xor_zero (a : UInt64) :
    a ^^^ 0 = a := by
  apply UInt64.toNat_inj.mp
  simp

private theorem UInt64.zero_xor (a : UInt64) :
    0 ^^^ a = a := by
  apply UInt64.toNat_inj.mp
  simp

private theorem Array.getElem!_setIfInBounds_ne {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (v : α) (hne : i ≠ j) :
    (xs.setIfInBounds i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hne]
  · simp [hi]

private theorem replicate_zero_getElem! (size slot : Nat) :
    (Array.replicate size (0 : UInt64))[slot]! = 0 := by
  rw [Array.getElem!_eq_getD]
  by_cases hslot : slot < (Array.replicate size (0 : UInt64)).size
  · have hslot' : slot < size := by
      simpa using hslot
    simp [Array.getD, hslot']
  · have hslot' : size ≤ slot := by
      simpa using Nat.le_of_not_gt hslot
    simp [Array.getD, hslot']
    rfl

private theorem xorWordList_append (xs ys : List UInt64) :
    xorWordList (xs ++ ys) = xorWordList xs ^^^ xorWordList ys := by
  induction xs with
  | nil =>
      simp [xorWordList]
  | cons x xs ih =>
      simp only [List.cons_append, xorWordList]
      rw [ih, UInt64.xor_assoc]

private theorem xorClmulAt_getElem!_contrib
    (acc : Array UInt64) {idx slot : Nat} (x y : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size) :
    (xorClmulAt acc idx x y)[slot]! =
      acc[slot]! ^^^ clmulWordAt idx x y slot := by
  unfold xorClmulAt clmulWordAt
  by_cases hLow : slot = idx
  · subst slot
    simp [hidx]
  · by_cases hHigh : slot = idx + 1
    · subst slot
      simp [hidx, hidxNext]
    · have hLow' : idx ≠ slot := Ne.symm hLow
      have hHigh' : idx + 1 ≠ slot := Ne.symm hHigh
      rcases hprod : clmul x y with ⟨hi, lo⟩
      simp [hidx, hidxNext, hLow, hHigh,
        Array.getElem!_setIfInBounds_ne, hLow', hHigh']

private theorem foldl_xorClmulAt_getElem!_contrib
    (js : List Nat) (acc : Array UInt64) (idx : Nat) (x : UInt64)
    (ys : Array UInt64) (slot : Nat)
    (hbound : ∀ j ∈ js, idx + j + 1 < acc.size) :
    (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc)[slot]! =
      (acc[slot]! ^^^
        xorWordList (js.map (fun j => clmulWordAt (idx + j) x ys[j]! slot))) := by
  induction js generalizing acc with
  | nil =>
      simp [xorWordList]
  | cons j js ih =>
      simp only [List.foldl_cons, List.map_cons]
      have htail := ih (xorClmulAt acc (idx + j) x ys[j]!)
        (by
          intro j' hj'
          have h := hbound j' (by simp [hj'])
          simpa [xorClmulAt_size] using h)
      rw [htail]
      have hhead := xorClmulAt_getElem!_contrib acc (idx := idx + j)
        (slot := slot) x ys[j]!
        (by
          have h := hbound j (by simp)
          omega)
        (hbound j (by simp))
      rw [hhead, xorWordList, UInt64.xor_assoc]

private theorem foldl_mulWords_getElem!_contrib
    (is : List Nat) (acc : Array UInt64) (xs ys : Array UInt64) (slot : Nat)
    (hbound : ∀ i ∈ is, ∀ j ∈ List.range ys.size, i + j + 1 < acc.size) :
    (is.foldl
      (fun acc i =>
        let x := xs[i]!
        (List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
          acc)
      acc)[slot]! =
      (acc[slot]! ^^^
        xorWordList
          (List.flatMap
            (fun i =>
              (List.range ys.size).map
                (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
            is)) := by
  induction is generalizing acc with
  | nil =>
      simp [xorWordList]
  | cons i is ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      have htail := ih
        ((List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!) acc)
        (by
          intro i' hi' j hj
          have h := hbound i' (by simp [hi']) j hj
          simpa [foldl_xorClmulAt_size] using h)
      rw [htail]
      have hinner := foldl_xorClmulAt_getElem!_contrib
        (List.range ys.size) acc i xs[i]! ys slot
        (by
          intro j hj
          exact hbound i (by simp) j hj)
      rw [hinner]
      rw [xorWordList_append, UInt64.xor_assoc]

private theorem clmulCoeffAt_zero_left (idx : Nat) (y : UInt64) (n : Nat) :
    clmulCoeffAt idx 0 y n = false := by
  unfold clmulCoeffAt
  rw [clmul_zero_left]
  by_cases hLow : n / 64 = idx
  · simp [hLow]
  · by_cases hHigh : n / 64 = idx + 1 <;> simp [hLow, hHigh]

private theorem clmulCoeffAt_xor_left
    (idx : Nat) (x y z : UInt64) (n : Nat) :
    clmulCoeffAt idx (x ^^^ y) z n =
      (clmulCoeffAt idx x z n != clmulCoeffAt idx y z n) := by
  unfold clmulCoeffAt
  by_cases hLow : n / 64 = idx
  · simp [hLow]
    rw [clmul_xor_left_snd_bit]
  · by_cases hHigh : n / 64 = idx + 1
    · simp [hHigh]
      rw [clmul_xor_left_fst_bit]
    · simp [hLow, hHigh]

private theorem clmulCoeffAt_zero_right (idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x 0 n = false := by
  unfold clmulCoeffAt
  rw [clmul_zero_right]
  by_cases hLow : n / 64 = idx
  · simp [hLow]
  · by_cases hHigh : n / 64 = idx + 1 <;> simp [hLow, hHigh]

private theorem clmulCoeffAt_xor_right
    (idx : Nat) (x y z : UInt64) (n : Nat) :
    clmulCoeffAt idx x (y ^^^ z) n =
      (clmulCoeffAt idx x y n != clmulCoeffAt idx x z n) := by
  unfold clmulCoeffAt
  by_cases hLow : n / 64 = idx
  · simp [hLow]
    rw [clmul_xor_right_snd_bit]
  · by_cases hHigh : n / 64 = idx + 1
    · simp [hHigh]
      rw [clmul_xor_right_fst_bit]
    · simp [hLow, hHigh]

private theorem clmulCoeffAt_xorWordList_left
    (words : List UInt64) (idx : Nat) (z : UInt64) (n : Nat) :
    clmulCoeffAt idx (xorWordList words) z n =
      xorBoolList (words.map (fun word => clmulCoeffAt idx word z n)) := by
  induction words with
  | nil =>
      change clmulCoeffAt idx 0 z n = false
      exact clmulCoeffAt_zero_left idx z n
  | cons word words ih =>
      rw [xorWordList, clmulCoeffAt_xor_left]
      change (clmulCoeffAt idx word z n != clmulCoeffAt idx (xorWordList words) z n) =
        xorBoolList (clmulCoeffAt idx word z n ::
          words.map (fun word => clmulCoeffAt idx word z n))
      rw [xorBoolList_cons, ih]

private theorem clmulCoeffAt_xorWordList_right
    (words : List UInt64) (idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x (xorWordList words) n =
      xorBoolList (words.map (fun word => clmulCoeffAt idx x word n)) := by
  induction words with
  | nil =>
      change clmulCoeffAt idx x 0 n = false
      exact clmulCoeffAt_zero_right idx x n
  | cons word words ih =>
      rw [xorWordList, clmulCoeffAt_xor_right]
      change (clmulCoeffAt idx x word n != clmulCoeffAt idx x (xorWordList words) n) =
        xorBoolList (clmulCoeffAt idx x word n ::
          words.map (fun word => clmulCoeffAt idx x word n))
      rw [xorBoolList_cons, ih]

private theorem coeffWords_xorClmulAt_contrib
    (acc : Array UInt64) {idx n : Nat} (x y : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size) :
    coeffWords (xorClmulAt acc idx x y) n =
      (coeffWords acc n != clmulCoeffAt idx x y n) := by
  unfold clmulCoeffAt
  by_cases hLow : n / 64 = idx
  · rw [coeffWords_xorClmulAt_low acc x y hidx hLow]
    simp [hLow]
  · by_cases hHigh : n / 64 = idx + 1
    · rw [coeffWords_xorClmulAt_high acc x y hidx hidxNext hHigh]
      simp [hHigh]
    · rw [coeffWords_xorClmulAt_ne acc x y hLow hHigh]
      simp [hLow, hHigh]

private theorem foldl_xorClmulAt_coeff_contrib
    (js : List Nat) (acc : Array UInt64) (idx : Nat) (x : UInt64)
    (ys : Array UInt64) (n : Nat)
    (hbound : ∀ j ∈ js, idx + j + 1 < acc.size) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc)
        n =
      (coeffWords acc n !=
        xorBoolList (js.map (fun j => clmulCoeffAt (idx + j) x ys[j]! n))) := by
  induction js generalizing acc with
  | nil =>
      simp [xorBoolList]
  | cons j js ih =>
      simp only [List.foldl_cons, List.map_cons]
      have hidx : idx + j < acc.size := by
        have h := hbound j (by simp)
        omega
      have hidxNext : idx + j + 1 < acc.size := hbound j (by simp)
      rw [ih]
      · rw [coeffWords_xorClmulAt_contrib acc x ys[j]! hidx hidxNext]
        rw [xorBoolList_cons, Bool.bne_assoc]
      · intro j' hj'
        have h := hbound j' (by simp [hj'])
        simpa [xorClmulAt_size] using h

private theorem foldl_mulWords_coeff_contrib
    (is : List Nat) (acc : Array UInt64) (xs ys : Array UInt64) (n : Nat)
    (hbound : ∀ i ∈ is, ∀ j ∈ List.range ys.size, i + j + 1 < acc.size) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n =
      (coeffWords acc n !=
        xorBoolList
          (List.flatMap
            (fun i =>
              (List.range ys.size).map
                (fun j => clmulCoeffAt (i + j) xs[i]! ys[j]! n))
            is)) := by
  induction is generalizing acc with
  | nil =>
      simp [xorBoolList]
  | cons i is ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      · have hinner := foldl_xorClmulAt_coeff_contrib
          (List.range ys.size) acc i xs[i]! ys n
          (by
            intro j hj
            exact hbound i (by simp) j hj)
        rw [hinner]
        rw [xorBoolList_append, Bool.bne_assoc]
      · intro i' hi' j hj
        have h := hbound i' (by simp [hi']) j hj
        simpa [foldl_xorClmulAt_size] using h

private theorem coeffWords_mulWords_contrib (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs ys) n =
      xorBoolList
        (List.flatMap
          (fun i =>
            (List.range ys.size).map
              (fun j => clmulCoeffAt (i + j) xs[i]! ys[j]! n))
          (List.range xs.size)) := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · have hxsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hxs
    simp [hxs, hxsize, coeffWords_empty, xorBoolList]
  · by_cases hys : ys.isEmpty
    · have hysize : ys.size = 0 := by
        simpa [Array.isEmpty] using hys
      have hflat :
          List.flatMap (fun _ : Nat => ([] : List Bool)) (List.range xs.size) = [] := by
        generalize hlist : List.range xs.size = is
        induction is with
        | nil => rfl
        | cons i is ih =>
            simp [List.flatMap_cons]
      simp [hxs, hys, hysize, coeffWords_empty, xorBoolList, hflat]
    · simp [hxs, hys]
      rw [foldl_mulWords_coeff_contrib]
      · rw [coeffWords_replicate_zero]
        simp
      · intro i hi j hj
        have hi' : i < xs.size := List.mem_range.mp hi
        have hj' : j < ys.size := List.mem_range.mp hj
        simp
        omega

/-- A raw product word is the XOR of all source word-pair contributions whose
low or high `clmul` word lands in that result slot. -/
private theorem mulWords_getElem!_contrib
    (xs ys : Array UInt64) (slot : Nat) :
    (mulWords xs ys)[slot]! =
      xorWordList
        (List.flatMap
          (fun i =>
            (List.range ys.size).map
              (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
          (List.range xs.size)) := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · have hxsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hxs
    simp [hxs, hxsize, xorWordList]
    rfl
  · by_cases hys : ys.isEmpty
    · have hysize : ys.size = 0 := by
        simpa [Array.isEmpty] using hys
      have hflat :
          List.flatMap (fun _ : Nat => ([] : List UInt64)) (List.range xs.size) = [] := by
        generalize hlist : List.range xs.size = is
        induction is with
        | nil => rfl
        | cons i is ih =>
            simp [List.flatMap_cons]
      simp [hxs, hys, hysize, xorWordList, hflat]
      rfl
    · simp [hxs, hys]
      rw [foldl_mulWords_getElem!_contrib]
      · rw [replicate_zero_getElem!, UInt64.zero_xor]
      · intro i hi j hj
        have hi' : i < xs.size := List.mem_range.mp hi
        have hj' : j < ys.size := List.mem_range.mp hj
        simp
        omega

/-- Expand a later `clmul` coefficient whose left input is an intermediate raw
product word into source word-pair contributions. -/
private theorem clmulCoeffAt_mulWords_left_contrib
    (xs ys : Array UInt64) (slot idx : Nat) (z : UInt64) (n : Nat) :
    clmulCoeffAt idx (mulWords xs ys)[slot]! z n =
      xorBoolList
        ((List.flatMap
          (fun i =>
            (List.range ys.size).map
              (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
          (List.range xs.size)).map
          (fun word => clmulCoeffAt idx word z n)) := by
  rw [mulWords_getElem!_contrib, clmulCoeffAt_xorWordList_left]

/-- Expand a later `clmul` coefficient whose right input is an intermediate raw
product word into source word-pair contributions. -/
private theorem clmulCoeffAt_mulWords_right_contrib
    (ys zs : Array UInt64) (slot idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x (mulWords ys zs)[slot]! n =
      xorBoolList
        ((List.flatMap
          (fun j =>
            (List.range zs.size).map
              (fun k => clmulWordAt (j + k) ys[j]! zs[k]! slot))
          (List.range ys.size)).map
          (fun word => clmulCoeffAt idx x word n)) := by
  rw [mulWords_getElem!_contrib, clmulCoeffAt_xorWordList_right]

/-- Source-word contribution list for one coefficient of the left-associated
raw product `(xs * ys) * zs`.  The outer product contributes a word slot and a
`zs` source word; each such intermediate word is expanded back to the
`xs`/`ys` source pair contributions that created it. -/
private def leftAssocSourceTripleContribs
    (xs ys zs : Array UInt64) (n : Nat) : List Bool :=
  List.flatMap
    (fun slot =>
      List.flatMap
        (fun k =>
          (List.flatMap
            (fun i =>
              (List.range ys.size).map
                (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
            (List.range xs.size)).map
            (fun word => clmulCoeffAt (slot + k) word zs[k]! n))
        (List.range zs.size))
    (List.range (mulWords xs ys).size)

/-- Source-word contribution list for one coefficient of the right-associated
raw product `xs * (ys * zs)`.  The outer product contributes an `xs` source
word and an intermediate word slot; each intermediate word is expanded back to
the `ys`/`zs` source pair contributions that created it. -/
private def rightAssocSourceTripleContribs
    (xs ys zs : Array UInt64) (n : Nat) : List Bool :=
  List.flatMap
    (fun i =>
      List.flatMap
        (fun slot =>
          (List.flatMap
            (fun j =>
              (List.range zs.size).map
                (fun k => clmulWordAt (j + k) ys[j]! zs[k]! slot))
            (List.range ys.size)).map
            (fun word => clmulCoeffAt (i + slot) xs[i]! word n))
        (List.range (mulWords ys zs).size))
    (List.range xs.size)

/-- Contributions from one fixed source triple `(i,j,k)` to the left-associated
word product, varying only the intermediate `(xs * ys)` result slot. -/
private def leftAssocFixedTripleContribs
    (i j k : Nat) (x y z : UInt64) (n slotBound : Nat) : List Bool :=
  (List.range slotBound).map
    (fun slot => clmulCoeffAt (slot + k) (clmulWordAt (i + j) x y slot) z n)

/-- Contributions from one fixed source triple `(i,j,k)` to the right-associated
word product, varying only the intermediate `(ys * zs)` result slot. -/
private def rightAssocFixedTripleContribs
    (i j k : Nat) (x y z : UInt64) (n slotBound : Nat) : List Bool :=
  (List.range slotBound).map
    (fun slot => clmulCoeffAt (i + slot) x (clmulWordAt (j + k) y z slot) n)

/-- The selected bit of one machine word, using the same projection shape as
the existing coefficient lemmas. -/
private def wordBitAt (word : UInt64) (bit : Nat) : Bool :=
  (((word >>> bit.toUInt64) &&& 1) != 0)

private theorem wordBitAt_getElem!_eq_coeff
    (p : GF2Poly) {i bit : Nat} (hbit : bit < 64) :
    wordBitAt p.words[i]! bit = p.coeff (64 * i + bit) := by
  have hdiv : (64 * i + bit) / 64 = i := by
    rw [Nat.mul_add_div (by decide : 64 > 0)]
    rw [Nat.div_eq_of_lt hbit, Nat.add_zero]
  have hmod : (64 * i + bit) % 64 = bit := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hbit
  rw [Array.getElem!_eq_getD]
  simp [coeff, coeffWords, wordBitAt, hdiv, hmod, default]

/-- The one-hot contribution of a selected source bit of a word. -/
private def oneHotBitWord (word : UInt64) (bit : Nat) : UInt64 :=
  if wordBitAt word bit then
    (1 : UInt64) <<< bit.toUInt64
  else
    0

private theorem xorWordList_oneHotBitWords_eq (word : UInt64) :
    xorWordList ((List.range 64).map (fun bit => oneHotBitWord word bit)) = word := by
  simp [xorWordList, oneHotBitWord, wordBitAt, List.range, List.range.loop]
  bv_decide

private theorem clmulCoeffAt_zero_word_right (idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x 0 n = false :=
  clmulCoeffAt_zero_right idx x n

private theorem clmul_rightBitFold_low
    (x y : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x y).2 bit =
      xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).2 bit)) := by
  have hlow : bit / 64 = 0 := Nat.div_eq_of_lt hbit
  have hmod : bit % 64 = bit := Nat.mod_eq_of_lt hbit
  have hcoeff :
      wordBitAt (clmul x y).2 bit = clmulCoeffAt 0 x y bit := by
    unfold wordBitAt clmulCoeffAt
    simp [hlow, hmod]
  rw [hcoeff]
  calc
    clmulCoeffAt 0 x y bit =
        clmulCoeffAt 0 x (xorWordList ((List.range 64).map
          (fun bit => oneHotBitWord y bit))) bit := by
          rw [xorWordList_oneHotBitWords_eq]
    _ = xorBoolList
        (List.map (fun word => clmulCoeffAt 0 x word bit)
          ((List.range 64).map (fun bit => oneHotBitWord y bit))) := by
          rw [clmulCoeffAt_xorWordList_right]
    _ = xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).2 bit)) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro b hb
          cases hyb : wordBitAt y b
          · simp [oneHotBitWord, hyb, clmulCoeffAt_zero_word_right]
          · simp [oneHotBitWord, hyb]
            unfold clmulCoeffAt wordBitAt
            simp [hlow, hmod]

private theorem clmul_rightBitFold_high
    (x y : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x y).1 bit =
      xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit)) := by
  have hhigh : (bit + 64) / 64 = 0 + 1 := by omega
  have hmod : (bit + 64) % 64 = bit := by omega
  have hcoeff :
      wordBitAt (clmul x y).1 bit = clmulCoeffAt 0 x y (bit + 64) := by
    unfold wordBitAt clmulCoeffAt
    simp [hhigh, hmod]
  rw [hcoeff]
  calc
    clmulCoeffAt 0 x y (bit + 64) =
        clmulCoeffAt 0 x (xorWordList ((List.range 64).map
          (fun bit => oneHotBitWord y bit))) (bit + 64) := by
          rw [xorWordList_oneHotBitWords_eq]
    _ = xorBoolList
        (List.map (fun word => clmulCoeffAt 0 x word (bit + 64))
          ((List.range 64).map (fun bit => oneHotBitWord y bit))) := by
          rw [clmulCoeffAt_xorWordList_right]
    _ = xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit)) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro b hb
          cases hyb : wordBitAt y b
          · simp [oneHotBitWord, hyb, clmulCoeffAt_zero_word_right]
          · simp [oneHotBitWord, hyb]
            unfold clmulCoeffAt wordBitAt
            simp [hhigh, hmod]

private theorem xorBoolList_range_false (n : Nat) :
    xorBoolList ((List.range n).map (fun _ => false)) = false := by
  induction n with
  | zero =>
      simp [xorBoolList]
  | succ n ih =>
      rw [List.range_succ, List.map_append, xorBoolList_append, ih]
      simp [xorBoolList]

private theorem xorBoolList_map_and_left (value : Bool) (bits : List Bool) :
    xorBoolList (bits.map (fun bit => value && bit)) =
      (value && xorBoolList bits) := by
  cases value
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, ih]
        simp
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, xorBoolList_cons, ih]
        simp

private theorem Bool.and_swap_middle (a b c : Bool) :
    (b && (a && c)) = ((a && b) && c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem xorBoolList_range_single_decide {n source : Nat} (value : Bool)
    (hsource : source < n) :
    xorBoolList ((List.range n).map (fun a => value && decide (a = source))) =
      value := by
  induction n generalizing source with
  | zero =>
      omega
  | succ n ih =>
      rw [List.range_succ, List.map_append, xorBoolList_append]
      by_cases hlast : source = n
      · have hleft :
            (List.range n).map (fun a => value && decide (a = source)) =
              (List.range n).map (fun _ => false) := by
          apply List.map_congr_left
          intro a ha
          have ha_lt : a < n := List.mem_range.mp ha
          simp [show a ≠ source by omega]
        rw [hleft, xorBoolList_range_false]
        simp [xorBoolList, hlast]
      · have hsource_lt : source < n := by omega
        rw [ih hsource_lt]
        simp [xorBoolList, show n ≠ source by omega]

private theorem xorBoolList_wordBitAt_sum_eq
    (x : UInt64) {b target : Nat} (hle : b ≤ target) (hsource : target - b < 64) :
    xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = target))) =
      wordBitAt x (target - b) := by
  rw [show
      (List.range 64).map (fun a => wordBitAt x a && decide (a + b = target)) =
        (List.range 64).map
          (fun a => wordBitAt x (target - b) && decide (a = target - b)) by
    apply List.map_congr_left
    intro a ha
    have ha_lt : a < 64 := List.mem_range.mp ha
    by_cases h : a = target - b
    · subst h
      simp [show target - b + b = target by omega]
    · have hsum : a + b ≠ target := by omega
      simp [h, hsum]]
  exact xorBoolList_range_single_decide (wordBitAt x (target - b)) hsource

private theorem xorBoolList_wordBitAt_sum_eq_false_of_target_lt
    (x : UInt64) {b target : Nat} (hlt : target < b) :
    xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = target))) =
      false := by
  rw [show
      (List.range 64).map (fun a => wordBitAt x a && decide (a + b = target)) =
        (List.range 64).map (fun _ => false) by
    apply List.map_congr_left
    intro a _ha
    simp [show a + b ≠ target by omega]]
  exact xorBoolList_range_false 64

private theorem xorBoolList_wordBitAt_sum_eq_false_of_source_ge
    (x : UInt64) {b target : Nat} (_hle : b ≤ target) (hsource : 64 ≤ target - b) :
    xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = target))) =
      false := by
  rw [show
      (List.range 64).map (fun a => wordBitAt x a && decide (a + b = target)) =
        (List.range 64).map (fun _ => false) by
    apply List.map_congr_left
    intro a ha
    have ha_lt : a < 64 := List.mem_range.mp ha
    simp [show a + b ≠ target by omega]]
  exact xorBoolList_range_false 64

private theorem clmul_oneHot_source_low
    (x : UInt64) {b bit : Nat} (hb : b < 64) (hbit : bit < 64) :
    wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).2 bit =
      xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = bit))) := by
  by_cases hbZero : b = 0
  · subst hbZero
    rw [clmul_oneHot_snd x hb]
    exact (xorBoolList_wordBitAt_sum_eq x (b := 0) (target := bit)
      (by omega) hbit).symm
  · have hbPos : 0 < b := Nat.pos_of_ne_zero hbZero
    by_cases hle : b ≤ bit
    · change ((((clmul x ((1 : UInt64) <<< b.toUInt64)).2 >>>
          bit.toUInt64) &&& 1) != 0) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit)))
      rw [clmul_oneHot_low_bit_shifted x hbPos hb hbit hle]
      change wordBitAt x (bit - b) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit)))
      exact (xorBoolList_wordBitAt_sum_eq x (b := b) (target := bit) hle (by omega)).symm
    · have hlt : bit < b := Nat.lt_of_not_ge hle
      change ((((clmul x ((1 : UInt64) <<< b.toUInt64)).2 >>>
          bit.toUInt64) &&& 1) != 0) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit)))
      rw [clmul_oneHot_low_bit_before_shift_false x hbPos hb hlt]
      exact (xorBoolList_wordBitAt_sum_eq_false_of_target_lt x hlt).symm

private theorem clmul_oneHot_source_high
    (x : UInt64) {b bit : Nat} (hb : b < 64) (hbit : bit < 64) :
    wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit =
      xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = bit + 64))) := by
  by_cases hbZero : b = 0
  · subst hbZero
    rw [clmul_oneHot_fst x hb]
    simp only [if_true]
    have hzero : wordBitAt 0 bit = false := by
      simp [wordBitAt]
    rw [hzero]
    exact (xorBoolList_wordBitAt_sum_eq_false_of_source_ge x
      (b := 0) (target := bit + 64) (by omega) (by omega)).symm
  · have hbPos : 0 < b := Nat.pos_of_ne_zero hbZero
    by_cases hleBit : b ≤ bit
    · change ((((clmul x ((1 : UInt64) <<< b.toUInt64)).1 >>>
          bit.toUInt64) &&& 1) != 0) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit + 64)))
      rw [clmul_oneHot_high_bit_after_carry_false x hb hbit hleBit]
      exact (xorBoolList_wordBitAt_sum_eq_false_of_source_ge x
        (b := b) (target := bit + 64) (by omega) (by omega)).symm
    · have hbitLt : bit < b := Nat.lt_of_not_ge hleBit
      have hsourceLt : bit + 64 - b < 64 := by omega
      have hsumGe : 64 ≤ bit + 64 - b + b := by omega
      have hsumEq : bit + 64 - b + b - 64 = bit := by omega
      have hleft :
          wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit =
            wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1
              (bit + 64 - b + b - 64) := by
        rw [hsumEq]
      rw [hleft]
      change ((((clmul x ((1 : UInt64) <<< b.toUInt64)).1 >>>
          (bit + 64 - b + b - 64).toUInt64) &&& 1) != 0) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit + 64)))
      rw [clmul_oneHot_high_bit_carry_word x hbPos hb hsourceLt hsumGe]
      change wordBitAt x (bit + 64 - b) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit + 64)))
      exact (xorBoolList_wordBitAt_sum_eq x
        (b := b) (target := bit + 64) (by omega) hsourceLt).symm

/-- Source bit-pair contribution for the coefficient of total bit index
`total` in one word-word carry-less product. -/
private def clmulSourcePairCoeff (x y : UInt64) (total : Nat) : Bool :=
  xorBoolList
    (List.flatMap
      (fun b =>
        (List.range 64).map
          (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = total)))
      (List.range 64))

private theorem clmulSourcePairCoeff_low
    (x y : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x y).2 bit = clmulSourcePairCoeff x y bit := by
  rw [clmul_rightBitFold_low x y hbit]
  unfold clmulSourcePairCoeff
  calc
    xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).2 bit))
        = xorBoolList
            ((List.range 64).map
              (fun b =>
                wordBitAt y b &&
                  xorBoolList
                    ((List.range 64).map
                      (fun a => wordBitAt x a && decide (a + b = bit))))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro b hb
            rw [clmul_oneHot_source_low x (List.mem_range.mp hb) hbit]
    _ = xorBoolList
            ((List.range 64).map
              (fun b =>
                xorBoolList
                  ((List.range 64).map
                    (fun a => (wordBitAt x a && wordBitAt y b) &&
                      decide (a + b = bit))))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro b _hb
            rw [← xorBoolList_map_and_left (wordBitAt y b)
              ((List.range 64).map
                (fun a => wordBitAt x a && decide (a + b = bit)))]
            apply congrArg xorBoolList
            rw [List.map_map]
            apply List.map_congr_left
            intro a _ha
            exact Bool.and_swap_middle (wordBitAt x a) (wordBitAt y b)
              (decide (a + b = bit))
    _ = xorBoolList
            (List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun a => (wordBitAt x a && wordBitAt y b) &&
                    decide (a + b = bit)))
              (List.range 64)) := by
            rw [xorBoolList_map_xorBoolList]

private theorem clmulSourcePairCoeff_high
    (x y : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x y).1 bit = clmulSourcePairCoeff x y (bit + 64) := by
  rw [clmul_rightBitFold_high x y hbit]
  unfold clmulSourcePairCoeff
  calc
    xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit))
        = xorBoolList
            ((List.range 64).map
              (fun b =>
                wordBitAt y b &&
                  xorBoolList
                    ((List.range 64).map
                      (fun a => wordBitAt x a && decide (a + b = bit + 64))))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro b hb
            rw [clmul_oneHot_source_high x (List.mem_range.mp hb) hbit]
    _ = xorBoolList
            ((List.range 64).map
              (fun b =>
                xorBoolList
                  ((List.range 64).map
                    (fun a => (wordBitAt x a && wordBitAt y b) &&
                      decide (a + b = bit + 64))))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro b _hb
            rw [← xorBoolList_map_and_left (wordBitAt y b)
              ((List.range 64).map
                (fun a => wordBitAt x a && decide (a + b = bit + 64)))]
            apply congrArg xorBoolList
            rw [List.map_map]
            apply List.map_congr_left
            intro a _ha
            exact Bool.and_swap_middle (wordBitAt x a) (wordBitAt y b)
              (decide (a + b = bit + 64))
    _ = xorBoolList
            (List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun a => (wordBitAt x a && wordBitAt y b) &&
                    decide (a + b = bit + 64)))
              (List.range 64)) := by
            rw [xorBoolList_map_xorBoolList]

private theorem clmulCoeffAt_sourcePairCoeff
    (idx : Nat) (x y : UInt64) (n : Nat) :
    clmulCoeffAt idx x y n =
      if n / 64 = idx then
        clmulSourcePairCoeff x y (n % 64)
      else if n / 64 = idx + 1 then
        clmulSourcePairCoeff x y (n % 64 + 64)
      else
        false := by
  unfold clmulCoeffAt
  by_cases hlow : n / 64 = idx
  · simp only [if_pos hlow]
    have hbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
    change wordBitAt (clmul x y).2 (n % 64) =
      clmulSourcePairCoeff x y (n % 64)
    exact clmulSourcePairCoeff_low x y hbit
  · by_cases hhigh : n / 64 = idx + 1
    · simp only [if_neg hlow, if_pos hhigh]
      have hbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
      change wordBitAt (clmul x y).1 (n % 64) =
        clmulSourcePairCoeff x y (n % 64 + 64)
      exact clmulSourcePairCoeff_high x y hbit
    · simp only [if_neg hlow, if_neg hhigh]

/-- Source bit-triple contribution for the coefficient of total bit index
`total` in a three-word carry-less product. -/
private def clmulSourceTripleCoeff (x y z : UInt64) (total : Nat) : Bool :=
  xorBoolList
    (List.flatMap
      (fun a =>
        List.flatMap
          (fun b =>
            (List.range 64).map
              (fun c =>
                (wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                  decide (a + b + c = total)))
          (List.range 64))
      (List.range 64))

private theorem xorBoolList_map_and_right_two (bits : List Bool) (left right : Bool) :
    xorBoolList (bits.map (fun bit => (bit && left) && right)) =
      ((xorBoolList bits && left) && right) := by
  cases left <;> cases right
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, ih]
        cases bit <;> simp
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, ih]
        cases bit <;> simp
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, ih]
        cases bit <;> simp
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, xorBoolList_cons, ih]
        cases bit <;> simp

private theorem xorBoolList_sourcePair_index_collapse_low
    (xy zc : Bool) {a b c bit : Nat} (hbit : bit < 64) :
    xorBoolList
        ((List.range 64).map
          (fun p => (((xy && decide (a + b = p)) && zc) && decide (p + c = bit)))) =
      ((xy && zc) && decide (a + b + c = bit)) := by
  cases xy <;> cases zc
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · by_cases hsum : a + b + c = bit
    · have hsource : a + b < 64 := by omega
      rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p)) && true) &&
                decide (p + c = bit))) =
            (List.range 64).map (fun p => true && decide (p = a + b)) by
        apply List.map_congr_left
        intro p hp
        have hpLt : p < 64 := List.mem_range.mp hp
        by_cases hpab : p = a + b
        · subst hpab
          simp [hsum]
        · have hleft : ¬ a + b = p := by omega
          have hright : p + c ≠ bit := by omega
          simp [hpab, hleft, hright]]
      simpa [hsum] using xorBoolList_range_single_decide true hsource
    · rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p)) && true) &&
                decide (p + c = bit))) =
            (List.range 64).map (fun _ => false) by
        apply List.map_congr_left
        intro p _hp
        by_cases hpab : a + b = p
        · subst hpab
          simp [hsum]
        · simp [hpab]]
      simp [xorBoolList_range_false, hsum]

private theorem xorBoolList_sourcePair_index_collapse_high
    (xy zc : Bool) {a b c bit : Nat}
    (ha : a < 64) (hb : b < 64) (hc : c < 64) (hbit : bit < 64) :
    xorBoolList
        ((List.range 64).map
          (fun p => (((xy && decide (a + b = p + 64)) && zc) &&
            decide (p + c = bit + 64)))) =
      ((xy && zc) && decide (a + b + c = bit + 128)) := by
  cases xy <;> cases zc
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · by_cases hsum : a + b + c = bit + 128
    · have hsourceGe : 64 ≤ a + b := by omega
      have hsource : a + b - 64 < 64 := by omega
      have hsourceEq : a + b - 64 + 64 = a + b := by omega
      rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p + 64)) && true) &&
                decide (p + c = bit + 64))) =
            (List.range 64).map (fun p => true && decide (p = a + b - 64)) by
        apply List.map_congr_left
        intro p hp
        have hpLt : p < 64 := List.mem_range.mp hp
        by_cases hpab : p = a + b - 64
        · subst hpab
          simp [hsourceEq]
          have hpc : a + b - 64 + c = bit + 64 := by omega
          simp [hpc]
        · have hleft : ¬ a + b = p + 64 := by omega
          have hright : p + c ≠ bit + 64 := by omega
          simp [hpab, hleft, hright]]
      simpa [hsum] using xorBoolList_range_single_decide true hsource
    · rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p + 64)) && true) &&
                decide (p + c = bit + 64))) =
            (List.range 64).map (fun _ => false) by
        apply List.map_congr_left
        intro p _hp
        by_cases hpab : a + b = p + 64
        · have hright : p + c ≠ bit + 64 := by
            intro hpc
            omega
          simp [hpab, hright]
        · simp [hpab]]
      simp [xorBoolList_range_false, hsum]

private theorem xorBoolList_sourcePair_index_collapse_middle_low
    (xy zc : Bool) {a b c bit : Nat} :
    xorBoolList
        ((List.range 64).map
          (fun p => (((xy && decide (a + b = p)) && zc) &&
            decide (p + c = bit + 64)))) =
      (((xy && zc) && decide (a + b + c = bit + 64)) &&
        decide (a + b < 64)) := by
  cases xy <;> cases zc
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · by_cases hsum : a + b + c = bit + 64
    · by_cases hsource : a + b < 64
      · rw [show
            (List.range 64).map
                (fun p => (((true && decide (a + b = p)) && true) &&
                  decide (p + c = bit + 64))) =
              (List.range 64).map (fun p => true && decide (p = a + b)) by
          apply List.map_congr_left
          intro p hp
          have hpLt : p < 64 := List.mem_range.mp hp
          by_cases hpab : p = a + b
          · subst hpab
            simp [hsum]
          · have hleft : ¬ a + b = p := by omega
            have hright : p + c ≠ bit + 64 := by omega
            simp [hpab, hleft, hright]]
        simpa [hsum, hsource] using xorBoolList_range_single_decide true hsource
      · rw [show
            (List.range 64).map
                (fun p => (((true && decide (a + b = p)) && true) &&
                  decide (p + c = bit + 64))) =
              (List.range 64).map (fun _ => false) by
          apply List.map_congr_left
          intro p hp
          have hpLt : p < 64 := List.mem_range.mp hp
          have hpne : ¬ a + b = p := by omega
          simp [hpne]]
        simp [xorBoolList_range_false, hsum, hsource]
    · rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p)) && true) &&
                decide (p + c = bit + 64))) =
            (List.range 64).map (fun _ => false) by
        apply List.map_congr_left
        intro p _hp
        by_cases hpab : a + b = p
        · subst hpab
          simp [hsum]
        · simp [hpab]]
      simp [xorBoolList_range_false, hsum]

private theorem xorBoolList_sourcePair_index_collapse_middle_high
    (xy zc : Bool) {a b c bit : Nat}
    (ha : a < 64) (hb : b < 64) :
    xorBoolList
        ((List.range 64).map
          (fun p => (((xy && decide (a + b = p + 64)) && zc) &&
            decide (p + c = bit)))) =
      (((xy && zc) && decide (a + b + c = bit + 64)) &&
        decide (64 ≤ a + b)) := by
  cases xy <;> cases zc
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · by_cases hsum : a + b + c = bit + 64
    · by_cases hsourceGe : 64 ≤ a + b
      · have hsource : a + b - 64 < 64 := by omega
        have hsourceEq : a + b - 64 + 64 = a + b := by omega
        rw [show
            (List.range 64).map
                (fun p => (((true && decide (a + b = p + 64)) && true) &&
                  decide (p + c = bit))) =
              (List.range 64).map (fun p => true && decide (p = a + b - 64)) by
          apply List.map_congr_left
          intro p hp
          have hpLt : p < 64 := List.mem_range.mp hp
          by_cases hpab : p = a + b - 64
          · subst hpab
            simp [hsourceEq]
            have hpc : a + b - 64 + c = bit := by omega
            simp [hpc]
          · have hleft : ¬ a + b = p + 64 := by omega
            have hright : p + c ≠ bit := by omega
            simp [hpab, hleft, hright]]
        simpa [hsum, hsourceGe] using xorBoolList_range_single_decide true hsource
      · rw [show
            (List.range 64).map
                (fun p => (((true && decide (a + b = p + 64)) && true) &&
                  decide (p + c = bit))) =
              (List.range 64).map (fun _ => false) by
          apply List.map_congr_left
          intro p _hp
          have hpne : ¬ a + b = p + 64 := by omega
          simp [hpne]]
        simp [xorBoolList_range_false, hsum, hsourceGe]
    · rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p + 64)) && true) &&
                decide (p + c = bit))) =
            (List.range 64).map (fun _ => false) by
        apply List.map_congr_left
        intro p _hp
        by_cases hpab : a + b = p + 64
        · have hright : p + c ≠ bit := by
            intro hpc
            omega
          simp [hpab, hright]
        · simp [hpab]]
      simp [xorBoolList_range_false, hsum]

private theorem clmulSourcePairCoeff_and_bit_low
    (x y : UInt64) {p : Nat} (hp : p < 64) (zc gate : Bool) :
    ((wordBitAt (clmul x y).2 p && zc) && gate) =
      xorBoolList
        ((List.range 64).flatMap
          (fun b =>
            (List.range 64).map
              (fun a =>
                ((((wordBitAt x a && wordBitAt y b) &&
                    decide (a + b = p)) && zc) && gate)))) := by
  rw [clmulSourcePairCoeff_low x y hp]
  unfold clmulSourcePairCoeff
  rw [← xorBoolList_map_and_right_two
    (List.flatMap
      (fun b =>
        (List.range 64).map
          (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = p)))
      (List.range 64)) zc gate]
  rw [List.map_flatMap]
  simp only [List.map_map]
  rfl

private theorem clmulSourcePairCoeff_and_bit_high
    (x y : UInt64) {p : Nat} (hp : p < 64) (zc gate : Bool) :
    ((wordBitAt (clmul x y).1 p && zc) && gate) =
      xorBoolList
        ((List.range 64).flatMap
          (fun b =>
            (List.range 64).map
              (fun a =>
                ((((wordBitAt x a && wordBitAt y b) &&
                    decide (a + b = p + 64)) && zc) && gate)))) := by
  rw [clmulSourcePairCoeff_high x y hp]
  unfold clmulSourcePairCoeff
  rw [← xorBoolList_map_and_right_two
    (List.flatMap
      (fun b =>
        (List.range 64).map
          (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = p + 64)))
      (List.range 64)) zc gate]
  rw [List.map_flatMap]
  simp only [List.map_map]
  rfl

private theorem xorBoolList_left_middle_low_sourceTriple_mask_collapse
    (x y z : UInt64) {bit : Nat} :
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64))))
              (List.range 64))
          (List.range 64)) := by
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64))
        =
      xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun b =>
                List.flatMap
                  (fun a =>
                    List.map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun p =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun p b =>
                      (List.range 64).map
                        (fun a =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p)) && wordBitAt z c) &&
                            decide (p + c = bit + 64))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun a =>
                        List.map
                          (fun p =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun p a =>
                        [((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64))])
    _ =
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64)))))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          apply xorBoolList_flatMap_congr_xor
          intro b _hb
          calc
            xorBoolList
                ((List.range 64).flatMap
                  (fun a =>
                    (List.range 64).map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    xorBoolList
                      ((List.range 64).map
                        (fun p =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p)) && wordBitAt z c) &&
                            decide (p + c = bit + 64)))))) := by
                  rw [xorBoolList_map_xorBoolList]
            _ =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro a _ha
                  simpa [Bool.and_assoc] using
                    xorBoolList_sourcePair_index_collapse_middle_low
                      (wordBitAt x a && wordBitAt y b) (wordBitAt z c)
                      (a := a) (b := b) (c := c) (bit := bit)
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64))))
              (List.range 64))
          (List.range 64)) := by
          calc
            xorBoolList
                (List.flatMap
                  (fun c =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun a =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (a + b < 64)))))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun c =>
                        (List.range 64).map
                          (fun a =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (a + b < 64)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun c b =>
                      (List.range 64).map
                        (fun a =>
                          (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 64)) && decide (a + b < 64))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun a =>
                        (List.range 64).map
                          (fun c =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (a + b < 64)))))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun c a =>
                        [(((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                          decide (a + b + c = bit + 64)) && decide (a + b < 64))])
            _ =
              xorBoolList
                (List.flatMap
                  (fun a =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun c =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (a + b < 64)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun b a =>
                      (List.range 64).map
                        (fun c =>
                          (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 64)) && decide (a + b < 64))))

private theorem xorBoolList_left_middle_high_sourceTriple_mask_collapse
    (x y z : UInt64) {bit : Nat} :
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
              (List.range 64))
          (List.range 64)) := by
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64))
        =
      xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun b =>
                List.flatMap
                  (fun a =>
                    List.map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun p =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun p b =>
                      (List.range 64).map
                        (fun a =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p + 64)) && wordBitAt z c) &&
                            decide (p + c = bit))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun a =>
                        List.map
                          (fun p =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun p a =>
                        [((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit))])
    _ =
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b)))))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          apply xorBoolList_flatMap_congr_xor
          intro b hb
          calc
            xorBoolList
                ((List.range 64).flatMap
                  (fun a =>
                    (List.range 64).map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    xorBoolList
                      ((List.range 64).map
                        (fun p =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p + 64)) && wordBitAt z c) &&
                            decide (p + c = bit)))))) := by
                  rw [xorBoolList_map_xorBoolList]
            _ =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro a ha
                  simpa [Bool.and_assoc] using
                    xorBoolList_sourcePair_index_collapse_middle_high
                      (wordBitAt x a && wordBitAt y b) (wordBitAt z c)
                      (a := a) (b := b) (c := c) (bit := bit)
                      (List.mem_range.mp ha) (List.mem_range.mp hb)
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
              (List.range 64))
          (List.range 64)) := by
          calc
            xorBoolList
                (List.flatMap
                  (fun c =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun a =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (64 ≤ a + b)))))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun c =>
                        (List.range 64).map
                          (fun a =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (64 ≤ a + b)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun c b =>
                      (List.range 64).map
                        (fun a =>
                          (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun a =>
                        (List.range 64).map
                          (fun c =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (64 ≤ a + b)))))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun c a =>
                        [(((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                          decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))])
            _ =
              xorBoolList
                (List.flatMap
                  (fun a =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun c =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (64 ≤ a + b)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun b a =>
                      (List.range 64).map
                        (fun c =>
                          (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))

private theorem xorBoolList_left_low_sourceTriple_collapse
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) =
      clmulSourceTripleCoeff x y z bit := by
  unfold clmulSourceTripleCoeff
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64))
        =
      xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun b =>
                List.flatMap
                  (fun a =>
                    List.map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun p =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun p b =>
                      (List.range 64).map
                        (fun a =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p)) && wordBitAt z c) &&
                            decide (p + c = bit))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun a =>
                        List.map
                          (fun p =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun p a =>
                        [((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit))])
    _ =
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit)))))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          apply xorBoolList_flatMap_congr_xor
          intro b _hb
          calc
            xorBoolList
                ((List.range 64).flatMap
                  (fun a =>
                    (List.range 64).map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit)))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    xorBoolList
                      ((List.range 64).map
                        (fun p =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p)) && wordBitAt z c) &&
                            decide (p + c = bit)))))) := by
                  rw [xorBoolList_map_xorBoolList]
            _ =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro a _ha
                  simpa [Bool.and_assoc] using
                    xorBoolList_sourcePair_index_collapse_low
                      (wordBitAt x a && wordBitAt y b) (wordBitAt z c)
                      (a := a) (b := b) (c := c) hbit
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit))))
              (List.range 64))
          (List.range 64)) := by
          calc
            xorBoolList
                (List.flatMap
                  (fun c =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun a =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit)))))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun c =>
                        (List.range 64).map
                          (fun a =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun c b =>
                      (List.range 64).map
                        (fun a =>
                          ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun a =>
                        (List.range 64).map
                          (fun c =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit)))))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun c a =>
                        [((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                          decide (a + b + c = bit))])
            _ =
              xorBoolList
                (List.flatMap
                  (fun a =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun c =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun b a =>
                      (List.range 64).map
                        (fun c =>
                          ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit))))

private theorem clmulAssoc_left_low_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul (clmul x y).2 z).2 bit =
      clmulSourceTripleCoeff x y z bit := by
  rw [clmulSourcePairCoeff_low (clmul x y).2 z hbit]
  unfold clmulSourcePairCoeff
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                  decide (p + c = bit))))
          (List.range 64))
        =
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                ((List.range 64).map
                  (fun p =>
                    ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                      decide (p + c = bit))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun p =>
                    xorBoolList
                      (List.flatMap
                        (fun b =>
                          List.map
                            (fun a =>
                              ((((wordBitAt x a && wordBitAt y b) &&
                                  decide (a + b = p)) && wordBitAt z c) &&
                                decide (p + c = bit)))
                            (List.range 64))
                        (List.range 64)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro p hp
                  exact clmulSourcePairCoeff_and_bit_low x y (List.mem_range.mp hp)
                    (wordBitAt z c) (decide (p + c = bit))
            _ =
              xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  rw [xorBoolList_map_xorBoolList]
    _ = clmulSourceTripleCoeff x y z bit := by
          exact xorBoolList_left_low_sourceTriple_collapse x y z hbit

private theorem clmulSourceTripleCoeff_reverse_outer
    (x y z : UInt64) (total : Nat) :
    clmulSourceTripleCoeff z y x total =
      clmulSourceTripleCoeff x y z total := by
  unfold clmulSourceTripleCoeff
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                      decide (c + b + a = total))))
              (List.range 64))
          (List.range 64))
        =
      xorBoolList
        (List.flatMap
          (fun b =>
            List.flatMap
              (fun c =>
                (List.range 64).map
                  (fun a =>
                    ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                      decide (c + b + a = total))))
              (List.range 64))
          (List.range 64)) := by
          exact xorBoolList_flatMap_ranges_swap_list 64 64
            (fun c b =>
              (List.range 64).map
                (fun a =>
                  ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                    decide (c + b + a = total))))
    _ =
      xorBoolList
        (List.flatMap
          (fun b =>
            List.flatMap
              (fun a =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                      decide (c + b + a = total))))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro b _hb
          simpa [List.flatMap_singleton] using
            xorBoolList_flatMap_ranges_swap_list 64 64
              (fun c a =>
                [((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                  decide (c + b + a = total))])
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                      decide (c + b + a = total))))
              (List.range 64))
          (List.range 64)) := by
          exact xorBoolList_flatMap_ranges_swap_list 64 64
            (fun b a =>
              (List.range 64).map
                (fun c =>
                  ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                    decide (c + b + a = total))))
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = total))))
              (List.range 64))
          (List.range 64)) := by
          apply congrArg xorBoolList
          apply List.flatMap_congr_left
          intro a _ha
          apply List.flatMap_congr_left
          intro b _hb
          apply List.map_congr_left
          intro c _hc
          cases wordBitAt x a <;> cases wordBitAt y b <;> cases wordBitAt z c <;>
            simp [show (c + b + a = total) ↔ (a + b + c = total) by omega]

private theorem clmulAssoc_right_low_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x (clmul y z).2).2 bit =
      clmulSourceTripleCoeff x y z bit := by
  calc
    wordBitAt (clmul x (clmul y z).2).2 bit
        = wordBitAt (clmul (clmul z y).2 x).2 bit := by
          rw [clmul_comm x (clmul y z).2, clmul_comm y z]
    _ = clmulSourceTripleCoeff z y x bit := by
          exact clmulAssoc_left_low_sourceTriple z y x hbit
    _ = clmulSourceTripleCoeff x y z bit := by
          exact clmulSourceTripleCoeff_reverse_outer x y z bit

private theorem xorBoolList_left_middle_sourceTriple_collapse
    (x y z : UInt64) {bit : Nat} (_hbit : bit < 64) :
    (xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                  decide (p + c = bit + 64))))
          (List.range 64)) !=
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                  decide (p + c = bit))))
          (List.range 64))) =
      clmulSourceTripleCoeff x y z (bit + 64) := by
  unfold clmulSourceTripleCoeff
  have hlow :
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                  decide (p + c = bit + 64))))
          (List.range 64)) =
      xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
    apply xorBoolList_flatMap_congr_xor
    intro c _hc
    calc
      xorBoolList
          ((List.range 64).map
            (fun p =>
              ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                decide (p + c = bit + 64))))
          =
        xorBoolList
          ((List.range 64).map
            (fun p =>
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64)))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro p hp
            exact clmulSourcePairCoeff_and_bit_low x y (List.mem_range.mp hp)
              (wordBitAt z c) (decide (p + c = bit + 64))
      _ =
        xorBoolList
          (List.flatMap
            (fun p =>
              List.flatMap
                (fun b =>
                  List.map
                    (fun a =>
                      ((((wordBitAt x a && wordBitAt y b) &&
                          decide (a + b = p)) && wordBitAt z c) &&
                        decide (p + c = bit + 64)))
                    (List.range 64))
                (List.range 64))
            (List.range 64)) := by
            rw [xorBoolList_map_xorBoolList]
  have hhigh :
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                  decide (p + c = bit))))
          (List.range 64)) =
      xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
    apply xorBoolList_flatMap_congr_xor
    intro c _hc
    calc
      xorBoolList
          ((List.range 64).map
            (fun p =>
              ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                decide (p + c = bit))))
          =
        xorBoolList
          ((List.range 64).map
            (fun p =>
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64)))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro p hp
            exact clmulSourcePairCoeff_and_bit_high x y (List.mem_range.mp hp)
              (wordBitAt z c) (decide (p + c = bit))
      _ =
        xorBoolList
          (List.flatMap
            (fun p =>
              List.flatMap
                (fun b =>
                  List.map
                    (fun a =>
                      ((((wordBitAt x a && wordBitAt y b) &&
                          decide (a + b = p + 64)) && wordBitAt z c) &&
                        decide (p + c = bit)))
                    (List.range 64))
                (List.range 64))
            (List.range 64)) := by
            rw [xorBoolList_map_xorBoolList]
  rw [hlow, hhigh]
  rw [xorBoolList_left_middle_low_sourceTriple_mask_collapse x y z,
    xorBoolList_left_middle_high_sourceTriple_mask_collapse x y z]
  exact
    xorBoolList_flatMap_bne_congr
      (xs := List.range 64)
      (left := fun a =>
        List.flatMap
          (fun b =>
            (List.range 64).map
              (fun c =>
                (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                  decide (a + b + c = bit + 64)) && decide (a + b < 64))))
          (List.range 64))
      (right := fun a =>
        List.flatMap
          (fun b =>
            (List.range 64).map
              (fun c =>
                (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                  decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
          (List.range 64))
      (both := fun a =>
        List.flatMap
          (fun b =>
            (List.range 64).map
              (fun c =>
                ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                  decide (a + b + c = bit + 64))))
          (List.range 64))
      (by
        intro a _ha
        exact
          xorBoolList_flatMap_bne_congr
            (xs := List.range 64)
            (left := fun b =>
              (List.range 64).map
                (fun c =>
                  (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                    decide (a + b + c = bit + 64)) && decide (a + b < 64))))
            (right := fun b =>
              (List.range 64).map
                (fun c =>
                  (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                    decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
            (both := fun b =>
              (List.range 64).map
                (fun c =>
                  ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                    decide (a + b + c = bit + 64))))
            (by
              intro b _hb
              exact
                xorBoolList_map_bne_congr
                  (xs := List.range 64)
                  (left := fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64)))
                  (right := fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b)))
                  (both := fun c =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)))
                  (by
                    intro c _hc
                    generalize
                      ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                        decide (a + b + c = bit + 64)) = term
                    by_cases hlt : a + b < 64
                    · have hge : ¬ 64 ≤ a + b := by omega
                      cases term <;> simp [hlt, hge]
                    · have hge : 64 ≤ a + b := by omega
                      cases term <;> simp [hlt, hge])))

private theorem clmulAssoc_left_middle_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    (wordBitAt (clmul (clmul x y).2 z).1 bit !=
        wordBitAt (clmul (clmul x y).1 z).2 bit) =
      clmulSourceTripleCoeff x y z (bit + 64) := by
  rw [clmulSourcePairCoeff_high (clmul x y).2 z hbit]
  rw [clmulSourcePairCoeff_low (clmul x y).1 z hbit]
  unfold clmulSourcePairCoeff
  exact xorBoolList_left_middle_sourceTriple_collapse x y z hbit

private theorem clmulAssoc_right_middle_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    (wordBitAt (clmul x (clmul y z).2).1 bit !=
        wordBitAt (clmul x (clmul y z).1).2 bit) =
      clmulSourceTripleCoeff x y z (bit + 64) := by
  calc
    (wordBitAt (clmul x (clmul y z).2).1 bit !=
        wordBitAt (clmul x (clmul y z).1).2 bit)
        =
      (wordBitAt (clmul (clmul z y).2 x).1 bit !=
        wordBitAt (clmul (clmul z y).1 x).2 bit) := by
          rw [clmul_comm x (clmul y z).2, clmul_comm x (clmul y z).1,
            clmul_comm y z]
    _ = clmulSourceTripleCoeff z y x (bit + 64) := by
          exact clmulAssoc_left_middle_sourceTriple z y x hbit
    _ = clmulSourceTripleCoeff x y z (bit + 64) := by
          exact clmulSourceTripleCoeff_reverse_outer x y z (bit + 64)

private theorem xorBoolList_left_high_sourceTriple_collapse
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) =
      clmulSourceTripleCoeff x y z (bit + 128) := by
  unfold clmulSourceTripleCoeff
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64))
        =
      xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun b =>
                List.flatMap
                  (fun a =>
                    List.map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun p =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun p b =>
                      (List.range 64).map
                        (fun a =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p + 64)) && wordBitAt z c) &&
                            decide (p + c = bit + 64))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun a =>
                        List.map
                          (fun p =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun p a =>
                        [((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit + 64))])
    _ =
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 128)))))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c hc
          apply xorBoolList_flatMap_congr_xor
          intro b hb
          calc
            xorBoolList
                ((List.range 64).flatMap
                  (fun a =>
                    (List.range 64).map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    xorBoolList
                      ((List.range 64).map
                        (fun p =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p + 64)) && wordBitAt z c) &&
                            decide (p + c = bit + 64)))))) := by
                  rw [xorBoolList_map_xorBoolList]
            _ =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 128)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro a ha
                  simpa [Bool.and_assoc] using
                    xorBoolList_sourcePair_index_collapse_high
                      (wordBitAt x a && wordBitAt y b) (wordBitAt z c)
                      (a := a) (b := b) (c := c)
                      (List.mem_range.mp ha) (List.mem_range.mp hb)
                      (List.mem_range.mp hc) hbit
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 128))))
              (List.range 64))
          (List.range 64)) := by
          calc
            xorBoolList
                (List.flatMap
                  (fun c =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun a =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 128)))))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun c =>
                        (List.range 64).map
                          (fun a =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 128)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun c b =>
                      (List.range 64).map
                        (fun a =>
                          ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 128))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun a =>
                        (List.range 64).map
                          (fun c =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 128)))))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun c a =>
                        [((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                          decide (a + b + c = bit + 128))])
            _ =
              xorBoolList
                (List.flatMap
                  (fun a =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun c =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 128)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun b a =>
                      (List.range 64).map
                        (fun c =>
                          ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 128))))

private theorem clmulAssoc_left_high_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul (clmul x y).1 z).1 bit =
      clmulSourceTripleCoeff x y z (bit + 128) := by
  rw [clmulSourcePairCoeff_high (clmul x y).1 z hbit]
  unfold clmulSourcePairCoeff
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                  decide (p + c = bit + 64))))
          (List.range 64))
        =
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                ((List.range 64).map
                  (fun p =>
                    ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                      decide (p + c = bit + 64))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun p =>
                    xorBoolList
                      (List.flatMap
                        (fun b =>
                          List.map
                            (fun a =>
                              ((((wordBitAt x a && wordBitAt y b) &&
                                  decide (a + b = p + 64)) && wordBitAt z c) &&
                                decide (p + c = bit + 64)))
                            (List.range 64))
                        (List.range 64)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro p hp
                  exact clmulSourcePairCoeff_and_bit_high x y (List.mem_range.mp hp)
                    (wordBitAt z c) (decide (p + c = bit + 64))
            _ =
              xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  rw [xorBoolList_map_xorBoolList]
    _ = clmulSourceTripleCoeff x y z (bit + 128) := by
          exact xorBoolList_left_high_sourceTriple_collapse x y z hbit

private theorem clmulAssoc_right_high_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x (clmul y z).1).1 bit =
      clmulSourceTripleCoeff x y z (bit + 128) := by
  calc
    wordBitAt (clmul x (clmul y z).1).1 bit
        = wordBitAt (clmul (clmul z y).1 x).1 bit := by
          rw [clmul_comm x (clmul y z).1, clmul_comm y z]
    _ = clmulSourceTripleCoeff z y x (bit + 128) := by
          exact clmulAssoc_left_high_sourceTriple z y x hbit
    _ = clmulSourceTripleCoeff x y z (bit + 128) := by
          exact clmulSourceTripleCoeff_reverse_outer x y z (bit + 128)

private theorem clmulCoeffAt_assoc_twoWord_low
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    ((((clmul (clmul x y).2 z).2 >>> bit.toUInt64) &&& 1) != 0) =
      ((((clmul x (clmul y z).2).2 >>> bit.toUInt64) &&& 1) != 0) := by
  change wordBitAt (clmul (clmul x y).2 z).2 bit =
    wordBitAt (clmul x (clmul y z).2).2 bit
  rw [clmulAssoc_left_low_sourceTriple x y z hbit,
    clmulAssoc_right_low_sourceTriple x y z hbit]

private theorem clmulCoeffAt_assoc_twoWord_middle
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    (((((clmul (clmul x y).2 z).1 >>> bit.toUInt64) &&& 1) != 0) !=
        ((((clmul (clmul x y).1 z).2 >>> bit.toUInt64) &&& 1) != 0)) =
      (((((clmul x (clmul y z).2).1 >>> bit.toUInt64) &&& 1) != 0) !=
        ((((clmul x (clmul y z).1).2 >>> bit.toUInt64) &&& 1) != 0)) := by
  change (wordBitAt (clmul (clmul x y).2 z).1 bit !=
      wordBitAt (clmul (clmul x y).1 z).2 bit) =
    (wordBitAt (clmul x (clmul y z).2).1 bit !=
      wordBitAt (clmul x (clmul y z).1).2 bit)
  rw [clmulAssoc_left_middle_sourceTriple x y z hbit,
    clmulAssoc_right_middle_sourceTriple x y z hbit]

private theorem clmulCoeffAt_assoc_twoWord_high
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    ((((clmul (clmul x y).1 z).1 >>> bit.toUInt64) &&& 1) != 0) =
      ((((clmul x (clmul y z).1).1 >>> bit.toUInt64) &&& 1) != 0) := by
  change wordBitAt (clmul (clmul x y).1 z).1 bit =
    wordBitAt (clmul x (clmul y z).1).1 bit
  rw [clmulAssoc_left_high_sourceTriple x y z hbit,
    clmulAssoc_right_high_sourceTriple x y z hbit]

private theorem clmulCoeffAt_assoc_twoWord
    (base n : Nat) (x y z : UInt64) :
    (clmulCoeffAt base (clmul x y).2 z n !=
      clmulCoeffAt (base + 1) (clmul x y).1 z n) =
    (clmulCoeffAt base x (clmul y z).2 n !=
      clmulCoeffAt (base + 1) x (clmul y z).1 n) := by
  unfold clmulCoeffAt
  by_cases h0 : n / 64 = base
  · have hbase02 : base ≠ base + 1 + 1 := by omega
    simp [h0, hbase02, clmulCoeffAt_assoc_twoWord_low x y z (Nat.mod_lt n (by decide : 0 < 64))]
  · by_cases h1 : n / 64 = base + 1
    · simp [h1, clmulCoeffAt_assoc_twoWord_middle x y z (Nat.mod_lt n (by decide : 0 < 64))]
    · by_cases h2 : n / 64 = base + 1 + 1
      · have hbase20 : base + 1 + 1 ≠ base := by omega
        simp [h2, hbase20,
          clmulCoeffAt_assoc_twoWord_high x y z (Nat.mod_lt n (by decide : 0 < 64))]
      · simp [h0, h1, h2]

/-- The raw product has enough intermediate slots to contain every source
word-pair contribution selected by the source ranges. -/
private theorem mulWords_size_source_pair
    {xs ys : Array UInt64} {i j : Nat}
    (hi : i ∈ List.range xs.size) (hj : j ∈ List.range ys.size) :
    i + j + 1 < (mulWords xs ys).size := by
  have hiLt : i < xs.size := List.mem_range.mp hi
  have hjLt : j < ys.size := List.mem_range.mp hj
  have hxs : ¬ xs.isEmpty := by
    intro h
    have hsize : xs.size = 0 := by
      simpa [Array.isEmpty] using h
    omega
  have hys : ¬ ys.isEmpty := by
    intro h
    have hsize : ys.size = 0 := by
      simpa [Array.isEmpty] using h
    omega
  unfold mulWords
  simp [hxs, hys, foldl_mulWords_size]
  omega

private theorem xorBoolList_range_single_active
    (f : Nat → Bool) {bound active : Nat}
    (hactive : active < bound)
    (hzero : ∀ slot, slot < bound → slot ≠ active → f slot = false) :
    xorBoolList ((List.range bound).map f) = f active := by
  induction bound with
  | zero =>
      omega
  | succ bound ih =>
      rw [List.range_succ, List.map_append, xorBoolList_append]
      by_cases hlast : active = bound
      · have hprefix :
            (List.range bound).map f = (List.range bound).map (fun _ => false) := by
          apply List.map_congr_left
          intro slot hslot
          have hslotLt : slot < bound := List.mem_range.mp hslot
          exact hzero slot (by omega) (by omega)
        rw [hprefix, xorBoolList_range_false]
        simp [xorBoolList, hlast]
      · have hactiveLt : active < bound := by omega
        rw [ih hactiveLt]
        · have htail : f bound = false := hzero bound (by omega) (by omega)
          simp [xorBoolList, htail]
        · intro slot hslot hslotNe
          exact hzero slot (by omega) hslotNe

private theorem clmulSourcePairCoeff_single_active
    (x y : UInt64) {a₀ b₀ total : Nat}
    (ha₀ : a₀ < 64) (hb₀ : b₀ < 64)
    (hx₀ : wordBitAt x a₀ = true) (hy₀ : wordBitAt y b₀ = true)
    (hsum : a₀ + b₀ = total)
    (hzero :
      ∀ a b, a < 64 → b < 64 → a + b = total → a ≠ a₀ ∨ b ≠ b₀ →
        (wordBitAt x a && wordBitAt y b) = false) :
    clmulSourcePairCoeff x y total = true := by
  unfold clmulSourcePairCoeff
  rw [← xorBoolList_map_xorBoolList]
  rw [xorBoolList_range_single_active
    (fun b =>
      xorBoolList
        ((List.range 64).map
          (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = total))))
    hb₀]
  · rw [xorBoolList_range_single_active
      (fun a => (wordBitAt x a && wordBitAt y b₀) && decide (a + b₀ = total))
      ha₀]
    · simp [hx₀, hy₀, hsum]
    · intro a ha hne
      by_cases hsum' : a + b₀ = total
      · have hfalse := hzero a b₀ ha hb₀ hsum' (Or.inl hne)
        simp [hfalse, hsum']
      · simp [hsum']
  · intro b hb hne
    have hinner :
        (List.range 64).map
            (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = total)) =
          (List.range 64).map (fun _ => false) := by
      apply List.map_congr_left
      intro a haMem
      have ha : a < 64 := List.mem_range.mp haMem
      by_cases hsum' : a + b = total
      · have hfalse := hzero a b ha hb hsum' (Or.inr hne)
        simp [hfalse, hsum']
      · simp [hsum']
    rw [hinner, xorBoolList_range_false]

private theorem xorBoolList_range_two_adjacent_active
    (f : Nat → Bool) {bound active : Nat}
    (hactive : active + 1 < bound)
    (hzero :
      ∀ slot, slot < bound → slot ≠ active → slot ≠ active + 1 → f slot = false) :
    xorBoolList ((List.range bound).map f) = (f active != f (active + 1)) := by
  induction bound with
  | zero =>
      omega
  | succ bound ih =>
      rw [List.range_succ, List.map_append, xorBoolList_append]
      by_cases hlast : active + 1 = bound
      · have hprefix :
            xorBoolList ((List.range bound).map f) = f active := by
          apply xorBoolList_range_single_active
          · omega
          · intro slot hslot hslotNe
            exact hzero slot (by omega) hslotNe (by omega)
        rw [hprefix]
        simp [xorBoolList, hlast]
      · have hactiveLt : active + 1 < bound := by omega
        rw [ih hactiveLt]
        · have htail : f bound = false := hzero bound (by omega) (by omega) (by omega)
          simp [xorBoolList, htail]
        · intro slot hslot hslotNe0 hslotNe1
          exact hzero slot (by omega) hslotNe0 hslotNe1

private theorem xorBoolList_leftAssocFixedTripleContribs_collapse
    (i j k : Nat) (x y z : UInt64) (n leftBound : Nat)
    (hleft : i + j + 1 < leftBound) :
    xorBoolList (leftAssocFixedTripleContribs i j k x y z n leftBound) =
      (clmulCoeffAt (i + j + k) (clmul x y).2 z n !=
        clmulCoeffAt (i + j + k + 1) (clmul x y).1 z n) := by
  unfold leftAssocFixedTripleContribs
  rw [xorBoolList_range_two_adjacent_active
    (fun slot => clmulCoeffAt (slot + k) (clmulWordAt (i + j) x y slot) z n)
    hleft]
  · simp [clmulWordAt]
    have hhigh : (i + j + 1) + k = i + j + k + 1 := by omega
    simp [hhigh]
  · intro slot _hslot hneLow hneHigh
    simp [clmulWordAt, hneLow, hneHigh, clmulCoeffAt_zero_left]

private theorem xorBoolList_rightAssocFixedTripleContribs_collapse
    (i j k : Nat) (x y z : UInt64) (n rightBound : Nat)
    (hright : j + k + 1 < rightBound) :
    xorBoolList (rightAssocFixedTripleContribs i j k x y z n rightBound) =
      (clmulCoeffAt (i + j + k) x (clmul y z).2 n !=
        clmulCoeffAt (i + j + k + 1) x (clmul y z).1 n) := by
  unfold rightAssocFixedTripleContribs
  rw [xorBoolList_range_two_adjacent_active
    (fun slot => clmulCoeffAt (i + slot) x (clmulWordAt (j + k) y z slot) n)
    hright]
  · simp [clmulWordAt]
    have hlow : i + (j + k) = i + j + k := by omega
    have hhigh : i + (j + k + 1) = i + j + k + 1 := by omega
    simp [hlow, hhigh]
  · intro slot _hslot hneLow hneHigh
    simp [clmulWordAt, hneLow, hneHigh, clmulCoeffAt_zero_right]

/-- Fixed source-word associativity for carry-less multiplication after
expanding only the intermediate packed-word slot. -/
private theorem xorBoolList_assoc_fixed_sourceTriple
    (i j k : Nat) (x y z : UInt64) (n leftBound rightBound : Nat)
    (hleft : i + j + 1 < leftBound) (hright : j + k + 1 < rightBound) :
    xorBoolList (leftAssocFixedTripleContribs i j k x y z n leftBound) =
      xorBoolList (rightAssocFixedTripleContribs i j k x y z n rightBound) := by
  rw [xorBoolList_leftAssocFixedTripleContribs_collapse i j k x y z n leftBound hleft,
    xorBoolList_rightAssocFixedTripleContribs_collapse i j k x y z n rightBound hright]
  exact clmulCoeffAt_assoc_twoWord (i + j + k) n x y z

/-- Regroup the left-associated source expansion by fixed source triples rather
than by intermediate product slot first. -/
private theorem leftAssocSourceTripleContribs_by_fixed
    (xs ys zs : Array UInt64) (n : Nat) :
    xorBoolList (leftAssocSourceTripleContribs xs ys zs n) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j =>
                List.flatMap
                  (fun k =>
                    leftAssocFixedTripleContribs i j k xs[i]! ys[j]! zs[k]! n
                      (mulWords xs ys).size)
                  (List.range zs.size))
              (List.range ys.size))
          (List.range xs.size)) := by
  unfold leftAssocSourceTripleContribs leftAssocFixedTripleContribs
  simp only [List.map_flatMap, List.map_map]
  calc
    xorBoolList
        (List.flatMap
          (fun slot =>
            List.flatMap
              (fun k =>
                List.flatMap
                  (fun i =>
                    (List.range ys.size).map
                      (fun j =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range xs.size))
              (List.range zs.size))
          (List.range (mulWords xs ys).size))
        =
      xorBoolList
        (List.flatMap
          (fun k =>
            List.flatMap
              (fun slot =>
                List.flatMap
                  (fun i =>
                    (List.range ys.size).map
                      (fun j =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range xs.size))
              (List.range (mulWords xs ys).size))
          (List.range zs.size)) := by
          exact xorBoolList_flatMap_ranges_swap_list
            (mulWords xs ys).size zs.size
            (fun slot k =>
              List.flatMap
                (fun i =>
                  (List.range ys.size).map
                    (fun j =>
                      clmulCoeffAt (slot + k)
                        (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                (List.range xs.size))
    _ =
      xorBoolList
        (List.flatMap
          (fun k =>
            List.flatMap
              (fun i =>
                List.flatMap
                  (fun slot =>
                    (List.range ys.size).map
                      (fun j =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range (mulWords xs ys).size))
              (List.range xs.size))
          (List.range zs.size)) := by
          apply xorBoolList_flatMap_congr_xor
          intro k _hk
          exact xorBoolList_flatMap_ranges_swap_list
            (mulWords xs ys).size xs.size
            (fun slot i =>
              (List.range ys.size).map
                (fun j =>
                  clmulCoeffAt (slot + k)
                    (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
    _ =
      xorBoolList
        (List.flatMap
          (fun k =>
            List.flatMap
              (fun i =>
                List.flatMap
                  (fun j =>
                    (List.range (mulWords xs ys).size).map
                      (fun slot =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range ys.size))
              (List.range xs.size))
          (List.range zs.size)) := by
          apply xorBoolList_flatMap_congr_xor
          intro k _hk
          apply xorBoolList_flatMap_congr_xor
          intro i _hi
          simpa [List.flatMap_singleton] using
            xorBoolList_flatMap_ranges_swap_list
              (mulWords xs ys).size ys.size
              (fun slot j =>
                [clmulCoeffAt (slot + k)
                  (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n])
    _ =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun k =>
                List.flatMap
                  (fun j =>
                    (List.range (mulWords xs ys).size).map
                      (fun slot =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range ys.size))
              (List.range zs.size))
          (List.range xs.size)) := by
          exact xorBoolList_flatMap_ranges_swap_list zs.size xs.size
            (fun k i =>
              List.flatMap
                (fun j =>
                  (List.range (mulWords xs ys).size).map
                    (fun slot =>
                      clmulCoeffAt (slot + k)
                        (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                (List.range ys.size))
    _ =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j =>
                List.flatMap
                  (fun k =>
                    (List.range (mulWords xs ys).size).map
                      (fun slot =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range zs.size))
              (List.range ys.size))
          (List.range xs.size)) := by
          apply xorBoolList_flatMap_congr_xor
          intro i _hi
          exact xorBoolList_flatMap_ranges_swap_list zs.size ys.size
            (fun k j =>
              (List.range (mulWords xs ys).size).map
                (fun slot =>
                  clmulCoeffAt (slot + k)
                    (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))

/-- Regroup the right-associated source expansion by fixed source triples rather
than by intermediate product slot first. -/
private theorem rightAssocSourceTripleContribs_by_fixed
    (xs ys zs : Array UInt64) (n : Nat) :
    xorBoolList (rightAssocSourceTripleContribs xs ys zs n) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j =>
                List.flatMap
                  (fun k =>
                    rightAssocFixedTripleContribs i j k xs[i]! ys[j]! zs[k]! n
                      (mulWords ys zs).size)
                  (List.range zs.size))
              (List.range ys.size))
          (List.range xs.size)) := by
  unfold rightAssocSourceTripleContribs rightAssocFixedTripleContribs
  simp only [List.map_flatMap, List.map_map]
  apply xorBoolList_flatMap_congr_xor
  intro i _hi
  calc
    xorBoolList
        (List.flatMap
          (fun slot =>
            List.flatMap
              (fun j =>
                (List.range zs.size).map
                  (fun k =>
                    clmulCoeffAt (i + slot) xs[i]!
                      (clmulWordAt (j + k) ys[j]! zs[k]! slot) n))
              (List.range ys.size))
          (List.range (mulWords ys zs).size))
        =
      xorBoolList
        (List.flatMap
          (fun j =>
            List.flatMap
              (fun slot =>
                (List.range zs.size).map
                  (fun k =>
                    clmulCoeffAt (i + slot) xs[i]!
                      (clmulWordAt (j + k) ys[j]! zs[k]! slot) n))
              (List.range (mulWords ys zs).size))
          (List.range ys.size)) := by
          exact xorBoolList_flatMap_ranges_swap_list
            (mulWords ys zs).size ys.size
            (fun slot j =>
              (List.range zs.size).map
                (fun k =>
                  clmulCoeffAt (i + slot) xs[i]!
                    (clmulWordAt (j + k) ys[j]! zs[k]! slot) n))
    _ =
      xorBoolList
        (List.flatMap
          (fun j =>
            List.flatMap
              (fun k =>
                (List.range (mulWords ys zs).size).map
                  (fun slot =>
                    clmulCoeffAt (i + slot) xs[i]!
                      (clmulWordAt (j + k) ys[j]! zs[k]! slot) n))
              (List.range zs.size))
          (List.range ys.size)) := by
          apply xorBoolList_flatMap_congr_xor
          intro j _hj
          simpa [List.flatMap_singleton] using
            xorBoolList_flatMap_ranges_swap_list
              (mulWords ys zs).size zs.size
              (fun slot k =>
                [clmulCoeffAt (i + slot) xs[i]!
                  (clmulWordAt (j + k) ys[j]! zs[k]! slot) n])

private theorem leftAssocSourceTripleContribs_slot
    (xs ys zs : Array UInt64) (slot n : Nat) :
    xorBoolList
        ((List.range zs.size).map
          (fun k => clmulCoeffAt (slot + k) (mulWords xs ys)[slot]! zs[k]! n)) =
      xorBoolList
        (List.flatMap
          (fun k =>
            (List.flatMap
              (fun i =>
                (List.range ys.size).map
                  (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
              (List.range xs.size)).map
              (fun word => clmulCoeffAt (slot + k) word zs[k]! n))
          (List.range zs.size)) := by
  rw [← xorBoolList_map_xorBoolList]
  congr 1
  apply List.map_congr_left
  intro k _hk
  exact clmulCoeffAt_mulWords_left_contrib xs ys slot (slot + k) zs[k]! n

private theorem rightAssocSourceTripleContribs_slot
    (xs ys zs : Array UInt64) (i n : Nat) :
    xorBoolList
        ((List.range (mulWords ys zs).size).map
          (fun slot => clmulCoeffAt (i + slot) xs[i]! (mulWords ys zs)[slot]! n)) =
      xorBoolList
        (List.flatMap
          (fun slot =>
            (List.flatMap
              (fun j =>
                (List.range zs.size).map
                  (fun k => clmulWordAt (j + k) ys[j]! zs[k]! slot))
              (List.range ys.size)).map
              (fun word => clmulCoeffAt (i + slot) xs[i]! word n))
          (List.range (mulWords ys zs).size)) := by
  rw [← xorBoolList_map_xorBoolList]
  congr 1
  apply List.map_congr_left
  intro slot _hslot
  exact clmulCoeffAt_mulWords_right_contrib ys zs slot (i + slot) xs[i]! n

/-- Coefficients of the left-associated raw product expand to the finite XOR
of the source-word triples contributing to `(xs * ys) * zs`. -/
private theorem coeffWords_mulWords_left_assoc_sourceTriples
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (mulWords xs ys) zs) n =
      xorBoolList (leftAssocSourceTripleContribs xs ys zs n) := by
  rw [coeffWords_mulWords_contrib]
  unfold leftAssocSourceTripleContribs
  exact xorBoolList_flatMap_congr_xor
    (fun slot _hslot => leftAssocSourceTripleContribs_slot xs ys zs slot n)

/-- Coefficients of the right-associated raw product expand to the finite XOR
of the source-word triples contributing to `xs * (ys * zs)`. -/
private theorem coeffWords_mulWords_right_assoc_sourceTriples
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs (mulWords ys zs)) n =
      xorBoolList (rightAssocSourceTripleContribs xs ys zs n) := by
  rw [coeffWords_mulWords_contrib]
  unfold rightAssocSourceTripleContribs
  exact xorBoolList_flatMap_congr_xor
    (fun i _hi => rightAssocSourceTripleContribs_slot xs ys zs i n)

/-- The source-triple XOR expansions of the two raw associated products
contribute the same coefficient.  Proving this requires the fixed source-word
triple identity: summing over the intermediate word slot in `(xs[i] * ys[j]) *
zs[k]` matches summing over the intermediate word slot in `xs[i] * (ys[j] *
zs[k])`. -/
private theorem xorBoolList_assoc_sourceTripleContribs
    (xs ys zs : Array UInt64) (n : Nat) :
    xorBoolList (leftAssocSourceTripleContribs xs ys zs n) =
      xorBoolList (rightAssocSourceTripleContribs xs ys zs n) := by
  rw [leftAssocSourceTripleContribs_by_fixed, rightAssocSourceTripleContribs_by_fixed]
  apply xorBoolList_flatMap_congr_xor
  intro i hi
  apply xorBoolList_flatMap_congr_xor
  intro j hj
  apply xorBoolList_flatMap_congr_xor
  intro k hk
  exact xorBoolList_assoc_fixed_sourceTriple i j k xs[i]! ys[j]! zs[k]! n
    (mulWords xs ys).size (mulWords ys zs).size
    (mulWords_size_source_pair hi hj)
    (mulWords_size_source_pair hj hk)

private theorem clmulCoeffAt_comm (i j : Nat) (x y : UInt64) (n : Nat) :
    clmulCoeffAt (i + j) x y n = clmulCoeffAt (j + i) y x n := by
  unfold clmulCoeffAt
  rw [Nat.add_comm i j, clmul_comm x y]

/-- Coefficients of the raw packed product are symmetric in the two input word
arrays. This is the local step from word-level `clmul_comm` to polynomial
multiplication commutativity. -/
private theorem coeffWords_mulWords_comm (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs ys) n = coeffWords (mulWords ys xs) n := by
  rw [coeffWords_mulWords_contrib xs ys n, coeffWords_mulWords_contrib ys xs n]
  rw [xorBoolList_wordPairs_swap xs.size ys.size
    (fun i j => clmulCoeffAt (i + j) xs[i]! ys[j]! n)]
  congr 1
  apply List.flatMap_congr_left
  intro j hj
  apply List.map_congr_left
  intro i hi
  exact clmulCoeffAt_comm i j xs[i]! ys[j]! n

private theorem coeffWords_mulWords_normalize_left
    (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords (normalizeWords xs) ys) n =
      coeffWords (mulWords xs ys) n := by
  rw [← coeffWords_mulWords_common_left (normalizeWords xs) ys n xs.size
    (normalizeWords_size_le xs)]
  rw [← coeffWords_mulWords_common_left xs ys n xs.size (Nat.le_refl xs.size)]
  simp [normalizeWords_getElem!]

private theorem coeffWords_mulWords_normalize_right
    (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs (normalizeWords ys)) n =
      coeffWords (mulWords xs ys) n := by
  rw [coeffWords_mulWords_comm xs (normalizeWords ys)]
  rw [coeffWords_mulWords_normalize_left ys xs]
  rw [coeffWords_mulWords_comm ys xs]

private theorem coeffWords_mulWords_ofWords_left
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (ofWords (mulWords xs ys)).words zs) n =
      coeffWords (mulWords (mulWords xs ys) zs) n := by
  change coeffWords (mulWords (normalizeWords (mulWords xs ys)) zs) n =
    coeffWords (mulWords (mulWords xs ys) zs) n
  exact coeffWords_mulWords_normalize_left (mulWords xs ys) zs n

private theorem coeffWords_mulWords_ofWords_right
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs (ofWords (mulWords ys zs)).words) n =
      coeffWords (mulWords xs (mulWords ys zs)) n := by
  change coeffWords (mulWords xs (normalizeWords (mulWords ys zs))) n =
    coeffWords (mulWords xs (mulWords ys zs)) n
  exact coeffWords_mulWords_normalize_right xs (mulWords ys zs) n

/-- Raw packed multiplication is coefficientwise associative.  This is the
source-triple frontier: the two source-triple expansions above reduce raw
associativity to a fixed-triple word contribution identity. -/
private theorem coeffWords_mulWords_assoc
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (mulWords xs ys) zs) n =
      coeffWords (mulWords xs (mulWords ys zs)) n := by
  rw [coeffWords_mulWords_left_assoc_sourceTriples,
    coeffWords_mulWords_right_assoc_sourceTriples]
  exact xorBoolList_assoc_sourceTripleContribs xs ys zs n

/-- Multiplication in `F_2[x]` via carry-less word products and XOR
accumulation. -/
def mul (p q : GF2Poly) : GF2Poly :=
  ofWords (mulWords p.words q.words)

instance : Mul GF2Poly where
  mul := mul

/-- Zero is a left annihilator for packed `GF(2)` polynomial multiplication. -/
@[simp] theorem zero_mul (p : GF2Poly) : (0 : GF2Poly) * p = 0 := by
  apply ext_words
  change (mul 0 p).words = #[]
  simp [mul, mulWords]

/-- Zero is a right annihilator for packed `GF(2)` polynomial multiplication. -/
@[simp] theorem mul_zero (p : GF2Poly) : p * (0 : GF2Poly) = 0 := by
  apply ext_words
  change (mul p 0).words = #[]
  simp [mul, mulWords]

/-- The normalized product stores no more than the raw convolution capacity. -/
theorem wordCount_mul_le (p q : GF2Poly) : (p * q).wordCount ≤ p.wordCount + q.wordCount := by
  have hnorm := normalizeWords_size_le (mulWords p.words q.words)
  have hraw : (mulWords p.words q.words).size ≤ p.wordCount + q.wordCount := by
    unfold mulWords GF2Poly.wordCount
    by_cases hxs : p.words.isEmpty <;> by_cases hys : q.words.isEmpty
    · simp [hxs, hys]
    · simp [hxs, hys]
    · simp [hxs, hys]
    · simp [hxs, hys, foldl_mulWords_size]
  calc
    (p * q).wordCount = (ofWords (mulWords p.words q.words)).words.size := by
      rfl
    _ ≤ (mulWords p.words q.words).size := hnorm
    _ ≤ p.wordCount + q.wordCount := hraw

/-- Multiplication by a monomial has the expected packed-word capacity bound. -/
theorem wordCount_mul_monomial_le (p : GF2Poly) (k : Nat) :
    (p * monomial k).wordCount ≤ p.wordCount + (k / 64 + 1) := by
  exact Nat.le_trans (wordCount_mul_le p (monomial k))
    (Nat.add_le_add_left (wordCount_monomial_le k) p.wordCount)

/-- Multiplication coefficients reduce to the raw carry-less word product. -/
@[simp]
theorem coeff_mul (p q : GF2Poly) (n : Nat) :
    (p * q).coeff n = coeffWords (mulWords p.words q.words) n := by
  change (ofWords (mulWords p.words q.words)).coeff n =
    coeffWords (mulWords p.words q.words) n
  simp

example (p q : GF2Poly) (n : Nat) :
    (p * q).coeff n = coeffWords (mulWords p.words q.words) n := by
  simp

/-- The unit polynomial is the degree-zero monomial. -/
theorem one_eq_monomial_zero : (1 : GF2Poly) = monomial 0 := by
  change one = monomial 0
  simp [one, monomial]

private theorem replicate_two_set_zero_one (lo hi : UInt64) :
    ((Array.replicate 2 (0 : UInt64)).set 0 lo (by simp)).set 1 hi (by simp) =
      #[lo, hi] := by
  rfl

/-- Multiplying two single packed words is the two-word carry-less product. -/
theorem ofUInt64_mul_ofUInt64 (a b : UInt64) :
    ofUInt64 a * ofUInt64 b = ofWords #[(clmul a b).2, (clmul a b).1] := by
  by_cases ha : a = 0
  · subst ha
    rw [clmul_zero_left]
    apply ext_words
    change (mul (ofWords #[(0 : UInt64)]) (ofUInt64 b)).words = (ofWords #[0, 0]).words
    simp [ofUInt64, mul, mulWords]
  by_cases hb : b = 0
  · subst hb
    rw [clmul_zero_right]
    apply ext_words
    change (mul (ofUInt64 a) (ofWords #[(0 : UInt64)])).words = (ofWords #[0, 0]).words
    simp [ofUInt64, mul, mulWords]
  apply ext_coeff
  intro n
  rw [coeff_mul]
  simp [ofUInt64, mulWords, xorClmulAt, Array.setIfInBounds, ha, hb,
    replicate_two_set_zero_one]

private theorem wordBitAt_getElem!_eq_false_of_degree?_lt
    {p : GF2Poly} {d i bit : Nat}
    (hp : p.degree? = some d) (hbit : bit < 64) (hlt : d < 64 * i + bit) :
    wordBitAt p.words[i]! bit = false := by
  rw [wordBitAt_getElem!_eq_coeff p hbit]
  exact coeff_eq_false_of_degree?_lt hp hlt

private theorem degree?_eq_some_word_lt {p : GF2Poly} {d : Nat}
    (hp : p.degree? = some d) :
    d / 64 < p.words.size := by
  have hcoeff := coeff_eq_true_of_degree?_eq_some hp
  by_cases hlt : d / 64 < p.words.size
  · exact hlt
  · have hfalse : p.coeff d = false := by
      simp [coeff, coeffWords, hlt]
    rw [hfalse] at hcoeff
    contradiction

private theorem wordBitAt_getElem!_eq_true_of_degree?_eq_some
    {p : GF2Poly} {d : Nat} (hp : p.degree? = some d) :
    wordBitAt p.words[d / 64]! (d % 64) = true := by
  have hbit : d % 64 < 64 := Nat.mod_lt d (by decide : 0 < 64)
  rw [wordBitAt_getElem!_eq_coeff p hbit]
  have hd : 64 * (d / 64) + d % 64 = d := by
    exact Nat.div_add_mod d 64
  rw [hd]
  exact coeff_eq_true_of_degree?_eq_some hp

private theorem clmulSourcePairCoeff_eq_false_of_forall
    (x y : UInt64) {total : Nat}
    (hzero :
      ∀ a b, a < 64 → b < 64 → a + b = total →
        (wordBitAt x a && wordBitAt y b) = false) :
    clmulSourcePairCoeff x y total = false := by
  unfold clmulSourcePairCoeff
  rw [← xorBoolList_map_xorBoolList]
  have houter :
      (List.range 64).map
          (fun b =>
            xorBoolList
              ((List.range 64).map
                (fun a => (wordBitAt x a && wordBitAt y b) &&
                  decide (a + b = total)))) =
        (List.range 64).map (fun _ => false) := by
    apply List.map_congr_left
    intro b hbMem
    have hb : b < 64 := List.mem_range.mp hbMem
    have hinner :
        (List.range 64).map
            (fun a => (wordBitAt x a && wordBitAt y b) &&
              decide (a + b = total)) =
          (List.range 64).map (fun _ => false) := by
      apply List.map_congr_left
      intro a haMem
      have ha : a < 64 := List.mem_range.mp haMem
      by_cases hsum : a + b = total
      · rw [hzero a b ha hb hsum]
        simp [hsum]
      · simp [hsum]
    rw [hinner, xorBoolList_range_false]
  rw [houter, xorBoolList_range_false]

private theorem source_pair_and_eq_false_of_not_leading
    {p q : GF2Poly} {dp dq i j a b : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (ha : a < 64) (hb : b < 64)
    (hsum : 64 * i + a + (64 * j + b) = dp + dq)
    (hnot : i ≠ dp / 64 ∨ j ≠ dq / 64 ∨ a ≠ dp % 64 ∨ b ≠ dq % 64) :
    (wordBitAt p.words[i]! a && wordBitAt q.words[j]! b) = false := by
  by_cases hpi : i = dp / 64
  · by_cases hpa : a = dp % 64
    · have hpidx : 64 * i + a = dp := by
        subst hpi
        subst hpa
        exact Nat.div_add_mod dp 64
      have hqidx : 64 * j + b = dq := by omega
      have hj : j = dq / 64 := by
        have hdiv := congrArg (fun n => n / 64) hqidx
        simpa [Nat.mul_add_div (by decide : 0 < 64), Nat.div_eq_of_lt hb] using hdiv
      have hbq : b = dq % 64 := by
        have hmod := congrArg (fun n => n % 64) hqidx
        simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hb] using hmod
      cases hnot with
      | inl hi => contradiction
      | inr hrest =>
          cases hrest with
          | inl hjne => contradiction
          | inr hrest2 =>
              cases hrest2 with
              | inl hane => contradiction
              | inr hbne => contradiction
    · have hqgt_or_hpgt : dq < 64 * j + b ∨ dp < 64 * i + a := by
        by_cases halt : a < dp % 64
        · left
          subst hpi
          have hdp := Nat.div_add_mod dp 64
          omega
        · right
          subst hpi
          have hdp := Nat.div_add_mod dp 64
          have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
          omega
      cases hqgt_or_hpgt with
      | inl hqgt =>
          have hqfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hq hb hqgt
          simp [hqfalse]
      | inr hpgt =>
          have hpfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hp ha hpgt
          simp [hpfalse]
  · by_cases hilt : i < dp / 64
    · have hqgt : dq < 64 * j + b := by
        have hdp := Nat.div_add_mod dp 64
        have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
        omega
      have hqfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hq hb hqgt
      simp [hqfalse]
    · have higt : dp < 64 * i + a := by
        have hdp := Nat.div_add_mod dp 64
        have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
        omega
      have hpfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hp ha higt
      simp [hpfalse]

private theorem clmulCoeffAt_degree_add_eq_false_of_not_leading_word
    {p q : GF2Poly} {dp dq i j : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (hnot : i ≠ dp / 64 ∨ j ≠ dq / 64) :
    clmulCoeffAt (i + j) p.words[i]! q.words[j]! (dp + dq) = false := by
  rw [clmulCoeffAt_sourcePairCoeff]
  by_cases hlow : (dp + dq) / 64 = i + j
  · simp only [if_pos hlow]
    apply clmulSourcePairCoeff_eq_false_of_forall
    intro a b ha hb hsum
    apply source_pair_and_eq_false_of_not_leading hp hq ha hb
    · have htarget := Nat.div_add_mod (dp + dq) 64
      omega
    · cases hnot with
      | inl hi => exact Or.inl hi
      | inr hj => exact Or.inr (Or.inl hj)
  · by_cases hhigh : (dp + dq) / 64 = i + j + 1
    · simp only [if_neg hlow, if_pos hhigh]
      apply clmulSourcePairCoeff_eq_false_of_forall
      intro a b ha hb hsum
      apply source_pair_and_eq_false_of_not_leading hp hq ha hb
      · have htarget := Nat.div_add_mod (dp + dq) 64
        omega
      · cases hnot with
        | inl hi => exact Or.inl hi
        | inr hj => exact Or.inr (Or.inl hj)
    · simp only [if_neg hlow, if_neg hhigh]

private theorem clmulCoeffAt_degree_add_leading_word
    {p q : GF2Poly} {dp dq : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq) :
    clmulCoeffAt (dp / 64 + dq / 64)
      p.words[dp / 64]! q.words[dq / 64]! (dp + dq) = true := by
  rw [clmulCoeffAt_sourcePairCoeff]
  by_cases hcarry : dp % 64 + dq % 64 < 64
  · have hlow : (dp + dq) / 64 = dp / 64 + dq / 64 := by
      have hdp := Nat.div_add_mod dp 64
      have hdq := Nat.div_add_mod dq 64
      omega
    have hmod : (dp + dq) % 64 = dp % 64 + dq % 64 := by
      have hdp := Nat.div_add_mod dp 64
      have hdq := Nat.div_add_mod dq 64
      omega
    simp only [if_pos hlow]
    rw [hmod]
    apply clmulSourcePairCoeff_single_active
      (a₀ := dp % 64) (b₀ := dq % 64)
    · exact Nat.mod_lt dp (by decide : 0 < 64)
    · exact Nat.mod_lt dq (by decide : 0 < 64)
    · exact wordBitAt_getElem!_eq_true_of_degree?_eq_some hp
    · exact wordBitAt_getElem!_eq_true_of_degree?_eq_some hq
    · rfl
    · intro a b ha hb hsum hnot
      apply source_pair_and_eq_false_of_not_leading hp hq ha hb
      · have hdp := Nat.div_add_mod dp 64
        have hdq := Nat.div_add_mod dq 64
        omega
      · exact Or.inr (Or.inr hnot)
  · have hhigh : (dp + dq) / 64 = dp / 64 + dq / 64 + 1 := by
      have hdp := Nat.div_add_mod dp 64
      have hdq := Nat.div_add_mod dq 64
      have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
      have hdqbit : dq % 64 < 64 := Nat.mod_lt dq (by decide : 0 < 64)
      omega
    have hlow : (dp + dq) / 64 ≠ dp / 64 + dq / 64 := by omega
    have hmod : (dp + dq) % 64 + 64 = dp % 64 + dq % 64 := by
      have hdp := Nat.div_add_mod dp 64
      have hdq := Nat.div_add_mod dq 64
      have htarget := Nat.div_add_mod (dp + dq) 64
      have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
      have hdqbit : dq % 64 < 64 := Nat.mod_lt dq (by decide : 0 < 64)
      omega
    simp only [if_neg hlow, if_pos hhigh]
    rw [hmod]
    apply clmulSourcePairCoeff_single_active
      (a₀ := dp % 64) (b₀ := dq % 64)
    · exact Nat.mod_lt dp (by decide : 0 < 64)
    · exact Nat.mod_lt dq (by decide : 0 < 64)
    · exact wordBitAt_getElem!_eq_true_of_degree?_eq_some hp
    · exact wordBitAt_getElem!_eq_true_of_degree?_eq_some hq
    · rfl
    · intro a b ha hb hsum hnot
      apply source_pair_and_eq_false_of_not_leading hp hq ha hb
      · have hdp := Nat.div_add_mod dp 64
        have hdq := Nat.div_add_mod dq 64
        omega
      · exact Or.inr (Or.inr hnot)

private theorem coeffWords_mulWords_degree_add_of_degree?_eq_some
    {p q : GF2Poly} {dp dq : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq) :
    coeffWords (mulWords p.words q.words) (dp + dq) = true := by
  rw [coeffWords_mulWords_contrib]
  rw [← xorBoolList_map_xorBoolList (List.range p.words.size)
    (fun i =>
      (List.range q.words.size).map
        (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! (dp + dq)))]
  rw [xorBoolList_range_single_active
    (fun i =>
      xorBoolList
        ((List.range q.words.size).map
          (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! (dp + dq))))
    (degree?_eq_some_word_lt hp)]
  · rw [xorBoolList_range_single_active
      (fun j =>
        clmulCoeffAt (dp / 64 + j) p.words[dp / 64]! q.words[j]! (dp + dq))
      (degree?_eq_some_word_lt hq)]
    · exact clmulCoeffAt_degree_add_leading_word hp hq
    · intro j hj hineq
      exact clmulCoeffAt_degree_add_eq_false_of_not_leading_word hp hq (Or.inr hineq)
  · intro i hi hineq
    have hinner :
        (List.range q.words.size).map
            (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! (dp + dq)) =
          (List.range q.words.size).map (fun _ => false) := by
      apply List.map_congr_left
      intro j _hj
      exact clmulCoeffAt_degree_add_eq_false_of_not_leading_word hp hq (Or.inl hineq)
    rw [hinner, xorBoolList_range_false]

private theorem clmulCoeffAt_above_degree_add_eq_false
    {p q : GF2Poly} {dp dq i j n : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (hn : dp + dq < n) :
    clmulCoeffAt (i + j) p.words[i]! q.words[j]! n = false := by
  rw [clmulCoeffAt_sourcePairCoeff]
  by_cases hlow : n / 64 = i + j
  · simp only [if_pos hlow]
    apply clmulSourcePairCoeff_eq_false_of_forall
    intro a b ha hb hsum
    have htotal : 64 * i + a + (64 * j + b) = n := by
      have hndecomp := Nat.div_add_mod n 64
      omega
    by_cases hpgt : dp < 64 * i + a
    · have hpfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hp ha hpgt
      simp [hpfalse]
    · have hqgt : dq < 64 * j + b := by omega
      have hqfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hq hb hqgt
      simp [hqfalse]
  · by_cases hhigh : n / 64 = i + j + 1
    · simp only [if_neg hlow, if_pos hhigh]
      apply clmulSourcePairCoeff_eq_false_of_forall
      intro a b ha hb hsum
      have htotal : 64 * i + a + (64 * j + b) = n := by
        have hndecomp := Nat.div_add_mod n 64
        omega
      by_cases hpgt : dp < 64 * i + a
      · have hpfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hp ha hpgt
        simp [hpfalse]
      · have hqgt : dq < 64 * j + b := by omega
        have hqfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hq hb hqgt
        simp [hqfalse]
    · simp only [if_neg hlow, if_neg hhigh]

private theorem coeffWords_mulWords_above_degree_add_eq_false
    {p q : GF2Poly} {dp dq n : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (hn : dp + dq < n) :
    coeffWords (mulWords p.words q.words) n = false := by
  rw [coeffWords_mulWords_contrib]
  rw [← xorBoolList_map_xorBoolList (List.range p.words.size)
    (fun i =>
      (List.range q.words.size).map
        (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! n))]
  have hrows :
      (List.range p.words.size).map
          (fun i =>
            xorBoolList
              ((List.range q.words.size).map
                (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! n))) =
        (List.range p.words.size).map (fun _ => false) := by
    apply List.map_congr_left
    intro i _hi
    have hinner :
        (List.range q.words.size).map
            (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! n) =
          (List.range q.words.size).map (fun _ => false) := by
      apply List.map_congr_left
      intro j _hj
      exact clmulCoeffAt_above_degree_add_eq_false hp hq hn
    rw [hinner, xorBoolList_range_false]
  rw [hrows, xorBoolList_range_false]

/-- The top coefficient of a product is the product of the two top
coefficients, hence set for nonzero `GF(2)` polynomials. -/
theorem coeff_mul_degree_add_of_degree?_eq_some {p q : GF2Poly} {dp dq : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq) :
    (p * q).coeff (dp + dq) = true := by
  rw [coeff_mul]
  exact coeffWords_mulWords_degree_add_of_degree?_eq_some hp hq

/-- Coefficients of a packed `GF(2)` product strictly above the sum of the
factor degrees vanish. -/
theorem coeff_mul_eq_false_of_degree_add_lt {p q : GF2Poly} {dp dq n : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (hn : dp + dq < n) :
    (p * q).coeff n = false := by
  rw [coeff_mul]
  exact coeffWords_mulWords_above_degree_add_eq_false hp hq hn

/-- The packed `GF(2)` product of two nonzero polynomials has degree exactly the
sum of the two factor degrees. -/
@[grind →]
theorem degree?_mul_of_degree?_eq_some {p q : GF2Poly} {dp dq : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq) :
    (p * q).degree? = some (dp + dq) := by
  apply degree?_eq_some_of_coeff_eq_true_of_forall_gt_false
  · exact coeff_mul_degree_add_of_degree?_eq_some hp hq
  · intro m hm
    exact coeff_mul_eq_false_of_degree_add_lt hp hq hm

/-- Left distributivity of packed `GF(2)` polynomial multiplication over
addition. -/
theorem left_distrib (p r q : GF2Poly) :
    (p + r) * q = p * q + r * q := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_add_eq_bne, coeff_mul, coeff_mul]
  change
    coeffWords (mulWords (normalizeWords (xorWords p.words r.words)) q.words) n =
      (coeffWords (mulWords p.words q.words) n !=
        coeffWords (mulWords r.words q.words) n)
  let raw := xorWords p.words r.words
  let m := raw.size
  have hraw := coeffWords_mulWords_xor_left p.words r.words q.words n
  rw [← coeffWords_mulWords_common_left raw q.words n m (by simp [m])] at hraw
  rw [← coeffWords_mulWords_common_left (normalizeWords raw) q.words n m
    (by
      dsimp [m, raw]
      exact normalizeWords_size_le _)]
  simpa [raw, normalizeWords_getElem!] using hraw

/-- Packed `GF(2)` polynomial multiplication is commutative. -/
theorem mul_comm (p q : GF2Poly) :
    p * q = q * p := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  exact coeffWords_mulWords_comm p.words q.words n

/-- Right distributivity of packed `GF(2)` polynomial multiplication over
addition. -/
theorem right_distrib (p q r : GF2Poly) :
    p * (q + r) = p * q + p * r := by
  rw [mul_comm p (q + r), left_distrib, mul_comm q p, mul_comm r p]

/-- Packed `GF(2)` polynomial multiplication is associative. -/
theorem mul_assoc (p q r : GF2Poly) :
    (p * q) * r = p * (q * r) := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  change
    coeffWords (mulWords (ofWords (mulWords p.words q.words)).words r.words) n =
      coeffWords (mulWords p.words (ofWords (mulWords q.words r.words)).words) n
  rw [coeffWords_mulWords_ofWords_left, coeffWords_mulWords_ofWords_right]
  exact coeffWords_mulWords_assoc p.words q.words r.words n

private theorem coeff_shiftLeft_lt (p : GF2Poly) {k n : Nat} (hn : n < k) :
    (p.shiftLeft k).coeff n = false := by
  rw [coeff_shiftLeft]
  by_cases hbitShift : k % 64 = 0
  · simp [hbitShift]
    have hword : n / 64 < k / 64 := by
      have hnSplit := Nat.div_add_mod n 64
      have hkSplit := Nat.div_add_mod k 64
      have hnBit := Nat.mod_lt n (by decide : 0 < 64)
      omega
    rw [coeffWords]
    have hget :
        (((Array.replicate (k / 64) (0 : UInt64)) ++ p.words)[n / 64]?).getD 0 = 0 := by
      rw [Array.getElem?_append_left]
      · simp [hword]
      · simp [hword]
    rw [hget, UInt64.bne_zero_eq_toNat_bne_zero]
    simp
  · simp [hbitShift, coeffWords_replicate_append_shiftLeftBitsList_lt p.words hbitShift hn]

private theorem coeff_shiftLeft_add_source_oob
    (p : GF2Poly) {k source : Nat} (hsource : p.words.size ≤ source / 64) :
    (p.shiftLeft k).coeff (source + k) = false := by
  rw [coeff_shiftLeft]
  by_cases hbitShift : k % 64 = 0
  · have hcoeff : p.coeff source = false := by
      simp [coeff, coeffWords, hsource]
    simp [hbitShift, coeffWords_replicate_append_add_of_mod_eq_zero, coeff] at hcoeff ⊢
    exact hcoeff
  · simp [hbitShift,
      coeffWords_replicate_append_shiftLeftBitsList_add_of_not_word
        p.words hbitShift (Nat.not_lt.mpr hsource)]

/-- Right multiplication by the monomial `x^k` shifts packed GF(2)
polynomials left by `k` coefficients. -/
@[simp]
theorem mul_monomial (q : GF2Poly) (k : Nat) :
    q * monomial k = q.mulXk k := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mulXk]
  by_cases hn : n < k
  · rw [coeffWords_mulWords_monomial_lt q.words hn]
    exact (coeff_shiftLeft_lt q hn).symm
  · let source := n - k
    have hn_eq : n = source + k := by
      dsimp [source]
      omega
    rw [hn_eq]
    by_cases hsource : source / 64 < q.words.size
    · rw [coeffWords_mulWords_monomial_source q.words hsource]
      exact (coeff_shiftLeft_add_of_word_lt (p := q) (k := k) (n := source) hsource).symm
    · have hsource_le : q.words.size ≤ source / 64 := Nat.le_of_not_gt hsource
      rw [coeffWords_mulWords_monomial_source_oob q.words hsource_le]
      exact (coeff_shiftLeft_add_source_oob q hsource_le).symm

/-- Left multiplication by the monomial `x^k` shifts packed GF(2)
polynomials left by `k` coefficients. -/
@[simp]
theorem monomial_mul (k : Nat) (q : GF2Poly) :
    monomial k * q = q.mulXk k := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mulXk]
  by_cases hn : n < k
  · rw [coeffWords_monomial_mulWords_lt q.words hn]
    exact (coeff_shiftLeft_lt q hn).symm
  · let source := n - k
    have hn_eq : n = source + k := by
      dsimp [source]
      omega
    rw [hn_eq]
    by_cases hsource : source / 64 < q.words.size
    · rw [coeffWords_monomial_mulWords_source q.words hsource]
      exact (coeff_shiftLeft_add_of_word_lt (p := q) (k := k) (n := source) hsource).symm
    · have hsource_le : q.words.size ≤ source / 64 := Nat.le_of_not_gt hsource
      rw [coeffWords_monomial_mulWords_source_oob q.words hsource_le]
      exact (coeff_shiftLeft_add_source_oob q hsource_le).symm

example (q : GF2Poly) (k : Nat) :
    (monomial k * q).degree? = (q.mulXk k).degree? := by
  simp

/-- Multiplication by `x^0` leaves a packed `GF(2)` polynomial unchanged. -/
@[simp] theorem mulXk_zero (p : GF2Poly) :
    p.mulXk 0 = p := by
  apply ext_coeff
  intro n
  rw [coeff_mulXk, coeff_shiftLeft]
  simp [coeff]

/-- One is a left identity for packed `GF(2)` polynomial multiplication. -/
@[simp] theorem one_mul (p : GF2Poly) :
    (1 : GF2Poly) * p = p := by
  rw [one_eq_monomial_zero, monomial_mul, mulXk_zero]

/-- One is a right identity for packed `GF(2)` polynomial multiplication. -/
@[simp] theorem mul_one (p : GF2Poly) :
    p * (1 : GF2Poly) = p := by
  rw [one_eq_monomial_zero, mul_monomial, mulXk_zero]

/-- Expanding a quotient update by an added monomial gives the product update
used by long division. -/
theorem add_monomial_mul (quot q : GF2Poly) (k : Nat) :
    (quot + monomial k) * q = quot * q + q.mulXk k := by
  rw [left_distrib, monomial_mul]

/-- The product of two monomials is the monomial whose exponent is the sum. -/
theorem monomial_mul_monomial (a b : Nat) :
    monomial a * monomial b = monomial (a + b) := by
  rw [monomial_mul]
  apply ext_coeff
  intro n
  by_cases hn_eq : n = a + b
  · subst hn_eq
    have hdeg : ((monomial b).mulXk a).degree? = some (b + a) :=
      degree?_mulXk_of_degree?_eq_some (degree?_monomial b)
    rw [coeff_monomial_self,
      show a + b = b + a from Nat.add_comm a b]
    exact coeff_eq_true_of_degree?_eq_some hdeg
  · rw [coeff_monomial_ne hn_eq]
    by_cases h_gt : a + b < n
    · have hdeg : ((monomial b).mulXk a).degree? = some (b + a) :=
        degree?_mulXk_of_degree?_eq_some (degree?_monomial b)
      exact coeff_eq_false_of_degree?_lt hdeg (by omega)
    · rw [coeff_mulXk]
      by_cases hn_lt_a : n < a
      · exact coeff_shiftLeft_lt (monomial b) hn_lt_a
      · have hn_ge_a : a ≤ n := Nat.le_of_not_gt hn_lt_a
        have hlt : n < a + b := by omega
        have hsource_lt_b : n - a < b := by omega
        have hsource_ne_b : n - a ≠ b := Nat.ne_of_lt hsource_lt_b
        have hword : (n - a) / 64 < (monomial b).words.size := by
          rw [words_monomial_size]
          have : (n - a) / 64 ≤ b / 64 :=
            Nat.div_le_div_right (Nat.le_of_lt hsource_lt_b)
          omega
        have hn_eq_source : n = (n - a) + a := by omega
        rw [hn_eq_source, coeff_shiftLeft_add_of_word_lt (monomial b) hword]
        exact coeff_monomial_ne hsource_ne_b

end GF2Poly
end Hex
