/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Init.Data.List.TakeDrop
public import Init.Data.Int.ToString
public import Init.Data.Nat.ToString
public import Init.Data.String.Basic
public import Init.Data.String.Lemmas.Basic

public section

namespace Hex.SignDet.Codec.Decimal

/-- Decode a nonempty decimal digit word. JSON token syntax, including the
leading-zero restriction, is checked separately by the enclosing lexer. -/
@[expose] def readDigits (text : String) : Option Nat :=
  let cs := text.toList
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (Nat.ofDigitChars 10 cs 0)

/-- Decode the actual UTF-8 bytes of a decimal digit word. -/
@[expose] def readNat (input : ByteArray) : Option Nat := do
  let text ← String.fromUTF8? input
  readDigits text

/-- The ordinary decimal printer and total digit reader agree for every Nat. -/
theorem readDigits_repr (n : Nat) : readDigits n.repr = some n := by
  have ha : (Nat.toDigits 10 n).all Char.isDigit = true := by
    apply List.all_eq_true.mpr
    intro c hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp [readDigits, Nat.toList_repr, Nat.toDigits_ne_nil, ha]

/-- Read a decimal digit prefix and retain the untouched following tokens. -/
@[expose] def readWord (input : List Char) : Option (Nat × List Char) := do
  let value ← readDigits (String.ofList (input.takeWhile Char.isDigit))
  return (value, input.dropWhile Char.isDigit)

/-- A printed natural number consumes exactly its digits when followed by a
non-digit delimiter or the end of the input. -/
theorem readWord_repr (n : Nat) (suffix : List Char)
    (h : suffix.takeWhile Char.isDigit = []) :
    readWord (n.repr.toList ++ suffix) = some (n, suffix) := by
  have hd : ∀ c ∈ n.repr.toList, c.isDigit := by
    intro c hc
    exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) (by simpa using hc)
  have hr : suffix.dropWhile Char.isDigit = suffix := by
    simpa only [h, List.nil_append] using
      (List.takeWhile_append_dropWhile (p := Char.isDigit) (l := suffix))
  simp only [readWord, List.takeWhile_append_of_pos hd, h, List.append_nil,
    String.ofList_toList, readDigits_repr, bind, Option.bind,
    List.dropWhile_append_of_pos hd, hr, pure]

/-- UTF-8 validation and decoding preserve the whole original string. -/
theorem fromUTF8_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.fromUTF8?, String.toUTF8_eq_toByteArray, s.isValidUTF8, ↓reduceDIte]
  rfl

/-- A byte roundtrip for the actual decimal printer, without a parser-success
premise or a fixed collection of test literals. -/
theorem readNat_repr (n : Nat) : readNat n.repr.toUTF8 = some n := by
  simp only [readNat, fromUTF8_toUTF8, bind, Option.bind]
  exact readDigits_repr n

/-- An optional minus precedes a decimal digit word. This helper does not
accept plus signs, decimal points or exponents. -/
@[expose] def readIntText (text : String) : Option Int :=
  if text.toList.head? = some '-' then
    (readDigits (String.ofList text.toList.tail)).map fun n => -(Int.ofNat n)
  else (readDigits text).map Int.ofNat

@[expose] def readInt (input : ByteArray) : Option Int := do
  let text ← String.fromUTF8? input
  readIntText text

private theorem head_repr_ne_minus (n : Nat) : n.repr.toList.head? ≠ some '-' := by
  intro h
  have hc : '-' ∈ Nat.toDigits 10 n := by simpa using List.mem_of_head? h
  have hd := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
  contradiction

private theorem readIntText_nat (n : Nat) : readIntText n.repr = some (Int.ofNat n) := by
  simp only [readIntText, ite_eq_right (head_repr_ne_minus n), readDigits_repr, Option.map_some]

/-- Every signed integer survives its actual printed UTF-8 bytes. -/
theorem readInt_repr (n : Int) : readInt n.repr.toUTF8 = some n := by
  simp only [readInt, fromUTF8_toUTF8, bind, Option.bind]
  cases n with
  | ofNat n =>
    rw [show (Int.ofNat n).repr = n.repr by simp [Int.repr_eq_ite]]
    exact readIntText_nat n
  | negSucc n =>
    simp [Int.repr_eq_ite, readIntText, String.toList_append]
    simpa only [← Nat.repr_eq_ofList_toDigits] using readDigits_repr (n + 1)

theorem readInt_toString (n : Int) : readInt (toString n).toUTF8 = some n := by
  simpa only [Int.toString_eq_repr] using readInt_repr n

/-- info: 'Hex.SignDet.Codec.Decimal.readNat_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readNat_repr
/-- info: 'Hex.SignDet.Codec.Decimal.readInt_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readInt_repr

end Hex.SignDet.Codec.Decimal
