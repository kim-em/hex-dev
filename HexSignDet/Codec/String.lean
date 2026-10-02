/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Decimal
public import Init.Data.Char.Lemmas
public import Init.Omega
import all Init.Data.Repr

public section

namespace Hex.SignDet.Codec.Str

/-- Decode one hexadecimal digit, including either JSON letter case. -/
@[expose] def hex (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
  else none

@[expose] def hex4 (a b c d : Char) : Option Nat := do
  let a ← hex a
  let b ← hex b
  let c ← hex c
  let d ← hex d
  return 4096 * a + 256 * b + 16 * c + d

/-- Read an escape after the backslash. Valid UTF-16 surrogate pairs are
combined; lone surrogates are rejected. Ordinary Unicode is read directly. -/
@[expose] def readEscape : List Char → Option (Char × List Char)
  | '"' :: rest => some ('"', rest)
  | '\\' :: rest => some ('\\', rest)
  | '/' :: rest => some ('/', rest)
  | 'b' :: rest => some ('\x08', rest)
  | 'f' :: rest => some ('\x0c', rest)
  | 'n' :: rest => some ('\n', rest)
  | 'r' :: rest => some ('\x0d', rest)
  | 't' :: rest => some ('\t', rest)
  | 'u' :: a :: b :: c :: d :: rest => do
    let value ← hex4 a b c d
    if value < 0xd800 ∨ 0xe000 ≤ value then return (Char.ofNat value, rest)
    else if value < 0xdc00 then
      match rest with
      | '\\' :: 'u' :: e :: f :: g :: h :: suffix => do
        let low ← hex4 e f g h
        if 0xdc00 ≤ low ∧ low < 0xe000 then
          return (Char.ofNat (0x10000 + (value - 0xd800) * 1024 + (low - 0xdc00)), suffix)
        else none
      | _ => none
    else none
  | _ => none

/-- JSON escaping, preserving all Unicode scalar values. -/
@[expose] def writeChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c.toNat < 32 then
    ['\\', 'u', '0', '0', Nat.digitChar (c.toNat / 16), Nat.digitChar (c.toNat % 16)]
  else [c]

@[expose] def writeBody (cs : List Char) : List Char := cs.flatMap writeChar

/-- A finite parser for a quoted body. Fuel bounds decoded characters; no
partial definition or assumed parser success is used by its roundtrip law. -/
@[expose] def readBody : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | fuel + 1, c :: rest =>
    if c = '"' then some ([], rest)
    else if c = '\\' then do
      let (c, rest) ← readEscape rest
      let (cs, suffix) ← readBody fuel rest
      return (c :: cs, suffix)
    else if c.toNat < 32 then none
    else do
      let (cs, suffix) ← readBody fuel rest
      return (c :: cs, suffix)
  | _, [] => none

private theorem hex_digit (n : Nat) (h : n < 16) : hex n.digitChar = some n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
    simp [hex, Nat.digitChar]
  | n + 16 => omega

private theorem hex4_control (n : Nat) (h : n < 32) :
    hex4 '0' '0' (Nat.digitChar (n / 16)) (Nat.digitChar (n % 16)) = some n := by
  have hz : hex '0' = some 0 := by simp [hex]
  simp only [hex4, hex_digit (n / 16) (by omega),
    hex_digit (n % 16) (Nat.mod_lt _ (by decide)), hz,
    bind, Option.bind, pure, Option.some.injEq]
  omega

private theorem readEscape_control (n : Nat) (h : n < 32) (suffix : List Char) :
    readEscape (['u', '0', '0', Nat.digitChar (n / 16), Nat.digitChar (n % 16)] ++ suffix) =
      some (Char.ofNat n, suffix) := by
  simp [readEscape, hex4_control n h, show n < 0xd800 by omega]

private theorem readBody_char (c : Char) (tail : List Char) (fuel : Nat) :
    readBody (fuel + 1) (writeChar c ++ tail) =
      (readBody fuel tail).map (fun (cs, suffix) => (c :: cs, suffix)) := by
  by_cases hq : c = '"'
  · subst c
    simp [writeChar, readBody, readEscape, bind, Option.bind]
    cases readBody fuel tail <;> rfl
  by_cases hb : c = '\\'
  · subst c
    simp [writeChar, readBody, readEscape, bind, Option.bind]
    cases readBody fuel tail <;> rfl
  by_cases hc : c.toNat < 32
  · simp [writeChar, hq, hb, hc, readBody, bind, Option.bind]
    rw [show readEscape ('u' :: '0' :: '0' :: (c.toNat / 16).digitChar ::
      (c.toNat % 16).digitChar :: tail) = some (c, tail) by
        simpa using readEscape_control c.toNat hc tail]
    dsimp only
    cases readBody fuel tail <;> rfl
  · simp [writeChar, hq, hb, hc, readBody, bind, Option.bind]
    cases readBody fuel tail <;> rfl

/-- Parsing the emitted body consumes exactly its characters and closing
quote, retaining an arbitrary following token suffix. -/
theorem readBody_write (cs suffix : List Char) (fuel : Nat) (h : cs.length < fuel) :
    readBody fuel (writeBody cs ++ '"' :: suffix) = some (cs, suffix) := by
  induction cs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [writeBody, readBody]
  | cons c cs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [writeBody, List.flatMap_cons, List.append_assoc, readBody_char]
      change (readBody fuel (writeBody cs ++ '"' :: suffix)).map _ = _
      rw [ih fuel (by simpa using h)]
      rfl

private theorem writeChar_length (c : Char) : 1 ≤ (writeChar c).length := by
  unfold writeChar
  split
  · decide
  · split
    · decide
    · split <;> simp only [List.length_cons, List.length_nil] <;> omega

private theorem writeBody_length (cs : List Char) : cs.length ≤ (writeBody cs).length := by
  induction cs with
  | nil => simp [writeBody]
  | cons c cs ih =>
    have hc := writeChar_length c
    simp only [writeBody, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

/-- Write a complete quoted JSON string. -/
@[expose] def write (text : String) : String :=
  String.ofList ('"' :: writeBody text.toList ++ ['"'])

/-- Count through the next unescaped quotation mark only. This avoids
rescanning the entire remaining JSON input for every string token. -/
@[expose] def scanBody : List Char → Nat
  | [] => 0
  | c :: rest =>
    if c = '"' then 1
    else if c = '\\' then
      match rest with
      | [] => 1
      | _ :: rest => 2 + scanBody rest
    else 1 + scanBody rest

private theorem digit_not_delimiter (n : Nat) (h : n < 16) :
    n.digitChar ≠ '"' ∧ n.digitChar ≠ '\\' := by
  have hd := hex_digit n h
  constructor
  · intro he; rw [he] at hd; simp [hex] at hd
  · intro he; rw [he] at hd; simp [hex] at hd

private theorem scanBody_write (cs : List Char) (suffix : List Char) :
    scanBody (writeBody cs ++ '"' :: suffix) = (writeBody cs).length + 1 := by
  induction cs with
  | nil =>
    simp only [writeBody, List.flatMap_nil, List.nil_append, List.length_nil]
    rw [scanBody.eq_def]
    rfl
  | cons c cs ih =>
    rw [show writeBody (c :: cs) = writeChar c ++ writeBody cs by simp [writeBody]]
    rw [List.append_assoc, List.length_append]
    by_cases hq : c = '"'
    · subst c
      simp [writeChar, ih, scanBody.eq_def]
      omega
    by_cases hb : c = '\\'
    · subst c
      simp [writeChar, ih, scanBody.eq_def]
      omega
    by_cases hc : c.toNat < 32
    · have hh := digit_not_delimiter (c.toNat / 16) (by omega)
      have hl := digit_not_delimiter (c.toNat % 16) (Nat.mod_lt _ (by decide))
      simp [writeChar, ih, scanBody.eq_def, hq, hb, hc, hh.1, hh.2, hl.1, hl.2]
      omega
    · simp only [writeChar, hq, hb, hc, ↓reduceIte, List.cons_append, List.nil_append,
        List.length_cons, List.length_nil]
      rw [scanBody.eq_def]
      simp [hq, hb, ih]
      omega

/-- Read a quoted prefix, retaining all following characters. The parser fuel
counts the quoted prefix, so later strings are not repeatedly scanned. -/
@[expose] def readPrefix (input : List Char) : Option (String × List Char) :=
  match input with
  | '"' :: rest => (readBody (scanBody rest) rest).map fun (cs, suffix) =>
      (String.ofList cs, suffix)
  | _ => none

theorem readPrefix_write (text : String) (suffix : List Char) :
    readPrefix ((write text).toList ++ suffix) = some (text, suffix) := by
  have hn := writeBody_length text.toList
  simp only [write, String.toList_ofList, List.cons_append, List.append_assoc,
    List.nil_append, readPrefix]
  rw [scanBody_write]
  rw [readBody_write text.toList suffix _ (by omega)]
  simp

@[expose] def writeBytes (text : String) : ByteArray := (write text).toUTF8

/-- Validate UTF-8 and require that the quoted string consumes all bytes. -/
@[expose] def readBytes (input : ByteArray) : Option String := do
  let text ← String.fromUTF8? input
  let (value, suffix) ← readPrefix text.toList
  if suffix.isEmpty then return value else none

/-- The actual byte printer and total parser agree for every Unicode string,
including control characters, quotes and backslashes. -/
theorem readBytes_write (text : String) : readBytes (writeBytes text) = some text := by
  have hp := readPrefix_write text []
  simp only [List.append_nil] at hp
  unfold readBytes writeBytes
  rw [Decimal.fromUTF8_toUTF8]
  simp [hp, bind, Option.bind]

/-- info: 'Hex.SignDet.Codec.Str.readBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readBytes_write

end Hex.SignDet.Codec.Str
