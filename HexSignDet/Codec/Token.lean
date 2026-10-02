/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.String

public section

namespace Hex.SignDet.Codec

/-- Tokens of the integer-only JSON certificate format. -/
inductive Token where
  | leftArray | rightArray | leftObject | rightObject | comma | colon | null
  | bool (value : Bool)
  | number (value : Int)
  | string (value : _root_.String)
  deriving DecidableEq, Repr

namespace Token

@[expose] def write : Token → List Char
  | .leftArray => ['[']
  | .rightArray => [']']
  | .leftObject => ['{']
  | .rightObject => ['}']
  | .comma => [',']
  | .colon => [':']
  | .null => "null".toList
  | .bool true => "true".toList
  | .bool false => "false".toList
  | .number n => n.repr.toList
  | .string s => (String.write s).toList

/-- Leading zeros are rejected by comparing the complete digit word with the
canonical decimal spelling of its parsed value. -/
@[expose] def readNumber (input : List Char) : Option (Nat × List Char) := do
  let (n, suffix) ← Decimal.readWord input
  if input.takeWhile Char.isDigit = n.repr.toList then return (n, suffix) else none

/-- Read exactly one token. Whitespace between tokens is handled by the lexer. -/
@[expose] def read (input : List Char) : Option (Token × List Char) :=
  if input.head?.any Char.isDigit then
    (readNumber input).map fun (n, suffix) => (.number n, suffix)
  else match input with
  | '[' :: rest => some (.leftArray, rest)
  | ']' :: rest => some (.rightArray, rest)
  | '{' :: rest => some (.leftObject, rest)
  | '}' :: rest => some (.rightObject, rest)
  | ',' :: rest => some (.comma, rest)
  | ':' :: rest => some (.colon, rest)
  | 'n' :: 'u' :: 'l' :: 'l' :: rest => some (.null, rest)
  | 't' :: 'r' :: 'u' :: 'e' :: rest => some (.bool true, rest)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => some (.bool false, rest)
  | '-' :: rest => (readNumber rest).map fun (n, suffix) => (.number (-(n : Int)), suffix)
  | '"' :: _ => (String.readPrefix input).map fun (s, suffix) => (.string s, suffix)
  | _ => none

/-- A space after each emitted token prevents digit/keyword concatenation and
makes token boundaries explicit in the byte-roundtrip proof. -/
@[expose] def emit (token : Token) : List Char := token.write ++ [' ']

private theorem repr_digits (n : Nat) : ∀ c ∈ n.repr.toList, c.isDigit = true := by
  intro c hc
  exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) (by simpa using hc)

private theorem repr_head (n : Nat) (suffix : List Char) :
    (n.repr.toList ++ suffix).head?.any Char.isDigit = true := by
  have hn : n.repr.toList ≠ [] := by simp
  cases he : n.repr.toList with
  | nil => contradiction
  | cons c cs =>
    have hc := repr_digits n c (by simp [he])
    simp [hc]

private theorem readNumber_repr (n : Nat) (suffix : List Char) :
    readNumber (n.repr.toList ++ ' ' :: suffix) = some (n, ' ' :: suffix) := by
  have h : (' ' :: suffix).takeWhile Char.isDigit = [] := by simp
  unfold readNumber
  rw [Decimal.readWord_repr n _ h]
  simp only [bind, Option.bind]
  rw [List.takeWhile_append_of_pos (repr_digits n)]
  simp only [h, List.append_nil, ↓reduceIte]
  rfl

/-- Every emitted token is read literally and leaves its following space and
all later tokens untouched. -/
theorem read_emit (token : Token) (suffix : List Char) :
    read (token.emit ++ suffix) = some (token, ' ' :: suffix) := by
  cases token with
  | leftArray | rightArray | leftObject | rightObject | comma | colon | null =>
    simp [emit, write, read]
  | bool b => cases b <;> simp [emit, write, read]
  | number n =>
    cases n with
    | ofNat n =>
      have hr : (Int.ofNat n).repr = n.repr := by simp [Int.repr_eq_ite]
      simp only [emit, write, hr, List.append_assoc, List.singleton_append]
      unfold read
      rw [repr_head]
      simp only [↓reduceIte, readNumber_repr, Option.map_some]
      rfl
    | negSucc n =>
      have hr : (Int.negSucc n).repr.toList = '-' :: (n + 1).repr.toList := by
        simp [Int.repr_eq_ite, Nat.toList_repr]
      simp only [emit, write, hr, List.cons_append, List.append_assoc]
      simp only [read, List.head?_cons, Option.any_some]
      simp only [show '-'.isDigit = false by decide, Bool.false_eq_true, ↓reduceIte]
      rw [readNumber_repr]
      rfl
  | string s =>
    have hp := String.readPrefix_write s (' ' :: suffix)
    simp only [String.write, _root_.String.toList_ofList, List.cons_append,
      List.append_assoc, List.nil_append] at hp
    simp [emit, write, String.write, read]
    exact hp

private theorem digit_not_space (c : Char) (h : c.isDigit = true) :
    c.isWhitespace = false := by
  have h1 : c ≠ ' ' := by intro hc; subst c; contradiction
  have h2 : c ≠ '\t' := by intro hc; subst c; contradiction
  have h3 : c ≠ '\r' := by intro hc; subst c; contradiction
  have h4 : c ≠ '\n' := by intro hc; subst c; contradiction
  simp [Char.isWhitespace, h1, h2, h3, h4]

private theorem repr_dropSpace (n : Nat) (suffix : List Char) :
    (n.repr.toList ++ suffix).dropWhile Char.isWhitespace = n.repr.toList ++ suffix := by
  have hn : n.repr.toList ≠ [] := by simp
  cases he : n.repr.toList with
  | nil => contradiction
  | cons c cs =>
    have hc := digit_not_space c (repr_digits n c (by simp [he]))
    simp [hc]

/-- A token's printed text begins with a non-whitespace character. -/
theorem dropSpace_emit (token : Token) (suffix : List Char) :
    (token.emit ++ suffix).dropWhile Char.isWhitespace = token.emit ++ suffix := by
  cases token with
  | leftArray | rightArray | leftObject | rightObject | comma | colon | null =>
    simp [emit, write]
  | bool b => cases b <;> simp [emit, write]
  | number n =>
    cases n with
    | ofNat n =>
      have hr : (Int.ofNat n).repr = n.repr := by simp [Int.repr_eq_ite]
      simp only [emit, write, hr, List.append_assoc]
      exact repr_dropSpace n _
    | negSucc n => simp [emit, write, Int.repr_eq_ite, _root_.String.toList_append]
  | string s => simp [emit, write, String.write]

/-- A finite lexer for untrusted certificate text. The caller chooses fuel;
byte decoding uses the actual number of input characters plus one. -/
@[expose] def lex : Nat → List Char → Option (List Token)
  | 0, _ => none
  | fuel + 1, input => do
    let rest := input.dropWhile Char.isWhitespace
    if rest.isEmpty then return []
    else do
      let (token, rest) ← read rest
      let tokens ← lex fuel rest
      return token :: tokens

/-- Emit a whitespace-separated token stream. -/
@[expose] def writeTokens (tokens : List Token) : List Char := tokens.flatMap emit

private theorem lex_space (fuel : Nat) (input : List Char) :
    lex fuel (' ' :: input) = lex fuel input := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [lex, List.dropWhile_cons_of_pos (p := Char.isWhitespace) (a := ' ') (by decide)]

theorem lex_writeTokens (tokens : List Token) (fuel : Nat) (h : tokens.length < fuel) :
    lex fuel (writeTokens tokens) = some tokens := by
  induction tokens generalizing fuel with
  | nil => cases fuel with
    | zero => omega
    | succ fuel => simp [writeTokens, lex]
  | cons token tokens ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hd := dropSpace_emit token (writeTokens tokens)
      have hr := read_emit token (writeTokens tokens)
      have hn : (token.emit ++ writeTokens tokens).isEmpty = false := by
        cases he : token.emit ++ writeTokens tokens with
        | nil => simp [he, read] at hr
        | cons c cs => rfl
      simp only [writeTokens, List.flatMap_cons]
      change lex (fuel + 1) (token.emit ++ writeTokens tokens) = _
      simp only [lex, hd, hn, hr, bind, Option.bind]
      rw [lex_space, ih fuel (by simpa using h)]
      rfl

private theorem writeTokens_length (tokens : List Token) :
    tokens.length ≤ (writeTokens tokens).length := by
  induction tokens with
  | nil => simp [writeTokens]
  | cons token tokens ih =>
    simp only [writeTokens, List.flatMap_cons, emit, List.length_append,
      List.length_cons] at *
    omega

/-- Validate UTF-8 and lex integer-only JSON certificate bytes. -/
@[expose] def readBytes (input : ByteArray) : Option (List Token) := do
  let text ← _root_.String.fromUTF8? input
  lex (text.toList.length + 1) text.toList

@[expose] def writeBytes (tokens : List Token) : ByteArray :=
  (_root_.String.ofList (writeTokens tokens)).toUTF8

/-- The actual byte lexer recovers every emitted token, including signed
integer literals and arbitrary Unicode strings. -/
theorem readBytes_write (tokens : List Token) :
    readBytes (writeBytes tokens) = some tokens := by
  unfold readBytes writeBytes
  rw [Decimal.fromUTF8_toUTF8]
  simp only [bind, Option.bind, _root_.String.toList_ofList]
  exact lex_writeTokens tokens _ (by have hn := writeTokens_length tokens; omega)

/-- info: 'Hex.SignDet.Codec.Token.readBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readBytes_write

end Token
end Hex.SignDet.Codec
