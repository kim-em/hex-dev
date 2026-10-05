/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Laws

public section

namespace Hex.SignDet.Codec

/-- Bounds apply to untrusted certificate decoding, not coefficient arithmetic
or mathematical root-domain validity. Callers can choose larger limits. -/
structure Limits where
  bytes : Nat := 16777216
  depth : Nat := 128
  digits : Nat := 4096

/-- Direct byte iteration agrees with array iteration. Compiled checking uses
`ByteArray.forInUnsafe` and does not box a copy of the byte buffer. -/
theorem forIn_data {β : Type v} {m : Type v → Type w} [Monad m]
    (input : ByteArray) (initial : β) (step : UInt8 → β → m (ForInStep β)) :
    forIn input initial step = forIn input.data initial step := by
  change ByteArray.forIn input initial step = Array.forIn' input.data initial (fun a _ b => step a b)
  unfold ByteArray.forIn Array.forIn'
  have loop (n : Nat) (bound : n ≤ input.size) (state : β) :
      ByteArray.forIn.loop input step n bound state =
        Array.forIn'.loop input.data (fun a _ b => step a b) n bound state := by
    induction n generalizing state with
    | zero => rfl
    | succ n ih =>
      simp only [ByteArray.forIn.loop, Array.forIn'.loop]
      congr 1
      funext result
      cases result with
      | done state => rfl
      | yield state => exact ih _ state
  exact loop _ _ _

/-- Bound nesting and integer-token size before JSON parsing. Numeric tokens
are integers only: exponent/fraction syntax is not part of this wire format.
Escapes and bracket characters inside strings do not affect nesting. The JSON
parser subsequently validates syntax and Unicode escapes. -/
def checkBytes (limits : Limits) (input : ByteArray) : Except String Unit := do
  if input.size > limits.bytes then throw "certificate byte limit exceeded"
  let mut quoted := false
  let mut escaped := false
  let mut depth := 0
  let mut number := false
  let mut digits := 0
  for byte in input do
    let c := byte.toNat
    if quoted then
      if escaped then escaped := false
      else if c == 92 then escaped := true
      else if c == 34 then quoted := false
      continue
    if number then
      if 48 ≤ c && c ≤ 57 then
        digits := digits + 1
        if digits > limits.digits then throw "integer token limit exceeded"
        continue
      if c == 46 || c == 69 || c == 101 then throw "noninteger numeric token"
      number := false
    if c == 34 then quoted := true
    else if c == 91 || c == 123 then
      depth := depth + 1
      if depth > limits.depth then throw "certificate nesting limit exceeded"
    else if c == 93 || c == 125 then
      if depth == 0 then throw "unmatched closing delimiter"
      depth := depth - 1
    else if c == 45 then
      number := true
      digits := 0
    else if 48 ≤ c && c ≤ 57 then
      number := true
      digits := 1
      if digits > limits.digits then throw "integer token limit exceeded"
  if quoted || depth != 0 then throw "truncated certificate syntax"

/-- UTF-8 and finite lexical limits are checked before the shared JSON parser
can allocate numeric values or recursively construct nested arrays. -/
def parse (limits : Limits) (input : ByteArray) : Except String Json := do
  checkBytes limits input
  let some value := Json.readBytes input | throw "invalid certificate JSON or UTF-8"
  return value

/-- Decode two byte records before invoking their existing structured reader.
This adapter also applies to readers that reconstruct a coefficient context. -/
@[expose] def decodePair {α : Type u} (reader : Json → Json → Except String α)
    (subject evidence : ByteArray) (limits : Limits := {}) : Except String α :=
  match parse limits subject with
  | .error message => .error message
  | .ok raw => match parse limits evidence with
    | .error message => .error message
    | .ok graph => reader raw graph

/-- The byte parser recovers the exact integer-only JSON value. The premise
is the caller's lexical policy (including syntax prechecks), not parser
success. This theorem does not characterize policy acceptance by value metrics. -/
theorem parse_write (value : Json) (limits : Limits)
    (bound : checkBytes limits value.writeBytes = .ok ()) :
    parse limits value.writeBytes = .ok value := by
  simp [parse, bound, Json.readBytes_write, bind, Except.bind, pure, Except.pure]

/-- Substitute both parsed records before applying their structured reader. -/
theorem decodePair_ok {α : Type u} (reader : Json → Json → Except String α)
    (subject evidence : ByteArray) (limits : Limits) (raw graph : Json)
    (subjectParsed : parse limits subject = .ok raw)
    (evidenceParsed : parse limits evidence = .ok graph) :
    decodePair reader subject evidence limits = reader raw graph := by
  simp only [decodePair, subjectParsed, evidenceParsed]

/-- An invalid first record rejects without evaluating the structured reader. -/
theorem decodePair_error {α : Type u} (reader : Json → Json → Except String α)
    (subject evidence : ByteArray) (limits : Limits) (message : String)
    (rejected : parse limits subject = .error message) :
    decodePair reader subject evidence limits = .error message := by
  simp only [decodePair, rejected]

/-- Byte decoding preserves the structured reader's full accepted result or
error. The assumptions check lexical limits, not parsing or reader success. -/
theorem decodePair_write {α : Type u} (reader : Json → Json → Except String α)
    (subject evidence : Json) (limits : Limits)
    (subjectBound : checkBytes limits subject.writeBytes = .ok ())
    (evidenceBound : checkBytes limits evidence.writeBytes = .ok ()) :
    decodePair reader subject.writeBytes evidence.writeBytes limits = reader subject evidence := by
  unfold decodePair
  rw [parse_write subject limits subjectBound, parse_write evidence limits evidenceBound]

end Hex.SignDet.Codec

namespace Hex.SignDet

/-- Serialize a coefficient or full immutable context in the shared byte format. -/
def ValueCodec.encodeBytes (codec : ValueCodec α) (value : α) : ByteArray :=
  (codec.encode value).writeBytes

/-- The shared lexical policy precedes parsing and literal value decoding. -/
def ValueCodec.decodeBytes (codec : ValueCodec α) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String α := do
  codec.decode (← Codec.parse limits input)

/-- A roundtrip for one covered value survives the actual shared byte
printer/parser under the caller's existing lexical resource policy. -/
theorem ValueCodec.decode_encode_of (codec : ValueCodec α) (value : α)
    (law : codec.decode (codec.encode value) = .ok value) (limits : Codec.Limits)
    (bound : Codec.checkBytes limits (codec.encodeBytes value) = .ok ()) :
    codec.decodeBytes (codec.encodeBytes value) limits = .ok value := by
  unfold ValueCodec.decodeBytes ValueCodec.encodeBytes at *
  rw [Codec.parse_write _ _ bound]
  simp only [bind, Except.bind]
  exact law

/-- Every lawful value codec survives the actual shared printer/parser, under
its caller's lexical resource policy. The JSON value stores integers directly,
so this law needs no premise about normalizing distinct numeric representations.
The parser may accept several byte spellings of that value. -/
theorem ValueCodec.decode_encode (codec : ValueCodec α) (law : codec.Lawful) (value : α)
    (limits : Codec.Limits)
    (bound : Codec.checkBytes limits (codec.encodeBytes value) = .ok ()) :
    codec.decodeBytes (codec.encodeBytes value) limits = .ok value := by
  exact codec.decode_encode_of value (law value) limits bound

/-- info: 'Hex.SignDet.ValueCodec.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ValueCodec.decode_encode

end Hex.SignDet
