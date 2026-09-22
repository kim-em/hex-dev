/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Basic

public section

namespace Hex.SignDet.Codec

/-- Bounds apply to untrusted certificate decoding, not coefficient arithmetic
or mathematical root-domain validity. Callers can choose larger limits. -/
structure Limits where
  bytes : Nat := 16777216
  depth : Nat := 128
  digits : Nat := 4096

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
  for i in [:input.size] do
    let c := input[i]!.toNat
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
def parse (limits : Limits) (input : ByteArray) : Except String Lean.Json := do
  checkBytes limits input
  let some text := String.fromUTF8? input | throw "invalid certificate UTF-8"
  Lean.Json.parse text

end Hex.SignDet.Codec
