/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Dag
public import Lean.Data.Json.Parser
public import Lean.Data.Json.FromToJson.Basic

public section

namespace Hex.SignDet
open Lean

/-- Literal coefficient or full-context encoding. Decoding supplies data only;
independent graph replay still checks all mathematical and context bindings.
A codec used for roundtrips must preserve the entire value, not a context hash. -/
structure ValueCodec (α : Type) where
  encode : α → Json
  decode : Json → Except String α

namespace ValueCodec

/-- Exact natural-number literals. -/
def nat : ValueCodec Nat := ⟨toJson, fromJson?⟩

/-- Canonical rational literals `[numerator, denominator]`, with positive
coprime denominator. Noncanonical pairs are rejected rather than normalized. -/
def rat : ValueCodec Rat where
  encode q := Json.arr #[toJson q.num, toJson q.den]
  decode j := do
    let a ← j.getArr?
    if a.size != 2 then throw "expected a rational pair"
    let num ← fromJson? (α := Int) a[0]!
    let den ← fromJson? (α := Nat) a[1]!
    if den == 0 then throw "zero rational denominator"
    let q := mkRat num den
    if q.num == num && q.den == den then return q
    else throw "noncanonical rational pair"

end ValueCodec

namespace Codec

/-- Require an exact array length before reading any fixed-position fields. -/
def tuple (n : Nat) (j : Json) : Except String (Vector Json n) := do
  let a ← j.getArr?
  if h : a.size = n then return ⟨a, h⟩
  else throw "wrong field count"

def array (encode : α → Json) (a : Array α) : Json := .arr (a.map encode)
def list (encode : α → Json) (a : List α) : Json := array encode a.toArray

def readArray (read : Json → Except String α) (j : Json) : Except String (Array α) := do
  (← j.getArr?).mapM read

def readList (read : Json → Except String α) (j : Json) : Except String (List α) :=
  Array.toList <$> readArray read j

/-- Dimensions come from the already decoded enclosing record. The supplied
array length is checked before decoding entries; no claimed dimension drives
an allocation or a loop over missing input. -/
def vector (n : Nat) (read : Json → Except String α) (j : Json) : Except String (Vector α n) := do
  let a ← tuple n j
  let values ← a.toArray.mapM read
  if h : values.size = n then return ⟨values, h⟩
  else throw "wrong decoded vector length"

def matrix (n m : Nat) (j : Json) : Except String (Matrix Int n m) :=
  Matrix.ofRows <$> vector n (vector m fromJson?) j

def encodeMatrix (a : Matrix Int n m) : Json :=
  array (array toJson) (a.rows.toArray.map Vector.toArray)

def index (n : Nat) (j : Json) : Except String (Fin n) := do
  let i ← fromJson? (α := Nat) j
  if h : i < n then return ⟨i, h⟩ else throw "index out of range"

def option (encode : α → Json) : Option α → Json
  | none => .arr #[]
  | some a => .arr #[encode a]

def readOption (read : Json → Except String α) (j : Json) : Except String (Option α) := do
  let a ← j.getArr?
  match a.toList with
  | [] => return none
  | [v] => some <$> read v
  | _ => throw "wrong optional field count"

variable {E : Type} [Zero E] [DecidableEq E]

/-- Coefficients are in increasing exponent order. No polynomial operation
is performed by the encoder. -/
def poly (value : ValueCodec E) (p : DensePoly E) : Json := array value.encode p.toArray

/-- Reject trailing literal zeros rather than silently changing a serialized
polynomial's coefficient vector. Coefficient equations are checked by replay. -/
def readPoly (value : ValueCodec E) (j : Json) : Except String (DensePoly E) := do
  let coefficients ← readArray value.decode j
  let p := DensePoly.ofCoeffs coefficients
  if p.toArray == coefficients then return p else throw "noncanonical polynomial vector"

def endpoint (value : ValueCodec E) : Endpoint E → Json
  | .negInf => .arr #[toJson (0 : Nat)]
  | .finite a => .arr #[toJson (1 : Nat), value.encode a]
  | .posInf => .arr #[toJson (2 : Nat)]

def readEndpoint (value : ValueCodec E) (j : Json) : Except String (Endpoint E) := do
  let a ← j.getArr?
  match a.toList with
  | [tag] =>
    match ← fromJson? (α := Nat) tag with
    | 0 => return .negInf
    | 2 => return .posInf
    | _ => throw "invalid infinite endpoint"
  | [tag, v] =>
    if (← fromJson? (α := Nat) tag) != 1 then throw "invalid finite endpoint"
    .finite <$> value.decode v
  | _ => throw "wrong endpoint field count"

end Codec
end Hex.SignDet
