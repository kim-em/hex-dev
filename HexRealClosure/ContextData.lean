/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Json

public section

namespace Hex.RealClosure.Tower

/-- Context identity uses the same literal JSON tree as certificates. Integer
values have one representation; equality retains every literal field. -/
abbrev Literal := Hex.SignDet.Codec.Json.Value
abbrev Literals := Hex.SignDet.Codec.Json.Values

namespace Literals

@[expose] def toList (xs : Literals) : List Literal := Hex.SignDet.Codec.Json.Values.toList xs
@[expose] def ofList (xs : List Literal) : Literals := Hex.SignDet.Codec.Json.Values.ofList xs
@[expose] def toArray (xs : Literals) : Array Literal := Hex.SignDet.Codec.Json.Values.toArray xs

@[simp] theorem ofList_toList (xs : Literals) : ofList xs.toList = xs := by
  exact Hex.SignDet.Codec.Json.Values.ofList_toList xs

@[simp] theorem toList_ofList (xs : List Literal) : (ofList xs).toList = xs := by
  exact Hex.SignDet.Codec.Json.Values.toList_ofList xs

@[simp] theorem toArray_eq (xs : Literals) : xs.toArray = xs.toList.toArray :=
  Hex.SignDet.Codec.Json.Values.toArray_eq xs

end Literals

/-- Literal data is already in the certificate JSON type. -/
@[expose] def Literal.toJson (literal : Literal) : Hex.SignDet.Codec.Json := literal

/-- Conversion is the identity and therefore preserves every JSON constructor. -/
@[expose] def Literal.ofJson (literal : Hex.SignDet.Codec.Json) : Option Literal := some literal

@[simp] theorem Literal.ofJson_toJson (literal : Literal) :
    Literal.ofJson literal.toJson = some literal := rfl

theorem Literal.toJson_ofJson (j : Hex.SignDet.Codec.Json) (x : Literal)
    (h : Literal.ofJson j = some x) : x.toJson = j := by
  exact (Option.some.inj h).symm

end Hex.RealClosure.Tower
