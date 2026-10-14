/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Value

public section

namespace Hex.SignDet.Codec

/-- Certificate JSON has integer numbers and literal ordered object fields. -/
abbrev Json := Hex.SignDet.Codec.Json.Value

namespace Json

instance : Inhabited Value := ⟨.null⟩

/-- Construct the literal recursive JSON array in list order. -/
@[expose] def Values.ofList (xs : List Value) : Values := xs.foldr Values.cons .nil

/-- Return every literal array element in order. -/
@[expose] def Values.toList : Values → List Value
  | .nil => []
  | .cons value rest => value :: rest.toList

/-- Append all literal elements to the supplied array using a width loop. -/
@[expose] def Values.pushArray : Values → Array Value → Array Value
  | .nil, result => result
  | .cons value rest, result => rest.pushArray (result.push value)

/-- Convert the entire literal JSON array using the width loop. -/
@[expose] def Values.toArray (values : Values) : Array Value := values.pushArray #[]

/-- Converting a list to literal JSON array data and back preserves order. -/
@[simp] theorem Values.toList_ofList (xs : List Value) : (ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons value xs ih =>
    change value :: (ofList xs).toList = value :: xs
    rw [ih]

/-- Converting literal JSON array data through a list preserves every element. -/
@[simp] theorem Values.ofList_toList (xs : Values) : ofList xs.toList = xs := by
  cases xs with
  | nil => rfl
  | cons value xs =>
    change Values.cons value (ofList xs.toList) = Values.cons value xs
    rw [Values.ofList_toList xs]

/-- The width loop appends precisely the reference list, in order. -/
private theorem Values.pushArray_eq (xs : Values) (result : Array Value) :
    xs.pushArray result = result ++ xs.toList.toArray := by
  cases xs with
  | nil => simp [pushArray, toList]
  | cons value xs =>
    rw [pushArray, Values.pushArray_eq xs]
    simp only [toList]
    conv => rhs; rw [List.toArray_cons]
    exact Array.append_singleton_assoc.symm

/-- The native array conversion agrees with the complete reference list. -/
@[simp] theorem Values.toArray_eq (xs : Values) : xs.toArray = xs.toList.toArray := by
  simp [toArray, pushArray_eq]

/-- Convert literal JSON array data to a list through the width loop. -/
@[expose] def Values.toListLoop (xs : Values) : List Value := xs.toArray.toList

/-- Compiled list conversion uses the width loop while preserving the
recursive reference definition used by literal roundtrip proofs. -/
@[csimp] theorem Values.toList_impl : Values.toList = Values.toListLoop := by
  funext xs
  simp only [Values.toListLoop, Values.toArray_eq, List.toList_toArray]

/-- Array construction preserves every element in order. -/
@[expose] def arr (xs : Array Json) : Json := .array (Values.ofList xs.toList)

/-- Accept only array values and return every ordered element. -/
@[expose] def Value.getArr? : Json → Except String (Array Json)
  | .array xs => .ok xs.toArray
  | _ => .error "expected an array"

/-- Accept only literal integer number values. -/
@[expose] def Value.getInt? : Json → Except String Int
  | .number n => .ok n
  | _ => .error "expected an integer"

/-- Accept only nonnegative integer number values, without coercing other JSON kinds. -/
@[expose] def Value.getNat? : Json → Except String Nat
  | .number (.ofNat n) => .ok n
  | _ => .error "expected a natural number"

/-- Accept only literal Boolean values. -/
@[expose] def Value.getBool? : Json → Except String Bool
  | .bool b => .ok b
  | _ => .error "expected a Boolean"

/-- Accept only literal string values. -/
@[expose] def Value.getStr? : Json → Except String String
  | .string s => .ok s
  | _ => .error "expected a string"

/-- Reading an array constructed from literal elements returns exactly those elements. -/
@[simp] theorem getArr_arr (xs : Array Json) : (arr xs).getArr? = .ok xs := by
  simp [arr, Value.getArr?]

/-- Literal integer-only JSON encoding for the supplied type. -/
class To (α : Type) where
  /-- Encode the entire literal value. -/
  encode : α → Json

/-- Partial literal JSON decoding for the supplied type. -/
class From (α : Type) where
  /-- Decode a literal value or report refusal. -/
  decode : Json → Except String α

/-- Use the supplied type-specific literal JSON encoder. -/
@[expose] def of [To α] (value : α) : Json := To.encode value
/-- Use the supplied type-specific partial JSON decoder. -/
@[expose] def decode [From α] (value : Json) : Except String α := From.decode value

instance : To Nat := ⟨fun n => .number (.ofNat n)⟩
instance : From Nat := ⟨Value.getNat?⟩
instance : To Int := ⟨Value.number⟩
instance : From Int := ⟨Value.getInt?⟩
instance : To Bool := ⟨Value.bool⟩
instance : From Bool := ⟨Value.getBool?⟩
instance : To String := ⟨Value.string⟩
instance : From String := ⟨Value.getStr?⟩
instance [To α] : To (Array α) := ⟨fun xs => arr (xs.map of)⟩
instance [From α] : From (Array α) := ⟨fun j => do (← j.getArr?).mapM decode⟩
instance [To α] : To (List α) := ⟨fun xs => of xs.toArray⟩
instance [From α] : From (List α) := ⟨fun j => Array.toList <$> decode (α := Array α) j⟩

/-- The array instance preserves element order and uses the actual element encoder. -/
theorem of_array [To α] (xs : Array α) : of xs = arr (xs.map of) := rfl
/-- The list instance preserves element order and uses the actual element encoder. -/
theorem of_list [To α] (xs : List α) : of xs = arr (xs.toArray.map of) := rfl

/-- Natural-number literals survive their actual scalar encoding and decoding. -/
@[simp] theorem read_of_nat (n : Nat) : decode (of n) = .ok n := rfl
/-- Integer literals survive their actual scalar encoding and decoding. -/
@[simp] theorem read_of_int (n : Int) : decode (of n) = .ok n := rfl
/-- Boolean literals survive their actual scalar encoding and decoding. -/
@[simp] theorem read_of_bool (b : Bool) : decode (of b) = .ok b := rfl
/-- String literals survive their actual scalar encoding and decoding. -/
@[simp] theorem read_of_string (s : String) : decode (of s) = .ok s := rfl

/-- info: 'Hex.SignDet.Codec.Json.getArr_arr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms getArr_arr

end Json
end Hex.SignDet.Codec
