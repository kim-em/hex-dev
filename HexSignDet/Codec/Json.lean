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

@[expose] def Values.ofList (xs : List Value) : Values := xs.foldr Values.cons .nil

@[expose] def Values.toList : Values → List Value
  | .nil => []
  | .cons value rest => value :: rest.toList

@[expose] def Values.pushArray : Values → Array Value → Array Value
  | .nil, result => result
  | .cons value rest, result => rest.pushArray (result.push value)

@[expose] def Values.toArray (values : Values) : Array Value := values.pushArray #[]

@[simp] theorem Values.toList_ofList (xs : List Value) : (ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons value xs ih =>
    change value :: (ofList xs).toList = value :: xs
    rw [ih]

@[simp] theorem Values.ofList_toList (xs : Values) : ofList xs.toList = xs := by
  cases xs with
  | nil => rfl
  | cons value xs =>
    change Values.cons value (ofList xs.toList) = Values.cons value xs
    rw [Values.ofList_toList xs]

private theorem Values.pushArray_eq (xs : Values) (result : Array Value) :
    xs.pushArray result = result ++ xs.toList.toArray := by
  cases xs with
  | nil => simp [pushArray, toList]
  | cons value xs =>
    rw [pushArray, Values.pushArray_eq xs]
    simp only [toList]
    conv => rhs; rw [List.toArray_cons]
    exact Array.append_singleton_assoc.symm

@[simp] theorem Values.toArray_eq (xs : Values) : xs.toArray = xs.toList.toArray := by
  simp [toArray, pushArray_eq]

/-- Array construction preserves every element in order. -/
@[expose] def arr (xs : Array Json) : Json := .array (Values.ofList xs.toList)

@[expose] def Value.getArr? : Json → Except String (Array Json)
  | .array xs => .ok xs.toArray
  | _ => .error "expected an array"

@[expose] def Value.getInt? : Json → Except String Int
  | .number n => .ok n
  | _ => .error "expected an integer"

@[expose] def Value.getNat? : Json → Except String Nat
  | .number (.ofNat n) => .ok n
  | _ => .error "expected a natural number"

@[expose] def Value.getBool? : Json → Except String Bool
  | .bool b => .ok b
  | _ => .error "expected a Boolean"

@[expose] def Value.getStr? : Json → Except String String
  | .string s => .ok s
  | _ => .error "expected a string"

@[simp] theorem getArr_arr (xs : Array Json) : (arr xs).getArr? = .ok xs := by
  simp [arr, Value.getArr?]

class To (α : Type) where
  encode : α → Json

class From (α : Type) where
  decode : Json → Except String α

@[expose] def of [To α] (value : α) : Json := To.encode value
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

theorem of_array [To α] (xs : Array α) : of xs = arr (xs.map of) := rfl
theorem of_list [To α] (xs : List α) : of xs = arr (xs.toArray.map of) := rfl

@[simp] theorem read_of_nat (n : Nat) : decode (of n) = .ok n := rfl
@[simp] theorem read_of_int (n : Int) : decode (of n) = .ok n := rfl
@[simp] theorem read_of_bool (b : Bool) : decode (of b) = .ok b := rfl
@[simp] theorem read_of_string (s : String) : decode (of s) = .ok s := rfl

/-- info: 'Hex.SignDet.Codec.Json.getArr_arr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms getArr_arr

end Json
end Hex.SignDet.Codec
