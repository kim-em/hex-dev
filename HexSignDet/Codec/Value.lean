/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Token

public section

namespace Hex.SignDet.Codec.Json

mutual
/-- Integer-only JSON data with explicit finite arrays and object fields. -/
inductive Value where
  | null
  | bool (value : Bool)
  | number (value : Int)
  | string (value : String)
  | array (values : Values)
  | object (fields : Fields)
  deriving DecidableEq, Repr
inductive Values where
  | nil
  | cons (value : Value) (rest : Values)
  deriving DecidableEq, Repr
inductive Fields where
  | nil
  | cons (key : String) (value : Value) (rest : Fields)
  deriving DecidableEq, Repr
end

mutual
@[expose] def Value.tokens : Value → List Token
  | .null => [.null]
  | .bool b => [.bool b]
  | .number n => [.number n]
  | .string s => [.string s]
  | .array xs => .leftArray :: xs.tokens ++ [.rightArray]
  | .object xs => .leftObject :: xs.tokens ++ [.rightObject]
@[expose] def Values.tokens : Values → List Token
  | .nil => []
  | .cons v .nil => v.tokens
  | .cons v rest@(.cons _ _) => v.tokens ++ .comma :: rest.tokens
@[expose] def Fields.tokens : Fields → List Token
  | .nil => []
  | .cons key v .nil => .string key :: .colon :: v.tokens
  | .cons key v rest@(.cons _ _ _) => .string key :: .colon :: v.tokens ++ .comma :: rest.tokens
end

mutual
/-- A token parser bounded by explicit fuel. Array/object tails reject trailing
commas by requiring a value after every comma. -/
@[expose] def read : Nat → List Token → Option (Value × List Token)
  | 0, _ => none
  | fuel + 1, input => match input with
    | .null :: rest => some (.null, rest)
    | .bool b :: rest => some (.bool b, rest)
    | .number n :: rest => some (.number n, rest)
    | .string s :: rest => some (.string s, rest)
    | .leftArray :: rest =>
      (readValues fuel true rest).map fun (xs, rest) => (.array xs, rest)
    | .leftObject :: rest =>
      (readFields fuel true rest).map fun (xs, rest) => (.object xs, rest)
    | _ => none
@[expose] def readValues : Nat → Bool → List Token → Option (Values × List Token)
  | 0, _, _ => none
  | fuel + 1, empty, input =>
    if empty && input.head? == some .rightArray then some (.nil, input.tail)
    else do
      let (value, rest) ← read fuel input
      match rest with
      | .rightArray :: suffix => return (.cons value .nil, suffix)
      | .comma :: suffix => do
        let (values, suffix) ← readValues fuel false suffix
        return (.cons value values, suffix)
      | _ => none
@[expose] def readFields : Nat → Bool → List Token → Option (Fields × List Token)
  | 0, _, _ => none
  | fuel + 1, empty, input =>
    if empty && input.head? == some .rightObject then some (.nil, input.tail)
    else match input with
    | .string key :: .colon :: input => do
      let (value, rest) ← read fuel input
      match rest with
      | .rightObject :: suffix => return (.cons key value .nil, suffix)
      | .comma :: suffix => do
        let (fields, suffix) ← readFields fuel false suffix
        return (.cons key value fields, suffix)
      | _ => none
    | _ => none
end

mutual
/-- A sufficient parser recursion bound, independent of integer magnitudes
and Unicode string lengths. -/
@[expose] def Value.rank : Value → Nat
  | .array xs => xs.rank + 1
  | .object xs => xs.rank + 1
  | _ => 0
@[expose] def Values.rank : Values → Nat
  | .nil => 0
  | .cons v xs => max v.rank xs.rank + 1
@[expose] def Fields.rank : Fields → Nat
  | .nil => 0
  | .cons _ v xs => max v.rank xs.rank + 1
end

private theorem read_all (fuel : Nat) :
    (∀ (value : Value) (suffix : List Token), value.rank < fuel →
      read fuel (value.tokens ++ suffix) = some (value, suffix)) ∧
    (∀ (values : Values) (suffix : List Token) (empty : Bool), values.rank < fuel →
      (values = .nil → empty = true) →
      readValues fuel empty (values.tokens ++ .rightArray :: suffix) = some (values, suffix)) ∧
    (∀ (fields : Fields) (suffix : List Token) (empty : Bool), fields.rank < fuel →
      (fields = .nil → empty = true) →
      readFields fuel empty (fields.tokens ++ .rightObject :: suffix) = some (fields, suffix)) := by
  induction fuel with
  | zero =>
    constructor
    · intro value suffix h; omega
    constructor
    · intro values suffix empty h he; omega
    · intro fields suffix empty h he; omega
  | succ fuel ih =>
    obtain ⟨iv, ia, io⟩ := ih
    constructor
    · intro value suffix h
      cases value with
      | null | bool b | number n | string s => simp [Value.tokens, read]
      | array xs =>
        have hx := ia xs suffix true (by simp only [Value.rank] at h; omega) (by simp)
        simp only [Value.tokens, List.cons_append, List.append_assoc, List.nil_append,
          read, hx, Option.map_some]
      | object xs =>
        have hx := io xs suffix true (by simp only [Value.rank] at h; omega) (by simp)
        simp only [Value.tokens, List.cons_append, List.append_assoc, List.nil_append,
          read, hx, Option.map_some]
    constructor
    · intro values suffix empty h he
      cases values with
      | nil => simp [Values.tokens, readValues, he rfl]
      | cons value values =>
        have hv : value.rank < fuel := by simp only [Values.rank] at h; omega
        have hs : values.rank < fuel := by simp only [Values.rank] at h; omega
        cases values with
        | nil =>
          have hr := iv value (.rightArray :: suffix) hv
          have hn : ((value.tokens ++ .rightArray :: suffix).head? == some .rightArray) = false := by
            cases value <;> simp [Value.tokens]
          rw [Values.tokens]
          simp only [readValues, hn, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          rw [hr]
          rfl
        | cons v vs =>
          have hr := iv value (.comma :: (Values.cons v vs).tokens ++ .rightArray :: suffix) hv
          simp only [List.cons_append] at hr
          have ht := ia (.cons v vs) suffix false hs (by simp)
          have hn : ((value.tokens ++ .comma :: ((Values.cons v vs).tokens ++ .rightArray :: suffix)).head?
              == some .rightArray) = false := by
            cases value <;> simp [Value.tokens]
          rw [Values.tokens]
          simp only [List.cons_append, List.append_assoc, readValues, hn, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte]
          rw [hr]
          simp only [bind, Option.bind]
          rw [ht]
          rfl
    · intro fields suffix empty h he
      cases fields with
      | nil => simp [Fields.tokens, readFields, he rfl]
      | cons key value fields =>
        have hv : value.rank < fuel := by simp only [Fields.rank] at h; omega
        have hs : fields.rank < fuel := by simp only [Fields.rank] at h; omega
        cases fields with
        | nil =>
          have hr := iv value (.rightObject :: suffix) hv
          simp [Fields.tokens, readFields, hr, bind, Option.bind]
        | cons key' v vs =>
          have hr := iv value (.comma :: (Fields.cons key' v vs).tokens ++ .rightObject :: suffix) hv
          have ht := io (.cons key' v vs) suffix false hs (by simp)
          simp only [List.cons_append] at hr
          rw [Fields.tokens]
          simp only [List.cons_append, List.append_assoc, readFields, List.head?_cons]
          simp only [show (some (Token.string key) == some Token.rightObject) = false by simp,
            Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          rw [hr]
          simp only [bind, Option.bind]
          rw [ht]
          rfl

/-- Parsing emitted values retains the entire arbitrary suffix. -/
theorem read_tokens (value : Value) (suffix : List Token) (fuel : Nat)
    (h : value.rank < fuel) : read fuel (value.tokens ++ suffix) = some (value, suffix) :=
  (read_all fuel).1 value suffix h

mutual
private theorem Value.rank_lt (value : Value) : value.rank < value.tokens.length := by
  cases value with
  | null | bool b | number n | string s => simp [Value.rank, Value.tokens]
  | array xs =>
    have hx := Values.rank_le xs
    simp only [Value.rank, Value.tokens, List.length_cons, List.length_append]
    omega
  | object xs =>
    have hx := Fields.rank_le xs
    simp only [Value.rank, Value.tokens, List.length_cons, List.length_append]
    omega
private theorem Values.rank_le (values : Values) : values.rank ≤ values.tokens.length := by
  cases values with
  | nil => simp [Values.rank, Values.tokens]
  | cons value values =>
    have hv := Value.rank_lt value
    have hs := Values.rank_le values
    cases values with
    | nil => simp [Values.rank, Values.tokens] at *; omega
    | cons v vs =>
      simp only [Values.rank, Values.tokens, List.length_cons, List.length_append] at *
      omega
private theorem Fields.rank_le (fields : Fields) : fields.rank ≤ fields.tokens.length := by
  cases fields with
  | nil => simp [Fields.rank, Fields.tokens]
  | cons key value fields =>
    have hv := Value.rank_lt value
    have hs := Fields.rank_le fields
    cases fields with
    | nil => simp [Fields.rank, Fields.tokens] at *; omega
    | cons key' v vs =>
      simp only [Fields.rank, Fields.tokens, List.length_cons, List.length_append] at *
      omega
end

/-- Print the actual UTF-8 JSON bytes of a finite value. -/
@[expose] def Value.writeBytes (value : Value) : ByteArray := Token.writeBytes value.tokens

/-- Validate UTF-8, lex integers/strings, parse the JSON structure, and require
that no trailing token remains. Fuel comes from the actual finite token count. -/
@[expose] def readBytes (input : ByteArray) : Option Value := do
  let tokens ← Token.readBytes input
  let (value, rest) ← read (tokens.length + 1) tokens
  if rest.isEmpty then return value else none

/-- Every finite integer-only JSON value survives its actual printed UTF-8
bytes. This includes arbitrary array/object nesting, Unicode and integer sizes;
there is no parser-success premise or fixed collection of literal fixtures. -/
theorem readBytes_write (value : Value) : readBytes value.writeBytes = some value := by
  unfold readBytes Value.writeBytes
  rw [Token.readBytes_write]
  simp only [bind, Option.bind]
  have hp := read_tokens value [] (value.tokens.length + 1)
    (by have hn := value.rank_lt; omega)
  simp only [List.append_nil] at hp
  rw [hp]
  rfl

/-- info: 'Hex.SignDet.Codec.Json.readBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readBytes_write

end Hex.SignDet.Codec.Json
