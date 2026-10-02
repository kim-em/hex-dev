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
  deriving DecidableEq, Repr, Hashable
inductive Values where
  | nil
  | cons (value : Value) (rest : Values)
  deriving DecidableEq, Repr, Hashable
inductive Fields where
  | nil
  | cons (key : String) (value : Value) (rest : Fields)
  deriving DecidableEq, Repr, Hashable
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
/-- Produce tokens with tail recursion across array/object width. -/
@[expose] def Value.tokensLoop : Value → List Token
  | .null => [.null]
  | .bool b => [.bool b]
  | .number n => [.number n]
  | .string s => [.string s]
  | .array xs => .leftArray :: Values.tokensLoop xs [] ++ [.rightArray]
  | .object xs => .leftObject :: Fields.tokensLoop xs [] ++ [.rightObject]
@[expose] def Values.tokensLoop : Values → List Token → List Token
  | .nil, reversed => reversed.reverse
  | .cons v .nil, reversed => (v.tokensLoop.reverseAux reversed).reverse
  | .cons v rest@(.cons _ _), reversed =>
    Values.tokensLoop rest (.comma :: v.tokensLoop.reverseAux reversed)
@[expose] def Fields.tokensLoop : Fields → List Token → List Token
  | .nil, reversed => reversed.reverse
  | .cons key v .nil, reversed =>
    (v.tokensLoop.reverseAux (.colon :: .string key :: reversed)).reverse
  | .cons key v rest@(.cons _ _ _), reversed =>
    Fields.tokensLoop rest (.comma :: v.tokensLoop.reverseAux (.colon :: .string key :: reversed))
end

mutual
private theorem Value.tokensLoop_eq (value : Value) : value.tokensLoop = value.tokens := by
  cases value with
  | null => simp [Value.tokensLoop, Value.tokens]
  | bool b => simp [Value.tokensLoop, Value.tokens]
  | number n => simp [Value.tokensLoop, Value.tokens]
  | string s => simp [Value.tokensLoop, Value.tokens]
  | array xs => simp [Value.tokensLoop, Value.tokens, Values.tokensLoop_eq]
  | object xs => simp [Value.tokensLoop, Value.tokens, Fields.tokensLoop_eq]
private theorem Values.tokensLoop_eq (values : Values) (reversed : List Token) :
    Values.tokensLoop values reversed = reversed.reverse ++ values.tokens := by
  cases values with
  | nil => simp [Values.tokensLoop, Values.tokens]
  | cons v rest =>
    have hv := v.tokensLoop_eq
    cases rest with
    | nil => simp [Values.tokensLoop, Values.tokens, hv, List.reverseAux_eq]
    | cons w ws =>
      rw [Values.tokensLoop, Values.tokensLoop_eq]
      simp [Values.tokens, hv, List.reverseAux_eq, List.append_assoc]
private theorem Fields.tokensLoop_eq (fields : Fields) (reversed : List Token) :
    Fields.tokensLoop fields reversed = reversed.reverse ++ fields.tokens := by
  cases fields with
  | nil => simp [Fields.tokensLoop, Fields.tokens]
  | cons key v rest =>
    have hv := v.tokensLoop_eq
    cases rest with
    | nil => simp [Fields.tokensLoop, Fields.tokens, hv, List.reverseAux_eq, List.append_assoc]
    | cons key' w ws =>
      rw [Fields.tokensLoop, Fields.tokensLoop_eq]
      simp [Fields.tokens, hv, List.reverseAux_eq, List.append_assoc]
end

mutual
/-- Finite reference parser for proofs. Array/object tails reject trailing
commas by requiring a value after every comma. Native parsing uses `readLoop`;
this reference retains one stack frame per element or field. -/
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

/-- Restore accumulated array elements in their literal order. -/
@[expose] def Values.prepend (reversed : List Value) (tail : Values) : Values :=
  reversed.foldl (fun tail value => .cons value tail) tail

/-- Restore accumulated object fields, retaining duplicate keys and their order. -/
@[expose] def Fields.prepend (reversed : List (String × Value)) (tail : Fields) : Fields :=
  reversed.foldl (fun tail (key, value) => .cons key value tail) tail

mutual
/-- The native parser uses tail recursion for the width of arrays and objects;
recursive calls through `readLoop` follow nesting only. -/
@[expose] def readLoop : Nat → List Token → Option (Value × List Token)
  | 0, _ => none
  | fuel + 1, input => match input with
    | .null :: rest => some (.null, rest)
    | .bool b :: rest => some (.bool b, rest)
    | .number n :: rest => some (.number n, rest)
    | .string s :: rest => some (.string s, rest)
    | .leftArray :: rest =>
      (readValuesLoop fuel true rest []).map fun (xs, rest) => (.array xs, rest)
    | .leftObject :: rest =>
      (readFieldsLoop fuel true rest []).map fun (xs, rest) => (.object xs, rest)
    | _ => none
@[expose] def readValuesLoop : Nat → Bool → List Token → List Value → Option (Values × List Token)
  | 0, _, _, _ => none
  | fuel + 1, empty, input, reversed =>
    if empty && input.head? == some .rightArray then some (Values.prepend reversed .nil, input.tail)
    else do
      let (value, rest) ← readLoop fuel input
      match rest with
      | .rightArray :: suffix => return (Values.prepend (value :: reversed) .nil, suffix)
      | .comma :: suffix => readValuesLoop fuel false suffix (value :: reversed)
      | _ => none
@[expose] def readFieldsLoop : Nat → Bool → List Token → List (String × Value) →
    Option (Fields × List Token)
  | 0, _, _, _ => none
  | fuel + 1, empty, input, reversed =>
    if empty && input.head? == some .rightObject then some (Fields.prepend reversed .nil, input.tail)
    else match input with
    | .string key :: .colon :: input => do
      let (value, rest) ← readLoop fuel input
      match rest with
      | .rightObject :: suffix => return (Fields.prepend ((key, value) :: reversed) .nil, suffix)
      | .comma :: suffix => readFieldsLoop fuel false suffix ((key, value) :: reversed)
      | _ => none
    | _ => none
end

private theorem readLoop_all (fuel : Nat) :
    (∀ input, readLoop fuel input = read fuel input) ∧
    (∀ empty input reversed, readValuesLoop fuel empty input reversed =
      (readValues fuel empty input).map (fun (xs, rest) => (Values.prepend reversed xs, rest))) ∧
    (∀ empty input reversed, readFieldsLoop fuel empty input reversed =
      (readFields fuel empty input).map (fun (xs, rest) => (Fields.prepend reversed xs, rest))) := by
  induction fuel with
  | zero => exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | succ fuel ih =>
    obtain ⟨iv, ia, io⟩ := ih
    constructor
    · intro input
      cases input with
      | nil => rfl
      | cons token rest =>
        cases token <;> simp [readLoop, read, ia, io, Values.prepend, Fields.prepend]
    constructor
    · intro empty input reversed
      simp only [readValuesLoop, readValues, iv]
      split
      · rfl
      · cases read fuel input with
        | none => rfl
        | some pair =>
          obtain ⟨value, rest⟩ := pair
          simp only [bind, Option.bind]
          cases rest with
          | nil => rfl
          | cons token suffix =>
            cases token <;> simp [ia, Values.prepend]
            cases readValues fuel false suffix <;> rfl
    · intro empty input reversed
      simp only [readFieldsLoop, readFields]
      split
      · rfl
      · cases input with
        | nil => rfl
        | cons token input =>
          cases token <;> try rfl
          rename_i key
          cases input with
          | nil => rfl
          | cons token input =>
            cases token <;> try rfl
            simp only [iv]
            cases read fuel input with
            | none => rfl
            | some pair =>
              obtain ⟨value, rest⟩ := pair
              simp only [bind, Option.bind]
              cases rest with
              | nil => rfl
              | cons token suffix =>
                cases token <;> simp [io, Fields.prepend]
                cases readFields fuel false suffix <;> rfl

/-- Native parsing agrees with the finite reference for every token sequence,
including malformed arrays/objects and insufficient fuel. -/
theorem readLoop_spec (fuel : Nat) (input : List Token) :
    readLoop fuel input = read fuel input := (readLoop_all fuel).1 input

/-- Native token production preserves the exact reference token list. -/
theorem Value.tokensLoop_spec (value : Value) : value.tokensLoop = value.tokens :=
  value.tokensLoop_eq

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
@[expose] def Value.writeBytes (value : Value) : ByteArray := Token.writeBytes value.tokensLoop

/-- Validate UTF-8, lex integers/strings, parse the JSON structure, and require
that no trailing token remains. Fuel comes from the actual finite token count.
This low-level operation has no byte/depth/digit guard. Certificate decoding
must run `Codec.checkBytes` first; unrestricted nesting can exhaust the stack. -/
@[expose] def readBytes (input : ByteArray) : Option Value := do
  let tokens ← Token.readBytes input
  let (value, rest) ← readLoop (tokens.length + 1) tokens
  if rest.isEmpty then return value else none

/-- Every finite integer-only JSON value survives its actual printed UTF-8
bytes. This includes arbitrary array/object nesting, Unicode and integer sizes;
there is no parser-success premise or fixed collection of literal fixtures. -/
theorem readBytes_write (value : Value) : readBytes value.writeBytes = some value := by
  unfold readBytes Value.writeBytes
  rw [Token.readBytes_write, Value.tokensLoop_eq]
  simp only [bind, Option.bind]
  rw [(readLoop_all _).1]
  have hp := read_tokens value [] (value.tokens.length + 1)
    (by have hn := value.rank_lt; omega)
  simp only [List.append_nil] at hp
  rw [hp]
  rfl

/-- info: 'Hex.SignDet.Codec.Json.readBytes_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readBytes_write

end Hex.SignDet.Codec.Json
