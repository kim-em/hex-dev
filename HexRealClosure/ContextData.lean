/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseCatalog
public import HexSignDet.Codec.Basic
import all Lean.Data.Json.Basic

public section

namespace Hex.RealClosure.Tower
open Lean

mutual
/-- Literal structured context data. Numbers retain both their mantissa and
exponent; equality never uses a hash, JSON printing, or numerical equivalence.
The shared positional certificate format uses arrays, numbers and strings. -/
inductive Literal where
  | number (mantissa : Int) (exponent : Nat)
  | string (value : String)
  | array (values : Literals)
  deriving DecidableEq, Repr, Hashable
inductive Literals where
  | nil
  | cons (head : Literal) (tail : Literals)
  deriving DecidableEq, Repr, Hashable
end

@[expose] def Literals.ofList : List Literal → Literals
  | [] => .nil
  | x :: xs => .cons x (Literals.ofList xs)

mutual
@[expose] def Literal.toJson : Literal → Json
  | .number m e => .num ⟨m, e⟩
  | .string s => .str s
  | .array xs => .arr xs.toArray
@[expose] def Literals.toArray : Literals → Array Json
  | .nil => #[]
  | .cons x xs => #[x.toJson] ++ xs.toArray
end

/-- Reject unsupported JSON shapes rather than assigning them a shared
fallback identity. No byte parsing or printing is involved. -/
@[expose] def Literal.ofJson : Json → Option Literal
  | .num n => some (.number n.mantissa n.exponent)
  | .str s => some (.string s)
  | .arr xs => (Literal.array ∘ Literals.ofList) <$> xs.toList.mapM Literal.ofJson
  | _ => none
termination_by j => sizeOf j
decreasing_by
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem (by simpa using ‹_ ∈ xs.toList›)) (by simp)

@[expose] def Literals.toList : Literals → List Literal
  | .nil => []
  | .cons x xs => x :: xs.toList

theorem Literals.ofList_toList (xs : Literals) : Literals.ofList xs.toList = xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [toList, ofList, Literals.ofList_toList xs]

theorem Literals.toArray_eq (xs : Literals) :
    xs.toArray = (xs.toList.map Literal.toJson).toArray := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    change #[x.toJson] ++ xs.toArray = (x.toJson :: xs.toList.map Literal.toJson).toArray
    conv => rhs; rw [List.toArray_cons]
    rw [Literals.toArray_eq xs]

theorem Literals.toList_ofList (xs : List Literal) :
    (Literals.ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Literals.ofList, Literals.toList, ih]

mutual
theorem Literal.ofJson_toJson (x : Literal) : Literal.ofJson x.toJson = some x := by
  cases x with
  | number m e => simp [Literal.toJson, Literal.ofJson]
  | string s => simp [Literal.toJson, Literal.ofJson]
  | array xs =>
    simp only [Literal.toJson, Literal.ofJson, Literals.toArray_eq]
    rw [Literals.read_list xs]
    simp [Literals.ofList_toList]

theorem Literals.read_list (xs : Literals) :
    (xs.toList.map Literal.toJson).mapM Literal.ofJson = some xs.toList := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [Literals.toList, Literal.ofJson_toJson x, Literals.read_list xs]
end

private theorem list_read_sound {A B : Type} (read : A → Option B) (write : B → A)
    (xs : List A) (ys : List B)
    (h : xs.mapM read = some ys)
    (hs : ∀ a ∈ xs, ∀ b, read a = some b → write b = a) : ys.map write = xs := by
  induction xs generalizing ys with
  | nil => simpa using h.symm
  | cons x xs ih =>
    cases hx : read x with
    | none => simp [hx] at h
    | some y =>
      cases ht : xs.mapM read with
      | none => simp [hx, ht] at h
      | some zs =>
        have he : y :: zs = ys := by simpa [hx, ht] using h
        subst ys
        simp only [List.map_cons]
        rw [hs x (by simp) y hx, ih zs ht (fun a ha => hs a (by simp [ha]))]

/-- Successful conversion retains the complete structured JSON value. This
rules out collisions from unsupported shapes or normalized numeric literals. -/
theorem Literal.toJson_ofJson (j : Json) (x : Literal)
    (h : Literal.ofJson j = some x) : x.toJson = j := by
  cases j with
  | num n => simp only [Literal.ofJson, Option.some.injEq] at h; cases h; rfl
  | str s => simp only [Literal.ofJson, Option.some.injEq] at h; cases h; rfl
  | arr js =>
    cases hr : js.toList.mapM Literal.ofJson with
    | none => simp [Literal.ofJson, hr] at h
    | some xs =>
      have he : Literal.array (Literals.ofList xs) = x := by
        simpa [Literal.ofJson, hr] using h
      subst x
      have hm := list_read_sound Literal.ofJson Literal.toJson js.toList xs hr
        (fun a ha b hb => Literal.toJson_ofJson a b hb)
      simp [Literal.toJson, Literals.toArray_eq, Literals.toList_ofList, hm]
  | null => simp [Literal.ofJson] at h
  | bool b => simp [Literal.ofJson] at h
  | obj fields => simp [Literal.ofJson] at h
termination_by sizeOf j
decreasing_by
  subst j
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem (by simpa using ha)) (by simp)

end Hex.RealClosure.Tower
