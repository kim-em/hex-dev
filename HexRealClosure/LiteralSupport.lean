/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ContextData
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic

public section

namespace Hex.RealClosure.Tower
open Lean

/-- The structured shapes used by native context and certificate encoders. -/
inductive Literal.Supported : Json → Prop
  | num (n : JsonNumber) : Supported (.num n)
  | str (s : String) : Supported (.str s)
  | arr (values : Array Json) (elements : ∀ j ∈ values, Supported j) : Supported (.arr values)

@[simp] theorem Literal.Supported.arr_iff (values : Array Json) :
    Supported (.arr values) ↔ ∀ j ∈ values, Supported j := by
  constructor
  · intro h; cases h with | arr _ hs => exact hs
  · exact Supported.arr values

private theorem mapM_exists {A B : Type} (read : A → Option B) (xs : List A)
    (h : ∀ x ∈ xs, ∃ y, read x = some y) : ∃ ys, xs.mapM read = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (fun z hz => h z (by simp [hz]))
    exact ⟨y :: ys, by simp [hy, hys]⟩

/-- Supported finite JSON always converts to the exact literal tree. -/
theorem Literal.Supported.read {j : Json} (h : Supported j) :
    ∃ literal, Literal.ofJson j = some literal := by
  induction h with
  | num n => exact ⟨.number n.mantissa n.exponent, by simp [Literal.ofJson]⟩
  | str s => exact ⟨.string s, by simp [Literal.ofJson]⟩
  | arr values hs ih =>
    obtain ⟨xs, hx⟩ := mapM_exists Literal.ofJson values.toList
      (fun j hj => ih j (by simpa using hj))
    exact ⟨.array (Literals.ofList xs), by simp [Literal.ofJson, hx]⟩

theorem Literal.Supported.array_map {A : Type} (write : A → Json) (xs : Array A)
    (h : ∀ x ∈ xs, Supported (write x)) : Supported (.arr (xs.map write)) := by
  apply Supported.arr
  intro j hj
  obtain ⟨x, hx, rfl⟩ := Array.mem_map.mp hj
  exact h x hx

theorem Literal.Supported.list_map {A : Type} (write : A → Json) (xs : List A)
    (h : ∀ x ∈ xs, Supported (write x)) : Supported (.arr (xs.toArray.map write)) :=
  Supported.array_map write xs.toArray (fun x hx => h x (by simpa using hx))

@[simp] theorem Literal.Supported.nat (n : Nat) : Supported (Lean.toJson n) := .num _
@[simp] theorem Literal.Supported.int (n : Int) : Supported (Lean.toJson n) := .num _
@[simp] theorem Literal.Supported.string (s : String) : Supported (Lean.toJson s) := .str _

@[simp] theorem Literal.Supported.toJson_array {A : Type} [ToJson A] (xs : Array A)
    (h : ∀ x ∈ xs, Supported (Lean.toJson x)) : Supported (Lean.toJson xs) :=
  Supported.array_map Lean.toJson xs h

@[simp] theorem Literal.Supported.toJson_list {A : Type} [ToJson A] (xs : List A)
    (h : ∀ x ∈ xs, Supported (Lean.toJson x)) : Supported (Lean.toJson xs) :=
  Supported.list_map Lean.toJson xs h

mutual
theorem Literal.supported_toJson (x : Literal) : Literal.Supported x.toJson := by
  cases x with
  | number m e => exact .num _
  | string s => exact .str _
  | array xs =>
    change Literal.Supported (.arr xs.toArray)
    rw [Literals.toArray_eq]
    simpa only [List.map_toArray] using
      Literal.Supported.list_map Literal.toJson xs.toList (Literals.supported_list xs)

theorem Literals.supported_list (xs : Literals) :
    ∀ x ∈ xs.toList, Literal.Supported x.toJson := by
  cases xs with
  | nil => simp [Literals.toList]
  | cons x xs =>
    intro y hy
    simp only [Literals.toList, List.mem_cons] at hy
    rcases hy with he | hy
    · simpa only [he] using Literal.supported_toJson x
    · exact Literals.supported_list xs y hy
end

end Hex.RealClosure.Tower
