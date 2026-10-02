/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMatrix.Basic

public section

/-! Structural integer list arithmetic for matrix certificates. -/

namespace Hex.Matrix.Lists

/-- Check a predicate at every index below a natural bound. -/
@[expose] def all (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => all p n && p n

/-- List lookup with an explicit default and structural recursion. -/
@[expose] def entry (zero : α) : List α → Nat → α
  | [], _ => zero
  | x :: _, 0 => x
  | _ :: xs, n + 1 => entry zero xs n

/-- Integer entry of a row list, padded with zeros. -/
@[expose] def get (rows : List (List Int)) (i j : Nat) : Int :=
  entry 0 (entry [] rows i) j

/-- Exact rectangular dimensions, including empty rows. -/
@[expose] def shape (n m : Nat) (rows : List (List Int)) : Bool :=
  Nat.beq rows.length n && rows.all (fun row => Nat.beq row.length m)

/-- A structurally recursive integer dot product. -/
@[expose] def dot : List Int → List Int → Int
  | a :: as, b :: bs => Int.add (Int.mul a b) (dot as bs)
  | _, _ => 0

/-- A column of a row list. -/
@[expose] def column (j : Nat) : List (List Int) → List Int
  | [] => []
  | row :: rows => entry 0 row j :: column j rows

/-- Check a matrix product against a supplied entry function. Shapes are
checked separately by the caller. -/
@[expose] def product (n m : Nat) (a b : List (List Int)) (c : Nat → Nat → Int) : Bool :=
  all (fun i => all (fun j => decide (dot (entry [] a i) (column j b) = c i j)) m) n

/-- The entry function for an identity matrix. -/
@[expose] def identity (i j : Nat) : Int := if Nat.beq i j then 1 else 0

/-- The entry function for a rectangular diagonal matrix. -/
@[expose] def diagonal (d : List Int) (i j : Nat) : Int :=
  if Nat.beq i j then entry 0 d i else 0

theorem all_iff (p : Nat → Bool) (n : Nat) :
    all p n = true ↔ ∀ i, i < n → p i = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
    simp only [all, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      by_cases hin : i < n
      · exact h i hin
      · have : i = n := by omega
        simpa [this] using hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem entry_eq_getD (zero : α) (xs : List α) (i : Nat) :
    entry zero xs i = xs.getD i zero := by
  induction xs generalizing i with
  | nil => simp [entry]
  | cons x xs ih => cases i <;> simp [entry, ih]

/-- Exact unnormalized integer coefficient addition. -/
@[expose] def add : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => Int.add x y :: add xs ys

/-- Integer coefficient scaling. -/
@[expose] def scale (a : Int) (xs : List Int) : List Int := xs.map (Int.mul a)

/-- Structural integer coefficient convolution. -/
@[expose] def mul : List Int → List Int → List Int
  | [], _ => []
  | x :: xs, ys => add (scale x ys) (0 :: mul xs ys)

end Hex.Matrix.Lists

namespace Hex.Matrix

/-- The row-major list observation used in matrix denotation proofs. -/
@[expose] def rowLists (A : Matrix R n m) : List (List R) := A.rows.toList.map Vector.toList

theorem length_rowLists (A : Matrix R n m) : (rowLists A).length = n := by
  simp [rowLists]

theorem entry_rowLists (A : Matrix R n m) (i : Fin n) :
    Lists.entry [] (rowLists A) i.val = A[i].toList := by
  simp [rowLists, Lists.entry_eq_getD, List.getD_eq_getElem?_getD, i.isLt]

theorem get_rowLists [Zero R] (A : Matrix R n m) (i : Fin n) (j : Fin m) :
    Lists.entry 0 (Lists.entry [] (rowLists A) i.val) j.val = A[i][j] := by
  rw [entry_rowLists]
  simp [Lists.entry_eq_getD, List.getD_eq_getElem?_getD, j.isLt]

end Hex.Matrix
