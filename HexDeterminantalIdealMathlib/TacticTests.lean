/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
import HexDeterminantalIdealMathlib.Tactic
import Mathlib.Algebra.Field.ZMod

example {F : Type} [Field F] [CharZero F] (x y : F) : True := by
  rank_locus !![x, y] 1 with h
  have : (!![x, y]).rank < 1 ↔ x = 0 ∧ y = 0 := h
  trivial

example {F : Type} [Field F] [CharZero F] (x : F) : True := by
  rank_locus !![x, 1; 1, x] 2 with h
  have : (!![x, 1; 1, x]).rank < 2 ↔ x ^ 2 - 1 = 0 := h
  trivial

example {F : Type} [Field F] [CharZero F] (x : F) : 1 ≤ (!![x, 1; 1, x]).rank := by
  rank_locus

example {F : Type} [Field F] [CharZero F] (x y : F) (hx : x = 0) (hy : y = 0) :
    (!![x, y]).rank < 1 := by rank_locus

example {F : Type} [Field F] [CharZero F] (x y : F) (hx : x = 0) (hy : y = 0) :
    (!![x, y]).rank = 0 := by rank_locus

example {F : Type} [Field F] [CharZero F] (x y : F) : (!![x, y]).rank ≤ 1 := by
  rank_locus

example (x : ℤ) : True := by
  rank_locus !![x, 2*x] 1 with h
  have : (!![x, 2*x]).rank < 1 ↔ x = 0 ∧ 2*x = 0 := h
  trivial

example {F : Type} [Field F] [CharZero F] (x y : F) :
    (!![x,y]).rank < 1 ↔ x = 0 ∧ y = 0 := (rank_locus% !![x,y] 1).proof

open MvPolynomial in
example : (rank_locus% (!![X (0 : Fin 2), X (1 : Fin 2)] :
    Matrix (Fin 1) (Fin 2) (MvPolynomial (Fin 2) ℤ)) 1).ideal?.isSome = true := rfl

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

example (x : ZMod 3) : True := by
  rank_locus !![x ^ 3 - x] 1 with h
  have : (!![x ^ 3 - x]).rank < 1 ↔ x ^ 3 - x = 0 := h
  trivial

example (x : ZMod 3) : 1 ≤ (!![x, 1; 1, x]).rank := by rank_locus

example (x : ZMod 3) : (!![x^3-x]).rank < 1 ↔ x^3-x = 0 :=
  (rank_locus% !![x^3-x] 1).proof

open MvPolynomial in
example : (rank_locus% (!![X (0 : Fin 2), X (1 : Fin 2)] :
    Matrix (Fin 1) (Fin 2) (MvPolynomial (Fin 2) (ZMod 3))) 1).ideal?.isSome = true := rfl

example (x : ℚ) : (!![x]).rank < 1 ↔ x = 0 := by
  rank_locus !![x] 1 with locus
  exact locus

example (x : ℚ) (hz : x = 0) : (!![x]).rank < 1 := by rank_locus
example (x : ℚ) (hz : x = 0) : (!![x]).rank ≤ 0 := by rank_locus
example (x : ℚ) (hn : x ≠ 0) : 1 ≤ (!![x]).rank := by rank_locus
example (x : ℚ) (hn : x ≠ 0) : (!![x]).rank = 1 := by rank_locus
example (x : ℚ) : (!![x]).rank < 1 ↔ x = 0 := (rank_locus% !![x] 1).proof

example (x y : ℚ) : (!![x, y]).rank < 1 ↔ x = 0 ∧ y = 0 := by
  rank_locus !![x, y] 1 with locus
  exact locus

example (x y : ℚ) (hx : x = 0) (hy : y = 0) : (!![x, y]).rank < 1 := by rank_locus
example (x y : ℚ) (hx : x = 0) (hy : y = 0) : (!![x, y]).rank ≤ 0 := by rank_locus
example (x y : ℚ) (hy : y ≠ 0) : 1 ≤ (!![x, y]).rank := by rank_locus
example (x y : ℚ) (hy : y ≠ 0) : (!![x, y]).rank = 1 := by rank_locus
example (x y : ℚ) : (!![x, y]).rank < 1 ↔ x = 0 ∧ y = 0 := (rank_locus% !![x, y] 1).proof

example (x : ℚ) : (!![x, 1; 1, x]).rank < 2 ↔ x ^ 2 - 1 = 0 := by
  rank_locus !![x, 1; 1, x] 2 with locus
  exact locus

example (x : ℚ) (hz : x ^ 2 - 1 = 0) : (!![x, 1; 1, x]).rank < 2 := by rank_locus
example (x : ℚ) (hz : x ^ 2 - 1 = 0) : (!![x, 1; 1, x]).rank ≤ 1 := by rank_locus
example (x : ℚ) (hn : x ^ 2 - 1 ≠ 0) : 2 ≤ (!![x, 1; 1, x]).rank := by rank_locus
example (x : ℚ) (hn : x ^ 2 - 1 ≠ 0) : (!![x, 1; 1, x]).rank = 2 := by rank_locus
example (x : ℚ) : (!![x, 1; 1, x]).rank < 2 ↔ x ^ 2 - 1 = 0 := (rank_locus% !![x, 1; 1, x] 2).proof

example (x y : ℚ) : (!![1, x; 1, y]).rank < 2 ↔ y - x = 0 := by
  rank_locus !![1, x; 1, y] 2 with locus
  exact locus

example (x y : ℚ) (hz : y - x = 0) : (!![1, x; 1, y]).rank < 2 := by rank_locus
example (x y : ℚ) (hz : y - x = 0) : (!![1, x; 1, y]).rank ≤ 1 := by rank_locus
example (x y : ℚ) (hn : y - x ≠ 0) : 2 ≤ (!![1, x; 1, y]).rank := by rank_locus
example (x y : ℚ) (hn : y - x ≠ 0) : (!![1, x; 1, y]).rank = 2 := by rank_locus
example (x y : ℚ) : (!![1, x; 1, y]).rank < 2 ↔ y - x = 0 := (rank_locus% !![1, x; 1, y] 2).proof

example (x : ZMod 3) : (!![x ^ 3 - x]).rank < 1 ↔ x ^ 3 - x = 0 := by
  rank_locus !![x ^ 3 - x] 1 with locus
  exact locus

example (x : ZMod 3) (hz : x ^ 3 - x = 0) : (!![x ^ 3 - x]).rank < 1 := by rank_locus
example (x : ZMod 3) (hz : x ^ 3 - x = 0) : (!![x ^ 3 - x]).rank ≤ 0 := by rank_locus
example (x : ZMod 3) (hn : x ^ 3 - x ≠ 0) : 1 ≤ (!![x ^ 3 - x]).rank := by rank_locus
example (x : ZMod 3) (hn : x ^ 3 - x ≠ 0) : (!![x ^ 3 - x]).rank = 1 := by rank_locus
example (x : ZMod 3) : (!![x ^ 3 - x]).rank < 1 ↔ x ^ 3 - x = 0 := (rank_locus% !![x ^ 3 - x] 1).proof

-- Unresolved conditions remain visible in generator order.
example (x y : ℚ) (hx : True → x = 0) (hy : True → y = 0) : (!![x,y]).rank < 1 := by
  rank_locus
  · guard_target = x = 0
    exact hx trivial
  · guard_target = y = 0
    exact hy trivial

example (x y : ℚ) (hx : True → x ≠ 0) : 1 ≤ (!![x,y]).rank := by
  rank_locus
  guard_target = x ≠ 0
  exact hx trivial

-- The automatic tiers reach a later generator before creating a side goal.
example (x y : ℚ) (hy : y ≠ 0) : 1 ≤ (!![x,y]).rank := by rank_locus

example (x y : ℚ) : True := by
  rank_locus !![x, 0, x, y] 1 with locus
  have : (!![x, 0, x, y]).rank < 1 ↔ x = 0 ∧ y = 0 := locus
  trivial

example (x : ℚ) : True := by
  rank_locus !![x] 0 with locus
  have : (!![x]).rank < 0 ↔ (1 : ℚ) = 0 := locus
  trivial

example (x : ℚ) : True := by
  rank_locus !![x] 2 with locus
  have : (!![x]).rank < 2 ↔ True := locus
  trivial

example : True := by
  rank_locus (fun (i : Fin 0) (_ : Fin 2) => (Fin.elim0 i : ℚ)) 1 with locus
  have : Matrix.rank (fun (i : Fin 0) (_ : Fin 2) => (Fin.elim0 i : ℚ)) < 1 ↔ True := locus
  trivial

example : Matrix.rank (fun (_ : Fin 2) (j : Fin 0) => (Fin.elim0 j : ℚ)) = 0 := by rank_locus

example (x : ℤ) (hx : x = 0) (h2 : 2*x = 0) : (!![x, 2*x]).rank < 1 := by rank_locus
example (x : ℤ) (hx : x ≠ 0) : (!![x, 2*x]).rank = 1 := by rank_locus

example (x : ℚ) : True := by
  fail_if_success rank_locus (config := {minorWork := 0}) !![x] 1
  guard_target = True
  trivial

-- A zero minor-count boundary has no factorial work, even at a large threshold.
example (x : ℚ) : True := by
  rank_locus (config := {minorWork := 0}) !![x] 1000 with locus
  have : (!![x]).rank < 1000 ↔ True := locus
  trivial

example (x : ℚ) (r : Nat) : True := by
  fail_if_success rank_locus !![x] r
  trivial

example : Hex.Matrix.indexTuples 2 4 = [[0,1], [0,2], [1,2], [0,3], [1,3], [2,3]] := by rfl

-- The displayed iff is valid without assuming characteristic zero.
example {F : Type} [Field F] (x : F) : (!![x]).rank < 1 ↔ x = 0 :=
  (rank_locus% !![x] 1).proof
