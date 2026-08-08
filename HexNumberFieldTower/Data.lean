/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField
public meta import HexNumberField

public section

/-!
# Raw number-tower level data

This module contains only the runtime description consumed by recursive
arithmetic and factorization. The public `NumberTower` wrapper is defined later
and certifies a complete top-first list of these levels.
-/
namespace Hex.NumberTower

/-- Runtime data for one monic algebraic extension. `defining[j]` is the
flattened lower-tower coefficient of `X^j`; the omitted coefficient of
`X^degree` is one. -/
structure Level where
  degree : Nat
  defining : Array (Array Rat)
  root : AlgebraicRoot

/-- Dimension represented by a top-first list of extension levels. -/
@[expose]
def levelsDim : List Level → Nat
  | [] => 1
  | level :: lower => level.degree * levelsDim lower

/-- Structural validity of one level above a lower field of dimension
`lowerDim`. -/
@[expose]
def Level.Structural (level : Level) (lowerDim : Nat) : Prop :=
  1 < level.degree ∧
    level.defining.size = level.degree ∧
    ∀ i, ∀ h : i < level.defining.size,
      (level.defining[i]'h).size = lowerDim

/-- Executable structural check for one raw level. -/
@[expose]
def Level.structuralCheck (level : Level) (lowerDim : Nat) : Bool :=
  1 < level.degree && level.defining.size = level.degree &&
    level.defining.all fun coefficient => coefficient.size = lowerDim

/-- The executable structural check exposes the erased width invariant used by
the certified wrapper. -/
theorem Level.structural_of_check {level : Level} {lowerDim : Nat}
    (h : level.structuralCheck lowerDim = true) :
    level.Structural lowerDim := by
  simp only [Level.structuralCheck, Bool.and_eq_true,
    decide_eq_true_eq] at h
  have hdegree := h.1.1
  have hsize := h.1.2
  have hall := h.2
  refine ⟨hdegree, hsize, ?_⟩
  intro i hi
  rw [Array.all_eq_true] at hall
  simpa using hall i hi

end Hex.NumberTower
