/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Data.Rat.Lemmas
public import Init.Data.Dyadic.Basic

@[expose] public section

namespace Hex.OrderedFn.Oracle

/-- Exact finite closed bounds. Accuracy and semantic containment are separate
theorems about the caller's approximation function. -/
structure Bounds where
  lower : Rat
  upper : Rat
  ordered : lower ≤ upper
  deriving DecidableEq, Repr

namespace Bounds

/-- Width of a finite enclosure. -/
def width (a : Bounds) : Rat := a.upper - a.lower

/-- Exact enclosure of a rational value. -/
def singleton (x : Rat) : Bounds := ⟨x, x, by exact Std.le_refl _⟩

/-- A dyadic input is converted exactly, without endpoint rounding. -/
def ofDyadic (x : Dyadic) : Bounds := singleton x.toRat

/-- Negate a closed bound, reversing its endpoints. -/
def neg (a : Bounds) : Bounds := ⟨-a.upper, -a.lower, by have := a.ordered; grind⟩

/-- Endpoint addition. -/
def add (a b : Bounds) : Bounds :=
  ⟨a.lower + b.lower, a.upper + b.upper, by have := a.ordered; have := b.ordered; grind⟩

/-- The smallest closed bound containing four exact rational values. -/
def hull4 (a b c d : Rat) : Bounds :=
  ⟨min (min a b) (min c d), max (max a b) (max c d), by grind [min, max]⟩

/-- Multiplication by the minimum and maximum of the four endpoint products. -/
def mul (a b : Bounds) : Bounds :=
  hull4 (a.lower * b.lower) (a.lower * b.upper)
    (a.upper * b.lower) (a.upper * b.upper)

/-- Intersection rejects inconsistent bounds. -/
def inter (a b : Bounds) : Option Bounds :=
  if h : max a.lower b.lower ≤ min a.upper b.upper then
    some ⟨max a.lower b.lower, min a.upper b.upper, h⟩
  else none

/-- Strict separation from zero, without treating a zero-containing bound as zero. -/
def separated (a : Bounds) : Bool := a.upper < 0 || 0 < a.lower

/-- Quotient enclosures require a denominator separated from zero.
This operation is independent of total rational-function division. -/
def div? (a b : Bounds) : Option Bounds :=
  if b.separated then
    some (hull4 (a.lower / b.lower) (a.lower / b.upper)
      (a.upper / b.lower) (a.upper / b.upper))
  else none

/-- Only strictly separated bounds yield a nonzero sign. -/
def sign? (a : Bounds) : Option Int :=
  if 0 < a.lower then some 1 else if a.upper < 0 then some (-1) else none

/-- Finite evaluation can additionally certify zero from an exact singleton. -/
def exactSign? (a : Bounds) : Option Int :=
  if a.lower = 0 ∧ a.upper = 0 then some 0 else a.sign?

theorem width_nonneg (a : Bounds) : 0 ≤ a.width := by
  have := a.ordered
  grind [width]

@[simp] theorem width_singleton (x : Rat) : (singleton x).width = 0 := by
  grind [width, singleton]

end Bounds

/-- The two computational procedures used at one real extension level. -/
structure Approximation (K : Type u) where
  coeff : K → Rat → Bounds
  constant : Rat → Bounds

/-- Start a real extension over the rationals with exact coefficient bounds. -/
def Approximation.ofConstant (constant : Rat → Bounds) : Approximation Rat :=
  ⟨fun c _ => .singleton c, constant⟩

/-- Requested-width guarantees for precisely these two procedures.
No guarantees are imposed on nonpositive requests. -/
structure ApproximationWidth {K : Type u} (a : Approximation K) : Prop where
  coeff : ∀ x δ, 0 < δ → (a.coeff x δ).width ≤ δ
  constant : ∀ δ, 0 < δ → (a.constant δ).width ≤ δ

theorem ApproximationWidth.ofConstant (constant : Rat → Bounds)
    (h : ∀ δ, 0 < δ → (constant δ).width ≤ δ) :
    ApproximationWidth (.ofConstant constant) where
  coeff c δ hδ := by
    change (Bounds.singleton c).width ≤ δ
    simpa using Std.le_of_lt hδ
  constant := h

end Hex.OrderedFn.Oracle
