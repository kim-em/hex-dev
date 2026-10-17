/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Data.Rat.Lemmas
public import Init.Data.Dyadic.Basic

/-!
Minimal exact rational bounds and caller approximation functions. Requested-width
proofs are separate from the computational providers and semantic containment.
-/

@[expose] public section

namespace Hex.OrderedFn.Oracle

/-- Exact finite closed bounds. Accuracy and semantic containment are separate
theorems about the caller's approximation function. -/
structure Bounds where
  /-- The included lower endpoint. -/
  lower : Rat
  /-- The included upper endpoint. -/
  upper : Rat
  /-- The endpoints form a nonempty closed interval. -/
  ordered : lower ≤ upper
  deriving DecidableEq, Repr

namespace Bounds

/-- Closed bounds are determined by their endpoints; the order proof carries no data. -/
@[ext (iff := false)] theorem ext {a b : Bounds}
    (hl : a.lower = b.lower) (hu : a.upper = b.upper) : a = b := by
  cases a
  cases b
  simp_all

/-- Equality of closed bounds is exactly equality of their endpoints. -/
theorem ext_iff {a b : Bounds} :
    a = b ↔ a.lower = b.lower ∧ a.upper = b.upper := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hl, hu⟩
    exact ext hl hu

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

/-- Intersection succeeds exactly when the proposed overlap has ordered endpoints. -/
@[simp] theorem inter_isSome (a b : Bounds) :
    (a.inter b).isSome = decide (max a.lower b.lower ≤ min a.upper b.upper) := by
  unfold inter
  split <;> simp_all

/-- A successful intersection has exactly the maximum lower and minimum upper endpoint.
Conversely, any closed bound with those endpoints is the returned intersection. -/
theorem inter_eq_some {a b c : Bounds} :
    a.inter b = some c ↔
      c.lower = max a.lower b.lower ∧ c.upper = min a.upper b.upper := by
  unfold inter
  split
  · constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨hl, hu⟩
      exact congrArg some (ext_iff.mpr ⟨hl.symm, hu.symm⟩)
  · constructor
    · intro h
      contradiction
    · rintro ⟨hl, hu⟩
      have hc := c.ordered
      rw [hl, hu] at hc
      contradiction

/-- Strict separation from zero, without treating a zero-containing bound as zero. -/
def separated (a : Bounds) : Bool := a.upper < 0 || 0 < a.lower

/-- Quotient enclosures require a denominator separated from zero.
This operation is independent of total rational-function division. -/
noncomputable def div? (a b : Bounds) : Option Bounds :=
  if b.separated then
    some (hull4 (a.lower / b.lower) (a.lower / b.upper)
      (a.upper / b.lower) (a.upper / b.upper))
  else none

/-- Positive reciprocal reverses the denominator order. -/
private theorem inv_le_of_pos {x y : Rat} (hx : 0 < x) (hxy : x ≤ y) :
    y⁻¹ ≤ x⁻¹ := by
  have hy : 0 < y := by grind
  have hxinv : 0 ≤ x⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hx)
  apply Rat.le_of_mul_le_mul_right (c := y) ?_ hy
  simpa only [Rat.inv_mul_cancel _ (Rat.ne_of_gt hx),
    Rat.inv_mul_cancel _ (Rat.ne_of_gt hy)] using
    Rat.mul_le_mul_of_nonneg_left hxy hxinv

/-- The two opposite corners bound every quotient corner in the positive case. -/
private theorem quotient_corners (a b : Bounds) (ha : 0 ≤ a.lower) (hb : 0 < b.lower) :
    a.lower / b.upper ≤ a.lower / b.lower ∧
    a.lower / b.lower ≤ a.upper / b.lower ∧
    a.lower / b.upper ≤ a.upper / b.upper ∧
    a.upper / b.upper ≤ a.upper / b.lower := by
  have hbu : 0 < b.upper := by have := b.ordered; grind
  have hau : 0 ≤ a.upper := by have := a.ordered; grind
  have hinv := inv_le_of_pos hb b.ordered
  have hbl := Rat.le_of_lt (Rat.inv_pos.mpr hb)
  have hbr := Rat.le_of_lt (Rat.inv_pos.mpr hbu)
  simpa only [Rat.div_def] using And.intro
    (Rat.mul_le_mul_of_nonneg_left hinv ha) (And.intro
    (Rat.mul_le_mul_of_nonneg_right a.ordered hbl) (And.intro
    (Rat.mul_le_mul_of_nonneg_right a.ordered hbr)
    (Rat.mul_le_mul_of_nonneg_left hinv hau)))

/-- Positive quotient bounds use their exact two extrema. Other signs retain
all four reference corners and the original denominator-separation guard. -/
def divImpl (a b : Bounds) : Option Bounds :=
  if h : 0 ≤ a.lower ∧ 0 < b.lower then
    some ⟨a.lower / b.upper, a.upper / b.lower, by
      have limits := quotient_corners a b h.1 h.2
      exact Rat.le_trans limits.1 limits.2.1⟩
  else if b.separated then
    some (hull4 (a.lower / b.lower) (a.lower / b.upper)
      (a.upper / b.lower) (a.upper / b.upper))
  else none

/-- The native positive quotient returns exactly the reference bounds or refusal. -/
@[csimp] theorem div_eq_impl : @div? = @divImpl := by
  funext a b
  unfold divImpl
  split
  · rename_i h
    have separated : b.separated = true := by simp [Bounds.separated, h.2]
    simp only [div?, separated, ite_true]
    have limits := quotient_corners a b h.1 h.2
    apply congrArg some
    apply ext <;> dsimp [hull4] <;> grind [min, max]
  · rfl

/-- Only strictly separated bounds yield a nonzero sign. -/
def sign? (a : Bounds) : Option Int :=
  if 0 < a.lower then some 1 else if a.upper < 0 then some (-1) else none

/-- Finite evaluation can additionally certify zero from an exact singleton. -/
def exactSign? (a : Bounds) : Option Int :=
  if a.lower = 0 ∧ a.upper = 0 then some 0 else a.sign?

/-- Every closed bound has nonnegative width. -/
theorem width_nonneg (a : Bounds) : 0 ≤ a.width := by
  have := a.ordered
  grind [width]

/-- An exact rational enclosure has zero width. -/
@[simp] theorem width_singleton (x : Rat) : (singleton x).width = 0 := by
  grind [width, singleton]

/-- Negating an enclosure preserves its width. -/
@[simp] theorem width_neg (a : Bounds) : a.neg.width = a.width := by
  grind [width, neg]

/-- Endpoint addition adds enclosure widths exactly. -/
@[simp] theorem width_add (a b : Bounds) : (a.add b).width = a.width + b.width := by
  grind [width, add]

end Bounds

/-- The two computational procedures used at one real extension level. -/
structure Approximation (K : Type u) where
  /-- Refine a predecessor coefficient at the requested rational width. -/
  coeff : K → Rat → Bounds
  /-- Refine the new constant at the requested rational width. -/
  constant : Rat → Bounds

/-- Start a real extension over the rationals with exact coefficient bounds. -/
def Approximation.ofConstant (constant : Rat → Bounds) : Approximation Rat :=
  ⟨fun c _ => .singleton c, constant⟩

/-- Requested-width guarantees for precisely these two procedures.
No guarantees are imposed on nonpositive requests. -/
structure ApproximationWidth {K : Type u} (a : Approximation K) : Prop where
  /-- Positive requests bound every coefficient enclosure's width. -/
  coeff : ∀ x δ, 0 < δ → (a.coeff x δ).width ≤ δ
  /-- Positive requests bound the new constant's enclosure width. -/
  constant : ∀ δ, 0 < δ → (a.constant δ).width ≤ δ

/-- Exact rational coefficient bounds leave only the constant's width obligation. -/
theorem ApproximationWidth.ofConstant (constant : Rat → Bounds)
    (h : ∀ δ, 0 < δ → (constant δ).width ≤ δ) :
    ApproximationWidth (.ofConstant constant) where
  coeff c δ hδ := by
    change (Bounds.singleton c).width ≤ δ
    simpa using Std.le_of_lt hδ
  constant := h

end Hex.OrderedFn.Oracle
