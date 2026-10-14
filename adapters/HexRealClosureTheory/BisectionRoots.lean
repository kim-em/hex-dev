/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.Bisection
public import HexRealRoots.Map
public import HexRealRootsTheory.TarskiSum

public section

namespace Hex.RealClosure.Bisection
open HexPolyTheory.Interpret HexSturmTheory HexRealRootsTheory.Tarski

variable {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [Field K] [IsStrictOrderedRing K] in
private theorem interval_split (lower upper : Endpoint K) (point x : K)
    (hc : InInterval lower upper point) (hx : x ≠ point) :
    InInterval lower upper x ↔
      InInterval lower (.finite point) x ∨ InInterval (.finite point) upper x := by
  simp only [inInterval_iff] at hc ⊢
  constructor
  · intro h
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exact Or.inl ⟨h.1, hlt⟩
    · exact Or.inr ⟨hgt, h.2⟩
  · rintro (⟨hl, hx⟩ | ⟨hx, hu⟩)
    · refine ⟨hl, ?_⟩
      cases upper with
      | negInf => exact hc.2
      | finite b => exact hx.trans hc.2
      | posInf => trivial
    · refine ⟨?_, hu⟩
      cases lower with
      | negInf => trivial
      | finite a => exact hc.1.trans hx
      | posInf => exact hc.1

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
variable [DecidableEq K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable {sign : E → Int} {p : DensePoly E} {point : E}

include hz h1 hs hm in
omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Exact linear deflation preserves the interpreted leading coefficient.
No literal equality between noncanonical coefficient representatives is asserted. -/
theorem Mode.leadingCoeff_head (mode : Mode sign p point) :
    (interpret φ hz mode.head).leadingCoeff = (interpret φ hz p).leadingCoeff := by
  cases mode with
  | regular _ => rfl
  | root d =>
    rw [d.factor φ hz h1 hs hm, Polynomial.leadingCoeff_mul,
      (Polynomial.monic_X_sub_C (φ point)).leadingCoeff, one_mul]
    rfl

include hz h1 hs hm in
omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The removed coefficient point and active head cover the original roots. -/
theorem Mode.roots (mode : Mode sign p point) (x : K) :
    (interpret φ hz p).IsRoot x ↔
      (∃ r ∈ mode.removed, x = φ r) ∨ (interpret φ hz mode.head).IsRoot x := by
  cases mode with
  | regular _ => simp [Mode.removed, Mode.head]
  | root d => simpa [Mode.removed, Mode.head] using d.roots φ hz h1 hs hm x

variable [NatCast E] [Neg E] [Inv E]
variable (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hzero : ∀ a, sign a = 0 ↔ φ a = 0)
variable (hn : ∀ a, φ (-a) = -φ a) (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))
variable (hpos : ∀ a, sign a = 1 ↔ 0 < φ a) (hneg : ∀ a, sign a < 0 ↔ φ a < 0)

include hz h1 hs hm ha hzero hn hi hnat hpos hneg in
/-- The actual returned intervals and removed point partition all original
roots in the input interval. -/
theorem Split.partition {lower upper : Endpoint E}
    (split : Split sign p lower upper point) (x : K) :
    (interpret φ hz p).IsRoot x ∧ InInterval (lower.map φ) (upper.map φ) x ↔
      (∃ r ∈ split.mode.removed, x = φ r) ∨
        ((interpret φ hz split.left.head).IsRoot x ∧
          InInterval (split.left.lower.map φ) (split.left.upper.map φ) x) ∨
        ((interpret φ hz split.right.head).IsRoot x ∧
          InInterval (split.right.lower.map φ) (split.right.upper.map φ) x) := by
  simp only [split.left_bound.2.1, split.left_bound.2.2.1, split.left_bound.2.2.2,
    split.right_bound.2.1, split.right_bound.2.2.1, split.right_bound.2.2.2, Endpoint.map]
  obtain ⟨dl, dr⟩ := split.domains φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
  have hc : InInterval (lower.map φ) (upper.map φ) (φ point) := by
    apply (inInterval_iff _ _ _).mpr
    cases lower <;> cases upper <;> exact ⟨dl.2.2.1, dr.2.2.1⟩
  have hnroot : ¬ (interpret φ hz split.mode.head).IsRoot (φ point) := dl.2.2.2.2
  have roots := split.mode.roots φ hz h1 hs hm x
  constructor
  · rintro ⟨hp, hx⟩
    rcases roots.mp hp with removed | active
    · exact Or.inl removed
    · have hne : x ≠ φ point := fun h => hnroot (h ▸ active)
      rcases (interval_split _ _ _ _ hc hne).mp hx with left | right
      · exact Or.inr (Or.inl ⟨active, left⟩)
      · exact Or.inr (Or.inr ⟨active, right⟩)
  · rintro (⟨r, hr, hx⟩ | ⟨active, left⟩ | ⟨active, right⟩)
    · have hp := split.mode.mem_removed r hr
      subst r
      exact ⟨roots.mpr (Or.inl ⟨point, hr, hx⟩), hx.symm ▸ hc⟩
    · have hne : x ≠ φ point := fun h => hnroot (h ▸ active)
      exact ⟨roots.mpr (Or.inr active), (interval_split _ _ _ _ hc hne).mpr (Or.inl left)⟩
    · have hne : x ≠ φ point := fun h => hnroot (h ▸ active)
      exact ⟨roots.mpr (Or.inr active), (interval_split _ _ _ _ hc hne).mpr (Or.inr right)⟩

end Hex.RealClosure.Bisection

/-- info: 'Hex.RealClosure.Bisection.Mode.leadingCoeff_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Mode.leadingCoeff_head

/-- info: 'Hex.RealClosure.Bisection.Mode.roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Mode.roots

/-- info: 'Hex.RealClosure.Bisection.Split.partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Split.partition
