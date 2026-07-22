/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.SimpleRoot
public import HexRootsMathlib.Certificate
public import HexRootsMathlib.Driver
public import HexRootsMathlib.HasOnlySimpleRoots
public import HexRootsMathlib.MahlerPrec

public section

/-!
# Semantic identity of isolated simple roots

Every refined atom has a canonical complex root. Under the rational-cast
separability hypothesis used by the Mahler bound, the executable disc
intersection relation is exactly equality of these roots.
-/

open Complex Metric Polynomial Set

namespace HexRootsMathlib

noncomputable section

namespace RefinedIsolation

/-- The unique root in a refined isolation's selected certified region. -/
@[expose] noncomputable def root {p : Hex.ZPoly} (i : Hex.RefinedIsolation p) : ℂ :=
  (DyadicRootIsolation.sound i.1).choose

/-- The selected root is a simple polynomial root, interior to the selected
region and unique in its closed counterpart. -/
theorem root_spec {p : Hex.ZPoly} (i : Hex.RefinedIsolation p) :
    (toPolyℂ p).eval (root i) = 0 ∧
      root i ∈ DyadicRootIsolation.openRegion i.1 ∧
      (toPolyℂ p).derivative.eval (root i) ≠ 0 ∧
      ∀ w, (toPolyℂ p).eval w = 0 →
        w ∈ DyadicRootIsolation.region i.1 → w = root i :=
  (DyadicRootIsolation.sound i.1).choose_spec

theorem isRoot {p : Hex.ZPoly} (i : Hex.RefinedIsolation p) :
    (toPolyℂ p).IsRoot (root i) :=
  (root_spec i).1

/-- The semantic root lies in its atom's selected closed region. -/
theorem root_mem_region {p : Hex.ZPoly} (i : Hex.RefinedIsolation p) :
    root i ∈ DyadicRootIsolation.region i.1 :=
  DyadicRootIsolation.openRegion_subset_region i.1 (root_spec i).2.1

/-- Both atom witness forms place the semantic root in the stored square's
circumscribed disc. -/
theorem root_mem_closedDisc {p : Hex.ZPoly} (i : Hex.RefinedIsolation p) :
    root i ∈ DyadicSquare.closedDisc i.1.square := by
  apply Certified.region_subset_closedDisc (.atom i.1)
  exact root_mem_region i

private theorem radius_lt_quarter {p : Hex.ZPoly}
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (i : Hex.RefinedIsolation p) {z : ℂ}
    (hz : (toPolyℂ p).IsRoot z) (hne : root i ≠ z) :
    DyadicSquare.radius i.1.square < ‖root i - z‖ / 4 := by
  have hpow : (2 : ℝ) ^ (-i.1.square.prec) ≤
      (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) := by
    have hi := i.property
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hsqrt : √2 < (1449 / 1024 : ℝ) := by
    convert sqrt_two_lt_sqrt2Hi using 1
    norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
  calc
    DyadicSquare.radius i.1.square =
        (2 : ℝ) ^ (-i.1.square.prec) * √2 := DyadicSquare.radius_eq _
    _ < (2 : ℝ) ^ (-i.1.square.prec) * (1449 / 1024 : ℝ) :=
      mul_lt_mul_of_pos_left hsqrt (zpow_pos (by norm_num) _)
    _ ≤ (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ < ‖root i - z‖ / 4 :=
      mahlerPrec_separates p hsep (root i) z (isRoot i) hz hne

/-- At separation precision, executable disc intersection is exactly semantic
root equality. Global separability is explicit because a local atom witness
does not imply that every root of the polynomial is simple. -/
theorem intersects_iff_root_eq {p : Hex.ZPoly}
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (i₁ i₂ : Hex.RefinedIsolation p) :
    Hex.Intersects i₁ i₂ ↔ root i₁ = root i₂ := by
  constructor
  · intro hmeet
    by_contra hne
    have hr₁ := radius_lt_quarter hsep i₁ (isRoot i₂) hne
    have hr₂ := radius_lt_quarter hsep i₂ (isRoot i₁) (Ne.symm hne)
    rw [norm_sub_rev] at hr₂
    have hc : dist (DyadicSquare.center i₁.1.square)
        (DyadicSquare.center i₂.1.square) ≤
        DyadicSquare.radius i₁.1.square + DyadicSquare.radius i₂.1.square :=
      DyadicSquare.dist_center_le_of_discsMeet hmeet
    have hm₁ : dist (root i₁) (DyadicSquare.center i₁.1.square) ≤
        DyadicSquare.radius i₁.1.square := by
      simpa only [DyadicSquare.closedDisc, Metric.mem_closedBall] using
        root_mem_closedDisc i₁
    have hm₂ : dist (DyadicSquare.center i₂.1.square) (root i₂) ≤
        DyadicSquare.radius i₂.1.square := by
      rw [dist_comm]
      simpa only [DyadicSquare.closedDisc, Metric.mem_closedBall] using
        root_mem_closedDisc i₂
    have hdist : dist (root i₁) (root i₂) ≤
        2 * (DyadicSquare.radius i₁.1.square +
          DyadicSquare.radius i₂.1.square) := by
      calc
        dist (root i₁) (root i₂) ≤
            dist (root i₁) (DyadicSquare.center i₁.1.square) +
              dist (DyadicSquare.center i₁.1.square) (root i₂) :=
          dist_triangle _ _ _
        _ ≤ dist (root i₁) (DyadicSquare.center i₁.1.square) +
            (dist (DyadicSquare.center i₁.1.square)
              (DyadicSquare.center i₂.1.square) +
              dist (DyadicSquare.center i₂.1.square) (root i₂)) :=
          by
            simpa only [add_assoc] using
              add_le_add_right (dist_triangle (DyadicSquare.center i₁.1.square)
                (DyadicSquare.center i₂.1.square) (root i₂))
                (dist (root i₁) (DyadicSquare.center i₁.1.square))
        _ ≤ DyadicSquare.radius i₁.1.square +
            ((DyadicSquare.radius i₁.1.square +
              DyadicSquare.radius i₂.1.square) +
              DyadicSquare.radius i₂.1.square) :=
          add_le_add hm₁ (add_le_add hc hm₂)
        _ = 2 * (DyadicSquare.radius i₁.1.square +
            DyadicSquare.radius i₂.1.square) := by ring
    have hnorm : dist (root i₁) (root i₂) = ‖root i₁ - root i₂‖ :=
      Complex.dist_eq _ _
    rw [hnorm] at hdist
    have : ‖root i₁ - root i₂‖ < ‖root i₁ - root i₂‖ := by
      nlinarith [hr₁, hr₂]
    exact (lt_irrefl _ this)
  · intro hroot
    by_contra hnot
    change ¬i₁.1.square.discsMeet i₂.1.square = true at hnot
    have hfalse : i₁.1.square.discsMeet i₂.1.square = false :=
      Bool.eq_false_of_not_eq_true hnot
    have hdisj := DyadicSquare.closedDisc_disjoint_of_discsMeet_eq_false
      i₁.1.square i₂.1.square hfalse
    exact (Set.disjoint_left.mp hdisj) (root_mem_closedDisc i₁)
      (hroot ▸ root_mem_closedDisc i₂)

/-- Under separability, `Intersects` is an equivalence relation on refined
isolations. -/
theorem intersects_equivalence {p : Hex.ZPoly}
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable) :
    Equivalence (@Hex.Intersects p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (intersects_iff_root_eq hsep i i).mpr rfl
  · intro i j hij
    have hroot := (intersects_iff_root_eq hsep i j).mp hij
    exact (intersects_iff_root_eq hsep j i).mpr hroot.symm
  · intro i j k hij hjk
    exact (intersects_iff_root_eq hsep i k).mpr <|
      (intersects_iff_root_eq hsep i j).mp hij |>.trans
        ((intersects_iff_root_eq hsep j k).mp hjk)

/-- Executable simple-root input supplies the separation hypothesis needed by
the intersection semantics. -/
theorem intersects_iff_root_eq_of_simple {p : Hex.ZPoly}
    (h : Hex.HasOnlySimpleRoots p) (hp : p ≠ 0)
    (i₁ i₂ : Hex.RefinedIsolation p) :
    Hex.Intersects i₁ i₂ ↔ root i₁ = root i₂ :=
  intersects_iff_root_eq (HasOnlySimpleRoots.separable h hp) i₁ i₂

end RefinedIsolation

namespace SimpleRoot

/-- Interpret a quotient root as its complex value. Separability makes the
stored intersection relation respect semantic root equality. -/
@[expose] noncomputable def rootOf {p : Hex.ZPoly}
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable) : Hex.SimpleRoot p → ℂ :=
  Quot.lift RefinedIsolation.root fun i j hij =>
    (RefinedIsolation.intersects_iff_root_eq hsep i j).mp hij

@[simp] theorem rootOf_mk {p : Hex.ZPoly}
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (i : Hex.RefinedIsolation p) :
    rootOf hsep (Hex.SimpleRoot.mk i) = RefinedIsolation.root i := rfl

end SimpleRoot

namespace RefinedIsolation

/-- The executable Boolean test is the proposition `Intersects`. -/
theorem sameRoot_eq_true_iff {p : Hex.ZPoly} (i₁ i₂ : Hex.RefinedIsolation p) :
    i₁.sameRoot i₂ = true ↔ Hex.Intersects i₁ i₂ := Iff.rfl

/-- Under separability, the executable test decides equality in the quotient
of refined isolations. -/
theorem sameRoot_iff_mk_eq {p : Hex.ZPoly}
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (i₁ i₂ : Hex.RefinedIsolation p) :
    i₁.sameRoot i₂ = true ↔ Hex.SimpleRoot.mk i₁ = Hex.SimpleRoot.mk i₂ := by
  rw [sameRoot_eq_true_iff]
  constructor
  · exact Quot.sound
  · intro heq
    apply (intersects_iff_root_eq hsep i₁ i₂).mpr
    simpa only [SimpleRoot.rootOf_mk] using
      congrArg (SimpleRoot.rootOf hsep) heq

end RefinedIsolation

end

end HexRootsMathlib

namespace Hex.RefinedIsolation

/-- Field-notation alias for the companion's semantic root. -/
noncomputable abbrev root {p : Hex.ZPoly} (i : Hex.RefinedIsolation p) : ℂ :=
  HexRootsMathlib.RefinedIsolation.root i

end Hex.RefinedIsolation

namespace Hex

/-- Mathlib interpretation of a quotient simple root. -/
noncomputable abbrev rootOf {p : Hex.ZPoly}
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable) : Hex.SimpleRoot p → ℂ :=
  HexRootsMathlib.SimpleRoot.rootOf hsep

end Hex
