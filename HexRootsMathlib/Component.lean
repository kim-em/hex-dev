/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Refine
public import HexRootsMathlib.Cauchy

public section

/-!
# Semantic regions and component invariants

This module records the companion-side invariants of certified results as
they re-enter the executable worklist. In particular, the doubled retained
square contains both possible atom regions and a cluster's circumscribed disc.
-/

namespace HexRootsMathlib

noncomputable section

namespace DyadicSquare

@[simp] theorem doubled_center (s : Hex.DyadicSquare) :
    center s.doubled = center s := rfl

@[simp] theorem doubled_prec (s : Hex.DyadicSquare) :
    s.doubled.prec = s.prec - 1 := rfl

@[simp] theorem doubled_halfWidth (s : Hex.DyadicSquare) :
    halfWidth s.doubled = 2 * halfWidth s := by
  rw [halfWidth_eq, halfWidth_eq, doubled_prec]
  rw [show -(s.prec - 1) = 1 + -s.prec by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

/-- A square is contained in its concentric doubled square. -/
theorem closedSquare_subset_doubled (s : Hex.DyadicSquare) :
    closedSquare s ⊆ closedSquare s.doubled := by
  intro z hz
  change supDist z (center s) ≤ halfWidth s at hz
  change supDist z (center s.doubled) ≤ halfWidth s.doubled
  rw [doubled_center, doubled_halfWidth]
  exact hz.trans (by
    have hwidth : 0 ≤ halfWidth s := by
      rw [halfWidth_eq]
      positivity
    linarith)

/-- The circumscribed closed disc is contained in the concentric doubled
square; this is the geometric reason certified re-entry must double. -/
theorem closedDisc_subset_doubled (s : Hex.DyadicSquare) :
    closedDisc s ⊆ closedSquare s.doubled := by
  intro z hz
  rw [closedDisc, Metric.mem_closedBall, Complex.dist_eq] at hz
  change supNorm (z - center s.doubled) ≤ halfWidth s.doubled
  rw [doubled_center, doubled_halfWidth]
  have hsqrt : √2 < (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg 2]
  have hwidth : 0 < halfWidth s := by
    rw [halfWidth_eq]
    positivity
  apply le_of_lt
  calc
    supNorm (z - center s) ≤ ‖z - center s‖ :=
      max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
    _ ≤ radius s := hz
    _ = halfWidth s * √2 := rfl
    _ < halfWidth s * 2 := mul_lt_mul_of_pos_left hsqrt hwidth
    _ = 2 * halfWidth s := by ring

end DyadicSquare

namespace Component

/-- The structural invariant actually required of a worklist component:
there is a first square and every square has its precision. Connectivity is
an algorithmic optimization and is not needed by soundness. -/
@[expose] def WellFormed (c : Hex.Component) : Prop :=
  0 < c.squares.size ∧
    ∀ s ∈ c.squares.toList, s.prec = c.prec

/-- The union of the closed squares retained by a component. -/
@[expose] def region (c : Hex.Component) : Set ℂ :=
  {z | ∃ s ∈ c.squares.toList, z ∈ DyadicSquare.closedSquare s}

/-- The initial Cauchy component is a nonempty singleton component. -/
theorem cauchy_wellFormed (p : Hex.ZPoly) (h : 0 < p.degree?.getD 0) :
    WellFormed (Hex.Component.cauchy p h) := by
  simp [WellFormed, Hex.Component.cauchy, Hex.Component.prec]

/-- Component-level restatement of executable Cauchy coverage. -/
theorem isRoot_mem_cauchy (p : Hex.ZPoly) (h : 0 < p.degree?.getD 0)
    {z : ℂ} (hz : (toPolyℂ p).IsRoot z) :
    z ∈ region (Hex.Component.cauchy p h) :=
  exists_mem_component_cauchy p h hz

/-- The executable enclosing square contains the union of all input squares,
without a common-precision or connectivity hypothesis. -/
theorem region_subset_encSquare (c : Hex.Component) :
    region c ⊆ DyadicSquare.closedSquare (Hex.encSquare c.squares) := by
  rintro z ⟨s, hs, hz⟩
  exact DyadicSquare.closedSquare_subset_encSquare hs hz

/-- The doubled enclosing square used by NK certification contains the whole
input component region. -/
theorem region_subset_doubledEnc (c : Hex.Component) :
    region c ⊆ DyadicSquare.closedSquare (Hex.encSquare c.squares).doubled :=
  (region_subset_encSquare c).trans
    (DyadicSquare.closedSquare_subset_doubled (Hex.encSquare c.squares))

end Component

namespace DyadicRootIsolation

/-- The certified region selected by an atom witness. If both disjuncts hold,
the Newton square is chosen; either choice contains the same unique root once
both semantic developments are available. -/
@[expose] def region {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p) : Set ℂ :=
  if Hex.nkWitness p iso.square then
    DyadicSquare.closedSquare iso.square
  else
    DyadicSquare.closedDisc iso.square

end DyadicRootIsolation

namespace Certified

/-- The region whose root count is asserted by a certified result. -/
@[expose] def region {p : Hex.ZPoly} : Hex.Certified p → Set ℂ
  | .atom iso => DyadicRootIsolation.region iso
  | .cluster cl => DyadicSquare.closedDisc (Hex.encSquare cl.squares)

/-- The root count carried by a certified result. -/
@[expose] def count {p : Hex.ZPoly} : Hex.Certified p → Nat
  | .atom _ => 1
  | .cluster cl => cl.k

theorem count_pos {p : Hex.ZPoly} (r : Hex.Certified p) : 0 < count r := by
  cases r with
  | atom => simp [count]
  | cluster cl => exact cl.k_pos

@[simp] theorem toComponent_squares {p : Hex.ZPoly} (r : Hex.Certified p) :
    r.toComponent.squares = #[r.square.doubled] := by
  cases r <;> rfl

@[simp] theorem toComponent_count {p : Hex.ZPoly} (r : Hex.Certified p) :
    r.toComponent.candidateK = count r := by
  cases r <;> rfl

@[simp] theorem toComponent_prec {p : Hex.ZPoly} (r : Hex.Certified p) :
    r.toComponent.prec = r.square.prec - 1 := by
  cases r <;> simp [Hex.Certified.toComponent, Hex.Certified.square,
    Hex.Component.prec]

@[simp] theorem toComponent_region {p : Hex.ZPoly} (r : Hex.Certified p) :
    Component.region r.toComponent =
      DyadicSquare.closedSquare r.square.doubled := by
  ext z
  simp [Component.region]

/-- Re-entry always constructs a nonempty common-precision component. -/
theorem toComponent_wellFormed {p : Hex.ZPoly} (r : Hex.Certified p) :
    Component.WellFormed r.toComponent := by
  simp [Component.WellFormed, Hex.Component.prec]

theorem toComponent_count_pos {p : Hex.ZPoly} (r : Hex.Certified p) :
    0 < r.toComponent.candidateK := by
  rw [toComponent_count]
  exact count_pos r

/-- The doubled square retained on re-entry contains the certified region,
for both atom certificate forms and for clusters. -/
theorem region_subset_doubled {p : Hex.ZPoly} (r : Hex.Certified p) :
    region r ⊆ DyadicSquare.closedSquare r.square.doubled := by
  cases r with
  | atom iso =>
      simp only [region, DyadicRootIsolation.region, Hex.Certified.square]
      split
      · exact DyadicSquare.closedSquare_subset_doubled iso.square
      · exact DyadicSquare.closedDisc_subset_doubled iso.square
  | cluster cl =>
      exact DyadicSquare.closedDisc_subset_doubled (Hex.encSquare cl.squares)

/-- Re-entry contains the stored square, independently of certificate form. -/
theorem square_subset_toComponent {p : Hex.ZPoly} (r : Hex.Certified p) :
    DyadicSquare.closedSquare r.square ⊆ Component.region r.toComponent := by
  rw [toComponent_region]
  exact DyadicSquare.closedSquare_subset_doubled r.square

/-- Re-entry contains the stored circumscribed disc, independently of
certificate form. This stronger conservative fact is useful to the loop
kernel, which need not inspect the atom-witness disjunction. -/
theorem disc_subset_toComponent {p : Hex.ZPoly} (r : Hex.Certified p) :
    DyadicSquare.closedDisc r.square ⊆ Component.region r.toComponent := by
  rw [toComponent_region]
  exact DyadicSquare.closedDisc_subset_doubled r.square

/-- The worklist region of `toComponent` contains the certified region. -/
theorem region_subset_toComponent {p : Hex.ZPoly} (r : Hex.Certified p) :
    region r ⊆ Component.region r.toComponent := by
  rw [toComponent_region]
  exact region_subset_doubled r

end Certified

end

end HexRootsMathlib
