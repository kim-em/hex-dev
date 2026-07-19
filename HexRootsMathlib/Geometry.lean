/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Basic
public import Mathlib.Analysis.Complex.Norm

public section

/-!
# Geometry for complex root isolation

This module relates the executable modulus bounds and dyadic squares from
`HexRoots` to the Euclidean and sup-norm geometry of `ℂ`.
-/

namespace HexRootsMathlib

noncomputable section

namespace GaussDyadic

/-- The real value of the executable lower modulus bound. -/
@[simp] theorem toReal_lo (z : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.lo z) =
      max |(toComplex z).re| |(toComplex z).im| := by
  simp [Hex.GaussDyadic.lo]

/-- The real value of the executable upper modulus bound. -/
@[simp] theorem toReal_hi (z : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.hi z) =
      |(toComplex z).re| + |(toComplex z).im| := by
  simp [Hex.GaussDyadic.hi]

/-- The executable `lo` bound is below the complex modulus. -/
theorem lo_le_norm (z : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.lo z) ≤ ‖toComplex z‖ := by
  rw [toReal_lo]
  exact max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

/-- The complex modulus is at most `√2` times the executable `lo` bound. -/
theorem norm_le_sqrt_two_mul_lo (z : Hex.GaussDyadic) :
    ‖toComplex z‖ ≤ √2 * Dyadic.toReal (Hex.GaussDyadic.lo z) := by
  simpa only [toReal_lo] using Complex.norm_le_sqrt_two_mul_max (toComplex z)

/-- The complex modulus is below the executable `hi` bound. -/
theorem norm_le_hi (z : Hex.GaussDyadic) :
    ‖toComplex z‖ ≤ Dyadic.toReal (Hex.GaussDyadic.hi z) := by
  rw [toReal_hi]
  exact Complex.norm_le_abs_re_add_abs_im _

/-- The executable `hi` bound is at most `√2` times the complex modulus. -/
theorem hi_le_sqrt_two_mul_norm (z : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.hi z) ≤ √2 * ‖toComplex z‖ := by
  rw [toReal_hi]
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  have hre : |(toComplex z).re| ^ 2 = (toComplex z).re ^ 2 := sq_abs _
  have him : |(toComplex z).im| ^ 2 = (toComplex z).im ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|(toComplex z).re| - |(toComplex z).im|)]

end GaussDyadic

/-! ### Rational bounds for `√2` -/

/-- The executable lower approximation `181/128` is strictly below `√2`. -/
theorem sqrt2Lo_lt_sqrt_two : Dyadic.toReal Hex.sqrt2Lo < √2 := by
  rw [← sq_lt_sq₀ (by
    simp [Hex.sqrt2Lo, Dyadic.toReal_ofIntWithPrec]
    positivity) (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
  have h := Dyadic.toReal_lt_toReal_iff.mpr Hex.sqrt2Lo_sq_lt_two
  have htwo : Dyadic.toReal (2 : _root_.Dyadic) = (2 : ℝ) := by
    change Dyadic.toReal (.ofInt 2) = (2 : ℝ)
    simp
  rw [htwo] at h
  simpa only [Dyadic.toReal_mul, pow_two] using h

/-- The executable upper approximation `1449/1024` is strictly above `√2`. -/
theorem sqrt_two_lt_sqrt2Hi : √2 < Dyadic.toReal Hex.sqrt2Hi := by
  rw [← sq_lt_sq₀ (Real.sqrt_nonneg _) (by
    simp [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    positivity), Real.sq_sqrt (by norm_num)]
  have h := Dyadic.toReal_lt_toReal_iff.mpr Hex.two_lt_sqrt2Hi_sq
  have htwo : Dyadic.toReal (2 : _root_.Dyadic) = (2 : ℝ) := by
    change Dyadic.toReal (.ofInt 2) = (2 : ℝ)
    simp
  rw [htwo] at h
  simpa only [Dyadic.toReal_mul, pow_two] using h

/-! ### Sup-norm squares and circumscribed discs -/

namespace SquareBounds

/-- A computed bounding box contains the full coordinate extent of a square. -/
def Contains (b : Hex.SquareBounds) (s : Hex.DyadicSquare) : Prop :=
  Dyadic.toReal b.xmin ≤ Dyadic.toReal (s.re - s.halfWidth) ∧
  Dyadic.toReal (s.re + s.halfWidth) ≤ Dyadic.toReal b.xmax ∧
  Dyadic.toReal b.ymin ≤ Dyadic.toReal (s.im - s.halfWidth) ∧
  Dyadic.toReal (s.im + s.halfWidth) ≤ Dyadic.toReal b.ymax

theorem bounds_contains (s : Hex.DyadicSquare) : Contains s.bounds s := by
  simp [Contains, Hex.DyadicSquare.bounds]

theorem contains_merge_left {b : Hex.SquareBounds} {s t : Hex.DyadicSquare}
    (h : Contains b s) : Contains (b.merge t) s := by
  rcases h with ⟨hxlo, hxhi, hylo, hyhi⟩
  simp only [Contains, Hex.SquareBounds.merge, Hex.DyadicSquare.bounds,
    Dyadic.toReal_min, Dyadic.toReal_max]
  exact ⟨min_le_left _ _ |>.trans hxlo, hxhi.trans (le_max_left _ _),
    min_le_left _ _ |>.trans hylo, hyhi.trans (le_max_left _ _)⟩

theorem contains_merge_right (b : Hex.SquareBounds) (s : Hex.DyadicSquare) :
    Contains (b.merge s) s := by
  simp only [Contains, Hex.SquareBounds.merge, Hex.DyadicSquare.bounds,
    Dyadic.toReal_min, Dyadic.toReal_max]
  exact ⟨min_le_right _ _, le_max_right _ _, min_le_right _ _, le_max_right _ _⟩

theorem contains_extend_old {b : Option Hex.SquareBounds} {s t : Hex.DyadicSquare}
    (h : ∃ box, b = some box ∧ Contains box s) :
    ∃ box, Hex.SquareBounds.extend b t = some box ∧ Contains box s := by
  obtain ⟨box, rfl, hs⟩ := h
  exact ⟨box.merge t, rfl, contains_merge_left hs⟩

theorem contains_extend_new (b : Option Hex.SquareBounds) (s : Hex.DyadicSquare) :
    ∃ box, Hex.SquareBounds.extend b s = some box ∧ Contains box s := by
  cases b with
  | none => exact ⟨s.bounds, rfl, bounds_contains s⟩
  | some box => exact ⟨box.merge s, rfl, contains_merge_right box s⟩

private theorem contains_foldl (l : List Hex.DyadicSquare)
    (b : Option Hex.SquareBounds) {s : Hex.DyadicSquare}
    (h : (∃ box, b = some box ∧ Contains box s) ∨ s ∈ l) :
    ∃ box, l.foldl Hex.SquareBounds.extend b = some box ∧ Contains box s := by
  induction l generalizing b with
  | nil =>
      rcases h with h | h
      · simpa using h
      · simp at h
  | cons t l ih =>
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | h
      · exact Or.inl (contains_extend_old h)
      · rw [List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inl (contains_extend_new b _)
        · exact Or.inr h

/-- Every input square is contained in the exact bounding box returned by the
executable fold. -/
theorem mem_boundingBox {squares : Array Hex.DyadicSquare}
    {s : Hex.DyadicSquare} (hs : s ∈ squares.toList) :
    ∃ box, Hex.boundingBox squares = some box ∧ Contains box s := by
  rw [Hex.boundingBox, ← Array.foldl_toList]
  exact contains_foldl squares.toList none (Or.inr hs)

end SquareBounds

/-- The sup norm on `ℂ`, used to view an axis-aligned square as a ball. -/
@[expose] def supNorm (z : ℂ) : ℝ := max |z.re| |z.im|

/-- The complex sup norm satisfies the triangle inequality. -/
theorem supNorm_add_le (z w : ℂ) :
    supNorm (z + w) ≤ supNorm z + supNorm w := by
  apply max_le
  · calc
      |(z + w).re| ≤ |z.re| + |w.re| := abs_add_le _ _
      _ ≤ max |z.re| |z.im| + max |w.re| |w.im| :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc
      |(z + w).im| ≤ |z.im| + |w.im| := abs_add_le _ _
      _ ≤ max |z.re| |z.im| + max |w.re| |w.im| :=
        add_le_add (le_max_right _ _) (le_max_right _ _)

/-- The distance associated to `supNorm`. -/
@[expose] def supDist (z w : ℂ) : ℝ := supNorm (z - w)

/-- A closed sup-norm ball in `ℂ`. -/
@[expose] def supClosedBall (c : ℂ) (r : ℝ) : Set ℂ :=
  {z | supDist z c ≤ r}

/-- An open sup-norm ball in `ℂ`. -/
@[expose] def supOpenBall (c : ℂ) (r : ℝ) : Set ℂ :=
  {z | supDist z c < r}

namespace DyadicSquare

/-
These names deliberately mirror `Hex.DyadicSquare.center` and `halfWidth`.
Dot notation on `s : Hex.DyadicSquare` selects the executable definitions;
the Mathlib interpretations use the explicit `DyadicSquare.*` prefix.
-/

/-- The complex centre of a dyadic square. -/
@[expose] def center (s : Hex.DyadicSquare) : ℂ :=
  GaussDyadic.toComplex s.center

/-- The real half-width of a dyadic square. -/
@[expose] def halfWidth (s : Hex.DyadicSquare) : ℝ :=
  Dyadic.toReal s.halfWidth

/-- The Euclidean radius of the square's circumscribed disc. -/
@[expose] def radius (s : Hex.DyadicSquare) : ℝ :=
  halfWidth s * √2

/-- The closed axis-aligned square represented by `s`. -/
@[expose] def closedSquare (s : Hex.DyadicSquare) : Set ℂ :=
  supClosedBall (center s) (halfWidth s)

/-- The interior of the axis-aligned square represented by `s`. -/
@[expose] def openSquare (s : Hex.DyadicSquare) : Set ℂ :=
  supOpenBall (center s) (halfWidth s)

/-- The open circumscribed disc of `s`. -/
@[expose] def disc (s : Hex.DyadicSquare) : Set ℂ :=
  Metric.ball (center s) (radius s)

/-- The closed circumscribed disc of `s`. -/
@[expose] def closedDisc (s : Hex.DyadicSquare) : Set ℂ :=
  Metric.closedBall (center s) (radius s)

@[simp] theorem center_eq (s : Hex.DyadicSquare) :
    center s = GaussDyadic.toComplex s.center := rfl

@[simp] theorem halfWidth_eq (s : Hex.DyadicSquare) :
    halfWidth s = (2 : ℝ) ^ (-s.prec) := by
  simp [halfWidth, Hex.DyadicSquare.halfWidth]

@[simp] theorem radius_eq (s : Hex.DyadicSquare) :
    radius s = (2 : ℝ) ^ (-s.prec) * √2 := by
  simp [radius]

@[simp] theorem disc_eq (s : Hex.DyadicSquare) :
    disc s = Metric.ball (center s) ((2 : ℝ) ^ (-s.prec) * √2) := by
  simp [disc]

theorem closedSquare_eq_supClosedBall (s : Hex.DyadicSquare) :
    closedSquare s = supClosedBall (center s) (halfWidth s) := rfl

/-- The centre belongs to its closed square. -/
theorem center_mem_closedSquare (s : Hex.DyadicSquare) : center s ∈ closedSquare s := by
  rw [closedSquare, supClosedBall, Set.mem_setOf_eq, supDist, sub_self, supNorm]
  simp only [Complex.zero_re, abs_zero, Complex.zero_im, max_self]
  rw [halfWidth_eq]
  exact (zpow_pos (by norm_num) _).le

theorem radiusLo_eq (s : Hex.DyadicSquare) :
    Dyadic.toReal s.radiusLo = halfWidth s * Dyadic.toReal Hex.sqrt2Lo := by
  simp only [Hex.DyadicSquare.radiusLo, Hex.sqrt2Lo, Dyadic.toReal_ofIntWithPrec,
    halfWidth_eq]
  rw [show -(s.prec + 7) = -s.prec + (-7) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem radiusHi_eq (s : Hex.DyadicSquare) :
    Dyadic.toReal s.radiusHi = halfWidth s * Dyadic.toReal Hex.sqrt2Hi := by
  simp only [Hex.DyadicSquare.radiusHi, Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec,
    halfWidth_eq]
  rw [show -(s.prec + 10) = -s.prec + (-10) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem radiusLo_lt_radius (s : Hex.DyadicSquare) :
    Dyadic.toReal s.radiusLo < radius s := by
  rw [radiusLo_eq, radius]
  apply mul_lt_mul_of_pos_left sqrt2Lo_lt_sqrt_two
  rw [halfWidth_eq]
  exact zpow_pos (by norm_num) _

theorem radius_lt_radiusHi (s : Hex.DyadicSquare) :
    radius s < Dyadic.toReal s.radiusHi := by
  rw [radiusHi_eq, radius]
  apply mul_lt_mul_of_pos_left sqrt_two_lt_sqrt2Hi
  rw [halfWidth_eq]
  exact zpow_pos (by norm_num) _

/-- The exact executable squared centre distance casts to the square of the
Euclidean distance. -/
@[simp] theorem toReal_distSq (z w : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.distSq z w) =
      dist (GaussDyadic.toComplex z) (GaussDyadic.toComplex w) ^ 2 := by
  simp [Hex.GaussDyadic.distSq, Complex.dist_eq, Complex.sq_norm]

/-- A negative executable disc-intersection test certifies disjoint closed
circumscribed discs. -/
theorem closedDisc_disjoint_of_discsMeet_eq_false (s t : Hex.DyadicSquare)
    (h : s.discsMeet t = false) : Disjoint (closedDisc s) (closedDisc t) := by
  have hnot : ¬ Hex.GaussDyadic.distSq s.center t.center ≤
      (2 : _root_.Dyadic) * .ofIntWithPrec 1 (2 * s.prec) +
        2 * .ofIntWithPrec 1 (2 * t.prec) +
        4 * .ofIntWithPrec 1 (s.prec + t.prec) := by
    simpa [Hex.DyadicSquare.discsMeet] using h
  have hrealnot : ¬ Dyadic.toReal (Hex.GaussDyadic.distSq s.center t.center) ≤
      Dyadic.toReal ((2 : _root_.Dyadic) * .ofIntWithPrec 1 (2 * s.prec) +
        2 * .ofIntWithPrec 1 (2 * t.prec) +
        4 * .ofIntWithPrec 1 (s.prec + t.prec)) := by
    simpa only [Dyadic.toReal_le_toReal_iff] using hnot
  have hlt := lt_of_not_ge hrealnot
  have hs : (2 : ℝ) ^ (-(2 * s.prec)) = ((2 : ℝ) ^ (-s.prec)) ^ 2 := by
    rw [show -(2 * s.prec) = (-s.prec) * 2 by ring, zpow_mul]
    rfl
  have ht : (2 : ℝ) ^ (-(2 * t.prec)) = ((2 : ℝ) ^ (-t.prec)) ^ 2 := by
    rw [show -(2 * t.prec) = (-t.prec) * 2 by ring, zpow_mul]
    rfl
  have hst : (2 : ℝ) ^ (-(s.prec + t.prec)) =
      (2 : ℝ) ^ (-s.prec) * (2 : ℝ) ^ (-t.prec) := by
    rw [show -(s.prec + t.prec) = -s.prec + -t.prec by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have htwo : Dyadic.toReal (2 : _root_.Dyadic) = (2 : ℝ) :=
    Dyadic.toReal_two
  have hfour : Dyadic.toReal (4 : _root_.Dyadic) = (4 : ℝ) := by
    change Dyadic.toReal (.ofInt 4) = (4 : ℝ)
    simp
  have hradii : (radius s + radius t) ^ 2 <
      dist (center s) (center t) ^ 2 := by
    rw [radius_eq, radius_eq]
    calc
      ((2 : ℝ) ^ (-s.prec) * √2 + (2 : ℝ) ^ (-t.prec) * √2) ^ 2 =
          2 * ((2 : ℝ) ^ (-s.prec)) ^ 2 +
          2 * ((2 : ℝ) ^ (-t.prec)) ^ 2 +
          4 * ((2 : ℝ) ^ (-s.prec) * (2 : ℝ) ^ (-t.prec)) := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ < _ := by
        simpa only [Dyadic.toReal_add, Dyadic.toReal_mul,
          Dyadic.toReal_ofIntWithPrec, Dyadic.toReal_ofInt, Int.cast_one,
          one_mul, Int.cast_ofNat, toReal_distSq, Hex.DyadicSquare.center,
          center_eq, hs, ht, hst, htwo, hfour] using hlt
  apply Metric.closedBall_disjoint_closedBall
  have hrs : 0 ≤ radius s + radius t := by
    simp only [radius_eq]
    exact add_nonneg
      (mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
        (Real.sqrt_nonneg _))
      (mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
        (Real.sqrt_nonneg _))
  exact (sq_lt_sq₀ hrs dist_nonneg).mp hradii

/-- The executable array test gives semantic disjointness for every ordered
pair of stored squares. -/
theorem closedDisc_disjoint_of_pairwiseDisjoint {ss : Array Hex.DyadicSquare}
    (h : Hex.pairwiseDisjoint ss = true) {i j : Nat}
    (hi : i < ss.size) (hj : j < ss.size) (hij : i < j) :
    Disjoint (closedDisc ss[i]) (closedDisc ss[j]) := by
  have hiAll := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  have hijAll := (List.all_eq_true.mp hiAll) j (List.mem_range.mpr hj)
  simp only [hij, ↓reduceIte] at hijAll
  have hgeti : ss.getD i ⟨0, 0, 0⟩ = ss[i] := by
    exact (Array.getElem_eq_getD (Hex.DyadicSquare.mk 0 0 0)).symm
  have hgetj : ss.getD j ⟨0, 0, 0⟩ = ss[j] := by
    exact (Array.getElem_eq_getD (Hex.DyadicSquare.mk 0 0 0)).symm
  rw [hgeti, hgetj] at hijAll
  exact closedDisc_disjoint_of_discsMeet_eq_false _ _
    (Bool.eq_false_of_not_eq_true' hijAll)

/-- The exact executable disc-containment check implies containment of the
represented closed circumscribed discs. -/
theorem closedDisc_subset_of_discInside {inner outer : Hex.DyadicSquare}
    (h : inner.discInside outer = true) :
    closedDisc inner ⊆ closedDisc outer := by
  have hdata : outer.prec ≤ inner.prec ∧
      Hex.GaussDyadic.distSq inner.center outer.center ≤
        (2 : _root_.Dyadic) * .ofIntWithPrec 1 (2 * outer.prec) +
          2 * .ofIntWithPrec 1 (2 * inner.prec) -
          4 * .ofIntWithPrec 1 (outer.prec + inner.prec) := by
    simpa [Hex.DyadicSquare.discInside] using of_decide_eq_true h
  have hradius : radius inner ≤ radius outer := by
    rw [radius_eq, radius_eq]
    apply mul_le_mul_of_nonneg_right
    · exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    · exact Real.sqrt_nonneg _
  have hreal := Dyadic.toReal_le_toReal_iff.mpr hdata.2
  have ho : (2 : ℝ) ^ (-(2 * outer.prec)) =
      ((2 : ℝ) ^ (-outer.prec)) ^ 2 := by
    rw [show -(2 * outer.prec) = (-outer.prec) * 2 by ring, zpow_mul]
    rfl
  have hi : (2 : ℝ) ^ (-(2 * inner.prec)) =
      ((2 : ℝ) ^ (-inner.prec)) ^ 2 := by
    rw [show -(2 * inner.prec) = (-inner.prec) * 2 by ring, zpow_mul]
    rfl
  have hoi : (2 : ℝ) ^ (-(outer.prec + inner.prec)) =
      (2 : ℝ) ^ (-outer.prec) * (2 : ℝ) ^ (-inner.prec) := by
    rw [show -(outer.prec + inner.prec) = -outer.prec + -inner.prec by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have htwo : Dyadic.toReal (2 : _root_.Dyadic) = (2 : ℝ) :=
    Dyadic.toReal_two
  have hfour : Dyadic.toReal (4 : _root_.Dyadic) = (4 : ℝ) := by
    change Dyadic.toReal (.ofInt 4) = (4 : ℝ)
    simp
  have hdistSq : dist (center inner) (center outer) ^ 2 ≤
      (radius outer - radius inner) ^ 2 := by
    rw [radius_eq, radius_eq]
    calc
      dist (center inner) (center outer) ^ 2 ≤
          2 * ((2 : ℝ) ^ (-outer.prec)) ^ 2 +
            2 * ((2 : ℝ) ^ (-inner.prec)) ^ 2 -
            4 * ((2 : ℝ) ^ (-outer.prec) * (2 : ℝ) ^ (-inner.prec)) := by
        simpa only [Dyadic.toReal_add, Dyadic.toReal_sub, Dyadic.toReal_mul,
          Dyadic.toReal_ofIntWithPrec, Dyadic.toReal_ofInt, Int.cast_one,
          one_mul, Int.cast_ofNat, toReal_distSq, Hex.DyadicSquare.center,
          center_eq, ho, hi, hoi, htwo, hfour] using hreal
      _ = ((2 : ℝ) ^ (-outer.prec) * √2 -
          (2 : ℝ) ^ (-inner.prec) * √2) ^ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hdist : dist (center inner) (center outer) ≤
      radius outer - radius inner := by
    apply (sq_le_sq₀ dist_nonneg (sub_nonneg.mpr hradius)).mp
    exact hdistSq
  intro z hz
  rw [closedDisc, Metric.mem_closedBall] at hz ⊢
  calc
    dist z (center outer) ≤ dist z (center inner) +
        dist (center inner) (center outer) := dist_triangle _ _ _
    _ ≤ radius inner + (radius outer - radius inner) := add_le_add hz hdist
    _ = radius outer := by ring

/-- The exact executable square-containment check implies containment of the
represented closed sup-norm squares. -/
theorem closedSquare_subset_of_squareInside {inner outer : Hex.DyadicSquare}
    (h : inner.squareInside outer = true) :
    closedSquare inner ⊆ closedSquare outer := by
  have hdy : Hex.Dyadic.max
        (Hex.Dyadic.abs (inner.re - outer.re))
        (Hex.Dyadic.abs (inner.im - outer.im)) + inner.halfWidth ≤
      outer.halfWidth := by
    simpa [Hex.DyadicSquare.squareInside] using h
  have hreal := Dyadic.toReal_le_toReal_iff.mpr hdy
  have hwidth (s : Hex.DyadicSquare) :
      Dyadic.toReal s.halfWidth = halfWidth s := by
    simp [Hex.DyadicSquare.halfWidth, halfWidth_eq]
  intro z hz
  change supNorm (z - center inner) ≤ halfWidth inner at hz
  change supNorm (z - center outer) ≤ halfWidth outer
  calc
    supNorm (z - center outer) =
        supNorm ((z - center inner) + (center inner - center outer)) := by
      congr 1
      ring
    _ ≤ supNorm (z - center inner) + supNorm (center inner - center outer) :=
      supNorm_add_le _ _
    _ ≤ halfWidth inner + supNorm (center inner - center outer) :=
      add_le_add hz le_rfl
    _ = supNorm (center inner - center outer) + halfWidth inner := add_comm _ _
    _ ≤ halfWidth outer := by
      simpa only [Dyadic.toReal_add, Dyadic.toReal_max, Dyadic.toReal_abs,
        Dyadic.toReal_sub, hwidth, center, GaussDyadic.toComplex_re,
        GaussDyadic.toComplex_im, Hex.DyadicSquare.center, Complex.sub_re,
        Complex.sub_im, supNorm] using hreal

/-- Every input square is contained in the power-of-two square constructed
from its array's exact bounding box. -/
theorem closedSquare_subset_encSquare {squares : Array Hex.DyadicSquare}
    {s : Hex.DyadicSquare} (hs : s ∈ squares.toList) :
    closedSquare s ⊆ closedSquare (Hex.encSquare squares) := by
  obtain ⟨b, hbox, hb⟩ := SquareBounds.mem_boundingBox hs
  rcases hb with ⟨hxlo, hxhi, hylo, hyhi⟩
  let xhalf := (b.xmax - b.xmin) >>> (1 : Int)
  let yhalf := (b.ymax - b.ymin) >>> (1 : Int)
  let w := Hex.Dyadic.max xhalf yhalf
  have hwidth (u : Hex.DyadicSquare) :
      Dyadic.toReal u.halfWidth = halfWidth u := by
    simp [Hex.DyadicSquare.halfWidth, halfWidth_eq]
  have hswidth : 0 < halfWidth s := by
    rw [halfWidth_eq]
    exact zpow_pos (by norm_num) _
  have hxspan : 2 * halfWidth s ≤
      Dyadic.toReal b.xmax - Dyadic.toReal b.xmin := by
    simp only [Dyadic.toReal_sub, Dyadic.toReal_add, hwidth] at hxlo hxhi
    linarith
  have hyspan : 2 * halfWidth s ≤
      Dyadic.toReal b.ymax - Dyadic.toReal b.ymin := by
    simp only [Dyadic.toReal_sub, Dyadic.toReal_add, hwidth] at hylo hyhi
    linarith
  have hxhalf : Dyadic.toReal xhalf =
      (Dyadic.toReal b.xmax - Dyadic.toReal b.xmin) / 2 := by
    simp [xhalf, Dyadic.toReal_shiftRight]
    ring
  have hyhalf : Dyadic.toReal yhalf =
      (Dyadic.toReal b.ymax - Dyadic.toReal b.ymin) / 2 := by
    simp [yhalf, Dyadic.toReal_shiftRight]
    ring
  have hwpos : 0 < Dyadic.toReal w := by
    have hxpos : 0 < Dyadic.toReal xhalf := by
      rw [hxhalf]
      linarith
    dsimp only [w]
    rw [Dyadic.toReal_max]
    exact hxpos.trans_le (le_max_left _ _)
  have hwceil : Dyadic.toReal w ≤
      (2 : ℝ) ^ Hex.Dyadic.ceilLog2 w :=
    Dyadic.toReal_le_two_pow_ceilLog2 w hwpos
  have hencWidth : halfWidth (Hex.encSquare squares) =
      (2 : ℝ) ^ Hex.Dyadic.ceilLog2 w := by
    rw [halfWidth_eq, Hex.encSquare, hbox]
    change (2 : ℝ) ^ (- -Hex.Dyadic.ceilLog2
      (Hex.Dyadic.max ((b.xmax - b.xmin) >>> (1 : Int))
        ((b.ymax - b.ymin) >>> (1 : Int)))) = _
    simp only [neg_neg]
    rfl
  have hencRe : (center (Hex.encSquare squares)).re =
      (Dyadic.toReal b.xmin + Dyadic.toReal b.xmax) / 2 := by
    simp only [center, Hex.encSquare, hbox, Hex.DyadicSquare.center,
      GaussDyadic.toComplex_re]
    rw [Dyadic.toReal_shiftRight, Dyadic.toReal_add]
    norm_num
    ring
  have hencIm : (center (Hex.encSquare squares)).im =
      (Dyadic.toReal b.ymin + Dyadic.toReal b.ymax) / 2 := by
    simp only [center, Hex.encSquare, hbox, Hex.DyadicSquare.center,
      GaussDyadic.toComplex_im]
    rw [Dyadic.toReal_shiftRight, Dyadic.toReal_add]
    norm_num
    ring
  intro z hz
  change supNorm (z - center s) ≤ halfWidth s at hz
  change supNorm (z - center (Hex.encSquare squares)) ≤
    halfWidth (Hex.encSquare squares)
  have hzre : |z.re - Dyadic.toReal s.re| ≤ halfWidth s := by
    exact (le_max_left _ _).trans hz
  have hzim : |z.im - Dyadic.toReal s.im| ≤ halfWidth s := by
    exact (le_max_right _ _).trans hz
  have hxlo' : Dyadic.toReal b.xmin ≤ Dyadic.toReal s.re - halfWidth s := by
    simpa only [Dyadic.toReal_sub, hwidth] using hxlo
  have hxhi' : Dyadic.toReal s.re + halfWidth s ≤ Dyadic.toReal b.xmax := by
    simpa only [Dyadic.toReal_add, hwidth] using hxhi
  have hylo' : Dyadic.toReal b.ymin ≤ Dyadic.toReal s.im - halfWidth s := by
    simpa only [Dyadic.toReal_sub, hwidth] using hylo
  have hyhi' : Dyadic.toReal s.im + halfWidth s ≤ Dyadic.toReal b.ymax := by
    simpa only [Dyadic.toReal_add, hwidth] using hyhi
  have hzboxRe : Dyadic.toReal b.xmin ≤ z.re ∧ z.re ≤ Dyadic.toReal b.xmax := by
    rw [abs_le] at hzre
    constructor <;> linarith [hxlo', hxhi']
  have hzboxIm : Dyadic.toReal b.ymin ≤ z.im ∧ z.im ≤ Dyadic.toReal b.ymax := by
    rw [abs_le] at hzim
    constructor <;> linarith [hylo', hyhi']
  rw [supNorm, Complex.sub_re, Complex.sub_im, hencRe, hencIm, max_le_iff]
  constructor
  · rw [hencWidth]
    have hmid : |z.re - (Dyadic.toReal b.xmin + Dyadic.toReal b.xmax) / 2| ≤
        (Dyadic.toReal b.xmax - Dyadic.toReal b.xmin) / 2 := by
      rw [abs_le]
      constructor <;> linarith [hzboxRe.1, hzboxRe.2]
    apply hmid.trans
    calc
      _ = Dyadic.toReal xhalf := hxhalf.symm
      _ ≤ Dyadic.toReal w := by
        dsimp only [w]
        rw [Dyadic.toReal_max]
        exact le_max_left _ _
      _ ≤ _ := hwceil
  · rw [hencWidth]
    have hmid : |z.im - (Dyadic.toReal b.ymin + Dyadic.toReal b.ymax) / 2| ≤
        (Dyadic.toReal b.ymax - Dyadic.toReal b.ymin) / 2 := by
      rw [abs_le]
      constructor <;> linarith [hzboxIm.1, hzboxIm.2]
    apply hmid.trans
    calc
      _ = Dyadic.toReal yhalf := hyhalf.symm
      _ ≤ Dyadic.toReal w := by
        dsimp only [w]
        rw [Dyadic.toReal_max]
        exact le_max_right _ _
      _ ≤ _ := hwceil

/-- The square is contained in its closed circumscribed Euclidean disc. -/
theorem closedSquare_subset_closedDisc (s : Hex.DyadicSquare) :
    closedSquare s ⊆ closedDisc s := by
  intro z hz
  rw [closedSquare, supClosedBall, Set.mem_setOf_eq] at hz
  rw [closedDisc, Metric.mem_closedBall, Complex.dist_eq]
  calc
    ‖z - center s‖ ≤ √2 * supNorm (z - center s) :=
      Complex.norm_le_sqrt_two_mul_max (z - center s)
    _ ≤ √2 * halfWidth s := mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)
    _ = radius s := by rw [radius, mul_comm]

/-- The closed square lies in the open disc obtained from the executable
strict upper radius bound. -/
theorem closedSquare_subset_ball_radiusHi (s : Hex.DyadicSquare) :
    closedSquare s ⊆ Metric.ball (center s) (Dyadic.toReal s.radiusHi) := by
  intro z hz
  have hclosed := closedSquare_subset_closedDisc s hz
  rw [closedDisc, Metric.mem_closedBall] at hclosed
  rw [Metric.mem_ball]
  exact hclosed.trans_lt (radius_lt_radiusHi s)

end DyadicSquare

end

end HexRootsMathlib
