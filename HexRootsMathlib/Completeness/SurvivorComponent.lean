/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.RootFreeConverse

public section

/-!
# Geometry of retained survivor components

The sharp T-zero converse puts all square centres of a glued component within
less than three leaf half-widths of one root. Consequently its exact bounding
box fits inside an eight-half-width square, and `encSquare` loses at most two
precision levels.
-/

namespace HexRootsMathlib

noncomputable section

namespace SquareBounds

/-- Every side of a bounding box lies strictly inside the coordinate box of
radius `d` about `z`. -/
private def Near (b : Hex.SquareBounds) (z : ℂ) (d : ℝ) : Prop :=
  z.re - d < Dyadic.toReal b.xmin ∧ Dyadic.toReal b.xmax < z.re + d ∧
    z.im - d < Dyadic.toReal b.ymin ∧ Dyadic.toReal b.ymax < z.im + d

private theorem near_merge {b : Hex.SquareBounds} {s : Hex.DyadicSquare}
    {z : ℂ} {d : ℝ} (hb : Near b z d) (hs : Near s.bounds z d) :
    Near (b.merge s) z d := by
  rcases hb with ⟨hbx0, hbx1, hby0, hby1⟩
  rcases hs with ⟨hsx0, hsx1, hsy0, hsy1⟩
  simp only [Near, Hex.SquareBounds.merge, Dyadic.toReal_min,
    Dyadic.toReal_max]
  exact ⟨lt_min hbx0 hsx0, max_lt hbx1 hsx1,
    lt_min hby0 hsy0, max_lt hby1 hsy1⟩

private theorem near_extend {b : Option Hex.SquareBounds}
    {s : Hex.DyadicSquare} {z : ℂ} {d : ℝ}
    (hb : ∀ box, b = some box → Near box z d) (hs : Near s.bounds z d) :
    ∀ box, Hex.SquareBounds.extend b s = some box → Near box z d := by
  cases b with
  | none =>
      intro box hbox
      simp only [Hex.SquareBounds.extend, Option.some.injEq] at hbox
      subst box
      exact hs
  | some b =>
      intro box hbox
      simp only [Hex.SquareBounds.extend, Option.some.injEq] at hbox
      subst box
      exact near_merge (hb b rfl) hs

private theorem near_foldl (squares : List Hex.DyadicSquare)
    (b : Option Hex.SquareBounds) (z : ℂ) (d : ℝ)
    (hb : ∀ box, b = some box → Near box z d)
    (hs : ∀ s ∈ squares, Near s.bounds z d) :
    ∀ box, squares.foldl Hex.SquareBounds.extend b = some box →
      Near box z d := by
  induction squares generalizing b with
  | nil => simpa using hb
  | cons s squares ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact near_extend hb (hs s (by simp))
      · intro t ht
        exact hs t (by simp [ht])

private theorem near_boundingBox {squares : Array Hex.DyadicSquare}
    {z : ℂ} {d : ℝ} (hs : ∀ s ∈ squares.toList, Near s.bounds z d) :
    ∀ box, Hex.boundingBox squares = some box → Near box z d := by
  rw [Hex.boundingBox, ← Array.foldl_toList]
  exact near_foldl squares.toList none z d (by simp) hs

end SquareBounds

namespace DyadicSquare

/-- A component whose common-precision centres satisfy the sharp survivor
bound loses at most two precision levels when passed to `encSquare`. -/
theorem encSquare_prec_of_near {squares : Array Hex.DyadicSquare}
    {z : ℂ} {prec : Int} (hne : 0 < squares.size)
    (hprec : ∀ s ∈ squares.toList, s.prec = prec)
    (hnear : ∀ s ∈ squares.toList,
      ‖z - center s‖ ≤ (65 / 32 : ℝ) * Dyadic.toReal s.radiusHi) :
    prec - 2 ≤ (Hex.encSquare squares).prec := by
  let h := (2 : ℝ) ^ (-prec)
  have hh : 0 < h := by dsimp [h]; positivity
  have hsqrt : Dyadic.toReal Hex.sqrt2Hi = (1449 / 1024 : ℝ) := by
    norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
  have hsquare : ∀ s ∈ squares.toList,
      SquareBounds.Near s.bounds z (4 * h) := by
    intro s hs
    have hsprec := hprec s hs
    have hwidth : halfWidth s = h := by
      rw [halfWidth_eq, hsprec]
    have hradius : Dyadic.toReal s.radiusHi = h * (1449 / 1024 : ℝ) := by
      rw [radiusHi_eq, hwidth, hsqrt]
    have hnorm := hnear s hs
    rw [hradius] at hnorm
    have hre : |z.re - (center s).re| ≤ ‖z - center s‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - center s)
    have him : |z.im - (center s).im| ≤ ‖z - center s‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - center s)
    have hconstant : (65 / 32 : ℝ) * (h * (1449 / 1024)) < 3 * h := by
      nlinarith
    have hre' : |z.re - Dyadic.toReal s.re| < 3 * h := by
      change |z.re - (center s).re| < 3 * h
      exact (hre.trans hnorm).trans_lt hconstant
    have him' : |z.im - Dyadic.toReal s.im| < 3 * h := by
      change |z.im - (center s).im| < 3 * h
      exact (him.trans hnorm).trans_lt hconstant
    rw [abs_lt] at hre' him'
    simp only [SquareBounds.Near, Hex.DyadicSquare.bounds,
      Dyadic.toReal_sub, Dyadic.toReal_add,
      show Dyadic.toReal s.halfWidth = h by
        simpa [Hex.DyadicSquare.halfWidth] using hwidth]
    exact ⟨by nlinarith [hre'.1], by nlinarith [hre'.2],
      by nlinarith [him'.1], by nlinarith [him'.2]⟩
  let s₀ := squares[0]
  have hs₀ : s₀ ∈ squares.toList := by
    apply Array.mem_toList_iff.mpr
    exact Array.getElem_mem hne
  obtain ⟨box, hbox, hcontains⟩ := SquareBounds.mem_boundingBox hs₀
  have hboxNear := SquareBounds.near_boundingBox hsquare box hbox
  let xhalf := (box.xmax - box.xmin) >>> (1 : Int)
  let yhalf := (box.ymax - box.ymin) >>> (1 : Int)
  let w := Hex.Dyadic.max xhalf yhalf
  have hxhalf : Dyadic.toReal xhalf =
      (Dyadic.toReal box.xmax - Dyadic.toReal box.xmin) / 2 := by
    simp [xhalf, Dyadic.toReal_shiftRight]
    ring
  have hyhalf : Dyadic.toReal yhalf =
      (Dyadic.toReal box.ymax - Dyadic.toReal box.ymin) / 2 := by
    simp [yhalf, Dyadic.toReal_shiftRight]
    ring
  have hwlt : Dyadic.toReal w < 4 * h := by
    rcases hboxNear with ⟨hx0, hx1, hy0, hy1⟩
    dsimp only [w]
    rw [Dyadic.toReal_max, max_lt_iff, hxhalf, hyhalf]
    constructor <;> nlinarith
  have hwpos : 0 < Dyadic.toReal w := by
    have hswidth : halfWidth s₀ = h := by
      rw [halfWidth_eq, hprec s₀ hs₀]
    have hxspan : 2 * h ≤
        Dyadic.toReal box.xmax - Dyadic.toReal box.xmin := by
      unfold SquareBounds.Contains at hcontains
      rcases hcontains with ⟨hx0, hx1, hy0, hy1⟩
      simp only [Dyadic.toReal_sub, Dyadic.toReal_add,
        show Dyadic.toReal s₀.halfWidth = h by
          simpa [Hex.DyadicSquare.halfWidth] using hswidth] at hx0 hx1
      linarith
    dsimp only [w]
    rw [Dyadic.toReal_max]
    exact (by rw [hxhalf]; linarith : 0 < Dyadic.toReal xhalf).trans_le
      (le_max_left _ _)
  have hencWidth : halfWidth (Hex.encSquare squares) =
      (2 : ℝ) ^ Hex.Dyadic.ceilLog2 w := by
    rw [halfWidth_eq, Hex.encSquare, hbox]
    change (2 : ℝ) ^ (- -Hex.Dyadic.ceilLog2
      (Hex.Dyadic.max ((box.xmax - box.xmin) >>> (1 : Int))
        ((box.ymax - box.ymin) >>> (1 : Int)))) = _
    simp only [neg_neg]
    rfl
  have hencLt : halfWidth (Hex.encSquare squares) < 8 * h := by
    rw [hencWidth]
    have hround := Dyadic.two_pow_ceilLog2_lt_two_mul_toReal w hwpos
    nlinarith
  rw [halfWidth_eq] at hencLt
  change (2 : ℝ) ^ (-(Hex.encSquare squares).prec) <
      8 * (2 : ℝ) ^ (-prec) at hencLt
  rw [show 8 * (2 : ℝ) ^ (-prec) = (2 : ℝ) ^ (3 - prec) by
    rw [show 3 - prec = (3 : Int) + -prec by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num] at hencLt
  have hexp : -(Hex.encSquare squares).prec < 3 - prec :=
    (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hencLt
  omega

end DyadicSquare

/-- The enclosing square of an actual retained glued component loses at most
two levels relative to its common leaf precision. -/
theorem encSquare_prec_of_glueCovered {p : Hex.ZPoly}
    {squares component : Array Hex.DyadicSquare} {prec : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) ≤ prec)
    (hprec : ∀ u ∈ squares.toList, u.prec = prec)
    (hkeep : ∀ u ∈ squares.toList, Hex.rootFree p u ≠ true)
    (hc : component ∈ (Hex.glueCovered squares).toList) :
    prec - 2 ≤ (Hex.encSquare component).prec := by
  obtain ⟨z, hz, hnear⟩ := exists_nearRoot_of_glueCovered hp hsize hsep
    (fun u hu => by rw [hprec u hu]; exact hdepth) hkeep hc
  apply DyadicSquare.encSquare_prec_of_near
  · have hconn := glueCovered_connected squares component hc
    by_contra hn
    have hz : component.size = 0 := Nat.eq_zero_of_not_pos hn
    have he : component = #[] := Array.eq_empty_of_size_eq_zero hz
    subst component
    exact hconn.1 rfl
  · intro u hu
    exact hprec u (mem_of_mem_glueCovered hc hu)
  · exact hnear

/-- A root-bearing component produced by the actual survivor/glue pipeline
passes the executable NK certifier three levels after `separationDepth`.

The three levels are exactly the two-level `encSquare` loss proved above and
the further one-level loss from the doubled square used by `certify?`.  Root
membership is a separate loop invariant: proximity of every retained square
to some root is used only to bound the component's extent. -/
theorem certify_nk_of_glueCovered {p : Hex.ZPoly}
    {squares component : Array Hex.DyadicSquare} {candidateK : Nat}
    {prec : Int} {z : ℂ}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 3 ≤ prec)
    (hprec : ∀ u ∈ squares.toList, u.prec = prec)
    (hkeep : ∀ u ∈ squares.toList, Hex.rootFree p u ≠ true)
    (hc : component ∈ (Hex.glueCovered squares).toList)
    (hz : (toPolyℂ p).IsRoot z)
    (hzcomponent : z ∈ Component.region ⟨component, candidateK⟩) :
    ∃ r, Hex.Component.certify? p .nk ⟨component, candidateK⟩ = some r ∧
      z ∈ Certified.region r := by
  have hleaf : (Hex.separationDepth p : Int) ≤ prec := by omega
  have henc := encSquare_prec_of_glueCovered hp hsize hsep hleaf hprec hkeep hc
  have hbase : (Hex.separationDepth p : Int) ≤
      (Hex.encSquare component).doubled.prec := by
    change (Hex.separationDepth p : Int) ≤ (Hex.encSquare component).prec - 1
    omega
  exact NKData.component_certify_nk_covers hsize hsep hz hzcomponent hbase

/-- The default mixed certifier inherits the same root-bearing survivor
guarantee from its NK prefix. -/
theorem certify_mixed_of_glueCovered {p : Hex.ZPoly}
    {squares component : Array Hex.DyadicSquare} {candidateK : Nat}
    {prec : Int} {z : ℂ}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 3 ≤ prec)
    (hprec : ∀ u ∈ squares.toList, u.prec = prec)
    (hkeep : ∀ u ∈ squares.toList, Hex.rootFree p u ≠ true)
    (hc : component ∈ (Hex.glueCovered squares).toList)
    (hz : (toPolyℂ p).IsRoot z)
    (hzcomponent : z ∈ Component.region ⟨component, candidateK⟩) :
    ∃ r, Hex.Component.certify? p .nkThenPellet ⟨component, candidateK⟩ = some r ∧
      z ∈ Certified.region r := by
  have hleaf : (Hex.separationDepth p : Int) ≤ prec := by omega
  have henc := encSquare_prec_of_glueCovered hp hsize hsep hleaf hprec hkeep hc
  have hbase : (Hex.separationDepth p : Int) ≤
      (Hex.encSquare component).doubled.prec := by
    change (Hex.separationDepth p : Int) ≤ (Hex.encSquare component).prec - 1
    omega
  exact NKData.component_certify_mixed_covers hsize hsep hz hzcomponent hbase

end

end HexRootsMathlib
