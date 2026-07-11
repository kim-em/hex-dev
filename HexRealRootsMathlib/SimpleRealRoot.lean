/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexRealRootsMathlib.Isolations
public import HexRealRoots.SimpleRealRoot
-- `import all` on `Separation` so `Dyadic.toReal` unfolds in the dyadic-order
-- helpers below, on `Basic` so `DensePoly.degree?_zero_getD` is available when
-- deriving `p ≠ 0` from an isolation's `count_one`, and on `SimpleRealRoot` so
-- the non-`@[expose]` bodies of `SimpleRealRoot` (a `Quot`) and `SimpleRealRoot.
-- mk` unfold — `Quot.lift`/`Quot.ind`/`Quot.sound` need `SimpleRealRoot p`
-- reducible to `Quot Overlaps` here.
import all HexRealRootsMathlib.Separation
import all HexRealRoots.Basic
import all HexRealRoots.SimpleRealRoot

public section

/-!
# Root identity: `Overlaps` classes are exactly the real roots

The executable layer (`HexRealRoots.SimpleRealRoot`) defines `SimpleRealRoot p`
as the `Quot` of `RefinedRealIsolation p` by interval overlap, taking the
quotient with `Quot` (which needs no equivalence proof) because the argument
that `Overlaps` is an equivalence is semantic. This module supplies that
argument:

* `overlaps_iff_same_root`: two refined isolations overlap iff they name the
  same real root. Both intervals have width `≤ 2^{−sepPrec p}`, which is below
  `sep(p)/4` (`sepPrec_separates'`); an overlap places a point within
  `sep(p)/2` of both roots, forcing them to coincide, and conversely two
  isolations of the same root both contain it, so they overlap.
* `SimpleRealRoot.toReal`: the well-defined real value of a root identity,
  lifting `theRoot` through the quotient by the forward direction.
* `SimpleRealRoot.toReal_isRoot`, `SimpleRealRoot.toReal_injective`: the lift
  lands on genuine roots and is injective (distinct classes name distinct
  roots, the backward direction via `Quot.sound`).
* `sameRoot_iff`: the executable boolean `sameRoot` decides equality in
  `SimpleRealRoot p`.

`theRoot hp iso` is the unique real root delivered by
`RealRootIsolation.exists_unique_root` for the isolation underlying `iso`.

## SPEC signature note

The SPEC states these with only `SquareFreeRat p`, and that is exactly what
they carry here — no separate `p ≠ 0` hypothesis. Unlike `RealRootIsolations.
isolates` or `isolateSturm?_isSome` (which have no isolation on hand and so
must assume `p ≠ 0`), every theorem here is handed a `RefinedRealIsolation`,
whose underlying `RealRootIsolation` carries `count_one`; that forces positive
degree (`degree_pos_of_count_one`), hence `p ≠ 0`. So the nonzero fact is
derived internally and the statements match the SPEC verbatim.
-/

namespace HexRealRootsMathlib

open Polynomial

noncomputable section

variable {p : Hex.ZPoly}

/-! ### Dyadic-order helpers (real values) -/

/-- Dyadic `≤` transfers to the real values. -/
private theorem toReal_le_toReal {a b : Dyadic} (h : a ≤ b) :
    Dyadic.toReal a ≤ Dyadic.toReal b := by
  have h2 : a.toRat ≤ b.toRat := Dyadic.toRat_le_toRat_iff.mpr h
  unfold Dyadic.toReal; exact_mod_cast h2

/-- Failing dyadic `≤` gives the reverse inequality on the real values (the
core `Dyadic` order need not be a `LinearOrder`, so this routes through the
total order on `ℚ` via `toRat`). -/
private theorem toReal_le_of_not_le {a b : Dyadic} (h : ¬ a ≤ b) :
    Dyadic.toReal b ≤ Dyadic.toReal a := by
  have h1 : ¬ (a.toRat ≤ b.toRat) := fun hh => h (Dyadic.toRat_le_toRat_iff.mp hh)
  have h2 : b.toRat ≤ a.toRat := (not_le.mp h1).le
  unfold Dyadic.toReal; exact_mod_cast h2

/-- Dyadic `<` coincides with the order of the real values. -/
private theorem toReal_lt_toReal_iff {a b : Dyadic} :
    Dyadic.toReal a < Dyadic.toReal b ↔ a < b := by
  unfold Dyadic.toReal
  rw [Rat.cast_lt, Dyadic.toRat_lt_toRat_iff]

/-- `Dyadic.toReal` is subtractive. -/
private theorem toReal_sub (a b : Dyadic) :
    Dyadic.toReal (a - b) = Dyadic.toReal a - Dyadic.toReal b := by
  unfold Dyadic.toReal; rw [Dyadic.toRat_sub]; push_cast; ring

/-- A real root of the real cast is a complex root of the complex cast. -/
private theorem isRoot_toPolyℂ {r : ℝ} (hr : (toPolyℝ p).IsRoot r) :
    (toPolyℂ p).IsRoot (r : ℂ) := by
  have hcomp : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  have hmap : toPolyℂ p = (toPolyℝ p).map (algebraMap ℝ ℂ) := by
    show (HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℂ)
        = ((HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ)
    rw [Polynomial.map_map, hcomp]
  rw [hmap]
  have h2 : Polynomial.IsRoot ((toPolyℝ p).map (algebraMap ℝ ℂ)) (algebraMap ℝ ℂ r) := hr.map
  simpa using h2

/-! ### The root of a refined isolation -/

/-- The unique real root isolated by a refined isolation, delivered by
`RealRootIsolation.exists_unique_root` for the underlying `RealRootIsolation`. -/
noncomputable def theRoot (hp : Hex.ZPoly.SquareFreeRat p)
    (iso : Hex.RefinedRealIsolation p) : ℝ :=
  (RealRootIsolation.exists_unique_root hp iso.1).choose

/-- `theRoot` is a root of `toPolyℝ p`. -/
theorem theRoot_isRoot (hp : Hex.ZPoly.SquareFreeRat p) (iso : Hex.RefinedRealIsolation p) :
    (toPolyℝ p).IsRoot (theRoot hp iso) :=
  (RealRootIsolation.exists_unique_root hp iso.1).choose_spec.1.1

/-- `theRoot` lies strictly above the isolation's lower endpoint. -/
theorem theRoot_lt (hp : Hex.ZPoly.SquareFreeRat p) (iso : Hex.RefinedRealIsolation p) :
    Dyadic.toReal iso.1.interval.lower < theRoot hp iso :=
  (RealRootIsolation.exists_unique_root hp iso.1).choose_spec.1.2.1

/-- `theRoot` lies at or below the isolation's upper endpoint. -/
theorem theRoot_le (hp : Hex.ZPoly.SquareFreeRat p) (iso : Hex.RefinedRealIsolation p) :
    theRoot hp iso ≤ Dyadic.toReal iso.1.interval.upper :=
  (RealRootIsolation.exists_unique_root hp iso.1).choose_spec.1.2.2

/-- The width of a refined isolation, on the real values, is at most
`2^{−sepPrec p}` (the defining property of `RefinedRealIsolation`). -/
private theorem refined_width (i : Hex.RefinedRealIsolation p) :
    Dyadic.toReal i.1.interval.upper - Dyadic.toReal i.1.interval.lower
      ≤ (2 : ℝ) ^ (-(Hex.sepPrec p : ℤ)) := by
  have h := toReal_le_toReal i.2
  rw [toReal_sub, toReal_twoPow] at h
  exact h

/-! ### `Overlaps` as a real-interval intersection -/

/-- `Overlaps` unfolds to a genuine intersection of the half-open real
intervals: `max lower < min upper`. -/
private theorem overlaps_iff_real (i₁ i₂ : Hex.RefinedRealIsolation p) :
    Hex.Overlaps i₁ i₂ ↔
      max (Dyadic.toReal i₁.1.interval.lower) (Dyadic.toReal i₂.1.interval.lower)
        < min (Dyadic.toReal i₁.1.interval.upper) (Dyadic.toReal i₂.1.interval.upper) := by
  have hmax : max (Dyadic.toReal i₁.1.interval.lower) (Dyadic.toReal i₂.1.interval.lower)
      = Dyadic.toReal (if i₁.1.interval.lower ≤ i₂.1.interval.lower
          then i₂.1.interval.lower else i₁.1.interval.lower) := by
    by_cases h : i₁.1.interval.lower ≤ i₂.1.interval.lower
    · rw [if_pos h, max_eq_right (toReal_le_toReal h)]
    · rw [if_neg h, max_eq_left (toReal_le_of_not_le h)]
  have hmin : min (Dyadic.toReal i₁.1.interval.upper) (Dyadic.toReal i₂.1.interval.upper)
      = Dyadic.toReal (if i₁.1.interval.upper ≤ i₂.1.interval.upper
          then i₁.1.interval.upper else i₂.1.interval.upper) := by
    by_cases h : i₁.1.interval.upper ≤ i₂.1.interval.upper
    · rw [if_pos h, min_eq_left (toReal_le_toReal h)]
    · rw [if_neg h, min_eq_right (toReal_le_of_not_le h)]
  rw [hmax, hmin, toReal_lt_toReal_iff]
  exact Iff.rfl

/-! ### Overlap iff same root -/

/-- **`Overlaps` classes are the real roots.** Two refined isolations of `p`
overlap iff they name the same real root of `toPolyℝ p`.

Forward: both widths are `≤ 2^{−sepPrec p}`, below `sep(p)/4`; an overlap point
sits within one width of each root, so the two roots are less than
`4 · 2^{−sepPrec p}` apart, and `sepPrec_separates'` forces them equal.
Backward: a common root lies in both half-open intervals, so `max lower` (below
the root) is under `min upper` (at or above it). -/
theorem overlaps_iff_same_root (hp : Hex.ZPoly.SquareFreeRat p)
    (i₁ i₂ : Hex.RefinedRealIsolation p) :
    Hex.Overlaps i₁ i₂ ↔ theRoot hp i₁ = theRoot hp i₂ := by
  constructor
  · intro hov
    -- `p ≠ 0` is derivable from either isolation's `count_one`.
    have hp0 : p ≠ 0 := by
      have hdeg := degree_pos_of_count_one i₁.1
      intro hh
      rw [hh] at hdeg
      simp only [Hex.DensePoly.degree?_zero_getD] at hdeg
      omega
    by_contra hne
    have h1l := theRoot_lt hp i₁
    have h1u := theRoot_le hp i₁
    have h2l := theRoot_lt hp i₂
    have h2u := theRoot_le hp i₂
    have hw1 := refined_width i₁
    have hw2 := refined_width i₂
    have hovr := (overlaps_iff_real i₁ i₂).mp hov
    -- `b` is a point common to both intervals: below every upper, above the max lower.
    set b := min (Dyadic.toReal i₁.1.interval.upper) (Dyadic.toReal i₂.1.interval.upper)
      with hbdef
    have hbu1 : b ≤ Dyadic.toReal i₁.1.interval.upper := min_le_left _ _
    have hbu2 : b ≤ Dyadic.toReal i₂.1.interval.upper := min_le_right _ _
    have hbl1 : Dyadic.toReal i₁.1.interval.lower < b :=
      lt_of_le_of_lt (le_max_left _ _) hovr
    have hbl2 : Dyadic.toReal i₂.1.interval.lower < b :=
      lt_of_le_of_lt (le_max_right _ _) hovr
    have hwpos : (0 : ℝ) < (2 : ℝ) ^ (-(Hex.sepPrec p : ℤ)) := by positivity
    -- Both roots sit within one width of `b`, so within `2·2^{−sepPrec}` of each other.
    have hbound : |theRoot hp i₁ - theRoot hp i₂| < 2 * (2 : ℝ) ^ (-(Hex.sepPrec p : ℤ)) := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    -- Separation forbids two distinct roots being that close.
    have hsep := sepPrec_separates' p hp0 hp (theRoot hp i₁ : ℂ) (theRoot hp i₂ : ℂ)
      (isRoot_toPolyℂ (theRoot_isRoot hp i₁)) (isRoot_toPolyℂ (theRoot_isRoot hp i₂))
      (fun h => hne (by exact_mod_cast h))
    have hnorm : ‖(theRoot hp i₁ : ℂ) - (theRoot hp i₂ : ℂ)‖
        = |theRoot hp i₁ - theRoot hp i₂| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hsep
    linarith
  · intro hsame
    rw [overlaps_iff_real]
    have h1l := theRoot_lt hp i₁
    have h1u := theRoot_le hp i₁
    have h2l := theRoot_lt hp i₂
    have h2u := theRoot_le hp i₂
    rw [hsame] at h1l h1u
    exact lt_of_lt_of_le (max_lt h1l h2l) (le_min h1u h2u)

/-! ### The quotient `SimpleRealRoot p` -/

/-- The real value of a root identity: `theRoot` lifted through the overlap
quotient. Well-defined by the forward direction of `overlaps_iff_same_root`. -/
noncomputable def _root_.Hex.SimpleRealRoot.toReal (hp : Hex.ZPoly.SquareFreeRat p) :
    Hex.SimpleRealRoot p → ℝ :=
  Quot.lift (theRoot hp) (fun _ _ hab => (overlaps_iff_same_root hp _ _).mp hab)

/-- The lifted value is a genuine root of `toPolyℝ p`. -/
theorem _root_.Hex.SimpleRealRoot.toReal_isRoot (hp : Hex.ZPoly.SquareFreeRat p)
    (s : Hex.SimpleRealRoot p) : (toPolyℝ p).IsRoot (s.toReal hp) := by
  induction s using Quot.ind with
  | _ i => exact theRoot_isRoot hp i

/-- Distinct root identities name distinct reals: `toReal` is injective. The
backward direction of `overlaps_iff_same_root` produces the `Overlaps` witness
that `Quot.sound` needs. -/
theorem _root_.Hex.SimpleRealRoot.toReal_injective (hp : Hex.ZPoly.SquareFreeRat p) :
    Function.Injective (Hex.SimpleRealRoot.toReal (p := p) hp) := by
  intro s₁ s₂ h
  induction s₁ using Quot.ind with
  | _ i₁ =>
    induction s₂ using Quot.ind with
    | _ i₂ =>
      have hEq : theRoot hp i₁ = theRoot hp i₂ := h
      exact Quot.sound ((overlaps_iff_same_root hp i₁ i₂).mpr hEq)

/-- **`sameRoot` decides equality in `SimpleRealRoot p`.** The executable
boolean overlap test on refined isolations is `true` exactly when they are the
same element of the quotient. -/
theorem sameRoot_iff (hp : Hex.ZPoly.SquareFreeRat p) (i₁ i₂ : Hex.RefinedRealIsolation p) :
    Hex.RefinedRealIsolation.sameRoot i₁ i₂ = true ↔
      Hex.SimpleRealRoot.mk i₁ = Hex.SimpleRealRoot.mk i₂ := by
  simp only [Hex.RefinedRealIsolation.sameRoot, decide_eq_true_iff]
  constructor
  · intro hov
    exact Quot.sound hov
  · intro heq
    have hEq : theRoot hp i₁ = theRoot hp i₂ :=
      congrArg (Hex.SimpleRealRoot.toReal hp) heq
    exact (overlaps_iff_same_root hp i₁ i₂).mpr hEq

end

end HexRealRootsMathlib
