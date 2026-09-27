/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Hasse
import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius on elliptic-curve points

For a curve defined over `ZMod p`, Frobenius on any extension field acts
coordinatewise on its affine points. Its fixed points are precisely the
points coming from the base field.
-/

namespace Hex.ECPP

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra (ZMod p) K]

set_option linter.style.haveILetI false in
omit [DecidableEq K] in
private theorem pow_eq_self_iff_base (x : K) :
    x ^ p = x ↔ ∃ y : ZMod p, algebraMap (ZMod p) K y = x := by
  haveI : CharP K p := charP_of_injective_algebraMap' (ZMod p) p
  rw [← Subfield.mem_bot_iff_pow_eq_self K p,
    ← ZMod.fieldRange_castHom_eq_bot p, RingHom.mem_fieldRange]
  simp only [Subsingleton.elim (ZMod.castHom (m := p) dvd_rfl K)
    (algebraMap (ZMod p) K)]

/-- The `p`-power Frobenius endomorphism on the points of a curve over `ZMod p`. -/
noncomputable def pointFrobenius (W : WeierstrassCurve.Affine (ZMod p)) :
    (W⁄K).Point →+ (W⁄K).Point :=
  WeierstrassCurve.Affine.Point.map (FiniteField.frobeniusAlgHom (ZMod p) K)

@[simp]
theorem pointFrobenius_zero (W : WeierstrassCurve.Affine (ZMod p)) :
    pointFrobenius p W (0 : (W⁄K).Point) = 0 :=
  rfl

theorem pointFrobenius_baseChange (W : WeierstrassCurve.Affine (ZMod p))
    (P : (W⁄(ZMod p)).Point) :
    pointFrobenius p W
        (WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) K P) =
      WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) K P := by
  exact WeierstrassCurve.Affine.Point.map_baseChange (W' := W)
    (FiniteField.frobeniusAlgHom (ZMod p) K) P

theorem pointFrobenius_fixed_coords (W : WeierstrassCurve.Affine (ZMod p))
    {x y : K} (h : (W⁄K).Nonsingular x y)
    (hfix : pointFrobenius p W (.some x y h) = .some x y h) :
    x ^ p = x ∧ y ^ p = y := by
  simp only [pointFrobenius, WeierstrassCurve.Affine.Point.map,
    FiniteField.coe_frobeniusAlgHom, ZMod.card] at hfix
  exact ⟨(WeierstrassCurve.Affine.Point.some.inj hfix).1,
    (WeierstrassCurve.Affine.Point.some.inj hfix).2⟩

theorem pointFrobenius_fixed_iff (W : WeierstrassCurve.Affine (ZMod p))
    (P : (W⁄K).Point) :
    pointFrobenius p W P = P ↔
      ∃ Q : (W⁄(ZMod p)).Point,
        WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) K Q = P := by
  constructor
  · intro hfix
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x y h =>
      obtain ⟨hx, hy⟩ := pointFrobenius_fixed_coords p W h hfix
      obtain ⟨a, ha⟩ := (pow_eq_self_iff_base p x).mp hx
      obtain ⟨b, hb⟩ := (pow_eq_self_iff_base p y).mp hy
      subst x
      subst y
      have hbase : (W⁄(ZMod p)).Nonsingular a b := by
        apply (W.baseChange_nonsingular
          (f := Algebra.ofId (ZMod p) K)
          (Algebra.ofId (ZMod p) K).injective a b).mp
        simpa only [Algebra.ofId_apply] using h
      exact ⟨.some a b hbase, rfl⟩
  · rintro ⟨Q, rfl⟩
    exact pointFrobenius_baseChange p W Q

/-- The rational points are exactly the Frobenius fixed points. -/
noncomputable def rationalPointsEquivFixed
    (W : WeierstrassCurve.Affine (ZMod p)) :
    (W⁄(ZMod p)).Point ≃
      {P : (W⁄K).Point // pointFrobenius p W P = P} := by
  classical
  refine Equiv.ofBijective
    (fun Q => ⟨WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) K Q,
      pointFrobenius_baseChange p W Q⟩) ?_
  constructor
  · intro Q₁ Q₂ h
    exact WeierstrassCurve.Affine.Point.map_injective
      (f := Algebra.ofId (ZMod p) K) (congrArg Subtype.val h)
  · intro P
    obtain ⟨Q, hQ⟩ := (pointFrobenius_fixed_iff p W P.val).mp P.property
    exact ⟨Q, Subtype.ext hQ⟩

noncomputable instance (W : WeierstrassCurve.Affine (ZMod p)) :
    Fintype {P : (W⁄K).Point // pointFrobenius p W P = P} :=
  Fintype.ofEquiv _ (rationalPointsEquivFixed p W)

theorem card_fixedPoints (W : WeierstrassCurve.Affine (ZMod p)) :
    Fintype.card {P : (W⁄K).Point // pointFrobenius p W P = P} =
      Fintype.card (W⁄(ZMod p)).Point :=
  (Fintype.card_congr (rationalPointsEquivFixed p W)).symm

/-- The endomorphism whose kernel is the set of rational points. -/
noncomputable def oneSubFrobenius
    (W : WeierstrassCurve.Affine (ZMod p)) :
    (W⁄K).Point →+ (W⁄K).Point :=
  AddMonoidHom.id _ - pointFrobenius p W

theorem mem_ker_oneSubFrobenius (W : WeierstrassCurve.Affine (ZMod p))
    (P : (W⁄K).Point) :
    P ∈ (oneSubFrobenius p W).ker ↔ pointFrobenius p W P = P := by
  simp only [AddMonoidHom.mem_ker, oneSubFrobenius,
    AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    exact sub_eq_zero.mpr h.symm

/-- The kernel of `1 - Frobenius` consists of the rational points. -/
noncomputable def rationalPointsEquivKer
    (W : WeierstrassCurve.Affine (ZMod p)) :
    (W⁄(ZMod p)).Point ≃ (oneSubFrobenius (K := K) p W).ker :=
  (rationalPointsEquivFixed p W).trans
    (Equiv.subtypeEquivProp
      (funext fun P => propext (mem_ker_oneSubFrobenius (K := K) p W P))).symm

noncomputable instance (W : WeierstrassCurve.Affine (ZMod p)) :
    Fintype (oneSubFrobenius (K := K) p W).ker :=
  Fintype.ofEquiv _ (rationalPointsEquivKer p W)

theorem card_ker_oneSubFrobenius (W : WeierstrassCurve.Affine (ZMod p)) :
    Fintype.card (oneSubFrobenius (K := K) p W).ker =
      Fintype.card (W⁄(ZMod p)).Point :=
  (Fintype.card_congr (rationalPointsEquivKer p W)).symm

end Hex.ECPP
