/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Hasse
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Prime-field points as fixed points of Frobenius

For an elliptic curve defined over `ZMod p`, the `p`-power Frobenius sends
affine coordinates `(x,y)` to `(x^p,y^p)` over an extension field. Its fixed
points are precisely the points defined over the prime field.

The equivalences here identify those rational points both with Frobenius
fixed points and with the kernel of `1 - Frobenius`. In particular, over an
algebraic closure this explains how the finite point count relates to an
endomorphism of the curve's group of points.
-/

@[expose] public section

namespace Hex.ECPP

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra (ZMod p) K]

set_option linter.style.haveILetI false in
omit [DecidableEq K] in
/-- The roots of `X^p - X` in an extension are exactly the prime subfield. -/
private theorem frobenius_fixed (x : K) :
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

/-- Frobenius fixes the point at infinity. -/
@[simp]
theorem pointFrobenius_zero (W : WeierstrassCurve.Affine (ZMod p)) :
    pointFrobenius p W (0 : (W⁄K).Point) = 0 :=
  rfl

/-- Every point defined over the prime field is fixed after base change. -/
theorem pointFrobenius_baseChange (W : WeierstrassCurve.Affine (ZMod p))
    (P : (W⁄(ZMod p)).Point) :
    pointFrobenius p W
        (WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) K P) =
      WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) K P := by
  exact WeierstrassCurve.Affine.Point.map_baseChange (W' := W)
    (FiniteField.frobeniusAlgHom (ZMod p) K) P

/-- A fixed affine point has both coordinates fixed by `p`-power Frobenius. -/
theorem pointFrobenius_fixed_coords (W : WeierstrassCurve.Affine (ZMod p))
    {x y : K} (h : (W⁄K).Nonsingular x y)
    (hfix : pointFrobenius p W (.some x y h) = .some x y h) :
    x ^ p = x ∧ y ^ p = y := by
  simp only [pointFrobenius, WeierstrassCurve.Affine.Point.map,
    FiniteField.coe_frobeniusAlgHom, ZMod.card] at hfix
  exact ⟨(WeierstrassCurve.Affine.Point.some.inj hfix).1,
    (WeierstrassCurve.Affine.Point.some.inj hfix).2⟩

/-- Characterize fixed points as points obtained by base change from `ZMod p`. -/
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
      obtain ⟨a, ha⟩ := (frobenius_fixed p x).mp hx
      obtain ⟨b, hb⟩ := (frobenius_fixed p y).mp hy
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

/-- Frobenius has as many fixed points as the curve has prime-field points. -/
theorem card_fixedPoints (W : WeierstrassCurve.Affine (ZMod p)) :
    Fintype.card {P : (W⁄K).Point // pointFrobenius p W P = P} =
      Fintype.card (W⁄(ZMod p)).Point :=
  (Fintype.card_congr (rationalPointsEquivFixed p W)).symm

/-- The endomorphism whose kernel is the set of rational points. -/
noncomputable def oneSubFrobenius
    (W : WeierstrassCurve.Affine (ZMod p)) :
    (W⁄K).Point →+ (W⁄K).Point :=
  AddMonoidHom.id _ - pointFrobenius p W

/-- `1 - Frobenius` vanishes exactly on Frobenius fixed points. -/
@[simp]
theorem oneSubFrobenius_eq_zero (W : WeierstrassCurve.Affine (ZMod p))
    (P : (W⁄K).Point) :
    oneSubFrobenius p W P = 0 ↔ pointFrobenius p W P = P := by
  simp only [oneSubFrobenius,
    AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    exact sub_eq_zero.mpr h.symm

/-- Membership in the kernel of `1 - Frobenius` is the fixed-point condition. -/
theorem mem_ker_oneSubFrobenius (W : WeierstrassCurve.Affine (ZMod p))
    (P : (W⁄K).Point) :
    P ∈ (oneSubFrobenius p W).ker ↔ pointFrobenius p W P = P := by
  simp only [AddMonoidHom.mem_ker, oneSubFrobenius_eq_zero]

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

/-- The kernel of `1 - Frobenius` has the prime-field point count. -/
theorem card_ker_oneSubFrobenius (W : WeierstrassCurve.Affine (ZMod p)) :
    Fintype.card (oneSubFrobenius (K := K) p W).ker =
      Fintype.card (W⁄(ZMod p)).Point :=
  (Fintype.card_congr (rationalPointsEquivKer p W)).symm

end Hex.ECPP
