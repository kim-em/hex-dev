/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Basic
public import Mathlib.RingTheory.AdjoinRoot

public section

/-!
# Fixed-presentation semantic laws

This module proves the operation laws needed to install a scoped field
structure on {name}`Hex.QAdjoin`. The executable carrier deliberately supplies
only its concrete operations; the {name}`AdjoinRoot` correspondence packages
those laws without changing the operations or their rational scalar action.
-/

namespace Hex.QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- The monic rational associate used for the quotient-field comparison. -/
@[expose]
noncomputable def definingPolynomial (p : ZPoly) : Polynomial Rat :=
  (p.leadingCoeff : Rat)⁻¹ • HexPolyZMathlib.toPolyℚ p

/-- The rational defining polynomial is the monic associate of the checked
integer polynomial. -/
theorem definingPolynomial_monic (p : ZPoly) [ZPoly.CheckedIrreducible p] :
    (definingPolynomial p).Monic := by
  have hirr := ZPoly.CheckedIrreducible.irreducibleRat p
  have hlc :
      (HexPolyZMathlib.toPolyℚ p).leadingCoeff =
        (p.leadingCoeff : Rat) := by
    rw [HexPolyZMathlib.toPolyℚ,
      Polynomial.leadingCoeff_map_of_injective
        (RingHom.injective_int (Int.castRingHom Rat)),
      HexPolyMathlib.leadingCoeff_toPolynomial]
    rfl
  rw [definingPolynomial, ← hlc, Polynomial.smul_eq_C_mul, mul_comm]
  exact Polynomial.monic_mul_leadingCoeff_inv hirr.ne_zero

/-- Monic normalization preserves the executable defining degree. -/
theorem natDegree_definingPolynomial (p : ZPoly)
    [ZPoly.CheckedIrreducible p] :
    (definingPolynomial p).natDegree = p.degree?.getD 0 := by
  have hirr := ZPoly.CheckedIrreducible.irreducibleRat p
  have hlc :
      (HexPolyZMathlib.toPolyℚ p).leadingCoeff =
        (p.leadingCoeff : Rat) := by
    rw [HexPolyZMathlib.toPolyℚ,
      Polynomial.leadingCoeff_map_of_injective
        (RingHom.injective_int (Int.castRingHom Rat)),
      HexPolyMathlib.leadingCoeff_toPolynomial]
    rfl
  have hlc0 : (p.leadingCoeff : Rat) ≠ 0 := by
    rw [← hlc]
    exact Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
  rw [definingPolynomial,
    Polynomial.natDegree_smul _ (inv_ne_zero hlc0),
    HexPolyZMathlib.toPolyℚ,
    Polynomial.natDegree_map_eq_of_injective
      (RingHom.injective_int (Int.castRingHom Rat)),
    HexPolyMathlib.natDegree_toPolynomial]

/-- The monic rational defining polynomial remains irreducible. -/
theorem definingPolynomial_irreducible (p : ZPoly)
    [ZPoly.CheckedIrreducible p] :
    _root_.Irreducible (definingPolynomial p) := by
  have hirr := ZPoly.CheckedIrreducible.irreducibleRat p
  have hlc :
      (HexPolyZMathlib.toPolyℚ p).leadingCoeff =
        (p.leadingCoeff : Rat) := by
    rw [HexPolyZMathlib.toPolyℚ,
      Polynomial.leadingCoeff_map_of_injective
        (RingHom.injective_int (Int.castRingHom Rat)),
      HexPolyMathlib.leadingCoeff_toPolynomial]
    rfl
  rw [definingPolynomial, ← hlc, Polynomial.smul_eq_C_mul, mul_comm,
    Polynomial.irreducible_mul_leadingCoeff_inv]
  exact hirr

/-- Send reduced executable coordinates to the corresponding {name}`AdjoinRoot`
class. This function is defined before a ring structure is installed on
{name}`Hex.QAdjoin`. -/
@[expose]
noncomputable def toAdjoinRoot (a : QAdjoin p x) :
    AdjoinRoot (definingPolynomial p) :=
  AdjoinRoot.mk (definingPolynomial p)
    (HexPolyMathlib.toPolynomial a.coeffs)

/-- Recover the unique reduced executable coordinates of an {name}`AdjoinRoot`
class. -/
private noncomputable def fromAdjoinRoot [ZPoly.CheckedIrreducible p]
    (a : AdjoinRoot (definingPolynomial p)) : QAdjoin p x where
  coeffs := HexPolyMathlib.ofPolynomial
    (AdjoinRoot.modByMonicHom (definingPolynomial_monic p) a)
  degree_lt := by
    rw [← HexPolyMathlib.natDegree_toPolynomial,
      HexPolyMathlib.toPolynomial_ofPolynomial,
      ← natDegree_definingPolynomial p]
    induction a using AdjoinRoot.induction_on with
    | _ f =>
        rw [AdjoinRoot.modByMonicHom_mk]
        apply Polynomial.natDegree_modByMonic_lt _
          (definingPolynomial_monic p)
        intro hone
        have hdegree := natDegree_definingPolynomial p
        rw [hone, Polynomial.natDegree_one] at hdegree
        exact (Nat.ne_of_gt
          (ZPoly.CheckedIrreducible.pos_degree (p := p))) hdegree.symm

/-- Reduced coordinates give a bijection with the quotient by the monic
rational defining relation. -/
theorem toAdjoinRoot_bijective [ZPoly.CheckedIrreducible p] :
    Function.Bijective (@toAdjoinRoot p x) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨@fromAdjoinRoot p x _, ?_, ?_⟩
  · intro a
    apply QAdjoin.ext
    apply (HexPolyMathlib.equiv (R := Rat)).injective
    change HexPolyMathlib.toPolynomial
        (HexPolyMathlib.ofPolynomial
          (AdjoinRoot.modByMonicHom (definingPolynomial_monic p)
            (toAdjoinRoot a))) =
      HexPolyMathlib.toPolynomial a.coeffs
    rw [HexPolyMathlib.toPolynomial_ofPolynomial, toAdjoinRoot,
      AdjoinRoot.modByMonicHom_mk]
    apply (Polynomial.modByMonic_eq_self_iff
      (definingPolynomial_monic p)).mpr
    apply Polynomial.degree_lt_degree
    rw [HexPolyMathlib.natDegree_toPolynomial,
      natDegree_definingPolynomial]
    exact a.degree_lt
  · intro a
    change AdjoinRoot.mk (definingPolynomial p)
      (HexPolyMathlib.toPolynomial
        (HexPolyMathlib.ofPolynomial
          (AdjoinRoot.modByMonicHom (definingPolynomial_monic p) a))) = a
    rw [HexPolyMathlib.toPolynomial_ofPolynomial]
    exact AdjoinRoot.mk_leftInverse (definingPolynomial_monic p) a

/-- The selected complex root zeros the monic rational defining polynomial. -/
theorem eval_definingPolynomial [ZPoly.CheckedIrreducible p]
    (rep : RefinedIsolation p) :
    (definingPolynomial p).eval₂ (algebraMap Rat ℂ) rep.root = 0 := by
  have hp := eval_reduceCoeffs (p := p) (ZPoly.toRatPoly p) rep
  rw [reduceCoeffs, HexPolyMathlib.toPolynomial_mod,
    EuclideanDomain.mod_self,
    Polynomial.eval₂_zero,
    HexPolyZMathlib.toPolynomial_toRatPoly] at hp
  rw [definingPolynomial, Polynomial.eval₂_smul, hp.symm, mul_zero]

/-- Evaluate the quotient presentation at its selected complex root. -/
@[expose]
noncomputable def rootHom [ZPoly.CheckedIrreducible p]
    (rep : RefinedIsolation p) :
    AdjoinRoot (definingPolynomial p) →+* ℂ :=
  AdjoinRoot.lift (algebraMap Rat ℂ) rep.root
    (eval_definingPolynomial rep)

/-- Quotient evaluation agrees with direct evaluation of executable
coordinates. -/
theorem rootHom_toAdjoinRoot [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    rootHom rep (toAdjoinRoot a) = toComplex a rep h := by
  rw [rootHom, toAdjoinRoot, AdjoinRoot.lift_mk]
  rfl

/-- Evaluation at the selected root is injective for a checked irreducible
presentation. -/
theorem toComplex_injective [ZPoly.CheckedIrreducible p]
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    Function.Injective (fun a : QAdjoin p x => toComplex a rep h) := by
  letI : Fact (_root_.Irreducible (definingPolynomial p)) :=
    ⟨definingPolynomial_irreducible p⟩
  intro a b hab
  apply toAdjoinRoot_bijective.1
  apply (rootHom rep).injective
  rw [rootHom_toAdjoinRoot a rep h, rootHom_toAdjoinRoot b rep h]
  exact hab

/-- The executable coordinate test recognizes precisely the zero element. -/
theorem isZero_iff (a : QAdjoin p x) : a.isZero ↔ a = 0 := by
  rw [QAdjoin.isZero, DensePoly.isZero_eq_true_iff]
  constructor
  · intro hsize
    apply QAdjoin.ext
    apply DensePoly.ext_coeff
    intro n
    change a.coeffs.coeff n = 0
    exact DensePoly.coeff_eq_zero_of_size_le a.coeffs (by omega)
  · intro ha
    subst a
    exact DensePoly.size_zero

/-- Irreducibility and the reduced-degree invariant make the executable gcd
guard in {name}`Hex.QAdjoin.inv` succeed for every nonzero element. -/
theorem inverse_gcd_size [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (ha : a.isZero = false) :
    (DensePoly.xgcdLeftMonic a.coeffs (ZPoly.toRatPoly p)).gcd.size = 1 := by
  let A := HexPolyMathlib.toPolynomial a.coeffs
  let P := HexPolyMathlib.toPolynomial (ZPoly.toRatPoly p)
  have ha0 : A ≠ 0 := by
    intro hA
    have hcoeffs : a.coeffs = 0 := by
      apply (HexPolyMathlib.equiv (R := Rat)).injective
      simpa [A] using hA
    have hazero : a = 0 := QAdjoin.ext hcoeffs
    have : a.isZero = true := (isZero_iff a).mpr hazero
    simp [ha] at this
  have hdeg : A.natDegree < P.natDegree := by
    dsimp [A, P]
    rw [HexPolyMathlib.natDegree_toPolynomial,
      HexPolyZMathlib.toPolynomial_toRatPoly, HexPolyZMathlib.toPolyℚ,
      Polynomial.natDegree_map_eq_of_injective
        (RingHom.injective_int (Int.castRingHom Rat)),
      HexPolyMathlib.natDegree_toPolynomial]
    exact a.degree_lt
  have hirr : _root_.Irreducible P := by
    simpa [P, HexPolyZMathlib.toPolynomial_toRatPoly] using
      ZPoly.CheckedIrreducible.irreducibleRat p
  have hnotdvd : ¬ P ∣ A :=
    Polynomial.not_dvd_of_natDegree_lt ha0 hdeg
  have hnormUnit : IsUnit (EuclideanDomain.gcd A P) := by
    apply EuclideanDomain.gcd_isUnit_iff.mpr
    exact ((EuclideanDomain.dvd_or_coprime P A hirr).resolve_left
      hnotdvd).symm
  let r := DensePoly.xgcdLeftMonic a.coeffs (ZPoly.toRatPoly p)
  have hdvd := DensePoly.xgcdLeftMonic_dvd
    a.coeffs (ZPoly.toRatPoly p)
  have hleft : HexPolyMathlib.toPolynomial r.gcd ∣ A := by
    rcases hdvd.1 with ⟨u, hu⟩
    refine ⟨HexPolyMathlib.toPolynomial u, ?_⟩
    simpa [r, A] using congrArg HexPolyMathlib.toPolynomial hu
  have hright : HexPolyMathlib.toPolynomial r.gcd ∣ P := by
    rcases hdvd.2 with ⟨u, hu⟩
    refine ⟨HexPolyMathlib.toPolynomial u, ?_⟩
    simpa [r, P] using congrArg HexPolyMathlib.toPolynomial hu
  have hgcdDvd : HexPolyMathlib.toPolynomial r.gcd ∣
      EuclideanDomain.gcd A P :=
    EuclideanDomain.dvd_gcd hleft hright
  have hunit : IsUnit
      (HexPolyMathlib.toPolynomial r.gcd) :=
    isUnit_of_dvd_unit hgcdDvd hnormUnit
  obtain ⟨c, hc, hcPoly⟩ := Polynomial.isUnit_iff.mp hunit
  have hgcdC :
      r.gcd = DensePoly.C c := by
    apply (HexPolyMathlib.equiv (R := Rat)).injective
    simpa only [HexPolyMathlib.equiv_apply,
      HexPolyMathlib.toPolynomial_C] using hcPoly.symm
  simpa [r, hgcdC] using DensePoly.size_C_of_ne_zero hc.ne_zero

/-- Fixed-presentation zero evaluates to complex zero. -/
theorem map_zero (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex (0 : QAdjoin p x) rep h = 0 := by
  change
    (HexPolyMathlib.toPolynomial (0 : DensePoly Rat)).eval₂
        (algebraMap Rat ℂ) rep.root = 0
  rw [HexPolyMathlib.toPolynomial_zero, Polynomial.eval₂_zero]

/-- Fixed-presentation one evaluates to complex one. -/
theorem map_one (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex (1 : QAdjoin p x) rep h = 1 := by
  change
    (HexPolyMathlib.toPolynomial (1 : DensePoly Rat)).eval₂
        (algebraMap Rat ℂ) rep.root = 1
  rw [HexPolyMathlib.toPolynomial_one, Polynomial.eval₂_one]

/-- Fixed-presentation negation agrees with complex negation. -/
theorem map_neg (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (-a) rep h = -toComplex a rep h := by
  change
    (HexPolyMathlib.toPolynomial
      (reduceCoeffs p (-a.coeffs))).eval₂
        (algebraMap Rat ℂ) rep.root =
      -(HexPolyMathlib.toPolynomial a.coeffs).eval₂
        (algebraMap Rat ℂ) rep.root
  rw [eval_reduceCoeffs, HexPolyMathlib.toPolynomial_neg,
    Polynomial.eval₂_neg]

/-- Fixed-presentation subtraction agrees with complex subtraction. -/
theorem map_sub (a b : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (a - b) rep h = toComplex a rep h - toComplex b rep h := by
  change
    (HexPolyMathlib.toPolynomial
      (reduceCoeffs p (a.coeffs - b.coeffs))).eval₂
        (algebraMap Rat ℂ) rep.root =
      (HexPolyMathlib.toPolynomial a.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root -
        (HexPolyMathlib.toPolynomial b.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root
  rw [eval_reduceCoeffs, HexPolyMathlib.toPolynomial_sub,
    Polynomial.eval₂_sub]

/-- The executable rational scalar action is semantic scalar multiplication. -/
theorem map_smul (q : Rat) (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (q • a) rep h = (q : ℂ) * toComplex a rep h := by
  change
    (HexPolyMathlib.toPolynomial
      (reduceCoeffs p (DensePoly.scale q a.coeffs))).eval₂
        (algebraMap Rat ℂ) rep.root =
      (q : ℂ) *
        (HexPolyMathlib.toPolynomial a.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root
  rw [eval_reduceCoeffs, HexPolyMathlib.toPolynomial_scale,
    Polynomial.eval₂_mul, Polynomial.eval₂_C]
  exact congrArg
    (fun z : ℂ =>
      z * (HexPolyMathlib.toPolynomial a.coeffs).eval₂
        (algebraMap Rat ℂ) rep.root)
    (map_ratCast (algebraMap Rat ℂ) q)

/-- Executable extended-GCD inversion agrees with complex inversion. -/
theorem map_inv [ZPoly.CheckedIrreducible p] (a : QAdjoin p x)
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex a⁻¹ rep h = (toComplex a rep h)⁻¹ := by
  by_cases ha : a.isZero = true
  · have hazero : a = 0 := (isZero_iff a).mp ha
    change toComplex (QAdjoin.inv a) rep h = _
    rw [QAdjoin.inv, ite_eq_left ha, map_zero, hazero, map_zero, inv_zero]
  · have haFalse : a.isZero = false := by
      cases hzero : a.isZero <;> simp_all
    let m := ZPoly.toRatPoly p
    let r := DensePoly.xgcdLeftMonic a.coeffs m
    have hs : r.gcd.size = 1 := by
      simpa [r, m] using inverse_gcd_size a haFalse
    have hpos : 0 < r.gcd.size := by omega
    have hlc0 : r.gcd.leadingCoeff ≠ 0 :=
      DensePoly.leadingCoeff_ne_zero_of_pos_size r.gcd hpos
    have hnat :
        (HexPolyMathlib.toPolynomial r.gcd).natDegree = 0 := by
      rw [HexPolyMathlib.natDegree_toPolynomial,
        DensePoly.degree?_eq_some_of_pos_size _ hpos, hs]
      rfl
    have hcoeff :
        (HexPolyMathlib.toPolynomial r.gcd).coeff 0 =
          r.gcd.leadingCoeff := by
      rw [HexPolyMathlib.coeff_toPolynomial,
        DensePoly.leadingCoeff_eq_coeff_last _ hpos, hs]
    have hgcdPoly :
        HexPolyMathlib.toPolynomial r.gcd =
          Polynomial.C r.gcd.leadingCoeff :=
      (Polynomial.eq_C_of_natDegree_eq_zero hnat).trans
        (congrArg Polynomial.C hcoeff)
    have hp :
        (HexPolyMathlib.toPolynomial m).eval₂
          (algebraMap Rat ℂ) rep.root = 0 := by
      have hp' := eval_reduceCoeffs (p := p) (ZPoly.toRatPoly p) rep
      rw [reduceCoeffs, HexPolyMathlib.toPolynomial_mod,
        EuclideanDomain.mod_self, Polynomial.eval₂_zero] at hp'
      simpa [m] using hp'.symm
    obtain ⟨t, hbezDense⟩ := DensePoly.xgcdLeftMonic_bezout a.coeffs m
    have hbez := congrArg HexPolyMathlib.toPolynomial hbezDense
    simp only [HexPolyMathlib.toPolynomial_add,
      HexPolyMathlib.toPolynomial_mul] at hbez
    have hbezEval := congrArg
      (fun f : Polynomial Rat =>
        f.eval₂ (algebraMap Rat ℂ) rep.root) hbez
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_mul] at hbezEval
    change
      (HexPolyMathlib.toPolynomial r.left).eval₂
          (algebraMap Rat ℂ) rep.root *
          toComplex a rep h +
        (HexPolyMathlib.toPolynomial t).eval₂
          (algebraMap Rat ℂ) rep.root *
          (HexPolyMathlib.toPolynomial m).eval₂
            (algebraMap Rat ℂ) rep.root =
        (HexPolyMathlib.toPolynomial r.gcd).eval₂
          (algebraMap Rat ℂ) rep.root at hbezEval
    rw [hp, mul_zero, add_zero, hgcdPoly, Polynomial.eval₂_C] at hbezEval
    have hcast :
        (algebraMap Rat ℂ) r.gcd.leadingCoeff =
          (r.gcd.leadingCoeff : ℂ) :=
      map_ratCast (algebraMap Rat ℂ) r.gcd.leadingCoeff
    have hlcC : (r.gcd.leadingCoeff : ℂ) ≠ 0 := by
      rw [← hcast]
      exact (map_ne_zero (algebraMap Rat ℂ)).mpr hlc0
    rw [hcast] at hbezEval
    have hvalue : toComplex a rep h ≠ 0 := by
      intro hzero
      apply ha
      apply (isZero_iff a).mpr
      apply toComplex_injective rep h
      change toComplex a rep h = toComplex (0 : QAdjoin p x) rep h
      rw [map_zero]
      exact hzero
    change toComplex (QAdjoin.inv a) rep h = _
    simp only [QAdjoin.inv, haFalse, Bool.false_eq_true, ite_false]
    rw [hs, ite_eq_left rfl, ite_eq_right hlc0]
    change
      (HexPolyMathlib.toPolynomial
        (reduceCoeffs p
          (DensePoly.scale r.gcd.leadingCoeff⁻¹ r.left))).eval₂
          (algebraMap Rat ℂ) rep.root = _
    rw [eval_reduceCoeffs, HexPolyMathlib.toPolynomial_scale,
      Polynomial.eval₂_mul, Polynomial.eval₂_C,
      map_inv₀ (algebraMap Rat ℂ) r.gcd.leadingCoeff]
    rw [mul_comm]
    change
      (HexPolyMathlib.toPolynomial r.left).eval₂
          (algebraMap Rat ℂ) rep.root /
        (r.gcd.leadingCoeff : ℂ) = (toComplex a rep h)⁻¹
    apply mul_right_cancel₀ hvalue
    rw [div_mul_eq_mul_div, hbezEval,
      div_self hlcC,
      mul_comm, Complex.mul_inv_cancel hvalue]

/-- Fixed-presentation division agrees with complex division. -/
theorem map_div [ZPoly.CheckedIrreducible p] (a b : QAdjoin p x)
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex (a / b) rep h = toComplex a rep h / toComplex b rep h := by
  change toComplex (a * b⁻¹) rep h = _
  rw [map_mul, map_inv]
  rfl

/-- Executable natural powers preserve the selected interpretation. -/
theorem map_natPow (a : QAdjoin p x) (n : Nat)
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex (natPow a n) rep h = toComplex a rep h ^ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases n with
      | zero => simp [natPow, map_one]
      | succ n =>
          have hlt : (n + 1) / 2 < n + 1 :=
            Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)
          rw [natPow]
          by_cases heven : (n + 1) % 2 = 0
          · rw [ite_eq_left heven, map_mul, ih ((n + 1) / 2) hlt,
              ← pow_add]
            have hdecomp := Nat.mod_add_div (n + 1) 2
            congr 1
            omega
          · rw [ite_eq_right heven, map_mul, map_mul,
              ih ((n + 1) / 2) hlt, ← pow_add, ← pow_succ]
            have hdecomp := Nat.mod_add_div (n + 1) 2
            have hmod := Nat.mod_two_eq_zero_or_one (n + 1)
            congr 1
            omega

/-- Executable integer powers preserve the selected interpretation. -/
theorem map_intPow [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (n : Int)
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex (intPow a n) rep h = toComplex a rep h ^ n := by
  cases n with
  | ofNat n => exact map_natPow a n rep h
  | negSucc n =>
      rw [intPow, map_inv, map_natPow]
      rfl

/-- The law-bearing field whose operations are exactly the existing
executable reduced-coordinate operations. -/
@[expose, reducible]
noncomputable def field (p : ZPoly) (x : SimpleRoot p)
    [ZPoly.CheckedIrreducible p] : Field (QAdjoin p x) := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  letI : SMul Nat (QAdjoin p x) :=
    ⟨fun n a => (n : Rat) • a⟩
  letI : SMul Int (QAdjoin p x) :=
    ⟨fun n a => (n : Rat) • a⟩
  letI : SMul ℚ≥0 (QAdjoin p x) :=
    ⟨fun q a => (q : Rat) • a⟩
  -- Deliberately retain the executable `SMul Rat` and `Pow` instances. The
  -- injected field must prove laws for those operations, not replace them.
  letI : NatCast (QAdjoin p x) :=
    ⟨fun n => (n : Rat) • (1 : QAdjoin p x)⟩
  letI : IntCast (QAdjoin p x) :=
    ⟨fun n => (n : Rat) • (1 : QAdjoin p x)⟩
  letI : NNRatCast (QAdjoin p x) :=
    ⟨fun q => (q : Rat) • (1 : QAdjoin p x)⟩
  letI : RatCast (QAdjoin p x) :=
    ⟨fun q => q • (1 : QAdjoin p x)⟩
  apply Function.Injective.field
    (fun a => toComplex a rep hrep) (toComplex_injective rep hrep)
  · exact map_zero rep hrep
  · exact map_one rep hrep
  · exact fun a b => map_add a b rep hrep
  · exact fun a b => map_mul a b rep hrep
  · exact fun a => map_neg a rep hrep
  · exact fun a b => map_sub a b rep hrep
  · exact fun a => map_inv a rep hrep
  · exact fun a b => map_div a b rep hrep
  · intro n a
    change toComplex ((n : Rat) • a) rep hrep = n • toComplex a rep hrep
    rw [map_smul, nsmul_eq_mul]
    rfl
  · intro n a
    change toComplex ((n : Rat) • a) rep hrep = n • toComplex a rep hrep
    rw [map_smul, zsmul_eq_mul]
    rfl
  · intro q a
    change toComplex ((q : Rat) • a) rep hrep = q • toComplex a rep hrep
    rw [map_smul, NNRat.smul_def]
    rfl
  · intro q a
    change toComplex (q • a) rep hrep = q • toComplex a rep hrep
    rw [map_smul, Rat.smul_def]
  · exact fun a n => map_natPow a n rep hrep
  · exact fun a n => map_intPow a n rep hrep
  · intro n
    change toComplex ((n : Rat) • (1 : QAdjoin p x)) rep hrep = (n : ℂ)
    rw [map_smul, map_one, mul_one]
    norm_cast
  · intro n
    change toComplex ((n : Rat) • (1 : QAdjoin p x)) rep hrep = (n : ℂ)
    rw [map_smul, map_one, mul_one]
    norm_cast
  · intro q
    change toComplex ((q : Rat) • (1 : QAdjoin p x)) rep hrep = (q : ℂ)
    rw [map_smul, map_one, mul_one]
    norm_cast
  · intro q
    change toComplex (q • (1 : QAdjoin p x)) rep hrep = (q : ℂ)
    rw [map_smul, map_one, mul_one]

namespace QAdjoinField

/-- Opt-in irreducibility witness for the monic rational defining polynomial. -/
scoped instance factIrreducible (p : ZPoly) [ZPoly.CheckedIrreducible p] :
    Fact (_root_.Irreducible (definingPolynomial p)) :=
  ⟨definingPolynomial_irreducible p⟩

/-- Opt-in field instance for a checked fixed presentation. It is scoped so
computational imports never acquire a noncomputable proof dictionary. Opening
the scope makes field notation proof-bearing and therefore noncomputable;
executable code should use the unscoped operations instead. -/
noncomputable scoped instance (p : ZPoly) (x : SimpleRoot p)
    [ZPoly.CheckedIrreducible p] : Field (QAdjoin p x) := field p x

/-- A checked rational presentation has characteristic zero. -/
noncomputable scoped instance (p : ZPoly) (x : SimpleRoot p)
    [ZPoly.CheckedIrreducible p] : CharZero (QAdjoin p x) := by
  letI : Field (QAdjoin p x) := field p x
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  constructor
  intro m n hmn
  have hvalue := congrArg (fun a : QAdjoin p x => toComplex a rep hrep) hmn
  change toComplex ((m : Rat) • (1 : QAdjoin p x)) rep hrep =
    toComplex ((n : Rat) • (1 : QAdjoin p x)) rep hrep at hvalue
  simp only [map_smul, map_one, mul_one] at hvalue
  exact_mod_cast hvalue

end QAdjoinField

open scoped QAdjoinField

/-! These examples pin the scoped field's data fields to the executable
operations. They intentionally use definitional equality, so a future change
that silently replaces an operation or the rational scalar action fails here. -/

section OperationRegression

variable (a b : QAdjoin p x) (q : Rat) [ZPoly.CheckedIrreducible p]

example : (0 : QAdjoin p x) = QAdjoin.instZero.zero := rfl
example : (1 : QAdjoin p x) = QAdjoin.instOne.one := rfl
example : a + b = QAdjoin.add a b := rfl
example : a - b = QAdjoin.sub a b := rfl
example : a * b = QAdjoin.mul a b := rfl
example : -a = QAdjoin.neg a := rfl
example : a⁻¹ = QAdjoin.inv a := rfl
example : a / b = QAdjoin.div a b := rfl
example : a ^ (3 : Nat) = QAdjoin.natPow a 3 := rfl
example : a ^ (-3 : Int) = QAdjoin.intPow a (-3) := rfl
example : q • a = QAdjoin.smul q a := rfl

end OperationRegression

/-- The quotient comparison preserves executable zero. -/
theorem toAdjoinRoot_zero [ZPoly.CheckedIrreducible p] :
    toAdjoinRoot (0 : QAdjoin p x) = 0 := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  letI : Fact (_root_.Irreducible (definingPolynomial p)) :=
    ⟨definingPolynomial_irreducible p⟩
  apply (rootHom rep).injective
  rw [rootHom_toAdjoinRoot, (rootHom rep).map_zero]
  exact map_zero rep hrep

/-- The quotient comparison preserves executable one. -/
theorem toAdjoinRoot_one [ZPoly.CheckedIrreducible p] :
    toAdjoinRoot (1 : QAdjoin p x) = 1 := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  letI : Fact (_root_.Irreducible (definingPolynomial p)) :=
    ⟨definingPolynomial_irreducible p⟩
  apply (rootHom rep).injective
  rw [rootHom_toAdjoinRoot, (rootHom rep).map_one]
  exact map_one rep hrep

/-- The quotient comparison preserves executable addition. -/
theorem toAdjoinRoot_add [ZPoly.CheckedIrreducible p]
    (a b : QAdjoin p x) :
    toAdjoinRoot (a + b) = toAdjoinRoot a + toAdjoinRoot b := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  letI : Fact (_root_.Irreducible (definingPolynomial p)) :=
    ⟨definingPolynomial_irreducible p⟩
  apply (rootHom rep).injective
  rw [rootHom_toAdjoinRoot, (rootHom rep).map_add,
    rootHom_toAdjoinRoot, rootHom_toAdjoinRoot]
  exact map_add a b rep hrep

/-- The quotient comparison preserves executable multiplication. -/
theorem toAdjoinRoot_mul [ZPoly.CheckedIrreducible p]
    (a b : QAdjoin p x) :
    toAdjoinRoot (a * b) = toAdjoinRoot a * toAdjoinRoot b := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  letI : Fact (_root_.Irreducible (definingPolynomial p)) :=
    ⟨definingPolynomial_irreducible p⟩
  apply (rootHom rep).injective
  rw [rootHom_toAdjoinRoot, (rootHom rep).map_mul,
    rootHom_toAdjoinRoot, rootHom_toAdjoinRoot]
  exact map_mul a b rep hrep

/-- The quotient comparison preserves executable rational scalar
multiplication. -/
theorem toAdjoinRoot_smul [ZPoly.CheckedIrreducible p]
    (q : Rat) (a : QAdjoin p x) :
    toAdjoinRoot (q • a) = q • toAdjoinRoot a := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  letI : Fact (_root_.Irreducible (definingPolynomial p)) :=
    ⟨definingPolynomial_irreducible p⟩
  apply (rootHom rep).injective
  rw [rootHom_toAdjoinRoot]
  conv_rhs => rw [Algebra.smul_def]
  rw [(rootHom rep).map_mul, RingHom.map_rat_algebraMap,
    rootHom_toAdjoinRoot]
  exact map_smul q a rep hrep

/-- The reduced-coordinate comparison as a ring homomorphism. -/
@[expose]
noncomputable def toAdjoinRootHom [ZPoly.CheckedIrreducible p] :
    QAdjoin p x →+* AdjoinRoot (definingPolynomial p) where
  toFun := toAdjoinRoot
  map_zero' := toAdjoinRoot_zero
  map_one' := toAdjoinRoot_one
  map_add' := toAdjoinRoot_add
  map_mul' := toAdjoinRoot_mul

/-- Reduced executable coordinates are ring-equivalent to the monic rational
{name}`AdjoinRoot` presentation. -/
@[expose]
noncomputable def adjoinRootEquiv [ZPoly.CheckedIrreducible p] :
    QAdjoin p x ≃+* AdjoinRoot (definingPolynomial p) :=
  RingEquiv.ofBijective toAdjoinRootHom toAdjoinRoot_bijective

/-- The packaged ring equivalence acts by the underlying comparison map. -/
@[simp]
theorem adjoinRootEquiv_apply [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) : adjoinRootEquiv a = toAdjoinRoot a := rfl

/-- Evaluation at the selected root as an injective ring homomorphism. -/
@[expose]
noncomputable def embedding [ZPoly.CheckedIrreducible p]
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    QAdjoin p x →+* ℂ where
  toFun := fun a => toComplex a rep h
  map_zero' := map_zero rep h
  map_one' := map_one rep h
  map_add' := fun a b => map_add a b rep h
  map_mul' := fun a b => map_mul a b rep h

/-- The packaged ring homomorphism acts by evaluation at the selected root. -/
@[simp]
theorem embedding_apply [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    embedding rep h a = toComplex a rep h := rfl

/-- The selected-root ring homomorphism is an embedding. -/
theorem embedding_injective [ZPoly.CheckedIrreducible p]
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    Function.Injective (embedding rep h) := toComplex_injective rep h

/-- Equality in a checked presentation is exactly equality of interpreted
complex values. -/
theorem eq_iff_toComplex [ZPoly.CheckedIrreducible p]
    (a b : QAdjoin p x) (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = x) :
    a = b ↔ toComplex a rep hrep = toComplex b rep hrep := by
  constructor
  · exact fun h => congrArg (fun value => toComplex value rep hrep) h
  · intro h
    exact @toComplex_injective p x _ rep hrep a b h

end Hex.QAdjoin
