/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZGcd.Gcd
public import HexPolyZ.Decomposition

public section
set_option backward.proofsInPublic true

/-!
Gauss descent from coprime cofactors to gcd maximality.
-/

namespace Hex

namespace ZPoly

private theorem dvdTrans {a b c : ZPoly} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨q, hq⟩
  rcases hbc with ⟨r, hr⟩
  refine ⟨q * r, ?_⟩
  calc
    c = b * r := hr
    _ = (a * q) * r := by rw [hq]
    _ = a * (q * r) := DensePoly.mul_assoc_poly a q r

private theorem toRatDvd {a b : ZPoly} (h : a ∣ b) :
    toRatPoly a ∣ toRatPoly b := by
  rcases h with ⟨q, hq⟩
  refine ⟨toRatPoly q, ?_⟩
  rw [← toRatPoly_mul, ← hq]

private theorem ratDvdTrans {a b c : DensePoly Rat}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨q, hq⟩
  rcases hbc with ⟨r, hr⟩
  refine ⟨q * r, ?_⟩
  calc
    c = b * r := hr
    _ = (a * q) * r := by rw [hq]
    _ = a * (q * r) := DensePoly.mul_assoc_poly a q r

private theorem ratDvdMulLeft {d p : DensePoly Rat} (q : DensePoly Rat)
    (h : d ∣ p) : d ∣ q * p := by
  rcases h with ⟨a, ha⟩
  refine ⟨q * a, ?_⟩
  calc
    q * p = q * (d * a) := by rw [ha]
    _ = (q * d) * a := (DensePoly.mul_assoc_poly q d a).symm
    _ = (d * q) * a := by rw [DensePoly.mul_comm_poly q d]
    _ = d * (q * a) := DensePoly.mul_assoc_poly d q a

private theorem ratDvdAdd {d p q : DensePoly Rat}
    (hp : d ∣ p) (hq : d ∣ q) : d ∣ p + q := by
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [ha, hb, DensePoly.mul_add_right_poly]

private theorem ratEqCOfSizeLe {p : DensePoly Rat} (hsize : p.size ≤ 1) :
    p = DensePoly.C (p.coeff 0) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C]
  cases n with
  | zero => simp
  | succ n =>
      rw [DensePoly.coeff_eq_zero_of_size_le p (by omega)]
      rfl

private theorem contentDvdOfDvd {a b : ZPoly} (h : a ∣ b) :
    content a ∣ content b := by
  rcases h with ⟨q, hq⟩
  refine ⟨content q, ?_⟩
  rw [hq, content_mul]

/-- A scalar dividing the content divides the whole integer polynomial. -/
private theorem C_dvd_of_dvd_content {p : ZPoly} {c : Int}
    (hc : c ∣ content p) : DensePoly.C c ∣ p := by
  rcases hc with ⟨k, hk⟩
  refine ⟨DensePoly.scale k (primitivePart p), ?_⟩
  calc
    p = DensePoly.scale (content p) (primitivePart p) :=
      (content_mul_primitivePart p).symm
    _ = DensePoly.scale (c * k) (primitivePart p) := by rw [hk]
    _ = DensePoly.scale c (DensePoly.scale k (primitivePart p)) :=
      (DensePoly.scale_scale c k (primitivePart p)).symm
    _ = DensePoly.C c * DensePoly.scale k (primitivePart p) :=
      (C_mul_eq_scale c _).symm

/-- Cofactors with no common nonunit have coprime integer contents. -/
private theorem coprimeContents {a b : ZPoly}
    (hcop : ∀ d : ZPoly, d ∣ a → d ∣ b → IsUnit d) :
    Int.gcd (content a) (content b) = 1 := by
  rw [Int.gcd_eq_one_iff]
  intro c hca hcb
  have hunit := hcop (DensePoly.C c)
    (C_dvd_of_dvd_content hca) (C_dvd_of_dvd_content hcb)
  rcases hunit with hpos | hneg
  · have hc : c = 1 := by
      have hcoeff := congrArg (fun p : ZPoly => p.coeff 0) hpos
      simpa using hcoeff
    rw [hc]
    exact ⟨1, by omega⟩
  · have hc : c = -1 := by
      have hcoeff := congrArg (fun p : ZPoly => p.coeff 0) hneg
      simpa using hcoeff
    rw [hc]
    exact ⟨-1, by omega⟩

/-- Absence of a common integer-polynomial nonunit forces the rational gcd of
the cofactors to be constant. -/
private theorem ratGcdSizeLeOne {a b : ZPoly}
    (hcop : ∀ d : ZPoly, d ∣ a → d ∣ b → IsUnit d) :
    (DensePoly.gcd (toRatPoly a) (toRatPoly b)).size ≤ 1 := by
  let cg := DensePoly.gcd (toRatPoly a) (toRatPoly b)
  by_cases hcgZero : cg = 0
  · change cg.size ≤ 1
    rw [hcgZero]
    exact Nat.zero_le 1
  · let r := ratPolyPrimitivePart cg
    rcases ratPolyPrimitivePart_rational_associate cg with ⟨u, hu⟩
    have hrNe : r ≠ 0 := by
      intro hrZero
      apply hcgZero
      change ratPolyPrimitivePart cg = 0 at hrZero
      rw [hu, hrZero, toRatPoly_zero]
      exact DensePoly.scale_zero_right u
    have hrContentNe : content r ≠ 0 := by
      intro hcontent
      apply hrNe
      have hreconstruct := content_mul_primitivePart r
      rw [hcontent] at hreconstruct
      exact hreconstruct.symm.trans
        (DensePoly.scale_zero_left_semiring (primitivePart r))
    have hrPrimitive : Primitive r :=
      ratPolyPrimitivePart_primitive cg hrContentNe
    have hrDvdCg : toRatPoly r ∣ cg := by
      refine ⟨DensePoly.scale u (1 : DensePoly Rat), ?_⟩
      calc
        cg = DensePoly.scale u (toRatPoly r) := hu
        _ = DensePoly.scale u (toRatPoly r * 1) := by
          rw [DensePoly.mul_one_right_poly]
        _ = toRatPoly r * DensePoly.scale u 1 :=
          DensePoly.mul_scale u (toRatPoly r) 1
    have hrDvdA : r ∣ a := by
      apply dvd_of_toRatPoly_dvd_of_primitive hrPrimitive
      exact ratDvdTrans hrDvdCg (DensePoly.gcd_dvd_left _ _)
    have hrDvdB : r ∣ b := by
      apply dvd_of_toRatPoly_dvd_of_primitive hrPrimitive
      exact ratDvdTrans hrDvdCg (DensePoly.gcd_dvd_right _ _)
    have hrUnit := hcop r hrDvdA hrDvdB
    have huNe : u ≠ 0 := by
      intro huZero
      apply hcgZero
      rw [hu, huZero]
      exact DensePoly.scale_zero_left_semiring (toRatPoly r)
    rw [show DensePoly.gcd (toRatPoly a) (toRatPoly b) = cg by rfl,
      hu, rat_size_scale huNe, size_toRatPoly]
    change r.size ≤ 1
    rcases hrUnit with hr | hr
    · rw [hr]
      exact Nat.le_refl _
    · rw [hr]
      exact Nat.le_refl _

set_option maxHeartbeats 1600000 in
/-- In one variable over the integers, exact coprime cofactors make their
common factor maximal.  The proof rationalizes a primitive part of `d`, uses
the field gcd laws over `Rat[x]`, and descends with
`dvd_of_toRatPoly_dvd_of_primitive`. -/
theorem dvd_gcd_of_coprimeCofactors {f h g : ZPoly}
    (hc : CoprimeCofactors f h g) (d : ZPoly)
    (hf : d ∣ f) (hh : d ∣ h) : d ∣ g := by
  unfold CoprimeCofactors at hc
  rcases hc with ⟨a, b, hfa, hhb, hcop⟩
  have zeroNotUnit : ¬ IsUnit (0 : ZPoly) := by decide
  by_cases hd : d = 0
  · subst d
    rcases hf with ⟨q, hq⟩
    rcases hh with ⟨r, hr⟩
    have hfZero : f = 0 := by
      rw [DensePoly.zero_mul] at hq
      exact hq
    have hhZero : h = 0 := by
      rw [DensePoly.zero_mul] at hr
      exact hr
    have hgZero : g = 0 := by
      apply Classical.byContradiction
      intro hg
      have haZero : a = 0 := by
        apply Classical.byContradiction
        intro ha
        have hprod := mul_ne_zero_of_ne_zero g a hg ha
        exact hprod (hfa.symm.trans hfZero)
      have hbZero : b = 0 := by
        apply Classical.byContradiction
        intro hb
        have hprod := mul_ne_zero_of_ne_zero g b hg hb
        exact hprod (hhb.symm.trans hhZero)
      have hunit := hcop 0
        ⟨1, by rw [haZero]; exact (DensePoly.zero_mul 1).symm⟩
        ⟨1, by rw [hbZero]; exact (DensePoly.zero_mul 1).symm⟩
      exact zeroNotUnit hunit
    refine ⟨0, ?_⟩
    rw [hgZero]
    exact (DensePoly.zero_mul 0).symm
  · have hdContent : content d ≠ 0 := by
      intro hcontent
      apply hd
      have hreconstruct := content_mul_primitivePart d
      rw [hcontent] at hreconstruct
      exact hreconstruct.symm.trans
        (DensePoly.scale_zero_left_semiring (primitivePart d))
    let primitive := primitivePart d
    have hprimitive : Primitive primitive :=
      primitivePart_primitive d hdContent
    have hprimitiveDvdD : primitive ∣ d := by
      refine ⟨DensePoly.C (content d), ?_⟩
      calc
        d = DensePoly.scale (content d) primitive :=
          (content_mul_primitivePart d).symm
        _ = DensePoly.C (content d) * primitive :=
          (C_mul_eq_scale (content d) primitive).symm
        _ = primitive * DensePoly.C (content d) :=
          DensePoly.mul_comm_poly _ _
    have hprimitiveDvdF : primitive ∣ f := dvdTrans hprimitiveDvdD hf
    have hprimitiveDvdH : primitive ∣ h := dvdTrans hprimitiveDvdD hh
    have hcofactorGcdSize := ratGcdSizeLeOne hcop
    have habNe : a ≠ 0 ∨ b ≠ 0 := by
      by_cases ha : a = 0
      · right
        intro hb
        have hunit := hcop 0
          ⟨1, by rw [ha]; exact (DensePoly.zero_mul 1).symm⟩
          ⟨1, by rw [hb]; exact (DensePoly.zero_mul 1).symm⟩
        exact zeroNotUnit hunit
      · exact Or.inl ha
    let xg := DensePoly.xgcd (toRatPoly a) (toRatPoly b)
    let scalar := xg.gcd.coeff 0
    have hxgSize : xg.gcd.size ≤ 1 := by
      rw [DensePoly.xgcd_gcd_eq_gcd]
      exact hcofactorGcdSize
    have hxgNe : xg.gcd ≠ 0 := by
      rw [DensePoly.xgcd_gcd_eq_gcd]
      intro hzero
      rcases habNe with ha | hb
      · apply toRatPoly_ne_zero_of_ne_zero a ha
        rcases DensePoly.gcd_dvd_left (toRatPoly a) (toRatPoly b) with ⟨q, hq⟩
        rw [hzero, DensePoly.zero_mul] at hq
        exact hq
      · apply toRatPoly_ne_zero_of_ne_zero b hb
        rcases DensePoly.gcd_dvd_right (toRatPoly a) (toRatPoly b) with ⟨q, hq⟩
        rw [hzero, DensePoly.zero_mul] at hq
        exact hq
    have hxgC : xg.gcd = DensePoly.C scalar := by
      simpa only [scalar] using ratEqCOfSizeLe hxgSize
    have hscalarNe : scalar ≠ 0 := by
      intro hzero
      apply hxgNe
      rw [hxgC, hzero]
      rfl
    let alpha := DensePoly.scale scalar⁻¹ xg.left
    let beta := DensePoly.scale scalar⁻¹ xg.right
    have hbez : xg.left * toRatPoly a + xg.right * toRatPoly b = xg.gcd := by
      simpa only [xg] using DensePoly.xgcd_bezout (toRatPoly a) (toRatPoly b)
    have hscaleC :
        DensePoly.scale scalar⁻¹ (DensePoly.C scalar) =
          (1 : DensePoly Rat) := by
      change DensePoly.scale scalar⁻¹ (DensePoly.C scalar) = DensePoly.C 1
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale_semiring, DensePoly.coeff_C,
        DensePoly.coeff_C]
      by_cases hn : n = 0
      · simp only [hn, ↓reduceIte]
        exact Rat.inv_mul_cancel scalar hscalarNe
      · simp only [hn, ↓reduceIte]
        exact Rat.mul_zero scalar⁻¹
    have hbezOne :
        alpha * toRatPoly a + beta * toRatPoly b = 1 := by
      calc
        alpha * toRatPoly a + beta * toRatPoly b =
            DensePoly.scale scalar⁻¹ (xg.left * toRatPoly a) +
              DensePoly.scale scalar⁻¹ (xg.right * toRatPoly b) := by
          simp only [alpha, beta, DensePoly.scale_mul]
        _ = DensePoly.scale scalar⁻¹
              (xg.left * toRatPoly a + xg.right * toRatPoly b) :=
          (DensePoly.scale_add _ _ _).symm
        _ = DensePoly.scale scalar⁻¹ xg.gcd := by rw [hbez]
        _ = DensePoly.scale scalar⁻¹ (DensePoly.C scalar) := by rw [hxgC]
        _ = 1 := hscaleC
    have hfRat : toRatPoly f = toRatPoly g * toRatPoly a := by
      rw [← toRatPoly_mul, hfa]
    have hhRat : toRatPoly h = toRatPoly g * toRatPoly b := by
      rw [← toRatPoly_mul, hhb]
    have hcomb :
        alpha * toRatPoly f + beta * toRatPoly h = toRatPoly g := by
      rw [hfRat, hhRat]
      have halpha :
          alpha * (toRatPoly g * toRatPoly a) =
            toRatPoly g * (alpha * toRatPoly a) := by
        calc
          alpha * (toRatPoly g * toRatPoly a) =
              (alpha * toRatPoly g) * toRatPoly a :=
            (DensePoly.mul_assoc_poly _ _ _).symm
          _ = (toRatPoly g * alpha) * toRatPoly a := by
            rw [DensePoly.mul_comm_poly alpha (toRatPoly g)]
          _ = toRatPoly g * (alpha * toRatPoly a) :=
            DensePoly.mul_assoc_poly _ _ _
      have hbeta :
          beta * (toRatPoly g * toRatPoly b) =
            toRatPoly g * (beta * toRatPoly b) := by
        calc
          beta * (toRatPoly g * toRatPoly b) =
              (beta * toRatPoly g) * toRatPoly b :=
            (DensePoly.mul_assoc_poly _ _ _).symm
          _ = (toRatPoly g * beta) * toRatPoly b := by
            rw [DensePoly.mul_comm_poly beta (toRatPoly g)]
          _ = toRatPoly g * (beta * toRatPoly b) :=
            DensePoly.mul_assoc_poly _ _ _
      calc
        alpha * (toRatPoly g * toRatPoly a) +
              beta * (toRatPoly g * toRatPoly b) =
            toRatPoly g * (alpha * toRatPoly a) +
              toRatPoly g * (beta * toRatPoly b) := by
          exact (congrArg
            (fun p : DensePoly Rat => p + beta * (toRatPoly g * toRatPoly b))
            halpha).trans (congrArg
              (fun p : DensePoly Rat => toRatPoly g * (alpha * toRatPoly a) + p)
              hbeta)
        _ = toRatPoly g *
              (alpha * toRatPoly a + beta * toRatPoly b) :=
          (DensePoly.mul_add_right_poly _ _ _).symm
        _ = toRatPoly g * 1 :=
          congrArg (fun p : DensePoly Rat => toRatPoly g * p) hbezOne
        _ = toRatPoly g := DensePoly.mul_one_right_poly _
    have hprimitiveDvdGRat : toRatPoly primitive ∣ toRatPoly g := by
      have hsum := ratDvdAdd
        (ratDvdMulLeft alpha (toRatDvd hprimitiveDvdF))
        (ratDvdMulLeft beta (toRatDvd hprimitiveDvdH))
      rw [hcomb] at hsum
      exact hsum
    have hprimitiveDvdG : primitive ∣ g :=
      dvd_of_toRatPoly_dvd_of_primitive hprimitive hprimitiveDvdGRat
    have hcontents := coprimeContents hcop
    have hcontentDvdF := contentDvdOfDvd hf
    have hcontentDvdH := contentDvdOfDvd hh
    have hfContent : content f = content g * content a := by
      have hcontent := congrArg content hfa
      rw [content_mul] at hcontent
      exact hcontent
    have hhContent : content h = content g * content b := by
      have hcontent := congrArg content hhb
      rw [content_mul] at hcontent
      exact hcontent
    have hcontentNatDvd :
        DensePoly.contentNat d ∣ Int.gcd (content f) (content h) := by
      apply Int.dvd_gcd
      · simpa [content, DensePoly.content] using hcontentDvdF
      · simpa [content, DensePoly.content] using hcontentDvdH
    have hcontentNatDvd' := hcontentNatDvd
    rw [hfContent, hhContent, Int.gcd_mul_left, hcontents, Nat.mul_one]
      at hcontentNatDvd'
    have hcontentDvdG : content d ∣ content g := by
      simpa [content, DensePoly.content] using
        (Int.ofNat_dvd_left.mpr hcontentNatDvd')
    rcases hprimitiveDvdG with ⟨s, hs⟩
    have hsContent : content s = content g := by
      have hcontent := congrArg content hs
      rw [content_mul, show content primitive = 1 from hprimitive,
        Int.one_mul] at hcontent
      exact hcontent.symm
    have hcontentDvdS : content d ∣ content s := by
      rw [hsContent]
      exact hcontentDvdG
    rcases C_dvd_of_dvd_content hcontentDvdS with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      g = primitive * s := hs
      _ = primitive * (DensePoly.C (content d) * t) := by rw [ht]
      _ = (primitive * DensePoly.C (content d)) * t :=
        (DensePoly.mul_assoc_poly _ _ _).symm
      _ = (DensePoly.C (content d) * primitive) * t := by
        rw [DensePoly.mul_comm_poly primitive (DensePoly.C (content d))]
      _ = DensePoly.scale (content d) primitive * t := by
        rw [C_mul_eq_scale]
      _ = d * t := by rw [content_mul_primitivePart]

/-- The public checked certificate packages coprime cofactors. -/
theorem gcdCert_coprimeCofactors (f h : ZPoly) :
    CoprimeCofactors f h (gcd f h) := by
  let cert := gcdCert f h
  have hcheck := gcdCert_checks f h
  have hcop := coprimeCofactors_of_checkGcd hcheck
  rw [gcd_eq_cert]
  exact hcop

/-- The canonical gcd divides the left input. -/
theorem gcd_dvd_left (f h : ZPoly) : gcd f h ∣ f := by
  let cert := gcdCert f h
  have hcheck := gcdCert_checks f h
  rcases checkGcd_sound hcheck with ⟨hf, _, _⟩
  refine ⟨cert.cofL, ?_⟩
  rw [gcd_eq_cert]
  exact hf

/-- The canonical gcd divides the right input. -/
theorem gcd_dvd_right (f h : ZPoly) : gcd f h ∣ h := by
  let cert := gcdCert f h
  have hcheck := gcdCert_checks f h
  rcases checkGcd_sound hcheck with ⟨_, hh, _⟩
  refine ⟨cert.cofR, ?_⟩
  rw [gcd_eq_cert]
  exact hh

/-- Every common divisor divides the canonical gcd. -/
theorem dvd_gcd (d f h : ZPoly) (hf : d ∣ f) (hh : d ∣ h) :
    d ∣ gcd f h :=
  dvd_gcd_of_coprimeCofactors (gcdCert_coprimeCofactors f h) d hf hh

/-- Two mutually dividing gcd candidates satisfying the public normalization
convention are equal. -/
theorem eq_of_normalized_dvd {p q : ZPoly}
    (hpNorm : NormalizedGcd p = true) (hqNorm : NormalizedGcd q = true)
    (hpq : p ∣ q) (hqp : q ∣ p) : p = q := by
  have hpCases : p = 0 ∨
      (0 < DensePoly.leadingCoeff p ∧ 0 < content p) := by
    simpa [NormalizedGcd, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] using hpNorm
  have hqCases : q = 0 ∨
      (0 < DensePoly.leadingCoeff q ∧ 0 < content q) := by
    simpa [NormalizedGcd, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] using hqNorm
  rcases hpCases with hpZero | hpPos
  · rcases hpq with ⟨a, ha⟩
    rw [hpZero, DensePoly.zero_mul] at ha
    exact hpZero.trans ha.symm
  · have hpNe : p ≠ 0 := by
      intro hpZero
      subst p
      have hleadZero : DensePoly.leadingCoeff (0 : ZPoly) = 0 := rfl
      omega
    rcases hqCases with hqZero | hqPos
    · subst q
      rcases hqp with ⟨a, ha⟩
      rw [DensePoly.zero_mul] at ha
      exact False.elim (hpNe ha)
    · have hqNe : q ≠ 0 := by
        intro hqZero'
        subst q
        have hleadZero : DensePoly.leadingCoeff (0 : ZPoly) = 0 := rfl
        omega
      rcases hpq with ⟨a, ha⟩
      rcases hqp with ⟨b, hb⟩
      have haNe : a ≠ 0 := by
        intro haZero
        apply hqNe
        rw [ha, haZero]
        exact (DensePoly.mul_comm_poly p 0).trans (DensePoly.zero_mul p)
      have hbNe : b ≠ 0 := by
        intro hbZero
        apply hpNe
        rw [hb, hbZero]
        exact (DensePoly.mul_comm_poly q 0).trans (DensePoly.zero_mul q)
      have hpab : p = p * (a * b) := by
        calc
          p = q * b := hb
          _ = (p * a) * b := by rw [ha]
          _ = p * (a * b) := DensePoly.mul_assoc_poly p a b
      have hab : a * b = 1 := by
        apply mul_right_cancel_of_ne_zero hpNe
        calc
          (a * b) * p = p * (a * b) := DensePoly.mul_comm_poly _ _
          _ = p := hpab.symm
          _ = 1 * p := by
            rw [DensePoly.mul_comm_poly (1 : ZPoly) p,
              DensePoly.mul_one_right_poly]
      have haSizePos : 0 < a.size := size_pos_of_ne_zero a haNe
      have hbSizePos : 0 < b.size := size_pos_of_ne_zero b hbNe
      have hsize := mul_size_eq_top_succ_of_nonzero a b haSizePos hbSizePos
      have habSize : (a * b).size = 1 := by rw [hab]; rfl
      have hsizeEq : 1 = a.size + b.size - 1 := habSize.symm.trans hsize
      have haSize : a.size = 1 := by omega
      have haC : a = DensePoly.C (a.coeff 0) := by
        apply DensePoly.ext_coeff
        intro n
        rw [DensePoly.coeff_C]
        cases n with
        | zero => simp
        | succ n =>
            rw [DensePoly.coeff_eq_zero_of_size_le a (by omega)]
            rfl
      have hleadA : 0 < DensePoly.leadingCoeff a := by
        have hlead := leadingCoeff_mul_of_nonzero p a hpNe haNe
        rw [← ha] at hlead
        have hprodPos :
            0 < DensePoly.leadingCoeff p * DensePoly.leadingCoeff a := by
          rw [← hlead]
          exact hqPos.1
        exact Int.pos_of_mul_pos_right hprodPos hpPos.1
      have hleadAB := leadingCoeff_mul_of_nonzero a b haNe hbNe
      rw [hab] at hleadAB
      have hleadOne : DensePoly.leadingCoeff (1 : ZPoly) = 1 := by rfl
      rw [hleadOne] at hleadAB
      have hleadAOne : DensePoly.leadingCoeff a = 1 :=
        Int.eq_one_of_mul_eq_one_right (Int.le_of_lt hleadA) hleadAB.symm
      have hcoeffA : a.coeff 0 = 1 := by
        rw [DensePoly.leadingCoeff_eq_coeff_last a haSizePos,
          haSize] at hleadAOne
        exact hleadAOne
      have haOne : a = 1 := by
        rw [haC, hcoeffA]
        rfl
      rw [ha, haOne, DensePoly.mul_one_right_poly]

end ZPoly

end Hex
