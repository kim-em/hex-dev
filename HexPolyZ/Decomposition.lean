/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly
public import HexPolyZ.Rational
import all HexPolyZ.Core
import all HexPolyZ.Rational

public section
set_option backward.proofsInPublic true

/-!
Integer primitive-square-free decomposition correctness: reassembly over
the rationals, squareFreeCore / repeatedPart primitivity and leading
coefficients, and the signed reassembly identity.
-/
namespace Hex

namespace ZPoly
/-- A primitive integer polynomial is nonzero. -/
theorem ne_zero_of_primitive (p : ZPoly) (hp : Primitive p) :
    p ≠ 0 := by
  intro hzero
  have hcontent : content p = 0 := by
    rw [hzero]
    simp [content, DensePoly.content_zero]
  rw [Primitive, hcontent] at hp
  contradiction

private theorem primitive_one :
    Primitive (1 : ZPoly) := by
  change content (DensePoly.C (1 : Int)) = 1
  rw [content_C_int]
  rfl

private theorem toRatPoly_injective {p q : ZPoly}
    (h : toRatPoly p = toRatPoly q) :
    p = q := by
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun r : DensePoly Rat => r.coeff n) h
  change (toRatPoly p).coeff n = (toRatPoly q).coeff n at hcoeff
  rw [coeff_toRatPoly, coeff_toRatPoly] at hcoeff
  exact_mod_cast hcoeff

private theorem ratPolyPrimitivePart_ne_zero_of_ne_zero (p : DensePoly Rat)
    (hp : p ≠ 0) :
    ratPolyPrimitivePart p ≠ 0 := by
  rcases ratPolyPrimitivePart_rational_associate p with ⟨unit, hunit⟩
  intro hprimitive_zero
  apply hp
  rw [hunit, hprimitive_zero, toRatPoly_zero]
  exact rat_scale_zero_right unit

private theorem int_eq_one_or_neg_one_of_natAbs_eq_one {c : Int}
    (habs : c.natAbs = 1) :
    c = 1 ∨ c = -1 := by
  cases c with
  | ofNat n =>
      left
      simp at habs
      subst n
      rfl
  | negSucc n =>
      right
      simp at habs
      have hn : n = 0 := by omega
      subst n
      rfl

/-- Sign-normalization fixes the constant `1`: its leading coefficient is already
positive, so `normalizePrimitiveSign (C 1) = 1`. -/
private theorem normalizePrimitiveSign_C_one :
    normalizePrimitiveSign (DensePoly.C (1 : Int)) = 1 := by
  unfold normalizePrimitiveSign
  have hlead : ¬ DensePoly.leadingCoeff (DensePoly.C (1 : Int)) < 0 := by
    simp [DensePoly.leadingCoeff, DensePoly.coeffs_C_of_ne_zero (by decide : (1 : Int) ≠ 0)]
  rw [if_neg hlead]
  rfl

/-- Sign-normalization sends the constant `-1` to `1`: its negative leading
coefficient triggers the negating branch, recovering the positive unit. -/
private theorem normalizePrimitiveSign_C_neg_one :
    normalizePrimitiveSign (DensePoly.C (-1 : Int)) = 1 := by
  unfold normalizePrimitiveSign
  have hlead : DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) < 0 := by
    simp [DensePoly.leadingCoeff, DensePoly.coeffs_C_of_ne_zero (by decide : (-1 : Int) ≠ 0)]
  rw [if_pos hlead]
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) (-1 : Int) (DensePoly.C (-1 : Int)) n
    (Int.mul_zero (-1 : Int))]
  change -1 * (DensePoly.C (-1 : Int)).coeff n = (DensePoly.C (1 : Int)).coeff n
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    change - (0 : Int) = (0 : Int)
    rfl

/-- A primitive polynomial of size at most one is a unit constant `±1`, which
sign-normalization collapses to `1`; the characterising case on primitive
constants. -/
private theorem normalizePrimitiveSign_eq_one_of_primitive_size_le_one
    (p : ZPoly) (hprimitive : Primitive p) (hsize : p.size ≤ 1) :
    normalizePrimitiveSign p = 1 := by
  have hpC := densePoly_eq_C_coeff_zero_of_size_le_one p hsize
  have hcontent :
      content (DensePoly.C (p.coeff 0)) = 1 := by
    have hprimitive_eq : content p = 1 := hprimitive
    rw [hpC] at hprimitive_eq
    exact hprimitive_eq
  have habs : (p.coeff 0).natAbs = 1 := by
    have hcast : ((p.coeff 0).natAbs : Int) = 1 := by
      simpa [content_C_int] using hcontent
    exact_mod_cast hcast
  rcases int_eq_one_or_neg_one_of_natAbs_eq_one habs with hcoeff | hcoeff
  · rw [hpC, hcoeff]
    exact normalizePrimitiveSign_C_one
  · rw [hpC, hcoeff]
    exact normalizePrimitiveSign_C_neg_one

private theorem squareFreeRat_one :
    SquareFreeRat 1 := by
  unfold SquareFreeRat
  rw [toRatPoly_one]
  exact DensePoly.size_C_le_one (1 : Rat)

/-- The primitive field reassembles over `Rat[x]` as a rational scalar multiple
of the product of the square-free core and repeated part. -/
theorem primitiveSquareFreeDecomposition_reassembly_over_rat (f : ZPoly) :
    let d := primitiveSquareFreeDecomposition f
    ∃ unit : Rat,
      toRatPoly d.primitive =
        DensePoly.scale unit (toRatPoly d.squareFreeCore * toRatPoly d.repeatedPart) := by
  unfold primitiveSquareFreeDecomposition
  by_cases hzero : (primitivePart f).isZero = true
  · refine ⟨0, ?_⟩
    rw [if_pos hzero]
    have hprimitive_zero : primitivePart f = 0 :=
      densePoly_eq_zero_of_isZero_true (primitivePart f) hzero
    rw [hprimitive_zero, toRatPoly_zero, rat_scale_zero]
  · rw [if_neg hzero]
    let ratPrimitive := toRatPoly (primitivePart f)
    let derivative := DensePoly.derivative ratPrimitive
    by_cases hderivative : derivative.isZero = true
    · rcases toRatPoly_normalizePrimitiveSign_rational_associate (primitivePart f) with
        ⟨unit, hunit⟩
      refine ⟨unit, ?_⟩
      rw [if_pos hderivative, toRatPoly_one, DensePoly.mul_one_right_poly]
      simpa [ratPrimitive] using hunit
    · rw [if_neg hderivative]
      let repeatedRat := DensePoly.gcd ratPrimitive derivative
      let quotientRat := ratPrimitive / repeatedRat
      rcases ratPolyPrimitivePart_rational_associate quotientRat with
        ⟨coreUnit, hcore⟩
      rcases ratPolyPrimitivePart_rational_associate repeatedRat with
        ⟨repeatedUnit, hrepeated⟩
      refine ⟨coreUnit * repeatedUnit, ?_⟩
      have htarget :
          ratPrimitive =
            DensePoly.scale (coreUnit * repeatedUnit)
              (toRatPoly (ratPolyPrimitivePart quotientRat) *
                toRatPoly (ratPolyPrimitivePart repeatedRat)) := by
        have hrec : quotientRat * repeatedRat = ratPrimitive := by
          simpa [quotientRat, repeatedRat] using rat_div_gcd_mul_reconstruct ratPrimitive derivative
        rw [← hrec]
        calc
          quotientRat * repeatedRat =
              DensePoly.scale coreUnit (toRatPoly (ratPolyPrimitivePart quotientRat)) *
                repeatedRat := by
            exact congrArg (fun x => x * repeatedRat) hcore
          _ =
              DensePoly.scale coreUnit (toRatPoly (ratPolyPrimitivePart quotientRat)) *
                DensePoly.scale repeatedUnit (toRatPoly (ratPolyPrimitivePart repeatedRat)) := by
            exact congrArg
              (fun x => DensePoly.scale coreUnit (toRatPoly (ratPolyPrimitivePart quotientRat)) * x)
              hrepeated
          _ =
              DensePoly.scale (coreUnit * repeatedUnit)
                (toRatPoly (ratPolyPrimitivePart quotientRat) *
                  toRatPoly (ratPolyPrimitivePart repeatedRat)) := by
            rw [rat_scale_mul_scale]
      simpa [ratPrimitive, derivative, repeatedRat, quotientRat] using htarget

/-- A nonzero square-free core from the primitive square-free decomposition is
square-free over `Rat[x]`. -/
theorem primitiveSquareFreeDecomposition_squareFreeCore
    (f : ZPoly)
    (hcore : (primitiveSquareFreeDecomposition f).squareFreeCore ≠ 0) :
    SquareFreeRat (primitiveSquareFreeDecomposition f).squareFreeCore := by
  unfold primitiveSquareFreeDecomposition at hcore ⊢
  by_cases hzero : (primitivePart f).isZero = true
  · simp [hzero] at hcore
  · simp [hzero]
    let p := primitivePart f
    let ratPrimitive := toRatPoly p
    let derivative := DensePoly.derivative ratPrimitive
    by_cases hderivative : derivative.isZero = true
    · have hderivative_eq : derivative = 0 :=
        densePoly_eq_zero_of_isZero_true derivative hderivative
      have hcontent_ne : content f ≠ 0 := by
        intro hcontent
        have hpart_zero : primitivePart f = 0 := by
          simpa [primitivePart] using
            DensePoly.primitivePart_eq_zero_of_content_eq_zero f
              (by simpa [content] using hcontent)
        have hisZero : (primitivePart f).isZero = true := by
          rw [hpart_zero]
          rfl
        rw [hisZero] at hzero
        contradiction
      have hprimitive : Primitive p := by
        simpa [p] using primitivePart_primitive f hcontent_ne
      have hsize : p.size ≤ 1 := by
        exact size_le_one_of_toRatPoly_derivative_zero p (by
          simpa [derivative, ratPrimitive] using hderivative_eq)
      have hcore_eq : normalizePrimitiveSign p = 1 :=
        normalizePrimitiveSign_eq_one_of_primitive_size_le_one p hprimitive hsize
      rw [if_pos hderivative]
      change SquareFreeRat (normalizePrimitiveSign p)
      rw [hcore_eq]
      exact squareFreeRat_one
    · rw [if_neg hderivative]
      let repeatedRat := DensePoly.gcd ratPrimitive derivative
      let quotientRat := ratPrimitive / repeatedRat
      have hp_ne : p ≠ 0 := by
        intro hp_zero
        apply hzero
        have hprimitive_zero : primitivePart f = 0 := by
          simpa [p] using hp_zero
        have hisZero : (primitivePart f).isZero = true := by
          rw [hprimitive_zero]
          rfl
        simpa [p] using hisZero
      have hratPrimitive_ne : ratPrimitive ≠ 0 := by
        exact toRatPoly_ne_zero_of_ne_zero p hp_ne
      have hrepeated_ne : repeatedRat ≠ 0 := by
        intro hrepeated_zero
        rcases DensePoly.gcd_dvd_left ratPrimitive derivative with ⟨a, ha⟩
        apply hratPrimitive_ne
        have hzero : ratPrimitive = 0 := by
          rw [show DensePoly.gcd ratPrimitive derivative = repeatedRat by rfl] at ha
          rw [hrepeated_zero, DensePoly.zero_mul] at ha
          exact ha
        exact hzero
      have hquotient_ne : quotientRat ≠ 0 := by
        intro hquotient_zero
        have hrec : quotientRat * repeatedRat = ratPrimitive := by
          simpa [quotientRat, repeatedRat] using
            rat_div_gcd_mul_reconstruct ratPrimitive derivative
        apply hratPrimitive_ne
        rw [hquotient_zero, DensePoly.zero_mul] at hrec
        exact hrec.symm
      have hsquare :
          (DensePoly.gcd quotientRat (DensePoly.derivative quotientRat)).size ≤ 1 := by
        simpa [quotientRat, repeatedRat, derivative] using
          rat_quotient_derivative_squareFree ratPrimitive
      rcases ratPolyPrimitivePart_rational_associate quotientRat with ⟨unit, hunit⟩
      let coreRat := toRatPoly (ratPolyPrimitivePart quotientRat)
      have hunit_core : quotientRat = DensePoly.scale unit coreRat := by
        simpa [coreRat] using hunit
      have hunit_ne : unit ≠ 0 := by
        intro hunit_zero
        apply hquotient_ne
        rw [hunit_core, hunit_zero]
        exact rat_scale_zero coreRat
      have htransfer :
          (DensePoly.gcd coreRat (DensePoly.derivative coreRat)).size ≤ 1 :=
        rat_squareFree_of_rational_associate
          (p := quotientRat)
          (q := coreRat)
          (u := unit)
          hunit_ne hquotient_ne hunit_core hsquare
      simpa [SquareFreeRat, coreRat] using htransfer

private theorem ratPolyPrimitivePart_div_gcd_mul_primitive
    (p : ZPoly) (hp_ne : p ≠ 0) :
    let ratPrimitive := toRatPoly p
    let derivative := DensePoly.derivative ratPrimitive
    let repeatedRat := DensePoly.gcd ratPrimitive derivative
    let quotientRat := ratPrimitive / repeatedRat
    Primitive (ratPolyPrimitivePart quotientRat * ratPolyPrimitivePart repeatedRat) := by
  let ratPrimitive := toRatPoly p
  let derivative := DensePoly.derivative ratPrimitive
  let repeatedRat := DensePoly.gcd ratPrimitive derivative
  let quotientRat := ratPrimitive / repeatedRat
  have hratPrimitive_ne : ratPrimitive ≠ 0 :=
    toRatPoly_ne_zero_of_ne_zero p hp_ne
  have hrepeated_ne : repeatedRat ≠ 0 := by
    intro hrepeated_zero
    rcases DensePoly.gcd_dvd_left ratPrimitive derivative with ⟨a, ha⟩
    apply hratPrimitive_ne
    have hzero : ratPrimitive = 0 := by
      rw [show DensePoly.gcd ratPrimitive derivative = repeatedRat by rfl] at ha
      rw [hrepeated_zero, DensePoly.zero_mul] at ha
      exact ha
    exact hzero
  have hquotient_ne : quotientRat ≠ 0 := by
    intro hquotient_zero
    have hrec : quotientRat * repeatedRat = ratPrimitive := by
      simpa [quotientRat, repeatedRat] using
        rat_div_gcd_mul_reconstruct ratPrimitive derivative
    apply hratPrimitive_ne
    rw [hquotient_zero, DensePoly.zero_mul] at hrec
    exact hrec.symm
  have hcore_ne : ratPolyPrimitivePart quotientRat ≠ 0 :=
    ratPolyPrimitivePart_ne_zero_of_ne_zero quotientRat hquotient_ne
  have hrepeated_part_ne : ratPolyPrimitivePart repeatedRat ≠ 0 :=
    ratPolyPrimitivePart_ne_zero_of_ne_zero repeatedRat hrepeated_ne
  have hcore_primitive : Primitive (ratPolyPrimitivePart quotientRat) :=
    ratPolyPrimitivePart_primitive quotientRat
      (content_ne_zero_of_ne_zero (ratPolyPrimitivePart quotientRat) hcore_ne)
  have hrepeated_primitive : Primitive (ratPolyPrimitivePart repeatedRat) :=
    ratPolyPrimitivePart_primitive repeatedRat
      (content_ne_zero_of_ne_zero (ratPolyPrimitivePart repeatedRat) hrepeated_part_ne)
  exact primitive_mul (ratPolyPrimitivePart quotientRat) (ratPolyPrimitivePart repeatedRat)
    hcore_primitive hrepeated_primitive

/-- For nonzero input, the product of the square-free core and repeated part is
primitive. -/
theorem primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive
    (f : ZPoly) (hf : f ≠ 0) :
    let d := primitiveSquareFreeDecomposition f
    Primitive (d.squareFreeCore * d.repeatedPart) := by
  have hcontent_ne : content f ≠ 0 := content_ne_zero_of_ne_zero f hf
  have hprimitive : Primitive (primitivePart f) :=
    primitivePart_primitive f hcontent_ne
  have hprimitive_ne : primitivePart f ≠ 0 :=
    ne_zero_of_primitive (primitivePart f) hprimitive
  have hprimitive_not_isZero : (primitivePart f).isZero = false := by
    cases hzero : (primitivePart f).isZero
    · rfl
    · exfalso
      exact hprimitive_ne (densePoly_eq_zero_of_isZero_true (primitivePart f) hzero)
  unfold primitiveSquareFreeDecomposition
  rw [if_neg (by simpa using hprimitive_not_isZero)]
  let p := primitivePart f
  let ratPrimitive := toRatPoly p
  let derivative := DensePoly.derivative ratPrimitive
  by_cases hderivative : derivative.isZero = true
  · rw [if_pos hderivative]
    have hderivative_eq : derivative = 0 :=
      densePoly_eq_zero_of_isZero_true derivative hderivative
    have hsize : p.size ≤ 1 := by
      exact size_le_one_of_toRatPoly_derivative_zero p (by
        simpa [derivative, ratPrimitive] using hderivative_eq)
    have hp_primitive : Primitive p := by
      simpa [p] using hprimitive
    have hcore_eq : normalizePrimitiveSign p = 1 :=
      normalizePrimitiveSign_eq_one_of_primitive_size_le_one p hp_primitive hsize
    rw [hcore_eq]
    change Primitive ((1 : ZPoly) * (1 : ZPoly))
    exact primitive_mul 1 1 primitive_one primitive_one
  · rw [if_neg hderivative]
    have hp_ne : p ≠ 0 := by
      simpa [p] using hprimitive_ne
    simpa [p, ratPrimitive, derivative] using
      ratPolyPrimitivePart_div_gcd_mul_primitive p hp_ne

/-- A nonzero degree-zero square-free core from the primitive square-free
decomposition is `1`. -/
theorem primitiveSquareFreeDecomposition_squareFreeCore_eq_one_of_degree_zero
    (f : ZPoly)
    (hcore_ne : (primitiveSquareFreeDecomposition f).squareFreeCore ≠ 0)
    (hdegree : (primitiveSquareFreeDecomposition f).squareFreeCore.degree?.getD 0 = 0) :
    (primitiveSquareFreeDecomposition f).squareFreeCore = 1 := by
  unfold primitiveSquareFreeDecomposition at hcore_ne hdegree ⊢
  by_cases hzero : (primitivePart f).isZero = true
  · simp [hzero] at hcore_ne
  · simp [hzero] at hcore_ne hdegree ⊢
    let p := primitivePart f
    let ratPrimitive := toRatPoly p
    let derivative := DensePoly.derivative ratPrimitive
    by_cases hderivative : derivative.isZero = true
    · rw [if_pos hderivative] at hcore_ne hdegree ⊢
      have hderivative_eq : derivative = 0 :=
        densePoly_eq_zero_of_isZero_true derivative hderivative
      have hcontent_ne : content f ≠ 0 := by
        intro hcontent
        have hpart_zero : primitivePart f = 0 := by
          simpa [primitivePart] using
            DensePoly.primitivePart_eq_zero_of_content_eq_zero f
              (by simpa [content] using hcontent)
        have hisZero : (primitivePart f).isZero = true := by
          rw [hpart_zero]
          rfl
        rw [hisZero] at hzero
        contradiction
      have hprimitive : Primitive p := by
        simpa [p] using primitivePart_primitive f hcontent_ne
      have hsize : p.size ≤ 1 := by
        exact size_le_one_of_toRatPoly_derivative_zero p (by
          simpa [derivative, ratPrimitive] using hderivative_eq)
      exact normalizePrimitiveSign_eq_one_of_primitive_size_le_one p hprimitive hsize
    · rw [if_neg hderivative] at hcore_ne hdegree ⊢
      let repeatedRat := DensePoly.gcd ratPrimitive derivative
      let quotientRat := ratPrimitive / repeatedRat
      let core := ratPolyPrimitivePart quotientRat
      have hsize : core.size ≤ 1 :=
        size_le_one_of_degree_getD_zero core (by simpa [core] using hdegree)
      have hcontent_ne : content core ≠ 0 :=
        content_ne_zero_of_ne_zero core (by simpa [core] using hcore_ne)
      have hprimitive : Primitive core :=
        ratPolyPrimitivePart_primitive quotientRat (by simpa [core] using hcontent_ne)
      have hnormalized : normalizePrimitiveSign core = 1 :=
        normalizePrimitiveSign_eq_one_of_primitive_size_le_one core hprimitive hsize
      have hlead_nonneg : 0 ≤ DensePoly.leadingCoeff core := by
        simpa [core] using leadingCoeff_ratPolyPrimitivePart_nonneg quotientRat
      have hself : normalizePrimitiveSign core = core :=
        normalizePrimitiveSign_eq_self_of_leadingCoeff_nonneg core hlead_nonneg
      rw [hself] at hnormalized
      simpa [core] using hnormalized

/-- Companion to `primitiveSquareFreeDecomposition_squareFreeCore_eq_one_of_degree_zero`:
when the recorded square-free core has degree zero (and is nonzero), the recorded
`repeatedPart` collapses to `1`. The derivative-zero branch settles the goal by the
literal `repeatedPart := 1` field, while the derivative-nonzero branch is ruled out
via the gcd-derivative degree arithmetic (`derivative.size ≤ ratPrimitive.size - 1`
combined with the quotient being a rational unit). -/
theorem primitiveSquareFreeDecomposition_repeatedPart_eq_one_of_squareFreeCore_degree_zero
    (f : ZPoly)
    (hcore_ne : (primitiveSquareFreeDecomposition f).squareFreeCore ≠ 0)
    (hdegree : (primitiveSquareFreeDecomposition f).squareFreeCore.degree?.getD 0 = 0) :
    (primitiveSquareFreeDecomposition f).repeatedPart = 1 := by
  unfold primitiveSquareFreeDecomposition at hcore_ne hdegree ⊢
  by_cases hzero : (primitivePart f).isZero = true
  · simp [hzero] at hcore_ne
  · simp [hzero] at hcore_ne hdegree ⊢
    let p := primitivePart f
    let ratPrimitive := toRatPoly p
    let derivative := DensePoly.derivative ratPrimitive
    by_cases hderivative : derivative.isZero = true
    · -- Case 2: `repeatedPart := 1` by definition.
      rw [if_pos hderivative]
    · -- Case 3: rule out via gcd-derivative degree arithmetic.
      exfalso
      rw [if_neg hderivative] at hcore_ne hdegree
      let repeatedRat := DensePoly.gcd ratPrimitive derivative
      let quotientRat := ratPrimitive / repeatedRat
      let core := ratPolyPrimitivePart quotientRat
      -- `core.size ≤ 1` from `hdegree` (matching the `_squareFreeCore` analogue).
      have hcore_size : core.size ≤ 1 :=
        size_le_one_of_degree_getD_zero core (by simpa [core] using hdegree)
      have hcore_ne' : core ≠ 0 := by simpa [core] using hcore_ne
      have hcore_prim : Primitive core :=
        ratPolyPrimitivePart_primitive quotientRat
          (content_ne_zero_of_ne_zero core hcore_ne')
      have hcore_lead_nonneg : 0 ≤ DensePoly.leadingCoeff core :=
        leadingCoeff_ratPolyPrimitivePart_nonneg quotientRat
      have hcore_normalize : normalizePrimitiveSign core = 1 :=
        normalizePrimitiveSign_eq_one_of_primitive_size_le_one core hcore_prim hcore_size
      have hcore_self : normalizePrimitiveSign core = core :=
        normalizePrimitiveSign_eq_self_of_leadingCoeff_nonneg core hcore_lead_nonneg
      have hcore_eq_one : core = 1 := hcore_self ▸ hcore_normalize
      -- `primitivePart f ≠ 0` (since `(primitivePart f).isZero ≠ true`).
      have hp_ne : primitivePart f ≠ 0 := by
        intro h
        apply hzero
        rw [h]
        rfl
      have hratPrim_ne : ratPrimitive ≠ 0 :=
        toRatPoly_ne_zero_of_ne_zero (primitivePart f) hp_ne
      have hratPrim_size_ne : ratPrimitive.size ≠ 0 := by
        intro h
        exact hratPrim_ne (rat_eq_zero_of_size_zero ratPrimitive h)
      -- `derivative ≠ 0` from `hderivative`.
      have hder_ne : derivative ≠ 0 := by
        intro h
        apply hderivative
        change derivative.isZero = true
        rw [h]
        rfl
      have hder_size_ne : derivative.size ≠ 0 := by
        intro h
        exact hder_ne (rat_eq_zero_of_size_zero derivative h)
      -- `ratPrimitive.size ≥ 2` (converse of `rat_size_le_one_of_derivative_zero`).
      have hratPrim_size_ge_two : 2 ≤ ratPrimitive.size := by
        by_cases hle : 2 ≤ ratPrimitive.size
        · exact hle
        · have hlt : ratPrimitive.size < 2 := Nat.lt_of_not_ge hle
          exact absurd
            (rat_derivative_zero_of_size_le_one ratPrimitive (by omega)) hder_ne
      -- `core = 1` + `rational_associate` ⇒ `quotientRat = scale u 1` for some `u : Rat`.
      rcases ratPolyPrimitivePart_rational_associate quotientRat with ⟨u, hu⟩
      change quotientRat = DensePoly.scale u (toRatPoly core) at hu
      rw [show core = 1 from hcore_eq_one, toRatPoly_one] at hu
      -- `ratPrimitive = quotientRat * repeatedRat` (reconstruction).
      have hreconstruct : quotientRat * repeatedRat = ratPrimitive :=
        rat_div_gcd_mul_reconstruct ratPrimitive derivative
      by_cases hu_zero : u = 0
      · -- `u = 0` ⇒ `quotientRat = 0` ⇒ `ratPrimitive = 0`, contradicting `hratPrim_ne`.
        apply hratPrim_ne
        rw [← hreconstruct, hu, hu_zero, rat_scale_zero, DensePoly.zero_mul]
      · -- `u ≠ 0`: `ratPrimitive = scale u repeatedRat`, so the sizes agree.
        have hratPrim_eq_scale : ratPrimitive = DensePoly.scale u repeatedRat := by
          rw [← hreconstruct, hu]
          have hmul := rat_scale_mul_scale u 1 1 repeatedRat
          rw [rat_scale_one, Rat.mul_one,
            DensePoly.mul_comm_poly (1 : DensePoly Rat) repeatedRat,
            DensePoly.mul_one_right_poly] at hmul
          exact hmul
        have hsize_eq : ratPrimitive.size = repeatedRat.size := by
          rw [hratPrim_eq_scale]
          exact rat_scale_size_of_ne_zero hu_zero repeatedRat
        have hrep_size_ne : repeatedRat.size ≠ 0 := hsize_eq ▸ hratPrim_size_ne
        have hrep_dvd_der : repeatedRat ∣ derivative :=
          DensePoly.gcd_dvd_right ratPrimitive derivative
        have hrep_le_der : repeatedRat.size ≤ derivative.size :=
          rat_size_le_of_dvd_nonzero hrep_size_ne hder_size_ne hrep_dvd_der
        have hder_le_pred : derivative.size ≤ ratPrimitive.size - 1 :=
          rat_derivative_size_le_pred ratPrimitive
        omega

/-- The square-free core produced by primitive square-free decomposition has
nonnegative leading coefficient. -/
theorem leadingCoeff_squareFreeCore_nonneg (f : ZPoly) :
    0 ≤ DensePoly.leadingCoeff (primitiveSquareFreeDecomposition f).squareFreeCore := by
  unfold primitiveSquareFreeDecomposition
  by_cases hzero : (primitivePart f).isZero
  · simp [hzero]
  · simp [hzero]
    by_cases hderiv :
        (DensePoly.derivative (toRatPoly (primitivePart f))).isZero
    · simp [hderiv]
      exact leadingCoeff_normalizePrimitiveSign_nonneg _
    · simp [hderiv]
      exact leadingCoeff_ratPolyPrimitivePart_nonneg _

/-- The repeated part produced by primitive square-free decomposition has
nonnegative leading coefficient. -/
theorem leadingCoeff_repeatedPart_nonneg (f : ZPoly) :
    0 ≤ DensePoly.leadingCoeff (primitiveSquareFreeDecomposition f).repeatedPart := by
  unfold primitiveSquareFreeDecomposition
  by_cases hzero : (primitivePart f).isZero
  · simp [hzero]
  · simp [hzero]
    by_cases hderiv :
        (DensePoly.derivative (toRatPoly (primitivePart f))).isZero
    · simp [hderiv]
    · simp [hderiv]
      exact leadingCoeff_ratPolyPrimitivePart_nonneg _

/-- For nonzero input, the product of the square-free core and repeated part has
positive leading coefficient. -/
theorem primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_leadingCoeff_pos
    (f : ZPoly) (hf : f ≠ 0) :
    let d := primitiveSquareFreeDecomposition f
    0 < DensePoly.leadingCoeff (d.squareFreeCore * d.repeatedPart) := by
  have hcontent_ne : content f ≠ 0 := content_ne_zero_of_ne_zero f hf
  have hprimitive : Primitive (primitivePart f) :=
    primitivePart_primitive f hcontent_ne
  have hprimitive_ne : primitivePart f ≠ 0 :=
    ne_zero_of_primitive (primitivePart f) hprimitive
  have hprimitive_not_isZero : (primitivePart f).isZero = false := by
    cases hzero : (primitivePart f).isZero
    · rfl
    · exfalso
      exact hprimitive_ne (densePoly_eq_zero_of_isZero_true (primitivePart f) hzero)
  unfold primitiveSquareFreeDecomposition
  rw [if_neg (by simpa using hprimitive_not_isZero)]
  let p := primitivePart f
  let ratPrimitive := toRatPoly p
  let derivative := DensePoly.derivative ratPrimitive
  by_cases hderivative : derivative.isZero = true
  · rw [if_pos hderivative]
    have hderivative_eq : derivative = 0 :=
      densePoly_eq_zero_of_isZero_true derivative hderivative
    have hsize : p.size ≤ 1 := by
      exact size_le_one_of_toRatPoly_derivative_zero p (by
        simpa [derivative, ratPrimitive] using hderivative_eq)
    have hp_primitive : Primitive p := by
      simpa [p] using hprimitive
    have hcore_eq : normalizePrimitiveSign p = 1 :=
      normalizePrimitiveSign_eq_one_of_primitive_size_le_one p hp_primitive hsize
    have hprod_pos : 0 < DensePoly.leadingCoeff ((1 : ZPoly) * (1 : ZPoly)) := by
      rw [leadingCoeff_mul_of_nonzero (1 : ZPoly) (1 : ZPoly)
        (by decide) (by decide)]
      exact Int.mul_pos leadingCoeff_one_pos leadingCoeff_one_pos
    simpa [p, hcore_eq] using hprod_pos
  · rw [if_neg hderivative]
    let repeatedRat := DensePoly.gcd ratPrimitive derivative
    let quotientRat := ratPrimitive / repeatedRat
    have hp_ne : p ≠ 0 := by
      simpa [p] using hprimitive_ne
    have hratPrimitive_ne : ratPrimitive ≠ 0 :=
      toRatPoly_ne_zero_of_ne_zero p hp_ne
    have hrepeated_ne : repeatedRat ≠ 0 := by
      intro hrepeated_zero
      rcases DensePoly.gcd_dvd_left ratPrimitive derivative with ⟨a, ha⟩
      apply hratPrimitive_ne
      have hzero : ratPrimitive = 0 := by
        rw [show DensePoly.gcd ratPrimitive derivative = repeatedRat by rfl] at ha
        rw [hrepeated_zero, DensePoly.zero_mul] at ha
        exact ha
      exact hzero
    have hquotient_ne : quotientRat ≠ 0 := by
      intro hquotient_zero
      have hrec : quotientRat * repeatedRat = ratPrimitive := by
        simpa [quotientRat, repeatedRat] using
          rat_div_gcd_mul_reconstruct ratPrimitive derivative
      apply hratPrimitive_ne
      rw [hquotient_zero, DensePoly.zero_mul] at hrec
      exact hrec.symm
    have hcore_pos :
        0 < DensePoly.leadingCoeff (ratPolyPrimitivePart quotientRat) :=
      leadingCoeff_ratPolyPrimitivePart_pos_of_ne_zero quotientRat hquotient_ne
    have hrepeated_pos :
        0 < DensePoly.leadingCoeff (ratPolyPrimitivePart repeatedRat) :=
      leadingCoeff_ratPolyPrimitivePart_pos_of_ne_zero repeatedRat hrepeated_ne
    have hcore_part_ne : ratPolyPrimitivePart quotientRat ≠ 0 :=
      ratPolyPrimitivePart_ne_zero_of_ne_zero quotientRat hquotient_ne
    have hrepeated_part_ne : ratPolyPrimitivePart repeatedRat ≠ 0 :=
      ratPolyPrimitivePart_ne_zero_of_ne_zero repeatedRat hrepeated_ne
    have hprod_pos :
        0 < DensePoly.leadingCoeff
          (ratPolyPrimitivePart quotientRat * ratPolyPrimitivePart repeatedRat) := by
      rw [leadingCoeff_mul_of_nonzero
        (ratPolyPrimitivePart quotientRat) (ratPolyPrimitivePart repeatedRat)
        hcore_part_ne hrepeated_part_ne]
      exact Int.mul_pos hcore_pos hrepeated_pos
    simpa [p, ratPrimitive, derivative, repeatedRat, quotientRat] using hprod_pos

/-- For nonzero input, the product of the square-free core and repeated part
reassembles the primitive part up to sign. -/
theorem primitiveSquareFreeDecomposition_reassembly_signed
    (f : ZPoly) (hf : f ≠ 0) :
    let d := primitiveSquareFreeDecomposition f
    ∃ ε : Int, (ε = 1 ∨ ε = -1) ∧
      DensePoly.scale ε (d.squareFreeCore * d.repeatedPart) =
        primitivePart f := by
  let d := primitiveSquareFreeDecomposition f
  have hdprimitive : d.primitive = primitivePart f := by
    simpa [d] using primitiveSquareFreeDecomposition_primitive f
  have hcontent_ne : content f ≠ 0 := content_ne_zero_of_ne_zero f hf
  have hprimitive : Primitive d.primitive := by
    rw [hdprimitive]
    exact primitivePart_primitive f hcontent_ne
  have hprimitive_ne : d.primitive ≠ 0 :=
    ne_zero_of_primitive d.primitive hprimitive
  have hproduct_primitive : Primitive (d.squareFreeCore * d.repeatedPart) := by
    simpa [d] using
      primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive f hf
  have hproduct_ne : d.squareFreeCore * d.repeatedPart ≠ 0 :=
    ne_zero_of_primitive (d.squareFreeCore * d.repeatedPart) hproduct_primitive
  rcases primitiveSquareFreeDecomposition_reassembly_over_rat f with ⟨unit, hunit⟩
  have hunit_product :
      toRatPoly d.primitive =
        DensePoly.scale unit (toRatPoly (d.squareFreeCore * d.repeatedPart)) := by
    simpa [d, toRatPoly_mul] using hunit
  rcases rational_associate_primitive_unit hprimitive hprimitive_ne
      hproduct_primitive hproduct_ne hunit_product with hunit_one | hunit_neg
  · refine ⟨1, Or.inl rfl, ?_⟩
    apply toRatPoly_injective
    rw [toRatPoly_scale_int]
    change DensePoly.scale (1 : Rat) (toRatPoly (d.squareFreeCore * d.repeatedPart)) =
      toRatPoly (primitivePart f)
    have htarget := hunit_product
    rw [hunit_one, rat_scale_one] at htarget
    rw [rat_scale_one, ← hdprimitive]
    exact htarget.symm
  · refine ⟨-1, Or.inr rfl, ?_⟩
    apply toRatPoly_injective
    rw [toRatPoly_scale_int]
    change DensePoly.scale (-1 : Rat) (toRatPoly (d.squareFreeCore * d.repeatedPart)) =
      toRatPoly (primitivePart f)
    have htarget := hunit_product
    rw [hunit_neg] at htarget
    rw [← hdprimitive]
    exact htarget.symm

/-- The `squareFreeCore` projection is the decomposition's square-free core.
A definitional bridge for consumers that cannot unfold the unexposed `def`. -/
theorem squareFreeCore_eq (f : ZPoly) :
    squareFreeCore f = (primitiveSquareFreeDecomposition f).squareFreeCore := rfl

/-- The square-free core of a nonzero polynomial is nonzero: in the signed
reassembly it is a factor of the (nonzero) primitive part. -/
theorem squareFreeCore_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    squareFreeCore f ≠ 0 := by
  intro hcore
  rcases primitiveSquareFreeDecomposition_reassembly_signed f hf with ⟨ε, _, hre⟩
  have hpne : primitivePart f ≠ 0 :=
    ne_zero_of_primitive (primitivePart f)
      (primitivePart_primitive f (content_ne_zero_of_ne_zero f hf))
  apply hpne
  rw [← hre,
    show (primitiveSquareFreeDecomposition f).squareFreeCore = 0 from hcore,
    DensePoly.zero_mul, DensePoly.scale_zero_right]

/-- The square-free core of a nonzero polynomial is square-free over `Rat[x]`:
combine the executable core square-freeness with core nonzeroness. -/
theorem squareFreeRat_squareFreeCore (f : ZPoly) (hf : f ≠ 0) :
    SquareFreeRat (squareFreeCore f) :=
  primitiveSquareFreeDecomposition_squareFreeCore f (squareFreeCore_ne_zero f hf)

/-- The rational cast of the primitive part's square-free `gcd` associate
divides its derivative: `gcd(r, r')` divides `r'`, and its primitive integer
representative is a rational associate of the `gcd`. -/
private theorem ratPolyPrimitivePart_gcd_dvd_derivative (rp : DensePoly Rat) :
    toRatPoly (ratPolyPrimitivePart (DensePoly.gcd rp (DensePoly.derivative rp))) ∣
      DensePoly.derivative rp := by
  have h1 : DensePoly.gcd rp (DensePoly.derivative rp) ∣ DensePoly.derivative rp :=
    DensePoly.gcd_dvd_right rp (DensePoly.derivative rp)
  rcases ratPolyPrimitivePart_rational_associate
    (DensePoly.gcd rp (DensePoly.derivative rp)) with ⟨u, hu⟩
  rcases h1 with ⟨b, hb⟩
  generalize hX :
      toRatPoly (ratPolyPrimitivePart (DensePoly.gcd rp (DensePoly.derivative rp))) = X
      at hu ⊢
  refine ⟨DensePoly.scale u b, ?_⟩
  have e1 : DensePoly.scale u X * b = DensePoly.scale u (X * b) := by
    have h := rat_scale_mul_scale u 1 X b
    rw [rat_scale_one, Rat.mul_one] at h
    exact h
  have e2 : X * DensePoly.scale u b = DensePoly.scale u (X * b) := by
    have h := rat_scale_mul_scale 1 u X b
    rw [rat_scale_one, Rat.one_mul] at h
    exact h
  calc DensePoly.derivative rp
      = DensePoly.gcd rp (DensePoly.derivative rp) * b := hb
    _ = DensePoly.scale u X * b := by rw [hu]
    _ = DensePoly.scale u (X * b) := e1
    _ = X * DensePoly.scale u b := e2.symm

/-- The rational cast of the repeated part divides the derivative of the
rational cast of the primitive part. The repeated part is a rational associate
of `gcd(primitive, primitive')`, which divides `primitive'`; this is the
divisibility the square-free-core root transfer consumes. -/
theorem toRatPoly_repeatedPart_dvd_derivative (f : ZPoly) :
    toRatPoly (primitiveSquareFreeDecomposition f).repeatedPart ∣
      DensePoly.derivative (toRatPoly (primitivePart f)) := by
  unfold primitiveSquareFreeDecomposition
  by_cases hzero : (primitivePart f).isZero
  · have hpz : primitivePart f = 0 :=
      densePoly_eq_zero_of_isZero_true (primitivePart f) hzero
    simp only [hzero, if_true]
    rw [hpz]
    simp only [toRatPoly_zero, DensePoly.derivative_zero]
    exact ⟨0, (DensePoly.zero_mul 0).symm⟩
  · simp only [hzero, Bool.false_eq_true, if_false]
    by_cases hderiv : (DensePoly.derivative (toRatPoly (primitivePart f))).isZero
    · simp only [hderiv, if_true]
      rw [toRatPoly_one]
      exact ⟨DensePoly.derivative (toRatPoly (primitivePart f)),
        by rw [DensePoly.mul_comm_poly, DensePoly.mul_one_right_poly]⟩
    · simp only [hderiv, Bool.false_eq_true, if_false]
      exact ratPolyPrimitivePart_gcd_dvd_derivative (toRatPoly (primitivePart f))

/-- A Bezout congruence witness proves that two integer polynomials are coprime
modulo `p`. -/
theorem coprimeModP_of_bezout
    (f g s t : ZPoly) (p : Nat)
    (hbez : congr (s * f + t * g) 1 p) :
    coprimeModP f g p := by
  exact ⟨s, t, hbez⟩


end ZPoly
end Hex
