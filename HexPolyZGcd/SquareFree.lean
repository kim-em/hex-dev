/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPolyZGcd.Maximal
public import HexPolyZGcd.Maximal

public section

/-!
Fast primitive square-free normalization driven by the checked integer gcd.
-/

namespace Hex

namespace ZPoly

/-- The gcd component of an accepted certificate satisfies the public
normalization convention. -/
private theorem normalizedOfCheck {f h : ZPoly} {cert : GcdCert}
    (hcheck : checkGcd f h cert = true) :
    NormalizedGcd cert.gcd = true := by
  unfold checkGcd at hcheck
  simp only [Bool.and_eq_true] at hcheck
  exact hcheck.1.1.2

/-- Scaling an integer polynomial by one leaves it unchanged. -/
private theorem scaleOne (p : ZPoly) :
    DensePoly.scale (1 : Int) p = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale_semiring, Int.one_mul]

/-- Sign normalization differs from its input by a unit of `Int`. -/
private theorem scaleNormalize (p : ZPoly) :
    ∃ ε : Int, (ε = 1 ∨ ε = -1) ∧
      DensePoly.scale ε (normalizePrimitiveSign p) = p := by
  unfold normalizePrimitiveSign
  by_cases hnegative : p.leadingCoeff < 0
  · rw [if_pos hnegative]
    refine ⟨-1, Or.inr rfl, ?_⟩
    rw [DensePoly.scale_scale]
    have hunit : (-1 : Int) * -1 = 1 := by omega
    rw [hunit]
    exact scaleOne p
  · rw [if_neg hnegative]
    exact ⟨1, Or.inl rfl, scaleOne p⟩

/-- Integer-gcd replacement for `primitiveSquareFreeDecomposition`'s rational
Euclidean bottleneck.  The return type and normalization convention are shared
with the existing reference implementation. -/
def sqfDecomp (f : ZPoly) : PrimitiveSquareFreeDecomposition :=
  let primitive := primitivePart f
  if primitive.isZero then
    { primitive, squareFreeCore := 0, repeatedPart := 0 }
  else
    let derivative := DensePoly.derivative primitive
    if derivative.isZero then
      { primitive
        squareFreeCore := normalizePrimitiveSign primitive
        repeatedPart := 1 }
    else if primitive.size ≤ 8 then
      -- Below the crossover, constructing and replaying a general certificate
      -- costs more than the rational Euclidean calculation itself.  Reuse its
      -- canonical integer candidate, but recover the core by one integer long
      -- division instead of the reference route's rational division and
      -- denominator clearing.
      let repeatedPart := rationalGcdCandidate primitive derivative
      { primitive
        squareFreeCore := normalizePrimitiveSign (DensePoly.divMod primitive repeatedPart).1
        repeatedPart }
    else
      let cert := gcdCert primitive derivative
      { primitive
        squareFreeCore := normalizePrimitiveSign cert.cofL
        repeatedPart := cert.gcd }

/-- The public checked gcd agrees with the canonical rational fallback on
every nonzero input pair. -/
private theorem gcd_eq_rationalCandidate {f h : ZPoly}
    (hnz : f ≠ 0 ∨ h ≠ 0) :
    gcd f h = rationalGcdCandidate f h := by
  let reference := rationalGcdCert f h
  have hreference := rationalGcdCert_checks f h
  have hreferenceGcd : reference.gcd = rationalGcdCandidate f h := by
    simpa only [reference] using rationalGcdCert_gcd hnz
  have hreferenceCop : CoprimeCofactors f h reference.gcd :=
    coprimeCofactors_of_checkGcd hreference
  have hreferenceSound := checkGcd_sound hreference
  have hreferenceDvdLeft : reference.gcd ∣ f :=
    ⟨reference.cofL, hreferenceSound.1⟩
  have hreferenceDvdRight : reference.gcd ∣ h :=
    ⟨reference.cofR, hreferenceSound.2.1⟩
  have hpublicDvdReference : gcd f h ∣ reference.gcd :=
    dvd_gcd_of_coprimeCofactors hreferenceCop (gcd f h)
      (gcd_dvd_left f h) (gcd_dvd_right f h)
  have hreferenceDvdPublic : reference.gcd ∣ gcd f h :=
    dvd_gcd reference.gcd f h hreferenceDvdLeft hreferenceDvdRight
  have hpublicNorm : NormalizedGcd (gcd f h) = true := by
    rw [gcd_eq_cert]
    exact normalizedOfCheck (gcdCert_checks f h)
  have heq : reference.gcd = gcd f h :=
    eq_of_normalized_dvd (normalizedOfCheck hreference) hpublicNorm
      hreferenceDvdPublic hpublicDvdReference
  exact heq.symm.trans hreferenceGcd

/-- Casting coefficients from `Int` to `Rat` commutes with formal
differentiation. -/
private theorem toRatPoly_derivative (p : ZPoly) :
    toRatPoly (DensePoly.derivative p) =
      DensePoly.derivative (toRatPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly, DensePoly.coeff_derivative_semiring,
    DensePoly.coeff_derivative_semiring, coeff_toRatPoly]
  rw [Rat.intCast_mul, Rat.intCast_natCast]

/-- The fast decomposition's repeated part is the checked gcd of the primitive
input and its derivative in the nondegenerate branch. -/
theorem sqfDecomp_repeatedPart (f : ZPoly)
    (hp : (primitivePart f).isZero = false)
    (hd : (DensePoly.derivative (primitivePart f)).isZero = false) :
    (sqfDecomp f).repeatedPart =
      gcd (primitivePart f) (DensePoly.derivative (primitivePart f)) := by
  let p := primitivePart f
  let derivative := DensePoly.derivative p
  have hpNot : ¬p.isZero = true := by
    intro hpTrue
    change (primitivePart f).isZero = true at hpTrue
    rw [hp] at hpTrue
    contradiction
  have hpNe : p ≠ 0 := by
    intro hpZero
    have hpTrue : p.isZero = true := by rw [hpZero]; rfl
    exact hpNot hpTrue
  unfold sqfDecomp
  rw [if_neg (by simpa only [p] using hpNot)]
  rw [if_neg (by
    intro hdTrue
    rw [hd] at hdTrue
    contradiction)]
  by_cases hsmall : p.size ≤ 8
  · rw [if_pos hsmall]
    exact (gcd_eq_rationalCandidate (Or.inl hpNe)).symm
  · rw [if_neg hsmall]
    exact (gcd_eq_cert p derivative).symm

namespace Repeated

/-- The fast and rational reference decompositions choose the same repeated
factor whenever the primitive input and its derivative are nonzero. -/
private theorem nondegenerate (f : ZPoly)
    (hp : (primitivePart f).isZero = false)
    (hd : (DensePoly.derivative (primitivePart f)).isZero = false) :
    (sqfDecomp f).repeatedPart =
      (primitiveSquareFreeDecomposition f).repeatedPart := by
  let p := primitivePart f
  let derivative := DensePoly.derivative p
  have hpNe : p ≠ 0 := by
    intro hpZero
    have hpTrue : p.isZero = true := by rw [hpZero]; rfl
    change (primitivePart f).isZero = true at hpTrue
    rw [hp] at hpTrue
    contradiction
  have hcontentNe : content f ≠ 0 := by
    intro hcontent
    apply hpNe
    simpa only [p, primitivePart] using
      DensePoly.primitivePart_eq_zero_of_content_eq_zero f
        (by simpa only [content] using hcontent)
  have hpPrimitive : Primitive p := by
    simpa only [p] using primitivePart_primitive f hcontentNe
  have hderivativeNe : derivative ≠ 0 := by
    intro hzero
    have htrue : derivative.isZero = true := by rw [hzero]; rfl
    change (DensePoly.derivative (primitivePart f)).isZero = true at htrue
    rw [hd] at htrue
    contradiction
  have hratDerivativeNe : DensePoly.derivative (toRatPoly p) ≠ 0 := by
    rw [← toRatPoly_derivative]
    exact toRatPoly_ne_zero_of_ne_zero derivative hderivativeNe
  have hpNot : ¬p.isZero = true := by
    intro htrue
    change (primitivePart f).isZero = true at htrue
    rw [hp] at htrue
    contradiction
  have hratNot : ¬(DensePoly.derivative (toRatPoly p)).isZero = true := by
    intro htrue
    apply hratDerivativeNe
    exact (DensePoly.size_eq_zero_iff _).mp
      ((DensePoly.isZero_eq_true_iff _).mp htrue)
  rw [sqfDecomp_repeatedPart f hp hd]
  rw [gcd_eq_rationalCandidate (Or.inl hpNe)]
  rw [rationalGcdCandidate_of_primitive hpPrimitive]
  unfold primitiveSquareFreeDecomposition
  rw [if_neg (by simpa only [p] using hpNot)]
  rw [if_neg (by simpa only [p] using hratNot)]
  rw [toRatPoly_derivative]

/-- The repeated factors also agree in the derivative-zero branch. -/
private theorem eqReference (f : ZPoly)
    (hp : (primitivePart f).isZero = false) :
    (sqfDecomp f).repeatedPart =
      (primitiveSquareFreeDecomposition f).repeatedPart := by
  by_cases hd : (DensePoly.derivative (primitivePart f)).isZero = true
  · have hpNot : ¬(primitivePart f).isZero = true := by
      intro htrue
      rw [hp] at htrue
      contradiction
    have hderivativeZero : DensePoly.derivative (primitivePart f) = 0 :=
      (DensePoly.size_eq_zero_iff _).mp
        ((DensePoly.isZero_eq_true_iff _).mp hd)
    have hratDerivativeZero :
        DensePoly.derivative (toRatPoly (primitivePart f)) = 0 := by
      rw [← toRatPoly_derivative, hderivativeZero, toRatPoly_zero]
    have hratTrue :
        (DensePoly.derivative (toRatPoly (primitivePart f))).isZero = true := by
      rw [hratDerivativeZero]
      rfl
    unfold sqfDecomp primitiveSquareFreeDecomposition
    rw [if_neg hpNot, if_pos hd, if_neg hpNot, if_pos hratTrue]
  · have hdFalse :
        (DensePoly.derivative (primitivePart f)).isZero = false := by
      cases hvalue : (DensePoly.derivative (primitivePart f)).isZero with
      | false => rfl
      | true => exact (hd hvalue).elim
    exact nondegenerate f hp hdFalse

end Repeated

/-- The fast decomposition retains the input's primitive part verbatim. -/
private theorem sqfDecomp_primitive (f : ZPoly) :
    (sqfDecomp f).primitive = primitivePart f := by
  let p := primitivePart f
  unfold sqfDecomp
  by_cases hp : p.isZero = true
  · rw [if_pos (by simpa only [p] using hp)]
  · rw [if_neg (by simpa only [p] using hp)]
    by_cases hd : (DensePoly.derivative p).isZero = true
    · rw [if_pos (by simpa only [p] using hd)]
    · rw [if_neg (by simpa only [p] using hd)]
      split <;> rfl

/-- Scaling twice by `-1` is the identity on integer polynomials. -/
private theorem scaleNegInvolutive (p : ZPoly) :
    DensePoly.scale (-1 : Int) (DensePoly.scale (-1 : Int) p) = p := by
  rw [DensePoly.scale_scale]
  have hunit : (-1 : Int) * -1 = 1 := by omega
  rw [hunit]
  exact scaleOne p

/-- Scaling by `-1` is injective on integer polynomials. -/
private theorem scaleNegInjective {p q : ZPoly}
    (h : DensePoly.scale (-1 : Int) p = DensePoly.scale (-1 : Int) q) :
    p = q := by
  have hscaled := congrArg (DensePoly.scale (-1 : Int)) h
  simpa only [scaleNegInvolutive] using hscaled

/-- The fast square-free core and repeated part reassemble the primitive input
up to the normalization sign. -/
theorem sqfDecomp_reassembly_signed (f : ZPoly) :
    let d := sqfDecomp f
    ∃ ε : Int, (ε = 1 ∨ ε = -1) ∧
      DensePoly.scale ε (d.squareFreeCore * d.repeatedPart) = d.primitive := by
  dsimp only
  let p := primitivePart f
  have hpDef : primitivePart f = p := rfl
  unfold sqfDecomp
  by_cases hp : p.isZero = true
  · rw [if_pos (by simpa only [p] using hp)]
    have hpZero : p = 0 :=
      (DensePoly.size_eq_zero_iff p).mp
        ((DensePoly.isZero_eq_true_iff p).mp hp)
    refine ⟨1, Or.inl rfl, ?_⟩
    rw [DensePoly.zero_mul, DensePoly.scale_zero_right]
    change 0 = primitivePart f
    rw [hpDef, hpZero]
  · rw [if_neg (by simpa only [p] using hp)]
    let derivative := DensePoly.derivative p
    by_cases hd : derivative.isZero = true
    · rw [if_pos (by simpa only [derivative, p] using hd)]
      rcases scaleNormalize p with ⟨ε, hε, hscale⟩
      refine ⟨ε, hε, ?_⟩
      rw [DensePoly.mul_one_right_poly]
      exact hscale
    · rw [if_neg (by simpa only [derivative, p] using hd)]
      have hpNe : p ≠ 0 := by
        intro hpZero
        apply hp
        rw [hpZero]
        rfl
      by_cases hsmall : p.size ≤ 8
      · rw [if_pos (by simpa only [p] using hsmall)]
        let repeated := rationalGcdCandidate p derivative
        let quotient := (DensePoly.divMod p repeated).1
        rcases scaleNormalize quotient with ⟨ε, hε, hscale⟩
        refine ⟨ε, hε, ?_⟩
        have hproduct : repeated * quotient = p := by
          simpa only [repeated, quotient] using
            rationalGcdCandidate_mul_quotient (f := p) (h := derivative)
              (Or.inl hpNe)
        rw [DensePoly.scale_mul, hscale]
        rw [DensePoly.mul_comm_poly quotient repeated]
        exact hproduct
      · rw [if_neg (by simpa only [p] using hsmall)]
        let cert := gcdCert p derivative
        rcases scaleNormalize cert.cofL with ⟨ε, hε, hscale⟩
        refine ⟨ε, hε, ?_⟩
        have hproduct : cert.gcd * cert.cofL = p := by
          exact (checkGcd_sound (gcdCert_checks p derivative)).1.symm
        rw [DensePoly.scale_mul, hscale]
        rw [DensePoly.mul_comm_poly cert.cofL cert.gcd]
        exact hproduct

/-- Every nonzero fast square-free core is square-free over `Rat[x]`. -/
theorem sqfDecomp_squareFreeCore (f : ZPoly)
    (hcore : (sqfDecomp f).squareFreeCore ≠ 0) :
    SquareFreeRat (sqfDecomp f).squareFreeCore := by
  let fast := sqfDecomp f
  let reference := primitiveSquareFreeDecomposition f
  have hfastCore : fast.squareFreeCore ≠ 0 := by
    simpa only [fast] using hcore
  have hpNe : primitivePart f ≠ 0 := by
    intro hpZero
    apply hfastCore
    have hpTrue : (primitivePart f).isZero = true := by
      rw [hpZero]
      rfl
    simp only [fast, sqfDecomp, hpTrue, if_pos]
  have hfNe : f ≠ 0 := by
    intro hfZero
    subst f
    apply hpNe
    rfl
  have hpFalse : (primitivePart f).isZero = false := by
    cases hp : (primitivePart f).isZero with
    | false => rfl
    | true =>
        exfalso
        apply hpNe
        exact (DensePoly.size_eq_zero_iff _).mp
          ((DensePoly.isZero_eq_true_iff _).mp hp)
  have hrepeated : fast.repeatedPart = reference.repeatedPart := by
    simpa only [fast, reference] using
      Repeated.eqReference f hpFalse
  rcases sqfDecomp_reassembly_signed f with ⟨ε, hε, hfastProduct⟩
  have hfastProduct' :
      DensePoly.scale ε (fast.squareFreeCore * fast.repeatedPart) =
        primitivePart f := by
    simpa only [fast, sqfDecomp_primitive] using hfastProduct
  have hfastRepeated : fast.repeatedPart ≠ 0 := by
    intro hrepeatedZero
    apply hpNe
    rw [hrepeatedZero, DensePoly.mul_comm_poly fast.squareFreeCore 0,
      DensePoly.zero_mul, DensePoly.scale_zero_right] at hfastProduct'
    exact hfastProduct'.symm
  rcases primitiveSquareFreeDecomposition_reassembly_signed f hfNe with
    ⟨δ, hδ, hreferenceProduct⟩
  have hreferenceCore : reference.squareFreeCore ≠ 0 := by
    intro hreferenceZero
    apply hpNe
    change DensePoly.scale δ
      (reference.squareFreeCore * reference.repeatedPart) = primitivePart f at hreferenceProduct
    rw [hreferenceZero, DensePoly.zero_mul, DensePoly.scale_zero_right] at hreferenceProduct
    exact hreferenceProduct.symm
  have hreferenceSquareFree : SquareFreeRat reference.squareFreeCore := by
    exact primitiveSquareFreeDecomposition_squareFreeCore f (by
      simpa only [reference] using hreferenceCore)
  have hproducts :
      DensePoly.scale ε (fast.squareFreeCore * fast.repeatedPart) =
        DensePoly.scale δ (reference.squareFreeCore * reference.repeatedPart) := by
    exact hfastProduct'.trans hreferenceProduct.symm
  rw [DensePoly.scale_mul, DensePoly.scale_mul, ← hrepeated] at hproducts
  have hcores :
      DensePoly.scale ε fast.squareFreeCore =
        DensePoly.scale δ reference.squareFreeCore :=
    mul_right_cancel_of_ne_zero hfastRepeated hproducts
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
  · rw [scaleOne, scaleOne] at hcores
    rw [hcores]
    exact hreferenceSquareFree
  · rw [scaleOne] at hcores
    rw [hcores]
    exact squareFreeRat_scale_neg_one reference.squareFreeCore hreferenceSquareFree
  · rw [scaleOne] at hcores
    have hcores' := congrArg (DensePoly.scale (-1 : Int)) hcores
    rw [scaleNegInvolutive] at hcores'
    rw [hcores']
    exact squareFreeRat_scale_neg_one reference.squareFreeCore hreferenceSquareFree
  · have hcores' := scaleNegInjective hcores
    rw [hcores']
    exact hreferenceSquareFree

#guard
  let x1 : ZPoly := DensePoly.ofList [1, 1]
  let x2 : ZPoly := DensePoly.ofList [2, 1]
  let f := x1 * x1 * x2
  let d := sqfDecomp f
  d.repeatedPart == x1 && d.squareFreeCore == x1 * x2

end ZPoly

end Hex
