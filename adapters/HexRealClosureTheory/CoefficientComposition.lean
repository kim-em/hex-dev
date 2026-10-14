/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.CoefficientMap

public section

namespace Hex.RealClosure.CoefficientMap

attribute [local instance 2000] Field.toGrindField

/-- Canonical coefficients read in the original native field dictionary. -/
@[expose] def nativeCoefficients {A : Type} [Lean.Grind.Field A] [DecidableEq A]
    (values : List (Hex.RationalFn A)) : List A := values.flatMap fun q =>
  (List.range q.num.size).map q.num.coeff ++ (List.range q.den.size).map q.den.coeff

variable {F G H : Type} [Field F] [Field G] [Field H]
variable [DecidableEq F] [DecidableEq G] [DecidableEq H]

private theorem subtype_map (first : CoefficientMap F G) (a : first.domain) :
    first.map (first.domain.subtype a) = first.value a := by
  change first.map (a : F) = first.value a
  exact first.map_mem _ a.property

/-- Compose two partial interpretations on exactly the coefficients that
belong to the first domain and whose interpreted values belong to the second.
This permits specialization through a symbolic rational-function stage. -/
noncomputable def comp (second : CoefficientMap G H) (first : CoefficientMap F G) :
    CoefficientMap F H where
  domain := (second.domain.comap first.value).map first.domain.subtype
  value := second.value.comp {
    toFun := fun a => ⟨first.map a, by
      obtain ⟨b, member, equal⟩ := a.property
      rw [← equal, subtype_map]
      exact member⟩
    map_zero' := Subtype.ext first.map_zero
    map_one' := Subtype.ext first.map_one
    map_add' := by
      intro a b
      apply Subtype.ext
      apply first.map_add
      · obtain ⟨x, _, equal⟩ := a.property
        exact equal ▸ x.property
      · obtain ⟨x, _, equal⟩ := b.property
        exact equal ▸ x.property
    map_mul' := by
      intro a b
      apply Subtype.ext
      apply first.map_mul
      · obtain ⟨x, _, equal⟩ := a.property
        exact equal ▸ x.property
      · obtain ⟨x, _, equal⟩ := b.property
        exact equal ▸ x.property }

omit [DecidableEq H] in
/-- The composed domain is the actual two successive membership conditions. -/
theorem comp_domain (second : CoefficientMap G H) (first : CoefficientMap F G) (a : F) :
    a ∈ (second.comp first).domain ↔ a ∈ first.domain ∧ first.map a ∈ second.domain := by
  constructor
  · rintro ⟨b, member, equal⟩
    subst a
    change first.value b ∈ second.domain at member
    exact ⟨b.property, by simpa only [subtype_map] using member⟩
  · rintro ⟨member, mapped⟩
    refine ⟨⟨a, member⟩, ?_, rfl⟩
    change first.value ⟨a, member⟩ ∈ second.domain
    simpa only [first.map_mem _ member] using mapped

/-- The total readers compose even outside the domains, because both use
zero as their fallback and every interpretation maps zero to zero. -/
theorem comp_map (second : CoefficientMap G H) (first : CoefficientMap F G) (a : F) :
    (second.comp first).map a = second.map (first.map a) := by
  classical
  by_cases member : a ∈ first.domain
  · by_cases mapped : first.map a ∈ second.domain
    · rw [map_mem _ _ ((comp_domain second first a).mpr ⟨member, mapped⟩),
        second.map_mem _ mapped]
      rfl
    · rw [map_nonmem _ _ ((comp_domain second first a).not.mpr (by simp [mapped])),
        second.map_nonmem _ mapped]
  · have firstZero : first.map a = 0 := first.map_nonmem _ member
    rw [map_nonmem _ _ ((comp_domain second first a).not.mpr (by simp [member])),
      firstZero, second.map_zero]

/-- Substitute a partial coefficient interpretation into fractions admitting
actual presentations whose substituted denominator polynomials survive. -/
noncomputable def fractions (first : CoefficientMap F G) :
    CoefficientMap (Hex.RationalFn F) (Hex.RationalFn G) where
  domain := Specialize.fractionRing first.domain first.value
  value := Specialize.FractionRing.evaluation first.domain first.value

/-- A supplied surviving presentation puts the actual fraction in the domain. -/
theorem fractions_mem (first : CoefficientMap F G) (q : Hex.RationalFn F)
    (presentation : Specialize.FractionPresentation first.domain first.value q) :
    q ∈ first.fractions.domain :=
  (Specialize.fractionRing_mem _ _ _).mpr ⟨presentation⟩

/-- Fraction substitution evaluates this exact presentation independently of
which witness the substitution ring chose. -/
theorem fractions_map (first : CoefficientMap F G) (q : Hex.RationalFn F)
    (presentation : Specialize.FractionPresentation first.domain first.value q) :
    first.fractions.map q = presentation.eval := by
  rw [map_mem _ _ (fractions_mem first q presentation)]
  exact Specialize.FractionRing.evaluation_eq first.domain first.value
    ⟨q, fractions_mem first q presentation⟩ presentation

/-- Finite membership of canonical coefficients and zero reflection on the
stored denominator produce a surviving fraction presentation. -/
theorem fraction_presentation (first : CoefficientMap F G) (q : Hex.RationalFn F)
    (num : ∀ i < q.num.size, q.num.coeff i ∈ first.domain)
    (den : ∀ i < q.den.size, q.den.coeff i ∈ first.domain)
    (reflects : ∀ i < q.den.size, first.map (q.den.coeff i) = 0 ↔ q.den.coeff i = 0) :
    ∃ presentation : Specialize.FractionPresentation first.domain first.value q,
      Specialize.nativeMap first.value presentation.num = first.polynomial q.num ∧
      Specialize.nativeMap first.value presentation.den = first.polynomial q.den := by
  classical
  obtain ⟨P, hp⟩ := first.polynomial_lift q.num num
  obtain ⟨Q, hq⟩ := first.polynomial_lift q.den den
  have source (p : Hex.DensePoly F) (r : Polynomial first.domain)
      (equal : r.map first.domain.subtype = HexPolyTheory.toPolynomial p) :
      Specialize.nativeMap first.domain.subtype r = p := by
    apply (HexPolyTheory.equiv (R := F)).injective
    exact (Specialize.nativeMap_toPolynomial _ r).trans equal
  have target (p : Hex.DensePoly F) (r : Polynomial first.domain)
      (equal : r.map first.domain.subtype = HexPolyTheory.toPolynomial p) :
      Specialize.nativeMap first.value r = first.polynomial p := by
    apply (HexPolyTheory.equiv (R := G)).injective
    exact (Specialize.nativeMap_toPolynomial _ r).trans (first.polynomial_map p r equal).symm
  have mappedDen : Specialize.nativeMap first.value Q ≠ 0 := by
    rw [target q.den Q hq]
    exact fun zero => q.den_ne_zero ((first.polynomial_zero q.den reflects).mp zero)
  refine ⟨⟨P, Q, ?_, mappedDen⟩, target q.num P hp, target q.den Q hq⟩
  rw [source q.num P hp, source q.den Q hq]
  exact q.represents_self

/-- The stored coefficient zero pattern retains the actual least nonzero
coefficient under a partial interpretation. -/
theorem polynomial_trailing (first : CoefficientMap F ℝ) (p : Hex.DensePoly F)
    (reflects : ∀ i < p.size, first.map (p.coeff i) = 0 ↔ p.coeff i = 0) :
    Hex.OrderedFn.Infinitesimal.lowestCoeff (first.polynomial p) =
      first.map (Hex.OrderedFn.Infinitesimal.lowestCoeff p) := by
  classical
  have all (i : Nat) : first.map (p.coeff i) = 0 ↔ p.coeff i = 0 := by
    by_cases bound : i < p.size
    · exact reflects i bound
    · rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt bound)]
      change first.map (0 : F) = 0 ↔ (0 : F) = 0
      simp only [first.map_zero]
  have mapped : HexPolyTheory.toPolynomial (first.polynomial p) =
      Specialize.mapCoefficients first.map first.map_zero (HexPolyTheory.toPolynomial p) := by
    ext i
    rw [HexPolyTheory.coeff_toPolynomial, first.polynomial_coeff,
      Specialize.mapCoefficients_coeff, HexPolyTheory.coeff_toPolynomial]
  rw [Hex.OrderedFn.Infinitesimal.lowestCoeff_eq, mapped,
    Specialize.mapCoefficients_trailing first.map first.map_zero _
      (fun i => by simpa only [HexPolyTheory.coeff_toPolynomial] using all i),
    Hex.OrderedFn.Infinitesimal.lowestCoeff_eq]

private theorem cast_sign_zero {A : Type} [Zero A] [LinearOrder A] (a : A) :
    (SignType.sign a : Int) = 0 ↔ a = 0 := by
  constructor
  · intro zero
    apply sign_eq_zero_iff.mp
    cases sign : SignType.sign a <;> simp_all
  · intro zero
    subst a
    simp

private theorem coefficient_sign [LinearOrder F] (first : CoefficientMap F ℝ)
    (p : Hex.DensePoly F)
    (signs : ∀ i < p.size, (SignType.sign (first.map (p.coeff i)) : Int) =
      (SignType.sign (p.coeff i) : Int)) (i : Nat) :
    (SignType.sign (first.map (p.coeff i)) : Int) = (SignType.sign (p.coeff i) : Int) := by
  by_cases bound : i < p.size
  · exact signs i bound
  · rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt bound)]
    change (SignType.sign (first.map (0 : F)) : Int) = (SignType.sign (0 : F) : Int)
    rw [first.map_zero]
    simp

/-- Finite sign agreement on the canonical numerator and denominator
coefficients preserves the actual infinitesimal sign after substitution.
No order-preserving homomorphism on the whole coefficient field is assumed. -/
theorem fractions_sign [LinearOrder F] [IsStrictOrderedRing F]
    (first : CoefficientMap F ℝ) (q : Hex.RationalFn F)
    (num : ∀ i < q.num.size, q.num.coeff i ∈ first.domain)
    (den : ∀ i < q.den.size, q.den.coeff i ∈ first.domain)
    (numSigns : ∀ i < q.num.size, (SignType.sign (first.map (q.num.coeff i)) : Int) =
      (SignType.sign (q.num.coeff i) : Int))
    (denSigns : ∀ i < q.den.size, (SignType.sign (first.map (q.den.coeff i)) : Int) =
      (SignType.sign (q.den.coeff i) : Int)) :
    q ∈ first.fractions.domain ∧
      Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign (first.fractions.map q) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q := by
  classical
  have reflect (p : Hex.DensePoly F)
      (signs : ∀ i < p.size, (SignType.sign (first.map (p.coeff i)) : Int) =
        (SignType.sign (p.coeff i) : Int)) (i : Nat) (bound : i < p.size) :
      first.map (p.coeff i) = 0 ↔ p.coeff i = 0 := by
    rw [← cast_sign_zero, signs i bound, cast_sign_zero]
  obtain ⟨presentation, mappedNum, mappedDen⟩ :=
    fraction_presentation first q num den (reflect q.den denSigns)
  refine ⟨fractions_mem first q presentation, ?_⟩
  rw [fractions_map first q presentation]
  have result := Hex.OrderedFn.Infinitesimal.sign_fraction Hex.OrderedFn.orderSign
    Hex.OrderedFn.Infinitesimal.orderSign_eq presentation.eval_spec presentation.nonzero
  rw [mappedNum, mappedDen, polynomial_trailing first q.num (reflect q.num numSigns),
    polynomial_trailing first q.den (reflect q.den denSigns),
    Hex.OrderedFn.Infinitesimal.orderSign_eq, Hex.OrderedFn.Infinitesimal.orderSign_eq,
    Hex.OrderedFn.Infinitesimal.lowestCoeff, Hex.OrderedFn.Infinitesimal.lowestCoeff,
    coefficient_sign first q.num numSigns, coefficient_sign first q.den denSigns] at result
  rw [result]
  simpa only [Hex.OrderedFn.Infinitesimal.orderSign_eq, Hex.OrderedFn.Infinitesimal.lowestCoeff] using
    (Hex.OrderedFn.Infinitesimal.sign_fraction Hex.OrderedFn.orderSign
      Hex.OrderedFn.Infinitesimal.orderSign_eq q.represents_self q.den_ne_zero).symm

/-- Ordinary point evaluation is a partial interpretation on exactly the
native rational functions whose canonical denominators survive at the point. -/
noncomputable def pointMap (t : ℝ) : CoefficientMap (Hex.RationalFn ℝ) ℝ where
  domain := Specialize.regularRing (RingHom.id ℝ) t
  value := Specialize.evaluation (RingHom.id ℝ) t

theorem pointMap_domain (t : ℝ) (q : Hex.RationalFn ℝ) :
    q ∈ (pointMap t).domain ↔ Specialize.Regular (RingHom.id ℝ) t q := Iff.rfl

/-- Read the actual fraction at an ordinary point using its surviving denominator. -/
theorem pointMap_map (t : ℝ) (q : Hex.RationalFn ℝ)
    (regular : Specialize.Regular (RingHom.id ℝ) t q) :
    (pointMap t).map q = Specialize.evalFraction q t := by
  classical
  rw [map_mem _ _ regular]
  change Specialize.evalMapped (RingHom.id ℝ) q t = Specialize.evalFraction q t
  simp only [Specialize.evalMapped, Polynomial.map_id, Specialize.evalFraction]

/-- Add one ordinary parameter after a partial interpretation of the preceding
coefficient field. This does not require a homomorphism on the entire field. -/
noncomputable def parameterMap (first : CoefficientMap F ℝ) (t : ℝ) :
    CoefficientMap (Hex.RationalFn F) ℝ := (pointMap t).comp first.fractions

/-- Both the coefficient presentation and its ordinary-point denominator must survive. -/
theorem parameterMap_domain (first : CoefficientMap F ℝ) (t : ℝ) (q : Hex.RationalFn F) :
    q ∈ (first.parameterMap t).domain ↔ q ∈ first.fractions.domain ∧
      Specialize.Regular (RingHom.id ℝ) t (first.fractions.map q) :=
  comp_domain _ _ _

/-- On an actual surviving presentation, the composed reader first substitutes
its coefficients and then evaluates the remaining indeterminate. -/
theorem parameterMap_map (first : CoefficientMap F ℝ) (t : ℝ) (q : Hex.RationalFn F)
    (presentation : Specialize.FractionPresentation first.domain first.value q)
    (regular : Specialize.Regular (RingHom.id ℝ) t presentation.eval) :
    (first.parameterMap t).map q = Specialize.evalFraction presentation.eval t := by
  rw [parameterMap, comp_map, fractions_map first q presentation, pointMap_map t _ regular]

private theorem nativeMap_C {A B : Type} [CommRing A] [Field B] [DecidableEq B]
    (hom : A →+* B) (a : A) : Specialize.nativeMap hom (Polynomial.C a) = Hex.DensePoly.C (hom a) := by
  apply (HexPolyTheory.equiv (R := B)).injective
  change HexPolyTheory.toPolynomial (Specialize.nativeMap hom (Polynomial.C a)) =
    HexPolyTheory.toPolynomial (Hex.DensePoly.C (hom a))
  rw [Specialize.nativeMap_toPolynomial, Polynomial.map_C, HexPolyTheory.toPolynomial_C]

private theorem nativeMap_one {A B : Type} [CommRing A] [Field B] [DecidableEq B]
    (hom : A →+* B) : Specialize.nativeMap hom 1 = 1 := by
  apply (HexPolyTheory.equiv (R := B)).injective
  change HexPolyTheory.toPolynomial (Specialize.nativeMap hom 1) = HexPolyTheory.toPolynomial 1
  rw [Specialize.nativeMap_toPolynomial, Polynomial.map_one, HexPolyTheory.toPolynomial_one]

private noncomputable def constantPresentation (first : CoefficientMap F ℝ) (a : first.domain) :
    Specialize.FractionPresentation first.domain first.value (Hex.RationalFn.C (a : F)) where
  num := Polynomial.C a
  den := 1
  represents := by
    rw [nativeMap_C, nativeMap_one]
    exact Hex.RationalFn.represents_ofPoly _
  nonzero := by
    rw [nativeMap_one]
    exact Hex.DensePoly.monic_ne_zero Hex.DensePoly.monic_one

private theorem constantPresentation_eval (first : CoefficientMap F ℝ) (a : first.domain) :
    (constantPresentation first a).eval = Hex.RationalFn.C (first.value a) := by
  have representation := (constantPresentation first a).eval_spec
  change Hex.RationalFn.Represents _ (Specialize.nativeMap first.value (Polynomial.C a))
    (Specialize.nativeMap first.value 1) at representation
  rw [nativeMap_C, nativeMap_one] at representation
  exact representation.eq (Hex.RationalFn.represents_ofPoly _)
    (Hex.DensePoly.monic_ne_zero Hex.DensePoly.monic_one)

/-- One ordinary parameter retains every previously interpreted coefficient,
including coefficients sent to zero by the preceding partial interpretation. -/
theorem parameterMap_C (first : CoefficientMap F ℝ) (t : ℝ) (a : F)
    (member : a ∈ first.domain) :
    Hex.RationalFn.C a ∈ (first.parameterMap t).domain ∧
      (first.parameterMap t).map (Hex.RationalFn.C a) = first.map a := by
  classical
  let presentation := constantPresentation first ⟨a, member⟩
  have value : presentation.eval = Hex.RationalFn.C (first.map a) := by
    rw [first.map_mem _ member]
    exact constantPresentation_eval first ⟨a, member⟩
  have regular : Specialize.Regular (RingHom.id ℝ) t presentation.eval := by
    rw [value]
    change ((HexPolyTheory.toPolynomial (1 : Hex.DensePoly ℝ)).map (RingHom.id ℝ)).eval t ≠ 0
    simp only [HexPolyTheory.toPolynomial_one, Polynomial.map_one, Polynomial.eval_one, ne_eq]
    exact one_ne_zero
  constructor
  · apply (parameterMap_domain first t _).mpr
    refine ⟨fractions_mem first _ presentation, ?_⟩
    rw [fractions_map first _ presentation]
    exact regular
  · rw [parameterMap_map first t _ presentation regular, value]
    simpa only [Specialize.evalMapped, Polynomial.map_id, Specialize.evalFraction, RingHom.id_apply] using
      Specialize.evalMapped_C (RingHom.id ℝ) (first.map a) t

private theorem nativeMap_X {A B : Type} [CommRing A] [Field B] [DecidableEq B]
    (hom : A →+* B) : Specialize.nativeMap hom Polynomial.X = Hex.DensePoly.monomial 1 1 := by
  apply (HexPolyTheory.equiv (R := B)).injective
  change HexPolyTheory.toPolynomial (Specialize.nativeMap hom Polynomial.X) =
    HexPolyTheory.toPolynomial (Hex.DensePoly.monomial 1 (1 : B))
  rw [Specialize.nativeMap_toPolynomial, Polynomial.map_X,
    HexPolyTheory.toPolynomial_monomial, Polynomial.monomial_one_one_eq_X]

private noncomputable def variablePresentation (first : CoefficientMap F ℝ) :
    Specialize.FractionPresentation first.domain first.value (Hex.RationalFn.X : Hex.RationalFn F) where
  num := Polynomial.X
  den := 1
  represents := by
    rw [nativeMap_X, nativeMap_one]
    exact Hex.RationalFn.represents_ofPoly _
  nonzero := by
    rw [nativeMap_one]
    exact Hex.DensePoly.monic_ne_zero Hex.DensePoly.monic_one

private theorem variablePresentation_eval (first : CoefficientMap F ℝ) :
    (variablePresentation first).eval = (Hex.RationalFn.X : Hex.RationalFn ℝ) := by
  have representation := (variablePresentation first).eval_spec
  change Hex.RationalFn.Represents _ (Specialize.nativeMap first.value Polynomial.X)
    (Specialize.nativeMap first.value 1) at representation
  rw [nativeMap_X, nativeMap_one] at representation
  exact representation.eq (Hex.RationalFn.represents_ofPoly _)
    (Hex.DensePoly.monic_ne_zero Hex.DensePoly.monic_one)

/-- The ordinary parameter is the interpretation of the actual new
indeterminate, independently of the preceding partial coefficient map. -/
theorem parameterMap_X (first : CoefficientMap F ℝ) (t : ℝ) :
    (Hex.RationalFn.X : Hex.RationalFn F) ∈ (first.parameterMap t).domain ∧
      (first.parameterMap t).map Hex.RationalFn.X = t := by
  classical
  let presentation := variablePresentation first
  have value : presentation.eval = (Hex.RationalFn.X : Hex.RationalFn ℝ) := variablePresentation_eval first
  have regular : Specialize.Regular (RingHom.id ℝ) t presentation.eval := by
    rw [value]
    change ((HexPolyTheory.toPolynomial (1 : Hex.DensePoly ℝ)).map (RingHom.id ℝ)).eval t ≠ 0
    simp only [HexPolyTheory.toPolynomial_one, Polynomial.map_one, Polynomial.eval_one, ne_eq]
    exact one_ne_zero
  constructor
  · apply (parameterMap_domain first t _).mpr
    refine ⟨fractions_mem first _ presentation, ?_⟩
    rw [fractions_map first _ presentation]
    exact regular
  · rw [parameterMap_map first t _ presentation regular, value]
    simpa only [Specialize.evalMapped, Polynomial.map_id, Specialize.evalFraction] using
      Specialize.evalMapped_X (RingHom.id ℝ) t

/-- A finite family of surviving fraction substitutions shares one positive
ordinary parameter. The queried infinitesimal signs are premises only for the
actual substituted family; no whole-field order embedding is required. -/
theorem exists_parameter (first : CoefficientMap F ℝ) (qs : List (Hex.RationalFn F))
    (sourceSign : Hex.RationalFn F → Int)
    (members : ∀ q ∈ qs, q ∈ first.fractions.domain)
    (signs : ∀ q ∈ qs, Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
      (first.fractions.map q) = sourceSign q)
    (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ ∀ q ∈ qs,
      q ∈ (first.parameterMap t).domain ∧
        (SignType.sign ((first.parameterMap t).map q) : Int) = sourceSign q := by
  classical
  obtain ⟨t, positive, below, stable⟩ := Specialize.exists_fraction_parameter
    (qs.toFinset.image first.fractions.map) cap positive
  refine ⟨t, positive, below, ?_⟩
  intro q member
  have queried := stable (first.fractions.map q)
    (Finset.mem_image.mpr ⟨q, List.mem_toFinset.mpr member, rfl⟩)
  have regular : Specialize.Regular (RingHom.id ℝ) t (first.fractions.map q) := by
    simpa only [Specialize.Regular, Polynomial.map_id] using queried.1
  refine ⟨(parameterMap_domain first t q).mpr ⟨members q member, regular⟩, ?_⟩
  rw [parameterMap, comp_map, pointMap_map t _ regular]
  exact queried.2.trans (signs q member)

/-- Canonical numerator and denominator coefficients of the actual finite
fraction family. All unstored coefficient positions are zero. -/
@[expose] def coefficients (qs : List (Hex.RationalFn F)) : List F :=
  nativeCoefficients qs

private theorem num_mem (qs : List (Hex.RationalFn F)) (q : Hex.RationalFn F)
    (member : q ∈ qs) (i : Nat) (bound : i < q.num.size) : q.num.coeff i ∈ coefficients qs :=
  List.mem_flatMap.mpr ⟨q, member, List.mem_append_left _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr bound, rfl⟩)⟩

private theorem den_mem (qs : List (Hex.RationalFn F)) (q : Hex.RationalFn F)
    (member : q ∈ qs) (i : Nat) (bound : i < q.den.size) : q.den.coeff i ∈ coefficients qs :=
  List.mem_flatMap.mpr ⟨q, member, List.mem_append_right _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr bound, rfl⟩)⟩

/-- A finite coefficient inventory alone supplies one sufficiently small
ordinary parameter preserving the actual fraction family's signs. This is
one infinitesimal step after any partial realization of its predecessor. -/
theorem exists_signs_parameter [LinearOrder F] [IsStrictOrderedRing F]
    (first : CoefficientMap F ℝ) (qs : List (Hex.RationalFn F))
    (data : ∀ a ∈ coefficients qs, a ∈ first.domain ∧
      (SignType.sign (first.map a) : Int) = (SignType.sign a : Int))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ ∀ q ∈ qs,
      q ∈ (first.parameterMap t).domain ∧
        (SignType.sign ((first.parameterMap t).map q) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q := by
  have substituted (q : Hex.RationalFn F) (member : q ∈ qs) := fractions_sign first q
    (fun i bound => (data _ (num_mem qs q member i bound)).1)
    (fun i bound => (data _ (den_mem qs q member i bound)).1)
    (fun i bound => (data _ (num_mem qs q member i bound)).2)
    (fun i bound => (data _ (den_mem qs q member i bound)).2)
  exact exists_parameter first qs (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
    (fun q member => (substituted q member).1) (fun q member => (substituted q member).2) cap positive

end Hex.RealClosure.CoefficientMap

/-- info: 'Hex.RealClosure.CoefficientMap.comp_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.comp_map

/-- info: 'Hex.RealClosure.CoefficientMap.parameterMap_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.parameterMap_map

/-- info: 'Hex.RealClosure.CoefficientMap.exists_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.exists_parameter


/-- info: 'Hex.RealClosure.CoefficientMap.fractions_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.fractions_sign

/-- info: 'Hex.RealClosure.CoefficientMap.exists_signs_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.exists_signs_parameter

/-- info: 'Hex.RealClosure.CoefficientMap.parameterMap_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.parameterMap_C

/-- info: 'Hex.RealClosure.CoefficientMap.parameterMap_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.parameterMap_X
