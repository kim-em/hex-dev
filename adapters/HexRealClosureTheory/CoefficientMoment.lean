/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.CoefficientReduction
public import HexSignDet.MomentReplay

public section

namespace Hex.RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

private theorem toPolynomial_natPow {K : Type} [Field K] [DecidableEq K]
    (p : Hex.DensePoly K) (n : Nat) :
    HexPolyTheory.toPolynomial (p.natPow n) = HexPolyTheory.toPolynomial p ^ n := by
  induction n with
  | zero => rw [Hex.DensePoly.natPow_zero, HexPolyTheory.toPolynomial_one, pow_zero]
  | succ n ih => rw [Hex.DensePoly.natPow_succ, HexPolyTheory.toPolynomial_mul, ih, pow_succ]

private theorem regular_coefficients (interpretation : RealClosure.CoefficientMap F G)
    (p : Hex.DensePoly F) (q : Polynomial (interpretation.domain))
    (lift : q.map (interpretation.domain).subtype = HexPolyTheory.toPolynomial p) :
    ∀ i, (p.coeff i) ∈ interpretation.domain := by
  intro i
  have coefficient := congrArg (fun r => r.coeff i) lift
  simp only [Polynomial.coeff_map, HexPolyTheory.coeff_toPolynomial] at coefficient
  change (q.coeff i).val = p.coeff i at coefficient
  rw [← coefficient]
  exact (q.coeff i).property

private theorem regular_product (interpretation : RealClosure.CoefficientMap F G)
    (p q : Hex.DensePoly F)
    (hp : ∀ i < p.size, (p.coeff i) ∈ interpretation.domain)
    (hq : ∀ i < q.size, (q.coeff i) ∈ interpretation.domain) :
    ∀ i < (p * q).size, (p * q).coeff i ∈ interpretation.domain := by
  classical
  obtain ⟨P, hP⟩ := polynomial_lift interpretation p hp
  obtain ⟨Q, hQ⟩ := polynomial_lift interpretation q hq
  have lift : (P * Q).map (interpretation.domain).subtype = HexPolyTheory.toPolynomial (p * q) := by
    rw [Polynomial.map_mul, hP, hQ, HexPolyTheory.toPolynomial_mul]
  exact fun i _ => regular_coefficients interpretation (p * q) (P * Q) lift i

private theorem regular_power (interpretation : RealClosure.CoefficientMap F G)
    (p : Hex.DensePoly F) (n : Nat)
    (hp : ∀ i < p.size, (p.coeff i) ∈ interpretation.domain) :
    ∀ i < (p.natPow n).size, (p.natPow n).coeff i ∈ interpretation.domain := by
  classical
  obtain ⟨P, hP⟩ := polynomial_lift interpretation p hp
  have lift : (P ^ n).map (interpretation.domain).subtype = HexPolyTheory.toPolynomial (p.natPow n) := by
    rw [Polynomial.map_pow, hP, toPolynomial_natPow]
  exact fun i _ => regular_coefficients interpretation (p.natPow n) (P ^ n) lift i

/-- The actual binary polynomial power maps from only its input guards. -/
theorem polynomial_natPow (interpretation : RealClosure.CoefficientMap F G)
    (p : Hex.DensePoly F) (n : Nat)
    (hp : ∀ i < p.size, (p.coeff i) ∈ interpretation.domain) :
    interpretation.polynomial (p.natPow n) = (interpretation.polynomial p).natPow n := by
  classical
  obtain ⟨P, hP⟩ := polynomial_lift interpretation p hp
  have lift : (P ^ n).map (interpretation.domain).subtype = HexPolyTheory.toPolynomial (p.natPow n) := by
    rw [Polynomial.map_pow, hP, toPolynomial_natPow]
  apply (HexPolyTheory.equiv (R := G)).injective
  change HexPolyTheory.toPolynomial _ = HexPolyTheory.toPolynomial _
  rw [polynomial_map interpretation _ _ lift, toPolynomial_natPow,
    polynomial_map interpretation p P hP, Polynomial.map_pow]

/-- Substitution of the actual moment fold, with regular input coefficients.
All accumulator products stay in the regular ring. -/
theorem moment_map (interpretation : RealClosure.CoefficientMap F G)
    (qs : List (Hex.DensePoly F)) (es : List Nat)
    (regular : ∀ p ∈ qs, ∀ i < p.size, (p.coeff i) ∈ interpretation.domain) :
    interpretation.polynomial (Hex.SignDet.moment qs es) =
      Hex.SignDet.moment (qs.map (fun p => interpretation.polynomial p)) es := by
  classical
  have fold (xs : List (Hex.DensePoly F))
      (hx : ∀ p ∈ xs, ∀ i < p.size, (p.coeff i) ∈ interpretation.domain)
      (prev : Hex.DensePoly F)
      (hp : ∀ i < prev.size, (prev.coeff i) ∈ interpretation.domain) :
      interpretation.polynomial (xs.foldl (· * ·) prev) =
        (xs.map (fun p => interpretation.polynomial p)).foldl (· * ·) (interpretation.polynomial prev) := by
    induction xs generalizing prev with
    | nil => rfl
    | cons p xs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih (fun q hq => hx q (List.mem_cons_of_mem _ hq)) (prev * p)
        (regular_product interpretation prev p hp (hx p (by simp)))]
      rw [polynomial_mul interpretation prev p hp (hx p (by simp))]
  have powers : ∀ p ∈ (qs.zip es).map (fun (q, n) => q.natPow n),
      ∀ i < p.size, (p.coeff i) ∈ interpretation.domain := by
    intro p hp
    obtain ⟨⟨q, n⟩, hq, rfl⟩ := List.mem_map.mp hp
    exact regular_power interpretation q n (regular q (List.of_mem_zip hq).1)
  have one : ∀ i < (1 : Hex.DensePoly F).size,
      (1 : Hex.DensePoly F).coeff i ∈ interpretation.domain := by
    intro i _
    change (Hex.DensePoly.C (1 : F)).coeff i ∈ interpretation.domain
    rw [Hex.DensePoly.coeff_C]
    split_ifs
    · exact (interpretation.domain).one_mem
    · exact (interpretation.domain).zero_mem
  rw [Hex.SignDet.moment, fold _ powers 1 one, polynomial_one]
  unfold Hex.SignDet.moment
  rw [List.zip_map_left, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pair hp
  obtain ⟨p, n⟩ := pair
  exact polynomial_natPow interpretation p n (regular p (List.of_mem_zip hp).1)

/-- info: 'Hex.RealClosure.CoefficientMap.polynomial_natPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.polynomial_natPow

/-- info: 'Hex.RealClosure.CoefficientMap.moment_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.moment_map

end Hex.RealClosure.CoefficientMap

namespace Hex.SignDet
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G] {Ctx : Type u}

/-- The actual chosen query operand maps, whether direct or reduced. -/
theorem queryPoly_map (interpretation : RealClosure.CoefficientMap F G)
    (qs : List (DensePoly F)) (es : List Nat)
    (reduction : Option (Reduction F))
    (regular : ∀ p ∈ qs, ∀ i < p.size, (p.coeff i) ∈ interpretation.domain) :
    interpretation.polynomial (queryPoly qs es reduction) =
      queryPoly (qs.map (fun p => interpretation.polynomial p)) es
        (reduction.map (Reduction.substitute interpretation)) := by
  cases reduction with
  | none => exact moment_map interpretation qs es regular
  | some r => rfl

/-- Finite obligations for the actual moment, optional reduction, and complete
Tarski replay. The ordered query list retains duplicates. -/
@[expose] noncomputable def momentCoefficients (p : DensePoly F)
    (a b : Endpoint F) (qs : List (DensePoly F)) (es : List Nat)
    (cert : TarskiCertificate F F Ctx)
    (reduction : Option (Reduction F)) : Finset F := by
  classical
  exact cert.coefficients p (queryPoly qs es reduction) a b ∪
    (qs.flatMap (fun q => q.toArray.toList)).toFinset ∪
    (reduction.toList.flatMap (fun r => (r.coefficients p qs es).toList)).toFinset

/-- Preserve the complete moment check on its literal exponent positions and
integer value, including all optional product reduction evidence. -/
theorem checkMoment_map [DecidableEq Ctx] (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (context : Ctx) (p : DensePoly F)
    (a b : Endpoint F) (qs : List (DensePoly F)) (es : List Nat)
    (value : Int) (cert : TarskiCertificate F F Ctx)
    (reduction : Option (Reduction F))
    (data : ∀ x ∈ momentCoefficients p a b qs es cert reduction,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : checkMoment sign context p a b qs es value cert reduction = true) :
    checkMoment targetSign context (interpretation.polynomial p)
      (a.substitute interpretation) (b.substitute interpretation)
      (qs.map (fun q => interpretation.polynomial q)) es value
      (cert.substitute interpretation) (reduction.map (Reduction.substitute interpretation)) = true := by
  classical
  have regular q (hq : q ∈ qs) i (hi : i < q.size) :=
    (data (q.coeff i) (Finset.mem_union_left _ (Finset.mem_union_right _
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨q, hq, coefficient_mem q i hi⟩))))).1
  have tarski_data x (hx : x ∈ cert.coefficients p (queryPoly qs es reduction) a b) :=
    data x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  simp only [checkMoment_eq, Sturm.check, Bool.and_eq_true] at accepted ⊢
  constructor
  · cases reduction with
    | none => simpa only [Option.map_none, List.length_map] using accepted.1
    | some r =>
      apply r.check_map interpretation sign targetSign p qs es _ accepted.1
      intro x hx
      exact data x (Finset.mem_union_right _ (List.mem_toFinset.mpr
        (List.mem_flatMap.mpr ⟨r, by simp, Finset.mem_toList.mpr hx⟩)))
  · rw [← queryPoly_map interpretation qs es reduction regular]
    exact TarskiCertificate.check_map interpretation sign targetSign context p (queryPoly qs es reduction)
      a b value cert tarski_data accepted.2

end Hex.SignDet

/-- info: 'Hex.SignDet.checkMoment_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.checkMoment_map
