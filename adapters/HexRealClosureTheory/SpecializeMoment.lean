/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.SpecializeReduction
public import HexSignDet.MomentReplay

public section

namespace Hex.RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F]

private theorem toPolynomial_natPow {K : Type} [Field K] [DecidableEq K]
    (p : Hex.DensePoly K) (n : Nat) :
    HexPolyTheory.toPolynomial (p.natPow n) = HexPolyTheory.toPolynomial p ^ n := by
  induction n with
  | zero => rw [Hex.DensePoly.natPow_zero, HexPolyTheory.toPolynomial_one, pow_zero]
  | succ n ih => rw [Hex.DensePoly.natPow_succ, HexPolyTheory.toPolynomial_mul, ih, pow_succ]

private theorem regular_coefficients (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (q : Polynomial (regularRing embedding t))
    (lift : q.map (regularRing embedding t).subtype = HexPolyTheory.toPolynomial p) :
    ∀ i, Regular embedding t (p.coeff i) := by
  intro i
  have coefficient := congrArg (fun r => r.coeff i) lift
  simp only [Polynomial.coeff_map, HexPolyTheory.coeff_toPolynomial] at coefficient
  change (q.coeff i).val = p.coeff i at coefficient
  rw [← coefficient]
  exact (q.coeff i).property

private theorem regular_product (embedding : F →+* ℝ) (t : ℝ)
    (p q : Hex.DensePoly (Hex.RationalFn F))
    (hp : ∀ i < p.size, Regular embedding t (p.coeff i))
    (hq : ∀ i < q.size, Regular embedding t (q.coeff i)) :
    ∀ i < (p * q).size, Regular embedding t ((p * q).coeff i) := by
  classical
  obtain ⟨P, hP⟩ := polynomial_lift embedding t p hp
  obtain ⟨Q, hQ⟩ := polynomial_lift embedding t q hq
  have lift : (P * Q).map (regularRing embedding t).subtype = HexPolyTheory.toPolynomial (p * q) := by
    rw [Polynomial.map_mul, hP, hQ, HexPolyTheory.toPolynomial_mul]
  exact fun i _ => regular_coefficients embedding t (p * q) (P * Q) lift i

private theorem regular_power (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (n : Nat)
    (hp : ∀ i < p.size, Regular embedding t (p.coeff i)) :
    ∀ i < (p.natPow n).size, Regular embedding t ((p.natPow n).coeff i) := by
  classical
  obtain ⟨P, hP⟩ := polynomial_lift embedding t p hp
  have lift : (P ^ n).map (regularRing embedding t).subtype = HexPolyTheory.toPolynomial (p.natPow n) := by
    rw [Polynomial.map_pow, hP, toPolynomial_natPow]
  exact fun i _ => regular_coefficients embedding t (p.natPow n) (P ^ n) lift i

/-- The actual binary polynomial power specializes from only its input guards. -/
theorem polynomial_natPow (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (n : Nat)
    (hp : ∀ i < p.size, Regular embedding t (p.coeff i)) :
    polynomial embedding (p.natPow n) t = (polynomial embedding p t).natPow n := by
  classical
  obtain ⟨P, hP⟩ := polynomial_lift embedding t p hp
  have lift : (P ^ n).map (regularRing embedding t).subtype = HexPolyTheory.toPolynomial (p.natPow n) := by
    rw [Polynomial.map_pow, hP, toPolynomial_natPow]
  apply (HexPolyTheory.equiv (R := ℝ)).injective
  change HexPolyTheory.toPolynomial _ = HexPolyTheory.toPolynomial _
  rw [polynomial_map embedding t _ _ lift, toPolynomial_natPow,
    polynomial_map embedding t p P hP, Polynomial.map_pow]

/-- Substitution of the actual moment fold, with regular input coefficients.
All accumulator products stay in the regular ring. -/
theorem moment_specialize (embedding : F →+* ℝ) (t : ℝ)
    (qs : List (Hex.DensePoly (Hex.RationalFn F))) (es : List Nat)
    (regular : ∀ p ∈ qs, ∀ i < p.size, Regular embedding t (p.coeff i)) :
    polynomial embedding (Hex.SignDet.moment qs es) t =
      Hex.SignDet.moment (qs.map (fun p => polynomial embedding p t)) es := by
  classical
  have fold (xs : List (Hex.DensePoly (Hex.RationalFn F)))
      (hx : ∀ p ∈ xs, ∀ i < p.size, Regular embedding t (p.coeff i))
      (prev : Hex.DensePoly (Hex.RationalFn F))
      (hp : ∀ i < prev.size, Regular embedding t (prev.coeff i)) :
      polynomial embedding (xs.foldl (· * ·) prev) t =
        (xs.map (fun p => polynomial embedding p t)).foldl (· * ·) (polynomial embedding prev t) := by
    induction xs generalizing prev with
    | nil => rfl
    | cons p xs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih (fun q hq => hx q (List.mem_cons_of_mem _ hq)) (prev * p)
        (regular_product embedding t prev p hp (hx p (by simp)))]
      rw [polynomial_mul embedding t prev p hp (hx p (by simp))]
  have powers : ∀ p ∈ (qs.zip es).map (fun (q, n) => q.natPow n),
      ∀ i < p.size, Regular embedding t (p.coeff i) := by
    intro p hp
    obtain ⟨⟨q, n⟩, hq, rfl⟩ := List.mem_map.mp hp
    exact regular_power embedding t q n (regular q (List.of_mem_zip hq).1)
  have one : ∀ i < (1 : Hex.DensePoly (Hex.RationalFn F)).size,
      Regular embedding t ((1 : Hex.DensePoly (Hex.RationalFn F)).coeff i) := by
    intro i _
    change Regular embedding t ((Hex.DensePoly.C 1).coeff i)
    rw [Hex.DensePoly.coeff_C]
    split_ifs
    · exact (regularRing embedding t).one_mem
    · exact (regularRing embedding t).zero_mem
  rw [Hex.SignDet.moment, fold _ powers 1 one, polynomial_one]
  unfold Hex.SignDet.moment
  rw [List.zip_map_left, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pair hp
  obtain ⟨p, n⟩ := pair
  exact polynomial_natPow embedding t p n (regular p (List.of_mem_zip hp).1)

/-- info: 'Hex.RealClosure.Specialize.polynomial_natPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_natPow

/-- info: 'Hex.RealClosure.Specialize.moment_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.moment_specialize

end Hex.RealClosure.Specialize

namespace Hex.SignDet
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F] {Ctx : Type u}

/-- The actual chosen query operand specializes, whether direct or reduced. -/
theorem queryPoly_specialize (embedding : F →+* ℝ) (t : ℝ)
    (qs : List (DensePoly (RationalFn F))) (es : List Nat)
    (reduction : Option (Reduction (RationalFn F)))
    (regular : ∀ p ∈ qs, ∀ i < p.size, Regular embedding t (p.coeff i)) :
    polynomial embedding (queryPoly qs es reduction) t =
      queryPoly (qs.map (fun p => polynomial embedding p t)) es
        (reduction.map (Reduction.specialize embedding t)) := by
  cases reduction with
  | none => exact moment_specialize embedding t qs es regular
  | some r => rfl

/-- Finite obligations for the actual moment, optional reduction, and complete
Tarski replay. The ordered query list retains duplicates. -/
@[expose] noncomputable def momentFractions (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F))) (es : List Nat)
    (cert : TarskiCertificate (RationalFn F) (RationalFn F) Ctx)
    (reduction : Option (Reduction (RationalFn F))) : Finset (RationalFn F) := by
  classical
  exact cert.fractions p (queryPoly qs es reduction) a b ∪
    (qs.flatMap (fun q => q.toArray.toList)).toFinset ∪
    (reduction.toList.flatMap (fun r => (r.fractions p qs es).toList)).toFinset

/-- Preserve the complete moment check on its literal exponent positions and
integer value, including all optional product reduction evidence. -/
theorem checkMoment_specialize [DecidableEq Ctx] (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (context : Ctx) (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F))) (es : List Nat)
    (value : Int) (cert : TarskiCertificate (RationalFn F) (RationalFn F) Ctx)
    (reduction : Option (Reduction (RationalFn F)))
    (data : ∀ x ∈ momentFractions p a b qs es cert reduction,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : checkMoment sign context p a b qs es value cert reduction = true) :
    checkMoment (fun x : ℝ => (SignType.sign x : Int)) context (polynomial embedding p t)
      (a.specialize embedding t) (b.specialize embedding t)
      (qs.map (fun q => polynomial embedding q t)) es value
      (cert.specialize embedding t) (reduction.map (Reduction.specialize embedding t)) = true := by
  classical
  have regular q (hq : q ∈ qs) i (hi : i < q.size) :=
    (data (q.coeff i) (Finset.mem_union_left _ (Finset.mem_union_right _
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨q, hq, coefficient_mem q i hi⟩))))).1
  have tarski_data x (hx : x ∈ cert.fractions p (queryPoly qs es reduction) a b) :=
    data x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  simp only [checkMoment_eq, Sturm.check, Bool.and_eq_true] at accepted ⊢
  constructor
  · cases reduction with
    | none => simpa only [Option.map_none, List.length_map] using accepted.1
    | some r =>
      apply r.check_specialize embedding t sign p qs es _ accepted.1
      intro x hx
      exact data x (Finset.mem_union_right _ (List.mem_toFinset.mpr
        (List.mem_flatMap.mpr ⟨r, by simp, Finset.mem_toList.mpr hx⟩)))
  · rw [← queryPoly_specialize embedding t qs es reduction regular]
    exact TarskiCertificate.check_specialize embedding t sign context p (queryPoly qs es reduction)
      a b value cert tarski_data accepted.2

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- One positive neighborhood retains the complete accepted moment evidence. -/
theorem moment_specialize_near [DecidableEq Ctx] (embedding : F →+* ℝ)
    (ordered : StrictMono embedding) (context : Ctx) (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F))) (es : List Nat)
    (value : Int) (cert : TarskiCertificate (RationalFn F) (RationalFn F) Ctx)
    (reduction : Option (Reduction (RationalFn F)))
    (accepted : checkMoment (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
      context p a b qs es value cert reduction = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      checkMoment (fun x : ℝ => (SignType.sign x : Int)) context (polynomial embedding p t)
        (a.specialize embedding t) (b.specialize embedding t)
        (qs.map (fun q => polynomial embedding q t)) es value
        (cert.specialize embedding t) (reduction.map (Reduction.specialize embedding t)) = true := by
  classical
  obtain ⟨η, positive, signs⟩ := finite_fractions_map embedding ordered
    (momentFractions p a b qs es cert reduction)
  refine ⟨η, positive, fun t ht small => ?_⟩
  apply checkMoment_specialize embedding t _ context p a b qs es value cert reduction _ accepted
  intro x hx
  have preserved := signs t ht small x hx
  exact ⟨preserved.1, fraction_zero embedding x t preserved.2, preserved.2⟩

/-- info: 'Hex.SignDet.checkMoment_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.checkMoment_specialize

/-- info: 'Hex.SignDet.moment_specialize_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.moment_specialize_near

end Hex.SignDet
