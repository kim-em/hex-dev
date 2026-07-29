/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.IntReductionMod.Descent
public import HexPolyZMathlib.Discriminant
public import Mathlib.Algebra.BigOperators.Associated

public section
set_option backward.proofsInPublic true

/-!
Checkable sufficient conditions for the fixed Berlekamp--Zassenhaus hot-path
prime selector.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

namespace HotPath

/-- A good prime for a positive-degree integer polynomial remains good for its
monic correspondent.  Modulo a prime preserving the source leading
coefficient, the defining dilation identity is an invertible change of
variable followed by multiplication by a unit, so coprimality with the
derivative is preserved. -/
theorem good_toMonic
    {core : Hex.ZPoly} {c : Hex.SmallPrimeCandidate}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial core).degree)
    (hgood : @Hex.isGoodPrime core c.p c.bounds = true) :
    @Hex.isGoodPrime (Hex.ZPoly.toMonic core).monic c.p c.bounds = true := by
  letI : Hex.ZMod64.Bounds c.p := c.bounds
  have hp_nat : _root_.Nat.Prime c.p := natPrime_of_hexNatPrime c.prime
  letI : Fact (_root_.Nat.Prime c.p) := ⟨hp_nat⟩
  let φ : ℤ →+* ZMod c.p := Int.castRingHom (ZMod c.p)
  let P : Polynomial (ZMod c.p) :=
    (HexPolyZMathlib.toPolynomial core).map φ
  let M : Hex.ZPoly := (Hex.ZPoly.toMonic core).monic
  let Q : Polynomial (ZMod c.p) :=
    (HexPolyZMathlib.toPolynomial M).map φ
  let u : ZMod c.p := φ (Hex.DensePoly.leadingCoeff core)
  let U : Polynomial (ZMod c.p) := Polynomial.C u * Polynomial.X
  have hu : u ≠ 0 := by
    have h :=
      IntReductionMod.leadingCoeff_castRingHom_ne_zero_of_isGoodPrime core hgood
    simpa [u, φ, HexPolyMathlib.leadingCoeff_toPolynomial] using h
  have hu_unit : IsUnit u := isUnit_iff_ne_zero.mpr hu
  have hPcop : IsCoprime P P.derivative := by
    have h :=
      (IntReductionMod.gcdIsUnit_iff_coprime (Hex.ZPoly.modP c.p core)).mp
        (Hex.isGoodPrime_squareFreeModP core c.p hgood)
    rw [IntReductionMod.toMathlibPolynomial_modP_eq_map_intCast_zmod] at h
    simpa [P, φ] using h
  have hdeg_nat : 1 ≤ (Hex.ZPoly.toMonic core).degree := by
    rw [Hex.ZPoly.toMonic_degree, ← HexPolyMathlib.natDegree_toPolynomial]
    exact (Polynomial.natDegree_pos_iff_degree_pos.mpr hdeg)
  let s : ZMod c.p :=
    φ (Hex.DensePoly.leadingCoeff core ^ ((Hex.ZPoly.toMonic core).degree - 1))
  have hs_unit : IsUnit s := by
    have := hu_unit.pow ((Hex.ZPoly.toMonic core).degree - 1)
    simpa [s, u, map_pow] using this
  have hkey : Q.comp U = Polynomial.C s * P := by
    have h := congrArg
      (fun z : Hex.ZPoly => (HexPolyZMathlib.toPolynomial z).map φ)
      (Hex.ZPoly.dilate_monic_toMonic core hdeg_nat)
    simpa [Q, U, u, s, P, M, HexPolyZMathlib.toPolynomial_dilate,
      HexPolyZMathlib.toPolynomial_mul, HexPolyZMathlib.toPolynomial_C,
      Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
      using h
  have hderiv :
      Polynomial.C u * Q.derivative.comp U =
        Polynomial.C s * P.derivative := by
    calc
      Polynomial.C u * Q.derivative.comp U = (Q.comp U).derivative := by
        rw [Polynomial.derivative_comp]
        simp [U]
      _ = (Polynomial.C s * P).derivative := congrArg Polynomial.derivative hkey
      _ = Polynomial.C s * P.derivative := by simp
  have hscaled :
      IsCoprime (Polynomial.C s * P) (Polynomial.C s * P.derivative) :=
    (isCoprime_mul_unit_left (Polynomial.isUnit_C.mpr hs_unit) P P.derivative).mpr hPcop
  have hcomp_scaled :
      IsCoprime (Q.comp U) (Polynomial.C u * Q.derivative.comp U) := by
    rw [hkey, hderiv]
    exact hscaled
  have hcomp : IsCoprime (Q.comp U) (Q.derivative.comp U) :=
    (isCoprime_mul_unit_left_right (Polynomial.isUnit_C.mpr hu_unit)
      (Q.comp U) (Q.derivative.comp U)).mp hcomp_scaled
  have hQcop : IsCoprime Q Q.derivative := by
    exact (HexPolyZMathlib.isCoprime_comp_unit_mul_X_iff hu_unit).mp
      (by simpa [U] using hcomp)
  have hQmod :
      IsCoprime
        (HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP c.p M))
        (Polynomial.derivative
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP c.p M))) := by
    rw [IntReductionMod.toMathlibPolynomial_modP_eq_map_intCast_zmod]
    simpa [Q, φ] using hQcop
  have hsq :
      Hex.gcdIsUnit
        (Hex.DensePoly.gcd (Hex.ZPoly.modP c.p M)
          (Hex.DensePoly.derivative (Hex.ZPoly.modP c.p M))) = true :=
    (IntReductionMod.gcdIsUnit_iff_coprime (Hex.ZPoly.modP c.p M)).mpr hQmod
  have hM_monic : Hex.DensePoly.Monic M := Hex.ZPoly.toMonic_monic_isMonic core
  have hM_cast :
      φ (HexPolyZMathlib.toPolynomial M).leadingCoeff ≠ 0 := by
    rw [HexPolyMathlib.leadingCoeff_toPolynomial,
      Hex.DensePoly.leadingCoeff_eq_one_of_monic hM_monic]
    simp [φ]
  have hM_adm : Hex.ZPoly.leadingCoeffModP M c.p ≠ 0 :=
    (IntReductionMod.intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero
      (p := c.p) (f := M)).mp (by simpa [φ] using hM_cast)
  exact Hex.isGoodPrime_of_admissible M c.p
    (Hex.isGoodPrime_ge_three core c.p hgood) hM_adm hsq

set_option maxHeartbeats 4000000 in
/-- If a candidate prime does not divide the leading-coefficient/discriminant
product, then it passes the executable good-prime check. -/
theorem good_of_not_dvd
    {g : Hex.ZPoly} {c : Hex.SmallPrimeCandidate}
    (hc : c ∈ Hex.hotPathCandidates)
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial g).degree)
    (hndvd : ¬ (c.p : ℤ) ∣
      (HexPolyZMathlib.toPolynomial g).leadingCoeff *
        (HexPolyZMathlib.toPolynomial g).discr) :
    @Hex.isGoodPrime g c.p c.bounds = true := by
  let P : Polynomial ℤ := HexPolyZMathlib.toPolynomial g
  let φ : ℤ →+* ZMod c.p := Int.castRingHom (ZMod c.p)
  let q : Polynomial (ZMod c.p) := P.map φ
  letI : Hex.ZMod64.Bounds c.p := c.bounds
  have hp_nat : _root_.Nat.Prime c.p := natPrime_of_hexNatPrime c.prime
  letI : Fact (_root_.Nat.Prime c.p) := ⟨hp_nat⟩
  have hp3 : 3 ≤ c.p := (Hex.mem_hotPathCandidates_prime hc).2.1
  have hlc_ndvd : ¬ (c.p : ℤ) ∣ P.leadingCoeff := by
    intro h
    exact hndvd (dvd_mul_of_dvd_left h P.discr)
  have hdisc_ndvd : ¬ (c.p : ℤ) ∣ P.discr := by
    intro h
    exact hndvd (dvd_mul_of_dvd_right h P.leadingCoeff)
  have hlc_cast : φ P.leadingCoeff ≠ 0 := by
    change ¬ ((P.leadingCoeff : ℤ) : ZMod c.p) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hlc_ndvd
  have hdisc_cast : φ P.discr ≠ 0 := by
    change ¬ ((P.discr : ℤ) : ZMod c.p) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdisc_ndvd
  have hadm : Hex.ZPoly.leadingCoeffModP g c.p ≠ 0 :=
    (IntReductionMod.intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero
      (p := c.p) (f := g)).mp (by simpa [P, φ] using hlc_cast)
  have hqdeg : 0 < q.degree := by
    change 0 < (P.map φ).degree
    rw [degree_map_eq_of_leadingCoeff_ne_zero φ hlc_cast]
    exact hdeg
  have hqdisc : q.discr ≠ 0 := by
    change (P.map φ).discr ≠ 0
    rw [Polynomial.discr_map_of_lc φ hdeg hlc_cast]
    exact hdisc_cast
  have hq_lc : q.leadingCoeff ≠ 0 := by
    change (P.map φ).leadingCoeff ≠ 0
    rw [leadingCoeff_map_of_leadingCoeff_ne_zero φ hlc_cast]
    exact hlc_cast
  have hres_pad_ne :
      q.resultant q.derivative q.natDegree (q.natDegree - 1) ≠ 0 := by
    rw [resultant_deriv hqdeg]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hq_lc)
      hqdisc
  have hderiv_le : q.derivative.natDegree ≤ q.natDegree - 1 :=
    natDegree_derivative_le q
  have hres_pad :
      q.resultant q.derivative q.natDegree (q.natDegree - 1) =
        q.leadingCoeff ^ ((q.natDegree - 1) - q.derivative.natDegree) *
          q.resultant q.derivative := by
    have h := resultant_add_right_deg q q.derivative q.natDegree
      q.derivative.natDegree ((q.natDegree - 1) - q.derivative.natDegree)
      le_rfl
    rw [Nat.add_sub_of_le hderiv_le] at h
    simpa [coeff_natDegree] using h
  have hres_ne : q.resultant q.derivative ≠ 0 := by
    intro hzero
    apply hres_pad_ne
    rw [hres_pad, hzero, mul_zero]
  have hq_ne : q ≠ 0 := leadingCoeff_ne_zero.mp hq_lc
  have hcop : IsCoprime q q.derivative := by
    by_contra hnot
    exact hres_ne ((resultant_eq_zero_iff).mpr ⟨Or.inl hq_ne, hnot⟩)
  have hcop_mod :
      IsCoprime
        (HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP c.p g))
        (Polynomial.derivative
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP c.p g))) := by
    rw [IntReductionMod.toMathlibPolynomial_modP_eq_map_intCast_zmod]
    simpa [q, P, φ] using hcop
  have hsq :
      Hex.gcdIsUnit
        (Hex.DensePoly.gcd (Hex.ZPoly.modP c.p g)
          (Hex.DensePoly.derivative (Hex.ZPoly.modP c.p g))) = true :=
    (IntReductionMod.gcdIsUnit_iff_coprime (Hex.ZPoly.modP c.p g)).mpr hcop_mod
  exact Hex.isGoodPrime_of_admissible g c.p hp3 hadm hsq

/-- Failure of `isGoodPrime` for a hot-path candidate forces that prime to
divide the leading-coefficient/discriminant product. -/
theorem dvd_discr_of_bad
    {g : Hex.ZPoly} {c : Hex.SmallPrimeCandidate}
    (hc : c ∈ Hex.hotPathCandidates)
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial g).degree)
    (hbad : @Hex.isGoodPrime g c.p c.bounds = false) :
    (c.p : ℤ) ∣
      (HexPolyZMathlib.toPolynomial g).leadingCoeff *
        (HexPolyZMathlib.toPolynomial g).discr := by
  by_contra hndvd
  have hgood := good_of_not_dvd hc hdeg hndvd
  rw [hgood] at hbad
  simp at hbad

/-- A candidate avoiding the leading-coefficient/discriminant product forces
the fixed selector to return prime data. -/
theorem choose_ne_none_of_not_dvd
    {g : Hex.ZPoly}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial g).degree)
    (h : ∃ c ∈ Hex.hotPathCandidates,
      ¬ (c.p : ℤ) ∣
        (HexPolyZMathlib.toPolynomial g).leadingCoeff *
          (HexPolyZMathlib.toPolynomial g).discr) :
    Hex.choosePrimeData? g ≠ none := by
  obtain ⟨c, hc, hndvd⟩ := h
  exact Hex.choosePrimeData?_ne_none_of_good hc (good_of_not_dvd hc hdeg hndvd)

/-- Any good member of the fixed candidate list forces the live selector to
succeed. -/
theorem choose_ne_none_of_good
    {g : Hex.ZPoly}
    (h : ∃ c ∈ Hex.hotPathCandidates,
      @Hex.isGoodPrime g c.p c.bounds = true) :
    Hex.choosePrimeData? g ≠ none := by
  obtain ⟨c, hc, hgood⟩ := h
  exact Hex.choosePrimeData?_ne_none_of_good hc hgood

/-- A good candidate for a positive-degree core also forces the selector on
its actual monic-transform input to succeed. -/
theorem toMonic_ne_none_of_good
    {core : Hex.ZPoly}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial core).degree)
    (h : ∃ c ∈ Hex.hotPathCandidates,
      @Hex.isGoodPrime core c.p c.bounds = true) :
    Hex.ZPoly.toMonicPrimeData? core ≠ none := by
  obtain ⟨c, hc, hgood⟩ := h
  exact Hex.ZPoly.toMonicPrimeData?_ne_none_of_good hc
    (good_toMonic hdeg hgood)

/-- The monic-transform selector succeeds when a hot-path candidate avoids
the transformed polynomial's leading-coefficient/discriminant product. -/
theorem toMonic_ne_none_of_not_dvd
    {core : Hex.ZPoly}
    (hdeg : 0 <
      (HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).degree)
    (h : ∃ c ∈ Hex.hotPathCandidates,
      ¬ (c.p : ℤ) ∣
        (HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).leadingCoeff *
          (HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).discr) :
    Hex.ZPoly.toMonicPrimeData? core ≠ none := by
  obtain ⟨c, hc, hndvd⟩ := h
  exact Hex.ZPoly.toMonicPrimeData?_ne_none_of_good hc
    (good_of_not_dvd hc hdeg hndvd)

/-- If a candidate fails on the monic transform, it divides the
leading-coefficient/discriminant product of the original positive-degree
core. -/
theorem dvd_core_discr_of_toMonic_bad
    {core : Hex.ZPoly} {c : Hex.SmallPrimeCandidate}
    (hc : c ∈ Hex.hotPathCandidates)
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial core).degree)
    (hbad :
      @Hex.isGoodPrime (Hex.ZPoly.toMonic core).monic c.p c.bounds = false) :
    (c.p : ℤ) ∣
      (HexPolyZMathlib.toPolynomial core).leadingCoeff *
        (HexPolyZMathlib.toPolynomial core).discr := by
  by_contra hndvd
  have hgood := good_of_not_dvd hc hdeg hndvd
  have hgoodM := good_toMonic hdeg hgood
  rw [hgoodM] at hbad
  simp at hbad

/-- Failure of the fixed selector forces the product of all 94 hot-path primes
to divide the absolute leading-coefficient/discriminant product. -/
theorem primorial_dvd_of_none
    {g : Hex.ZPoly}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial g).degree)
    (hnone : Hex.choosePrimeData? g = none) :
    Hex.hotPathPrimorial ∣
      Int.natAbs
        ((HexPolyZMathlib.toPolynomial g).leadingCoeff *
          (HexPolyZMathlib.toPolynomial g).discr) := by
  let values : List Nat := Hex.hotPathCandidates.map fun c => c.p
  let primes : Finset Nat := values.toFinset
  let M : ℤ :=
    (HexPolyZMathlib.toPolynomial g).leadingCoeff *
      (HexPolyZMathlib.toPolynomial g).discr
  have hprime : ∀ p ∈ primes, Prime p := by
    intro p hp
    have hp_values : p ∈ values := List.mem_toFinset.mp hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp_values
    exact (natPrime_of_hexNatPrime c.prime).prime
  have hdiv : ∀ p ∈ primes, p ∣ M.natAbs := by
    intro p hp
    have hp_values : p ∈ values := List.mem_toFinset.mp hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp_values
    have hbad :=
      Hex.mem_hotPathCandidates_isGoodPrime_false_of_choosePrimeData?_none
        hnone hc
    exact Int.natCast_dvd.mp (dvd_discr_of_bad hc hdeg hbad)
  have hall : (∏ p ∈ primes, p) ∣ M.natAbs :=
    Finset.prod_primes_dvd M.natAbs hprime hdiv
  have hnodup : values.Nodup := by
    exact Hex.hotPathPrimeValues_nodup
  have hprod : primes.prod id = values.prod := by
    simpa [primes] using List.prod_toFinset id hnodup
  change values.prod ∣ M.natAbs
  rw [← hprod]
  exact hall

/-- Failure of the adaptive selector has the same complete hot-path failure
certificate as the fixed selector: every candidate is bad. -/
theorem adaptive_primorial_dvd_of_none
    {g : Hex.ZPoly} (extra : Nat)
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial g).degree)
    (hnone : Hex.choosePrimeDataAdaptive? g extra = none) :
    Hex.hotPathPrimorial ∣
      Int.natAbs
        ((HexPolyZMathlib.toPolynomial g).leadingCoeff *
          (HexPolyZMathlib.toPolynomial g).discr) := by
  let values : List Nat := Hex.hotPathCandidates.map fun c => c.p
  let primes : Finset Nat := values.toFinset
  let M : ℤ :=
    (HexPolyZMathlib.toPolynomial g).leadingCoeff *
      (HexPolyZMathlib.toPolynomial g).discr
  have hprime : ∀ p ∈ primes, Prime p := by
    intro p hp
    have hp_values : p ∈ values := List.mem_toFinset.mp hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp_values
    exact (natPrime_of_hexNatPrime c.prime).prime
  have hdiv : ∀ p ∈ primes, p ∣ M.natAbs := by
    intro p hp
    have hp_values : p ∈ values := List.mem_toFinset.mp hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp_values
    have hbad : @Hex.isGoodPrime g c.p c.bounds = false := by
      cases hgood : @Hex.isGoodPrime g c.p c.bounds with
      | false => rfl
      | true =>
          exact False.elim
            ((Hex.choosePrimeDataAdaptive?_ne_none_of_good
              (extra := extra) hc hgood) hnone)
    exact Int.natCast_dvd.mp (dvd_discr_of_bad hc hdeg hbad)
  have hall : (∏ p ∈ primes, p) ∣ M.natAbs :=
    Finset.prod_primes_dvd M.natAbs hprime hdiv
  have hnodup : values.Nodup := Hex.hotPathPrimeValues_nodup
  have hprod : primes.prod id = values.prod := by
    simpa [primes] using List.prod_toFinset id hnodup
  change values.prod ∣ M.natAbs
  rw [← hprod]
  exact hall

/-- Failure of the selector on the monic transform forces the 94-prime
primorial to divide the absolute leading-coefficient/discriminant product of
the original core. -/
theorem toMonic_primorial_dvd_of_none
    {core : Hex.ZPoly}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial core).degree)
    (hnone : Hex.ZPoly.toMonicPrimeData? core = none) :
    Hex.hotPathPrimorial ∣
      Int.natAbs
        ((HexPolyZMathlib.toPolynomial core).leadingCoeff *
          (HexPolyZMathlib.toPolynomial core).discr) := by
  let values : List Nat := Hex.hotPathCandidates.map fun c => c.p
  let primes : Finset Nat := values.toFinset
  let M : ℤ :=
    (HexPolyZMathlib.toPolynomial core).leadingCoeff *
      (HexPolyZMathlib.toPolynomial core).discr
  have hprime : ∀ p ∈ primes, Prime p := by
    intro p hp
    have hp_values : p ∈ values := List.mem_toFinset.mp hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp_values
    exact (natPrime_of_hexNatPrime c.prime).prime
  have hdiv : ∀ p ∈ primes, p ∣ M.natAbs := by
    intro p hp
    have hp_values : p ∈ values := List.mem_toFinset.mp hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp_values
    have hbad :
        @Hex.isGoodPrime (Hex.ZPoly.toMonic core).monic c.p c.bounds = false := by
      cases hgood :
          @Hex.isGoodPrime (Hex.ZPoly.toMonic core).monic c.p c.bounds with
      | false => rfl
      | true =>
          exact False.elim
            ((Hex.ZPoly.toMonicPrimeData?_ne_none_of_good hc hgood) hnone)
    exact Int.natCast_dvd.mp (dvd_core_discr_of_toMonic_bad hc hdeg hbad)
  have hall : (∏ p ∈ primes, p) ∣ M.natAbs :=
    Finset.prod_primes_dvd M.natAbs hprime hdiv
  have hnodup : values.Nodup := Hex.hotPathPrimeValues_nodup
  have hprod : primes.prod id = values.prod := by
    simpa [primes] using List.prod_toFinset id hnodup
  change values.prod ∣ M.natAbs
  rw [← hprod]
  exact hall

/-- Selector failure gives the primorial lower bound as soon as the integer
discriminant product is nonzero. -/
theorem primorial_le_of_none
    {g : Hex.ZPoly}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial g).degree)
    (hdisc : (HexPolyZMathlib.toPolynomial g).discr ≠ 0)
    (hnone : Hex.choosePrimeData? g = none) :
    Hex.hotPathPrimorial ≤
      Int.natAbs
        ((HexPolyZMathlib.toPolynomial g).leadingCoeff *
          (HexPolyZMathlib.toPolynomial g).discr) := by
  have hpoly : HexPolyZMathlib.toPolynomial g ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
  have hlc : (HexPolyZMathlib.toPolynomial g).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr hpoly
  have hM :
      (HexPolyZMathlib.toPolynomial g).leadingCoeff *
        (HexPolyZMathlib.toPolynomial g).discr ≠ 0 :=
    mul_ne_zero hlc hdisc
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hM)
    (primorial_dvd_of_none hdeg hnone)

/-- Monic-transform selector failure gives the primorial lower bound on the
original core's leading-coefficient/discriminant product. -/
theorem toMonic_primorial_le_of_none
    {core : Hex.ZPoly}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial core).degree)
    (hdisc : (HexPolyZMathlib.toPolynomial core).discr ≠ 0)
    (hnone : Hex.ZPoly.toMonicPrimeData? core = none) :
    Hex.hotPathPrimorial ≤
      Int.natAbs
        ((HexPolyZMathlib.toPolynomial core).leadingCoeff *
          (HexPolyZMathlib.toPolynomial core).discr) := by
  have hpoly : HexPolyZMathlib.toPolynomial core ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
  have hlc : (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr hpoly
  have hM :
      (HexPolyZMathlib.toPolynomial core).leadingCoeff *
        (HexPolyZMathlib.toPolynomial core).discr ≠ 0 :=
    mul_ne_zero hlc hdisc
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hM)
    (toMonic_primorial_dvd_of_none hdeg hnone)

/-- A strict primorial bound forces the fixed selector to succeed. -/
theorem choose_ne_none_of_lt_primorial
    {g : Hex.ZPoly}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial g).degree)
    (hdisc : (HexPolyZMathlib.toPolynomial g).discr ≠ 0)
    (hlt : Int.natAbs
      ((HexPolyZMathlib.toPolynomial g).leadingCoeff *
        (HexPolyZMathlib.toPolynomial g).discr) < Hex.hotPathPrimorial) :
    Hex.choosePrimeData? g ≠ none := by
  intro hnone
  have hle := primorial_le_of_none hdeg hdisc hnone
  omega

/-- A strict primorial bound on the original core forces the selector on its
monic transform to succeed. -/
theorem toMonic_ne_none_of_core_lt_primorial
    {core : Hex.ZPoly}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial core).degree)
    (hdisc : (HexPolyZMathlib.toPolynomial core).discr ≠ 0)
    (hlt : Int.natAbs
      ((HexPolyZMathlib.toPolynomial core).leadingCoeff *
        (HexPolyZMathlib.toPolynomial core).discr) < Hex.hotPathPrimorial) :
    Hex.ZPoly.toMonicPrimeData? core ≠ none := by
  intro hnone
  have hle := toMonic_primorial_le_of_none hdeg hdisc hnone
  omega

/-- Separable positive-degree form of the core-facing strict primorial
criterion. -/
theorem toMonic_ne_none_of_separable_lt_primorial
    {core : Hex.ZPoly}
    (hdeg : 0 < (HexPolyZMathlib.toPolynomial core).degree)
    (hsep : ((HexPolyZMathlib.toPolynomial core).map
      (Int.castRingHom ℚ)).Separable)
    (hlt : Int.natAbs
      ((HexPolyZMathlib.toPolynomial core).leadingCoeff *
        (HexPolyZMathlib.toPolynomial core).discr) < Hex.hotPathPrimorial) :
    Hex.ZPoly.toMonicPrimeData? core ≠ none := by
  have habs := Polynomial.one_le_abs_discr hdeg hsep
  apply toMonic_ne_none_of_core_lt_primorial hdeg
  · intro hzero
    rw [hzero] at habs
    simp at habs
  · exact hlt

/-- Normalized square-free-core specialization of the checkable primorial
criterion consumed by the factorization dispatcher. -/
theorem normalizedCore_toMonic_ne_none_of_lt_primorial
    {f : Hex.ZPoly} (hf : f ≠ 0)
    (hdeg : 0 <
      (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).squareFreeCore).degree)
    (hlt : Int.natAbs
      ((HexPolyZMathlib.toPolynomial
          (Hex.normalizeForFactor f).squareFreeCore).leadingCoeff *
        (HexPolyZMathlib.toPolynomial
          (Hex.normalizeForFactor f).squareFreeCore).discr) <
        Hex.hotPathPrimorial) :
    Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore ≠ none := by
  exact toMonic_ne_none_of_separable_lt_primorial hdeg
    (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_separable f hf)
    hlt

/-- Transformed-monic form of the strict primorial selector criterion. -/
theorem toMonic_ne_none_of_lt_primorial
    {core : Hex.ZPoly}
    (hdeg : 0 <
      (HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).degree)
    (hdisc :
      (HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).discr ≠ 0)
    (hlt : Int.natAbs
      ((HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).leadingCoeff *
        (HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).discr) <
          Hex.hotPathPrimorial) :
    Hex.ZPoly.toMonicPrimeData? core ≠ none := by
  intro hnone
  have hpoly :
      HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
  have hlc :
      (HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr hpoly
  have hM :
      (HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).leadingCoeff *
        (HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic).discr ≠ 0 :=
    mul_ne_zero hlc hdisc
  have hnone' :
      Hex.choosePrimeDataAdaptive? (Hex.ZPoly.toMonic core).monic
        Hex.ZPoly.primeProbeFuel = none := hnone
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hM)
    (adaptive_primorial_dvd_of_none Hex.ZPoly.primeProbeFuel hdeg hnone')
  omega

end HotPath

end HexBerlekampZassenhausMathlib
