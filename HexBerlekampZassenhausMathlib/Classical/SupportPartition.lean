/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Hensel.DirectLift
public import HexBerlekampZassenhausMathlib.ModPPartition
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.SubsetCoprimality
import all HexBerlekampZassenhausMathlib.IntReductionMod.Descent

public section
set_option backward.proofsInPublic true

/-!
# Direct modular-support partition

Integer irreducible factors are indexed by subsets of the cached direct
modular factorization.  Canonical lifting turns those subsets into the sole
Hensel basis.  This avoids the old second, dilation-coordinate support model.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/-- Sign normalization changes an integer polynomial only by a unit. -/
theorem normalizeFactorSign_associated (q : Hex.ZPoly) :
    Associated (HexPolyZMathlib.toPolynomial (Hex.normalizeFactorSign q))
      (HexPolyZMathlib.toPolynomial q) := by
  unfold Hex.normalizeFactorSign
  split
  · rw [← Hex.ZPoly.C_mul_eq_scale, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_C]
    have hunit : IsUnit (Polynomial.C (-1 : ℤ)) :=
      Polynomial.isUnit_C.mpr (isUnit_one.neg)
    refine ⟨hunit.unit, ?_⟩
    rw [hunit.unit_spec, mul_comm, ← mul_assoc, ← Polynomial.C_mul]
    norm_num
  · exact Associated.refl _

/-- Distinct irreducible integer factors have disjoint direct modular
supports at the selected square-free prime. -/
theorem modPFactorSubset_disjoint_of_modPFactorization
    {core : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hval : ModPFactorization core data)
    (hcore_pos : 0 < core.degree?.getD 0)
    {f g : Hex.ZPoly} {S T : ModPFactorSubset data}
    (hf_irr : Irreducible (HexPolyZMathlib.toPolynomial f)) (hf_dvd : f ∣ core)
    (hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g)) (hg_dvd : g ∣ core)
    (hS : RepresentsIntegerFactorModP data f S)
    (hT : RepresentsIntegerFactorModP data g T)
    (hnotassoc :
      ¬ Associated (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial g)) :
    Disjoint S T := by
  letI := data.bounds
  have hcore_modP_nz :
      (@Hex.ZPoly.modP data.p data.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core data.p hval.good
  exact modPFactorSubset_disjoint_of_not_associated hval.prime
    (modPSubsetPartitionHypotheses_of_modPFactorization core data hcore_pos hval)
    hcore_modP_nz
    (IntReductionMod.squarefree_toMathlibPolynomial_monicModPImage_of_goodPrime
      core data hval.prime hval.good)
    hf_irr hf_dvd hg_irr hg_dvd hS hT hnotassoc

/-- The selected direct candidate, expressed on a modular support. -/
@[expose]
noncomputable def directSupportCandidate
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (S : ModPFactorSubset data) : Hex.ZPoly :=
  let d := Hex.ZPoly.directLiftData core B data
  scaledRecombinationCandidate core d
    (liftedSubsetOfModPSubset data d
      (henselLiftData_liftedFactors_size_eq
        (Hex.ZPoly.monicTarget core data.p
          (Hex.precisionForCoeffBound B data.p))
        (Hex.precisionForCoeffBound B data.p) data) S)

/-- The good-prime leading coefficient remains nonzero in `ZMod p`, expressed
from the stronger precision-level gcd invariant owned by the direct lift. -/
theorem leadingCoeff_cast_ne_zero_of_gcd
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hprime : Hex.Nat.Prime data.p)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1) :
    ((Hex.DensePoly.leadingCoeff core : Int) : ZMod data.p) ≠ 0 := by
  intro hzero
  have hp_dvd_lc :
      (data.p : Int) ∣ Hex.DensePoly.leadingCoeff core :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (Hex.DensePoly.leadingCoeff core) data.p).mp hzero
  have hp_dvd_pow :
      (data.p : Int) ∣
        Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p) := by
    rw [Int.ofNat_eq_natCast]
    exact_mod_cast dvd_pow_self data.p (by omega : Hex.precisionForCoeffBound B data.p ≠ 0)
  rw [Int.gcd_eq_one_iff] at hgcd
  have hp_dvd_one := hgcd (data.p : Int) hp_dvd_lc hp_dvd_pow
  have hp_nat_dvd_one : data.p ∣ 1 := by
    exact_mod_cast hp_dvd_one
  have hp_eq_one : data.p = 1 := Nat.dvd_one.mp hp_nat_dvd_one
  exact (natPrime_of_hexNatPrime hprime).ne_one hp_eq_one

/-- Modulo the selected prime, a direct candidate is associated to the product
of exactly its selected lifted factors.

The centered lift is congruent to the scaled lifted product.  Its content is a
unit modulo `p` because that mapped polynomial is nonzero; primitive-part and
sign normalization therefore change it only by units.  Finally the
leading-coefficient scale is itself a unit. -/
theorem directSupportCandidate_map_associated
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (facts : DirectLiftFacts core B data)
    (hprime : Hex.Nat.Prime data.p)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (S : ModPFactorSubset data) :
    letI := data.bounds
    let d := Hex.ZPoly.directLiftData core B data
    let T := liftedSubsetOfModPSubset data d
      (henselLiftData_liftedFactors_size_eq
        (Hex.ZPoly.monicTarget core data.p
          (Hex.precisionForCoeffBound B data.p))
        (Hex.precisionForCoeffBound B data.p) data) S
    Associated
      ((HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T)).map
          (Int.castRingHom (ZMod data.p)))
      ((HexPolyZMathlib.toPolynomial
        (liftedFactorProduct d T)).map
          (Int.castRingHom (ZMod data.p))) := by
  letI := data.bounds
  letI : Fact (_root_.Nat.Prime data.p) :=
    ⟨natPrime_of_hexNatPrime hprime⟩
  let d := Hex.ZPoly.directLiftData core B data
  let T := liftedSubsetOfModPSubset data d
    (henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data) S
  let P := liftedFactorProduct d T
  let scaled := scaledLiftedFactorProduct core d T
  let raw := Hex.centeredLiftPoly scaled (d.p ^ d.k)
  let pp := Hex.ZPoly.primitivePart raw
  let cast := Int.castRingHom (ZMod data.p)
  have hk : 0 < d.k := by
    dsimp [d, Hex.ZPoly.directLiftData]
    omega
  have hp_dvd : data.p ∣ d.p ^ d.k := by
    simpa [d, Hex.ZPoly.directLiftData] using dvd_pow_self data.p hk.ne'
  have hraw_congr : Hex.ZPoly.congr raw scaled data.p :=
    Hex.ZPoly.congr_of_dvd_modulus _ _ hp_dvd
      (centeredLiftPoly_congr_self scaled (d.p ^ d.k))
  have hraw_map :
      (HexPolyZMathlib.toPolynomial raw).map cast =
        (HexPolyZMathlib.toPolynomial scaled).map cast :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq raw scaled data.p hraw_congr
  have hP_monic : Hex.DensePoly.Monic P :=
    liftedFactorProduct_monic d T (fun i _ => facts.liftedMonic i)
  have hP_map_monic :
      ((HexPolyZMathlib.toPolynomial P).map cast).Monic :=
    (HexHenselMathlib.toPolynomial_monic_of_dense_monic P hP_monic).map cast
  have hlc_ne :
      cast (Hex.DensePoly.leadingCoeff core) ≠ 0 := by
    simpa [cast] using
      leadingCoeff_cast_ne_zero_of_gcd core B data hprime hprecision hgcd
  have hscaled_map :
      (HexPolyZMathlib.toPolynomial scaled).map cast =
        Polynomial.C (cast (Hex.DensePoly.leadingCoeff core)) *
          (HexPolyZMathlib.toPolynomial P).map cast := by
    unfold scaled scaledLiftedFactorProduct P
    rw [← Hex.ZPoly.C_mul_eq_scale, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_C, Polynomial.map_mul, Polynomial.map_C]
  have hraw_ne :
      (HexPolyZMathlib.toPolynomial raw).map cast ≠ 0 := by
    rw [hraw_map, hscaled_map]
    exact mul_ne_zero
      (Polynomial.C_ne_zero.mpr hlc_ne) hP_map_monic.ne_zero
  have hdecomp :
      (HexPolyZMathlib.toPolynomial raw).map cast =
        Polynomial.C (cast (Hex.ZPoly.content raw)) *
          (HexPolyZMathlib.toPolynomial pp).map cast := by
    unfold pp
    rw [HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart,
      Polynomial.map_mul, Polynomial.map_C]
  have hcontent_ne : cast (Hex.ZPoly.content raw) ≠ 0 := by
    intro hz
    apply hraw_ne
    rw [hdecomp, hz, Polynomial.C_0, zero_mul]
  have hcontent_unit :
      IsUnit (Polynomial.C (cast (Hex.ZPoly.content raw))) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcontent_ne)
  have hpp_raw :
      Associated ((HexPolyZMathlib.toPolynomial pp).map cast)
        ((HexPolyZMathlib.toPolynomial raw).map cast) := by
    refine ⟨hcontent_unit.unit, ?_⟩
    rw [hdecomp, hcontent_unit.unit_spec]
    exact mul_comm _ _
  have hnorm_pp :
      Associated
        ((HexPolyZMathlib.toPolynomial
          (Hex.normalizeFactorSign pp)).map cast)
        ((HexPolyZMathlib.toPolynomial pp).map cast) :=
    (normalizeFactorSign_associated pp).map
      (Polynomial.mapRingHom cast)
  have hlc_unit :
      IsUnit (Polynomial.C (cast (Hex.DensePoly.leadingCoeff core))) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc_ne)
  have hscaled_P :
      Associated ((HexPolyZMathlib.toPolynomial scaled).map cast)
        ((HexPolyZMathlib.toPolynomial P).map cast) := by
    rw [hscaled_map]
    have hC :
        Associated (Polynomial.C (cast (Hex.DensePoly.leadingCoeff core))) 1 :=
      associated_one_iff_isUnit.mpr hlc_unit
    simpa using
      hC.mul_right
        ((HexPolyZMathlib.toPolynomial P).map cast)
  have hraw_P :
      Associated ((HexPolyZMathlib.toPolynomial raw).map cast)
        ((HexPolyZMathlib.toPolynomial P).map cast) := by
    rw [hraw_map]
    exact hscaled_P
  exact hnorm_pp.trans (hpp_raw.trans hraw_P)

/-- Divisibility between products of the cached distinct modular factors
reflects subset containment. -/
theorem modPSubset_subset_of_product_dvd
    {core : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hval : ModPFactorization core data)
    {S T : ModPFactorSubset data}
    (hdvd :
      letI := data.bounds
      HexBerlekampMathlib.toMathlibPolynomial
          (modPFactorProduct data S) ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (modPFactorProduct data T)) :
    S ⊆ T := by
  classical
  letI := data.bounds
  letI : Fact (_root_.Nat.Prime data.p) :=
    ⟨natPrime_of_hexNatPrime hval.prime⟩
  have hinj :=
    toMathlibPolynomial_modPFactor_injective_of_modPFactorization
      core data hval
  have hmonic :=
    toMathlibPolynomial_modPFactor_monic_of_modPFactorization
      core data hval
  intro i hiS
  have hi_dvd_S :
      HexBerlekampMathlib.toMathlibPolynomial (modPFactor data i) ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (modPFactorProduct data S) := by
    rw [toMathlibPolynomial_modPFactorProduct]
    exact Finset.dvd_prod_of_mem _ hiS
  have hi_dvd_T := hi_dvd_S.trans hdvd
  rw [toMathlibPolynomial_modPFactorProduct] at hi_dvd_T
  have hi_prime :=
    (hval.irreducible i).prime
  rcases (Prime.dvd_finsetProd_iff hi_prime
      (fun j : ModPFactorIndex data =>
        HexBerlekampMathlib.toMathlibPolynomial (modPFactor data j))).mp
      hi_dvd_T with ⟨j, hjT, hij_dvd⟩
  have hij_assoc :=
    (hval.irreducible i).associated_of_dvd (hval.irreducible j) hij_dvd
  have hij_poly :=
    Polynomial.eq_of_monic_of_associated (hmonic i) (hmonic j) hij_assoc
  have hij : i = j := hinj hij_poly
  simpa [hij] using hjT

/-- Structural support containment for the direct candidate. -/
theorem directSupport_subset_of_dvd
    {core factor : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    {S T : ModPFactorSubset data}
    (hrecover : directSupportCandidate core B data S = factor)
    (hdvd : factor ∣ directSupportCandidate core B data T) :
    S ⊆ T := by
  letI := data.bounds
  have hcand_dvd :
      (HexPolyZMathlib.toPolynomial
        (directSupportCandidate core B data S)).map
          (Int.castRingHom (ZMod data.p)) ∣
      (HexPolyZMathlib.toPolynomial
        (directSupportCandidate core B data T)).map
          (Int.castRingHom (ZMod data.p)) := by
    have hdvd' :
        directSupportCandidate core B data S ∣
          directSupportCandidate core B data T := by
      rw [hrecover]
      exact hdvd
    have hz := HexPolyMathlib.toPolynomial_dvd hdvd'
    exact Polynomial.map_dvd (Int.castRingHom (ZMod data.p)) hz
  have hSassoc :=
    directSupportCandidate_map_associated core B data facts
      hval.prime hprecision hgcd S
  have hTassoc :=
    directSupportCandidate_map_associated core B data facts
      hval.prime hprecision hgcd T
  have hprod_dvd :
      (HexPolyZMathlib.toPolynomial
        (liftedFactorProduct (Hex.ZPoly.directLiftData core B data)
          (liftedSubsetOfModPSubset data
            (Hex.ZPoly.directLiftData core B data)
            (henselLiftData_liftedFactors_size_eq
              (Hex.ZPoly.monicTarget core data.p
                (Hex.precisionForCoeffBound B data.p))
              (Hex.precisionForCoeffBound B data.p) data) S))).map
          (Int.castRingHom (ZMod data.p)) ∣
      (HexPolyZMathlib.toPolynomial
        (liftedFactorProduct (Hex.ZPoly.directLiftData core B data)
          (liftedSubsetOfModPSubset data
            (Hex.ZPoly.directLiftData core B data)
            (henselLiftData_liftedFactors_size_eq
              (Hex.ZPoly.monicTarget core data.p
                (Hex.precisionForCoeffBound B data.p))
              (Hex.precisionForCoeffBound B data.p) data) T))).map
          (Int.castRingHom (ZMod data.p)) :=
    hSassoc.symm.dvd.trans (hcand_dvd.trans hTassoc.dvd)
  rw [facts.subsetProductMap S, facts.subsetProductMap T] at hprod_dvd
  exact modPSubset_subset_of_product_dvd hval hprod_dvd

/-- A normalized nonzero integer polynomial has positive leading
coefficient. -/
theorem leadingCoeff_pos_of_normalized
    {f : Hex.ZPoly} (hf : f ≠ 0)
    (hnorm : Hex.normalizeFactorSign f = f) :
    0 < Hex.DensePoly.leadingCoeff f := by
  have hnonneg :
      0 ≤ Hex.DensePoly.leadingCoeff f := by
    rw [← hnorm]
    exact Hex.normalizeFactorSign_leadingCoeff_nonneg f
  have hne :
      Hex.DensePoly.leadingCoeff f ≠ 0 :=
    Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero f hf
  omega

/-- Every normalized irreducible divisor of the primitive direct polynomial is
recovered exactly from its unique modular support. -/
theorem directSupportCandidate_eq_of_irreducible_dvd
    {core factor : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hrecovery :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    (hval : ModPFactorization core data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    {S : ModPFactorSubset data}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hnorm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorModP data factor S) :
    directSupportCandidate core B data S = factor := by
  have hfactor_ne : factor ≠ 0 := by
    intro hzero
    exact hirr.ne_zero (by rw [hzero]; exact HexPolyZMathlib.toPolynomial_zero)
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  obtain ⟨cofactor, hfactorization⟩ := hdvd
  have hfactor_dvd : factor ∣ core := ⟨cofactor, hfactorization⟩
  have hproduct : factor * cofactor = core := hfactorization.symm
  have hcofactor_ne : cofactor ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    rw [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.equiv_apply,
      ← hproduct, HexPolyZMathlib.toPolynomial_mul, hzero]
    simp
  have hfactor_lc_pos :
      0 < Hex.DensePoly.leadingCoeff factor :=
    leadingCoeff_pos_of_normalized hfactor_ne hnorm
  have hcore_lc :
      Hex.DensePoly.leadingCoeff core =
        Hex.DensePoly.leadingCoeff factor *
          Hex.DensePoly.leadingCoeff cofactor := by
    rw [← hproduct]
    exact Hex.ZPoly.leadingCoeff_mul_of_nonzero factor cofactor
      hfactor_ne hcofactor_ne
  have hcofactor_lc_pos :
      0 < Hex.DensePoly.leadingCoeff cofactor := by
    nlinarith
  have hfactor_primitive : Hex.ZPoly.Primitive factor :=
    zpoly_primitive_of_dvd_primitive_basic hcore_primitive hfactor_dvd
  have hfactor_primitivePart :
      Hex.ZPoly.primitivePart factor = factor :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive factor hfactor_primitive
  let modulus : Int :=
    Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)
  have hfactor_lc_dvd :
      Hex.DensePoly.leadingCoeff factor ∣
        Hex.DensePoly.leadingCoeff core :=
    ⟨Hex.DensePoly.leadingCoeff cofactor, hcore_lc⟩
  have hcofactor_lc_dvd :
      Hex.DensePoly.leadingCoeff cofactor ∣
        Hex.DensePoly.leadingCoeff core :=
    ⟨Hex.DensePoly.leadingCoeff factor, by rw [hcore_lc]; ring⟩
  have hgcd_factor :
      Int.gcd (Hex.DensePoly.leadingCoeff factor) modulus = 1 :=
    gcd_eq_one_of_dvd_left hfactor_lc_dvd (by simpa [modulus] using hgcd)
  have hgcd_cofactor :
      Int.gcd (Hex.DensePoly.leadingCoeff cofactor) modulus = 1 :=
    gcd_eq_one_of_dvd_left hcofactor_lc_dvd (by simpa [modulus] using hgcd)
  simpa [directSupportCandidate] using
    (directCandidate_eq_of_modP_support
      (core := core) (factor := factor) (cofactor := cofactor)
      (B := B) (data := data) (S := S)
      hval (Hex.ZPoly.size_pos_of_ne_zero core hcore_ne)
      (Hex.ZPoly.size_pos_of_ne_zero factor hfactor_ne)
      hproduct hcore_lc hgcd hgcd_factor hgcd_cofactor
      hcofactor_lc_pos hfactor_primitivePart hnorm hprecision
      hrecovery hrep)

/-- The direct support model retained by recursive recombination.  Every
remaining modular index belongs to exactly one irreducible divisor of the
current target, and its direct candidate is that normalized factor. -/
structure DirectSupportPartition
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (J : ModPFactorSubset data) (target : Hex.ZPoly) : Prop where
  /-- The current target has no repeated irreducible factors. -/
  targetSquarefree : Squarefree (HexPolyZMathlib.toPolynomial target)
  /-- Every irreducible divisor of the target has a support inside `J`. -/
  existsSupport :
    ∀ {factor : Hex.ZPoly},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ target →
      ∃ S : ModPFactorSubset data,
        S ⊆ J ∧ RepresentsIntegerFactorModP data factor S
  /-- Every remaining modular index belongs to a recovered irreducible factor. -/
  cover :
    ∀ {i : ModPFactorIndex data}, i ∈ J →
      ∃ (factor : Hex.ZPoly) (S : ModPFactorSubset data),
        Irreducible (HexPolyZMathlib.toPolynomial factor) ∧
        factor ∣ target ∧
        S ⊆ J ∧
        i ∈ S ∧
        RepresentsIntegerFactorModP data factor S ∧
        Hex.normalizeFactorSign factor = factor ∧
        directSupportCandidate core B data S = factor
  /-- Nonassociated irreducible factors have disjoint modular supports. -/
  pairwiseDisjoint :
    ∀ {f g : Hex.ZPoly} {S T : ModPFactorSubset data},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      S ⊆ J →
      RepresentsIntegerFactorModP data f S →
      Irreducible (HexPolyZMathlib.toPolynomial g) →
      g ∣ target →
      T ⊆ J →
      RepresentsIntegerFactorModP data g T →
      ¬ Associated (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial g) →
      Disjoint S T
  /-- Associated irreducible factors have the same modular support. -/
  unique :
    ∀ {f g : Hex.ZPoly} {S T : ModPFactorSubset data},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      S ⊆ J →
      RepresentsIntegerFactorModP data f S →
      Irreducible (HexPolyZMathlib.toPolynomial g) →
      g ∣ target →
      T ⊆ J →
      RepresentsIntegerFactorModP data g T →
      Associated (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial g) →
      S = T

/-- Construct the initial direct support partition from the selected cached
good-prime factorization. -/
theorem directSupportPartition_initial
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_degree_pos : 0 < core.degree?.getD 0)
    (hcore_squarefree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hrecovery :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    (hval : ModPFactorization core data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1) :
    DirectSupportPartition core B data Finset.univ core := by
  letI := data.bounds
  have hpart :=
    modPSubsetPartitionHypotheses_of_modPFactorization
      core data hcore_degree_pos hval
  refine
    { targetSquarefree := hcore_squarefree
      existsSupport := ?_
      cover := ?_
      pairwiseDisjoint := ?_
      unique := ?_ }
  · intro factor hirr hdvd
    obtain ⟨S, hrep⟩ := hpart.exists_subset hirr hdvd
    exact ⟨S, Finset.subset_univ S, hrep⟩
  · intro i _
    obtain ⟨g, S, hg_irr, hg_dvd, hiS, hg_rep⟩ :=
      modPFactor_index_cover core data hcore_degree_pos hval i
    let factor := Hex.normalizeFactorSign g
    have hassoc :
        Associated (HexPolyZMathlib.toPolynomial factor)
          (HexPolyZMathlib.toPolynomial g) :=
      normalizeFactorSign_associated g
    have hfactor_irr :
        Irreducible (HexPolyZMathlib.toPolynomial factor) :=
      hassoc.symm.irreducible hg_irr
    have hfactor_dvd : factor ∣ core :=
      HexPolyMathlib.toPolynomial_dvd_iff.mp
        (hassoc.dvd.trans (HexPolyMathlib.toPolynomial_dvd hg_dvd))
    have hfactor_rep : RepresentsIntegerFactorModP data factor S :=
      representsIntegerFactorModP_of_associated hval.prime hassoc.symm hg_rep
    have hfactor_norm :
        Hex.normalizeFactorSign factor = factor :=
      Hex.normalizeFactorSign_idem g
    refine ⟨factor, S, hfactor_irr, hfactor_dvd,
      Finset.subset_univ S, hiS, hfactor_rep, hfactor_norm, ?_⟩
    exact directSupportCandidate_eq_of_irreducible_dvd
      hcore_primitive hcore_lc_pos hrecovery hval hprecision hgcd
      hfactor_irr hfactor_dvd hfactor_norm hfactor_rep
  · intro f g S T hf_irr hf_dvd _ hS hg_irr hg_dvd _ hT hnotassoc
    exact modPFactorSubset_disjoint_of_modPFactorization
      hval hcore_degree_pos hf_irr hf_dvd hg_irr hg_dvd hS hT hnotassoc
  · intro f g S T _ _ _ hS hg_irr hg_dvd _ hT hassoc
    exact unique_modPFactorSubset_up_to_associated
      hval.prime hpart hg_irr hg_dvd hS hT hassoc

/-- The support containing the distinguished head modular factor. -/
theorem DirectSupportPartition.coverHead
    {core target : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {J : ModPFactorSubset data}
    (h : DirectSupportPartition core B data J target)
    (head : ModPFactorIndex data) (hhead : head ∈ J) :
    ∃ (factor : Hex.ZPoly) (S : ModPFactorSubset data),
      Irreducible (HexPolyZMathlib.toPolynomial factor) ∧
      factor ∣ target ∧
      S ⊆ J ∧
      head ∈ S ∧
      RepresentsIntegerFactorModP data factor S ∧
      Hex.normalizeFactorSign factor = factor ∧
      directSupportCandidate core B data S = factor :=
  h.cover hhead

/-- A nonzero modular polynomial divides its monic normalization. -/
private theorem fpPoly_dvd_monicImage
    {p : Nat} [Hex.ZMod64.Bounds p]
    {g : Hex.FpPoly p} (hg : g.isZero = false) :
    g ∣ monicModPImage g := by
  unfold monicModPImage
  simp only [hg, Bool.false_eq_true, ↓reduceIte]
  refine ⟨Hex.DensePoly.C (Hex.DensePoly.leadingCoeff g)⁻¹, ?_⟩
  calc
    Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff g)⁻¹ g =
        Hex.DensePoly.C (Hex.DensePoly.leadingCoeff g)⁻¹ * g := by
      rw [Hex.FpPoly.C_mul_eq_scale]
    _ = g * Hex.DensePoly.C (Hex.DensePoly.leadingCoeff g)⁻¹ :=
      Hex.DensePoly.mul_comm_poly _ _

/-- If an accepted direct candidate contains a modular index, then it contains
the irreducible integer factor represented by the true support containing that
index.

Factor the accepted candidate in `ℤ[X]`.  The distinguished modular prime
factor divides its mapped normalized-factor product, so it divides the image
of one normalized integer factor.  That factor has a support in the direct
partition containing the same modular index.  Pairwise disjointness forces it
to be associated to the distinguished true factor. -/
theorem DirectSupportPartition.factorDvdCandidate
    {core target factor : Hex.ZPoly}
    {B : Nat} {data : Hex.PrimeChoiceData}
    {J S T : ModPFactorSubset data}
    (h : DirectSupportPartition core B data J target)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hcore_degree_pos : 0 < core.degree?.getD 0)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd : factor ∣ target)
    (hSJ : S ⊆ J)
    (hfactor_rep : RepresentsIntegerFactorModP data factor S)
    {i : ModPFactorIndex data} (hiS : i ∈ S)
    (hiT : i ∈ T)
    (hcandidate_dvd :
      directSupportCandidate core B data T ∣ target) :
    factor ∣ directSupportCandidate core B data T := by
  classical
  letI := data.bounds
  letI : Fact (_root_.Nat.Prime data.p) :=
    ⟨natPrime_of_hexNatPrime hval.prime⟩
  let cast := Int.castRingHom (ZMod data.p)
  let candidate := directSupportCandidate core B data T
  let candidatePoly := HexPolyZMathlib.toPolynomial candidate
  let candidateMap := candidatePoly.map cast
  let fi :=
    HexBerlekampMathlib.toMathlibPolynomial (modPFactor data i)
  have hcand_assoc :
      Associated candidateMap
        (HexBerlekampMathlib.toMathlibPolynomial
          (modPFactorProduct data T)) := by
    have hassoc :=
      directSupportCandidate_map_associated core B data facts
        hval.prime hprecision hgcd T
    have hsubset := facts.subsetProductMap T
    exact (by
      simpa [candidateMap, candidatePoly, candidate,
        directSupportCandidate] using
        hassoc.trans (Associated.of_eq hsubset))
  have hprod_monic :
      (HexBerlekampMathlib.toMathlibPolynomial
        (modPFactorProduct data T)).Monic := by
    rw [toMathlibPolynomial_modPFactorProduct]
    exact Polynomial.monic_prod_of_monic T
      (fun j => HexBerlekampMathlib.toMathlibPolynomial
        (modPFactor data j))
      (fun j _ =>
        toMathlibPolynomial_modPFactor_monic_of_modPFactorization
          core data hval j)
  have hcand_map_ne : candidateMap ≠ 0 :=
    hcand_assoc.ne_zero_iff.mpr hprod_monic.ne_zero
  have hcand_poly_ne : candidatePoly ≠ 0 := by
    intro hz
    apply hcand_map_ne
    simp [candidateMap, hz]
  have hcand_ne : candidate ≠ 0 := by
    intro hz
    apply hcand_poly_ne
    simp [candidatePoly, hz]
  have hfi_dvd_product :
      fi ∣ HexBerlekampMathlib.toMathlibPolynomial
        (modPFactorProduct data T) := by
    rw [toMathlibPolynomial_modPFactorProduct]
    exact Finset.dvd_prod_of_mem
      (fun j : ModPFactorIndex data =>
        HexBerlekampMathlib.toMathlibPolynomial (modPFactor data j))
      hiT
  have hfi_dvd_candidate : fi ∣ candidateMap :=
    hfi_dvd_product.trans hcand_assoc.symm.dvd
  have hnormalized_assoc :
      Associated
        ((UniqueFactorizationMonoid.normalizedFactors candidatePoly).prod.map cast)
        candidateMap :=
    (UniqueFactorizationMonoid.prod_normalizedFactors hcand_poly_ne).map
      (Polynomial.mapRingHom cast)
  have hfi_dvd_mapped_factors :
      fi ∣
        ((UniqueFactorizationMonoid.normalizedFactors candidatePoly).map
          (Polynomial.map cast)).prod := by
    rw [← Polynomial.map_multiset_prod]
    exact hfi_dvd_candidate.trans hnormalized_assoc.symm.dvd
  have hfi_prime : Prime fi :=
    (hval.irreducible i).prime
  let mapped :=
    (UniqueFactorizationMonoid.normalizedFactors candidatePoly).map
      (Polynomial.map cast)
  have hfi_dvd_list : fi ∣ mapped.toList.prod := by
    rw [Multiset.prod_toList]
    exact hfi_dvd_mapped_factors
  obtain ⟨gMap, hgMap_mem, hfi_dvd_gMap⟩ :=
    (Prime.dvd_prod_iff hfi_prime).mp hfi_dvd_list
  have hgMap_mem' : gMap ∈ mapped :=
    Multiset.mem_toList.mp hgMap_mem
  obtain ⟨gPoly, hgPoly_mem, hgMap_eq⟩ :=
    Multiset.mem_map.mp hgMap_mem'
  subst gMap
  let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
  have hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    simpa [g] using
      UniqueFactorizationMonoid.irreducible_of_normalized_factor
        gPoly hgPoly_mem
  have hgPoly_dvd_candidate : gPoly ∣ candidatePoly :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hgPoly_mem
  have hg_dvd_candidate : g ∣ candidate := by
    apply HexPolyMathlib.toPolynomial_dvd_iff.mp
    simpa [g] using hgPoly_dvd_candidate
  have hg_dvd_target : g ∣ target :=
    zpoly_dvd_trans hg_dvd_candidate hcandidate_dvd
  obtain ⟨U, hUJ, hg_rep⟩ :=
    h.existsSupport hg_irr hg_dvd_target
  have hgMap_ne :
      (HexPolyZMathlib.toPolynomial g).map cast ≠ 0 := by
    have hmap_dvd :
        (HexPolyZMathlib.toPolynomial g).map cast ∣ candidateMap :=
      Polynomial.map_dvd cast
        (HexPolyMathlib.toPolynomial_dvd hg_dvd_candidate)
    obtain ⟨r, hr⟩ := hmap_dvd
    intro hz
    apply hcand_map_ne
    rw [hr, hz, zero_mul]
  have hmodP_ne :
      HexBerlekampMathlib.toMathlibPolynomial
          (Hex.ZPoly.modP data.p g) ≠ 0 := by
    rw [toMathlibPolynomial_modP_eq_map_intCast_zmod]
    exact hgMap_ne
  have hmodP_isZero :
      (Hex.ZPoly.modP data.p g).isZero = false := by
    cases hz : (Hex.ZPoly.modP data.p g).isZero with
    | false => rfl
    | true =>
        exfalso
        apply hmodP_ne
        have hsize :
            (Hex.ZPoly.modP data.p g).size = 0 :=
          (Hex.DensePoly.isZero_eq_true_iff _).mp hz
        have hzero : Hex.ZPoly.modP data.p g = 0 :=
          (Hex.DensePoly.size_eq_zero_iff _).mp hsize
        rw [hzero]
        apply Polynomial.ext
        intro n
        rw [Polynomial.coeff_zero,
          HexBerlekampMathlib.coeff_toMathlibPolynomial,
          Hex.DensePoly.coeff_eq_zero_of_size_le _
            (show (0 : Hex.FpPoly data.p).size ≤ n by simp)]
        exact HexModArithMathlib.ZMod64.toZMod_zero
  have hfi_dvd_modP :
      fi ∣ HexBerlekampMathlib.toMathlibPolynomial
        (Hex.ZPoly.modP data.p g) := by
    rw [toMathlibPolynomial_modP_eq_map_intCast_zmod,
      show HexPolyZMathlib.toPolynomial g = gPoly by
        exact HexPolyZMathlib.toPolynomial_ofPolynomial gPoly]
    exact hfi_dvd_gMap
  have hfi_dvd_monic :
      fi ∣ HexBerlekampMathlib.toMathlibPolynomial
        (monicModPImage (Hex.ZPoly.modP data.p g)) :=
    hfi_dvd_modP.trans
      (HexBerlekampMathlib.toMathlibPolynomial_dvd
        (fpPoly_dvd_monicImage hmodP_isZero))
  have hmodPart :=
    modPSubsetPartitionHypotheses_of_modPFactorization
      core data hcore_degree_pos hval
  have hinj :=
    toMathlibPolynomial_modPFactor_injective_of_modPFactorization
      core data hval
  have hmonic :=
    toMathlibPolynomial_modPFactor_monic_of_modPFactorization
      core data hval
  have hiU : i ∈ U :=
    mem_modPSubset_of_dvd
      (natPrime_of_hexNatPrime hval.prime)
      hmodPart hinj hmonic hg_rep hfi_dvd_monic
  have hassoc :
      Associated (HexPolyZMathlib.toPolynomial factor)
        (HexPolyZMathlib.toPolynomial g) := by
    by_contra hnot
    have hdisj :=
      h.pairwiseDisjoint hfactor_irr hfactor_dvd hSJ hfactor_rep
        hg_irr hg_dvd_target hUJ hg_rep hnot
    exact Finset.disjoint_left.mp hdisj hiS hiU
  exact zpoly_dvd_trans
    (HexPolyMathlib.toPolynomial_dvd_iff.mp hassoc.dvd)
    hg_dvd_candidate

/-- The modular support of the distinguished true factor is contained in any
accepted direct support containing the distinguished modular index. -/
theorem DirectSupportPartition.supportSubsetCandidate
    {core target factor : Hex.ZPoly}
    {B : Nat} {data : Hex.PrimeChoiceData}
    {J S T : ModPFactorSubset data}
    (h : DirectSupportPartition core B data J target)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hcore_degree_pos : 0 < core.degree?.getD 0)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd : factor ∣ target)
    (hSJ : S ⊆ J)
    (hfactor_rep : RepresentsIntegerFactorModP data factor S)
    (hrecover : directSupportCandidate core B data S = factor)
    {i : ModPFactorIndex data} (hiS : i ∈ S) (hiT : i ∈ T)
    (hcandidate_dvd :
      directSupportCandidate core B data T ∣ target) :
    S ⊆ T := by
  have hfactor_dvd_candidate :=
    h.factorDvdCandidate hval facts hcore_degree_pos hprecision hgcd
      hfactor_irr hfactor_dvd hSJ hfactor_rep hiS hiT hcandidate_dvd
  exact directSupport_subset_of_dvd hval facts hprecision hgcd
    hrecover hfactor_dvd_candidate

/-- Remove one emitted irreducible support and transport the partition to the
exact quotient without selecting another prime or performing another lift. -/
theorem DirectSupportPartition.remove
    {core target quotient emitted : Hex.ZPoly}
    {B : Nat} {data : Hex.PrimeChoiceData}
    {J S : ModPFactorSubset data}
    (h : DirectSupportPartition core B data J target)
    (hquot : quotient * emitted = target)
    (hSrep : RepresentsIntegerFactorModP data emitted S)
    (hSJ : S ⊆ J)
    (hEmittedIrr : Irreducible (HexPolyZMathlib.toPolynomial emitted))
    (hEmittedDvd : emitted ∣ target) :
    DirectSupportPartition core B data (J \ S) quotient := by
  have hquot_poly :
      HexPolyZMathlib.toPolynomial quotient *
          HexPolyZMathlib.toPolynomial emitted =
        HexPolyZMathlib.toPolynomial target := by
    rw [← HexPolyZMathlib.toPolynomial_mul, hquot]
  have hquot_squarefree :
      Squarefree (HexPolyZMathlib.toPolynomial quotient) :=
    Squarefree.squarefree_of_dvd
      ⟨HexPolyZMathlib.toPolynomial emitted, hquot_poly.symm⟩
      h.targetSquarefree
  have hdvd_target :
      ∀ {f : Hex.ZPoly}, f ∣ quotient → f ∣ target :=
    fun hdvd => zpoly_dvd_trans hdvd ⟨emitted, hquot.symm⟩
  have hnotassoc :
      ∀ {f : Hex.ZPoly},
        Irreducible (HexPolyZMathlib.toPolynomial f) →
        f ∣ quotient →
        ¬ Associated (HexPolyZMathlib.toPolynomial f)
          (HexPolyZMathlib.toPolynomial emitted) := by
    intro f hf_irr hf_dvd hassoc
    have hemit_dvd_quot :
        HexPolyZMathlib.toPolynomial emitted ∣
          HexPolyZMathlib.toPolynomial quotient :=
      hassoc.symm.dvd.trans (HexPolyMathlib.toPolynomial_dvd hf_dvd)
    have hsquare_dvd :
        HexPolyZMathlib.toPolynomial emitted *
            HexPolyZMathlib.toPolynomial emitted ∣
          HexPolyZMathlib.toPolynomial target := by
      rw [← hquot_poly]
      exact mul_dvd_mul_right hemit_dvd_quot _
    exact hEmittedIrr.not_isUnit (h.targetSquarefree _ hsquare_dvd)
  refine
    { targetSquarefree := hquot_squarefree
      existsSupport := ?_
      cover := ?_
      pairwiseDisjoint := ?_
      unique := ?_ }
  · intro f hf_irr hf_dvd
    obtain ⟨T, hTJ, hTrep⟩ :=
      h.existsSupport hf_irr (hdvd_target hf_dvd)
    have hdisj :=
      h.pairwiseDisjoint hf_irr (hdvd_target hf_dvd) hTJ hTrep
        hEmittedIrr hEmittedDvd hSJ hSrep
        (hnotassoc hf_irr hf_dvd)
    refine ⟨T, ?_, hTrep⟩
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨hTJ hi, fun hiS => Finset.disjoint_left.mp hdisj hi hiS⟩
  · intro i hi
    obtain ⟨hiJ, hiS⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨f, T, hf_irr, hf_dvd_target, hTJ, hiT, hTrep, hnorm, hcand⟩ :=
      h.cover hiJ
    by_cases hassoc :
        Associated (HexPolyZMathlib.toPolynomial f)
          (HexPolyZMathlib.toPolynomial emitted)
    · have hTS : T = S :=
        h.unique hf_irr hf_dvd_target hTJ hTrep
          hEmittedIrr hEmittedDvd hSJ hSrep hassoc
      exact False.elim (hiS (hTS ▸ hiT))
    · have hf_dvd_target_poly :
          HexPolyZMathlib.toPolynomial f ∣
            HexPolyZMathlib.toPolynomial target :=
        HexPolyMathlib.toPolynomial_dvd hf_dvd_target
      rw [← hquot_poly] at hf_dvd_target_poly
      have hf_dvd_quot_poly :
          HexPolyZMathlib.toPolynomial f ∣
            HexPolyZMathlib.toPolynomial quotient := by
        rcases hf_irr.prime.dvd_or_dvd hf_dvd_target_poly with hq | he
        · exact hq
        · exact absurd (hf_irr.associated_of_dvd hEmittedIrr he) hassoc
      have hf_dvd_quot : f ∣ quotient :=
        HexPolyMathlib.toPolynomial_dvd_iff.mp hf_dvd_quot_poly
      have hdisj :=
        h.pairwiseDisjoint hf_irr hf_dvd_target hTJ hTrep
          hEmittedIrr hEmittedDvd hSJ hSrep hassoc
      refine ⟨f, T, hf_irr, hf_dvd_quot, ?_, hiT, hTrep, hnorm, hcand⟩
      intro j hj
      exact Finset.mem_sdiff.mpr
        ⟨hTJ hj, fun hjS => Finset.disjoint_left.mp hdisj hj hjS⟩
  · intro f g T U hf_irr hf_dvd hTJ hTrep
      hg_irr hg_dvd hUJ hUrep hfg
    exact h.pairwiseDisjoint hf_irr (hdvd_target hf_dvd)
      (fun _ hi => (Finset.mem_sdiff.mp (hTJ hi)).1) hTrep
      hg_irr (hdvd_target hg_dvd)
      (fun _ hi => (Finset.mem_sdiff.mp (hUJ hi)).1) hUrep hfg
  · intro f g T U hf_irr hf_dvd hTJ hTrep
      hg_irr hg_dvd hUJ hUrep hfg
    exact h.unique hf_irr (hdvd_target hf_dvd)
      (fun _ hi => (Finset.mem_sdiff.mp (hTJ hi)).1) hTrep
      hg_irr (hdvd_target hg_dvd)
      (fun _ hi => (Finset.mem_sdiff.mp (hUJ hi)).1) hUrep hfg

end HexBerlekampZassenhausMathlib
