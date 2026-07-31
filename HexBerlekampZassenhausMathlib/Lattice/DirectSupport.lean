/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Classical.SupportPartition
public import HexBerlekampZassenhausMathlib.Lattice
public import HexBerlekampZassenhausMathlib.PartitionRefinement
import all HexBerlekampZassenhausMathlib.ModPFactor

public section
set_option backward.proofsInPublic true

/-!
# Direct-coordinate factor supports for CLD

The classical and CLD engines use the same modular support and the same
canonical `coreLiftData` lift.  A `DirectFactorCertificate` packages the two
facts downstream consumers need:

* the executable scaled candidate is the normalized integer factor;
* before centering, the scaled lifted product is congruent to that factor
  multiplied by the leading coefficient of its cofactor.

There is no dilation-coordinate factor or correspondence layer.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- Lift a modular support into the sole canonical Hensel basis. -/
@[expose]
def directLiftedSupport
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (S : ModPFactorSubset data) :
    LiftedFactorSubset (Hex.ZPoly.coreLiftData core B data) :=
  liftedSubsetOfModPSubset data (Hex.ZPoly.coreLiftData core B data)
    (henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data) S

/-- `BHKS.supportProduct` and the canonical finite-support product select the
same direct lifted factors. -/
theorem supportProduct_coe_eq_liftedFactorProduct
    (f : Hex.ZPoly) (d : Hex.LiftData) (p a : Nat)
    (S : LiftedFactorSubset d) :
    BHKS.supportProduct (Hex.bhksLatticeBasis f p a d.liftedFactors)
        (↑S : Set (LiftedFactorIndex d)) =
      liftedFactorProduct d S := by
  classical
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial _ = HexPolyZMathlib.toPolynomial _
  rw [toPolynomial_liftedFactorProduct]
  show HexPolyZMathlib.toPolynomial
      (Array.polyProduct
        ((((List.finRange d.liftedFactors.size).filter fun i =>
            @decide (i ∈ (↑S : Set (LiftedFactorIndex d)))
              (Classical.propDecidable _)).map
          fun i => d.liftedFactors.getD i.val 1).toArray)) =
    ∏ i ∈ S, HexPolyZMathlib.toPolynomial (liftedFactor d i)
  rw [polyProduct_toPolynomial, List.toList_toArray, List.map_map]
  simp only [Function.comp_def]
  rw [← List.prod_toFinset
    (fun i : LiftedFactorIndex d => HexPolyZMathlib.toPolynomial
      (d.liftedFactors.getD i.val 1))
    ((List.nodup_finRange d.liftedFactors.size).filter _)]
  refine Finset.prod_congr ?_ (fun i _ => ?_)
  · ext i
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, Finset.mem_coe]
  · show HexPolyZMathlib.toPolynomial (d.liftedFactors.getD i.val 1) =
      HexPolyZMathlib.toPolynomial (liftedFactor d i)
    congr 1
    unfold liftedFactor
    simp [Array.getD, i.isLt]

/-- One normalized irreducible integer factor, indexed by its direct modular
support and carrying the exact congruence used by the CLD column proof. -/
structure DirectFactorCertificate
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (S : ModPFactorSubset data) where
  factor : Hex.ZPoly
  cofactor : Hex.ZPoly
  irreducible : Irreducible (HexPolyZMathlib.toPolynomial factor)
  factor_mul : factor * cofactor = core
  represented : RepresentsIntegerFactorModP data factor S
  normalized : Hex.normalizeFactorSign factor = factor
  supportNonempty : S.Nonempty
  candidate_eq : directSupportCandidate core B data S = factor
  inputScale_coprime :
    Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1
  scaledProduct_congr :
    Hex.ZPoly.congr
      (scaledLiftedFactorProduct core
        (Hex.ZPoly.coreLiftData core B data)
        (directLiftedSupport core B data S))
      (Hex.DensePoly.scale
        (Hex.DensePoly.leadingCoeff cofactor) factor)
      ((Hex.ZPoly.coreLiftData core B data).p ^
        (Hex.ZPoly.coreLiftData core B data).k)

/-- View a direct factor certificate as the logarithmic-derivative recovery
package used by the lattice geometry. -/
@[expose]
noncomputable def DirectFactorCertificate.recoveredLift
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {S : ModPFactorSubset data}
    (C : DirectFactorCertificate core B data S) :
    BHKS.RecoveredLift
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.coreLiftData core B data).p
        (Hex.ZPoly.coreLiftData core B data).k
        (Hex.ZPoly.coreLiftData core B data).liftedFactors)
      (↑(directLiftedSupport core B data S) :
        Set (LiftedFactorIndex (Hex.ZPoly.coreLiftData core B data))) := by
  let d := Hex.ZPoly.coreLiftData core B data
  refine
    { f := core
      p := d.p
      a := d.k
      liftedFactors := d.liftedFactors
      basis_eq := rfl
      factor := C.factor
      cofactor := C.cofactor
      factor_mul := C.factor_mul
      factorScale := Hex.DensePoly.leadingCoeff C.cofactor
      inputScale_coprime := C.inputScale_coprime
      scaledProduct_congr := ?_ }
  rw [supportProduct_coe_eq_liftedFactorProduct
    core d d.p d.k (directLiftedSupport core B data S)]
  simpa [d, scaledLiftedFactorProduct] using C.scaledProduct_congr

namespace DirectFactorCertificate

private theorem intCast_isUnit
    (a : Int) (M : Nat)
    (h : Int.gcd a (Int.ofNat M) = 1) :
    IsUnit ((a : Int) : ZMod M) := by
  have hcop : IsCoprime a (Int.ofNat M) :=
    Int.isCoprime_iff_gcd_eq_one.mpr h
  have hmap := hcop.map (Int.castRingHom (ZMod M))
  apply isCoprime_zero_right.mp
  simpa using hmap

theorem factor_dvd
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {S : ModPFactorSubset data}
    (C : DirectFactorCertificate core B data S) :
    C.factor ∣ core :=
  ⟨C.cofactor, C.factor_mul.symm⟩

theorem factor_ne
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {S : ModPFactorSubset data}
    (C : DirectFactorCertificate core B data S) :
    C.factor ≠ 0 := by
  intro hzero
  exact C.irreducible.ne_zero (by
    rw [hzero]
    exact HexPolyZMathlib.toPolynomial_zero)

theorem primitive
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {S : ModPFactorSubset data}
    (C : DirectFactorCertificate core B data S)
    (hcore_primitive : Hex.ZPoly.Primitive core) :
    Hex.ZPoly.Primitive C.factor :=
  zpoly_primitive_of_dvd_primitive_basic hcore_primitive C.factor_dvd

theorem leadingCoeff_pos
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {S : ModPFactorSubset data}
    (C : DirectFactorCertificate core B data S) :
    0 < Hex.DensePoly.leadingCoeff C.factor :=
  leadingCoeff_pos_of_normalized C.factor_ne C.normalized

theorem degree_pos
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {S : ModPFactorSubset data}
    (C : DirectFactorCertificate core B data S)
    (hcore_primitive : Hex.ZPoly.Primitive core) :
    0 < C.factor.degree?.getD 0 := by
  exact Hex.degree_pos_of_primitive_norm_record
    C.factor (C.primitive hcore_primitive) C.normalized
    (shouldRecordPolynomialFactor_of_irreducible_toPolynomial C.irreducible)

/-- Every local Hensel factor in a certified direct support divides the
represented integer factor modulo the full lift modulus.  The only scalar
cancelled here is the cofactor leading coefficient, which is a unit because it
divides the input leading coefficient. -/
theorem liftedFactor_map_dvd
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {S : ModPFactorSubset data}
    (C : DirectFactorCertificate core B data S)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (i : LiftedFactorIndex (Hex.ZPoly.coreLiftData core B data))
    (hi : i ∈ directLiftedSupport core B data S) :
    (HexPolyZMathlib.toPolynomial
      (liftedFactor (Hex.ZPoly.coreLiftData core B data) i)).map
        (Int.castRingHom (ZMod
          ((Hex.ZPoly.coreLiftData core B data).p ^
            (Hex.ZPoly.coreLiftData core B data).k))) ∣
      (HexPolyZMathlib.toPolynomial C.factor).map
        (Int.castRingHom (ZMod
          ((Hex.ZPoly.coreLiftData core B data).p ^
            (Hex.ZPoly.coreLiftData core B data).k))) := by
  classical
  let d := Hex.ZPoly.coreLiftData core B data
  let M := d.p ^ d.k
  let φ := Int.castRingHom (ZMod M)
  let P := liftedFactorProduct d (directLiftedSupport core B data S)
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hfactor_ne : C.factor ≠ 0 :=
    C.factor_ne
  have hcofactor_ne : C.cofactor ≠ 0 := by
    intro hzero
    apply hcore_ne
    rw [← C.factor_mul, hzero, Hex.DensePoly.mul_comm_poly,
      Hex.DensePoly.zero_mul]
  have hcore_lc :
      Hex.DensePoly.leadingCoeff core =
        Hex.DensePoly.leadingCoeff C.factor *
          Hex.DensePoly.leadingCoeff C.cofactor := by
    calc
      Hex.DensePoly.leadingCoeff core =
          Hex.DensePoly.leadingCoeff (C.factor * C.cofactor) :=
        congrArg Hex.DensePoly.leadingCoeff C.factor_mul.symm
      _ = Hex.DensePoly.leadingCoeff C.factor *
          Hex.DensePoly.leadingCoeff C.cofactor :=
        Hex.ZPoly.leadingCoeff_mul_of_nonzero
          C.factor C.cofactor hfactor_ne hcofactor_ne
  have hcofactor_lc_dvd :
      Hex.DensePoly.leadingCoeff C.cofactor ∣
        Hex.DensePoly.leadingCoeff core :=
    ⟨Hex.DensePoly.leadingCoeff C.factor, by
      rw [hcore_lc, Int.mul_comm]⟩
  have hgcd_cofactor :
      Int.gcd (Hex.DensePoly.leadingCoeff C.cofactor)
        (Int.ofNat M) = 1 := by
    exact gcd_eq_one_of_dvd_left hcofactor_lc_dvd
      (by simpa [M, d, Hex.ZPoly.coreLiftData] using C.inputScale_coprime)
  have hcofactor_unit :
      IsUnit (Polynomial.C (φ
        (Hex.DensePoly.leadingCoeff C.cofactor))) :=
    Polynomial.isUnit_C.mpr
      (intCast_isUnit _ _ hgcd_cofactor)
  have hi_dvd_product :
      (HexPolyZMathlib.toPolynomial (liftedFactor d i)).map φ ∣
        (HexPolyZMathlib.toPolynomial P).map φ := by
    unfold P
    rw [toPolynomial_liftedFactorProduct, Polynomial.map_prod]
    exact Finset.dvd_prod_of_mem
      (fun j : LiftedFactorIndex d =>
        (HexPolyZMathlib.toPolynomial (liftedFactor d j)).map φ) hi
  have hi_dvd_scaled :
      (HexPolyZMathlib.toPolynomial (liftedFactor d i)).map φ ∣
        (HexPolyZMathlib.toPolynomial
          (scaledLiftedFactorProduct core d
            (directLiftedSupport core B data S))).map φ := by
    have hscaled :
        (HexPolyZMathlib.toPolynomial
          (scaledLiftedFactorProduct core d
            (directLiftedSupport core B data S))).map φ =
          Polynomial.C (φ (Hex.DensePoly.leadingCoeff core)) *
            (HexPolyZMathlib.toPolynomial P).map φ := by
      unfold scaledLiftedFactorProduct P
      rw [← Hex.ZPoly.C_mul_eq_scale, HexPolyZMathlib.toPolynomial_mul,
        HexPolyZMathlib.toPolynomial_C, Polynomial.map_mul, Polynomial.map_C]
    rw [hscaled]
    exact dvd_mul_of_dvd_right hi_dvd_product _
  have hcongr :
      (HexPolyZMathlib.toPolynomial
        (scaledLiftedFactorProduct core d
          (directLiftedSupport core B data S))).map φ =
        (HexPolyZMathlib.toPolynomial
          (Hex.DensePoly.scale
            (Hex.DensePoly.leadingCoeff C.cofactor) C.factor)).map φ := by
    exact HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ M
      (by simpa only [M, d] using C.scaledProduct_congr)
  have hright :
      (HexPolyZMathlib.toPolynomial
        (Hex.DensePoly.scale
          (Hex.DensePoly.leadingCoeff C.cofactor) C.factor)).map φ =
        Polynomial.C (φ (Hex.DensePoly.leadingCoeff C.cofactor)) *
          (HexPolyZMathlib.toPolynomial C.factor).map φ := by
    rw [← Hex.ZPoly.C_mul_eq_scale, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_C, Polynomial.map_mul, Polynomial.map_C]
  rw [hcongr, hright, hcofactor_unit.dvd_mul_left] at hi_dvd_scaled
  simpa only [d, M, φ] using hi_dvd_scaled

end DirectFactorCertificate

theorem directSupport_nonempty_of_represents
    {core factor : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {S : ModPFactorSubset data}
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hval : ModPFactorization core data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hnorm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorModP data factor S) :
    S.Nonempty := by
  letI := data.bounds
  letI : Hex.ZMod64.PrimeModulus data.p :=
    Hex.ZMod64.primeModulusOfPrime hval.prime
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  subst S
  have hfactor_ne : factor ≠ 0 := by
    intro hzero
    exact hirr.ne_zero (by rw [hzero]; exact HexPolyZMathlib.toPolynomial_zero)
  have hfactor_degree : 0 < factor.degree?.getD 0 := by
    have hfactor_primitive : Hex.ZPoly.Primitive factor :=
      zpoly_primitive_of_dvd_primitive_basic hcore_primitive hdvd
    have hrecord : Hex.shouldRecordPolynomialFactor factor = true :=
      shouldRecordPolynomialFactor_of_irreducible_toPolynomial hirr
    exact Hex.degree_pos_of_primitive_norm_record
      factor hfactor_primitive hnorm hrecord
  have hfactor_size : 2 ≤ factor.size := by
    have hsize_pos := Hex.ZPoly.size_pos_of_ne_zero factor hfactor_ne
    rw [Hex.DensePoly.degree?_eq_some_of_pos_size factor hsize_pos] at hfactor_degree
    simp only [Option.getD_some] at hfactor_degree
    omega
  obtain ⟨cofactor, hfactorization⟩ := hdvd
  have hcore_ne : core ≠ 0 :=
    Hex.ZPoly.ne_zero_of_primitive core hcore_primitive
  have hcofactor_ne : cofactor ≠ 0 := by
    intro hzero
    apply hcore_ne
    calc
      core = factor * 0 := by simpa [hzero] using hfactorization
      _ = 0 * factor := Hex.DensePoly.mul_comm_poly _ _
      _ = 0 := Hex.DensePoly.zero_mul factor
  have hlc :
      Hex.DensePoly.leadingCoeff core =
        Hex.DensePoly.leadingCoeff factor *
          Hex.DensePoly.leadingCoeff cofactor := by
    rw [hfactorization]
    exact Hex.ZPoly.leadingCoeff_mul_of_nonzero factor cofactor
      hfactor_ne hcofactor_ne
  have hfactor_lc_dvd :
      Hex.DensePoly.leadingCoeff factor ∣
        Hex.DensePoly.leadingCoeff core :=
    ⟨Hex.DensePoly.leadingCoeff cofactor, hlc⟩
  have hgcd_factor :
      Int.gcd (Hex.DensePoly.leadingCoeff factor)
          (Int.ofNat
            (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1 :=
    gcd_eq_one_of_dvd_left hfactor_lc_dvd hgcd
  have hk : 0 < Hex.precisionForCoeffBound B data.p := by omega
  have hpk : 1 < data.p ^ Hex.precisionForCoeffBound B data.p :=
    Nat.one_lt_pow hk.ne' hval.prime.one_lt
  have hadm : Hex.leadingCoeffAdmissible factor data.p :=
    leadingCoeffAdmissible_of_gcd_pow factor data.p
      (Hex.precisionForCoeffBound B data.p)
      hval.prime hpk hk hgcd_factor
  have hmod_size :
      (Hex.ZPoly.modP data.p factor).size = factor.size :=
    Hex.size_modP_eq_of_leadingCoeffAdmissible factor data.p hadm
  have hmod_pos : 0 < (Hex.ZPoly.modP data.p factor).size := by omega
  have hmod_nonzero :
      (Hex.ZPoly.modP data.p factor).isZero = false :=
    (Hex.DensePoly.isZero_eq_false_iff _).mpr hmod_pos
  have hlead_ne :
      Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP data.p factor) ≠
        (0 : Hex.ZMod64 data.p) :=
    fpPoly_leadingCoeff_ne_zero_of_size_pos
      (Hex.ZPoly.modP data.p factor) hmod_pos
  have hinv_ne :
      (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP data.p factor))⁻¹ ≠
        (0 : Hex.ZMod64 data.p) :=
    Hex.ZMod64.inv_ne_zero_of_prime hval.prime hlead_ne
  have hmonic_size :
      (monicModPImage (Hex.ZPoly.modP data.p factor)).size =
        factor.size := by
    unfold monicModPImage
    simp only [hmod_nonzero, Bool.false_eq_true, ↓reduceIte]
    rw [Hex.FpPoly.scale_size_eq_of_ne_zero hinv_ne, hmod_size]
  have hrep_eq :
      modPFactorProduct data (∅ : ModPFactorSubset data) =
        monicModPImage (Hex.ZPoly.modP data.p factor) := by
    exact hrep
  have hrep_one :
      (1 : Hex.FpPoly data.p) =
        monicModPImage (Hex.ZPoly.modP data.p factor) := by
    simpa [modPFactorProduct] using hrep_eq
  have hrep_size := congrArg Hex.DensePoly.size hrep_one
  rw [Hex.DensePoly.size_one
    (Hex.ZMod64.one_ne_zero_of_prime hval.prime)] at hrep_size
  rw [hmonic_size] at hrep_size
  omega

/-- Package a normalized irreducible divisor and its direct modular support
as the single certificate consumed by the CLD proof. -/
@[expose]
noncomputable def directFactorCertificate
    {core factor : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    {S : ModPFactorSubset data}
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hrecovery :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    (hval : ModPFactorization core data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hnorm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorModP data factor S) :
    DirectFactorCertificate core B data S := by
  have hfactor_ne : factor ≠ 0 := by
    intro hzero
    exact hirr.ne_zero (by
      rw [hzero]
      exact HexPolyZMathlib.toPolynomial_zero)
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  let cofactor := Classical.choose hdvd
  have hfactorization : core = factor * cofactor :=
    Classical.choose_spec hdvd
  have hproduct : factor * cofactor = core := hfactorization.symm
  have hcofactor_ne : cofactor ≠ 0 := by
    intro hzero
    apply hcore_ne
    calc
      core = factor * 0 := by simpa [hzero] using hproduct.symm
      _ = 0 * factor := Hex.DensePoly.mul_comm_poly _ _
      _ = 0 := Hex.DensePoly.zero_mul factor
  have hcore_lc :
      Hex.DensePoly.leadingCoeff core =
        Hex.DensePoly.leadingCoeff factor *
          Hex.DensePoly.leadingCoeff cofactor := by
    rw [← hproduct]
    exact Hex.ZPoly.leadingCoeff_mul_of_nonzero factor cofactor
      hfactor_ne hcofactor_ne
  have hfactor_lc_pos :
      0 < Hex.DensePoly.leadingCoeff factor :=
    leadingCoeff_pos_of_normalized hfactor_ne hnorm
  have hcofactor_lc_pos :
      0 < Hex.DensePoly.leadingCoeff cofactor := by
    nlinarith
  have hfactor_lc_dvd :
      Hex.DensePoly.leadingCoeff factor ∣
        Hex.DensePoly.leadingCoeff core :=
    ⟨Hex.DensePoly.leadingCoeff cofactor, hcore_lc⟩
  have hcofactor_lc_dvd :
      Hex.DensePoly.leadingCoeff cofactor ∣
        Hex.DensePoly.leadingCoeff core :=
    ⟨Hex.DensePoly.leadingCoeff factor, by rw [hcore_lc]; ring⟩
  have hgcd_factor :
      Int.gcd (Hex.DensePoly.leadingCoeff factor)
          (Int.ofNat
            (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1 :=
    gcd_eq_one_of_dvd_left hfactor_lc_dvd hgcd
  have hgcd_cofactor :
      Int.gcd (Hex.DensePoly.leadingCoeff cofactor)
          (Int.ofNat
            (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1 :=
    gcd_eq_one_of_dvd_left hcofactor_lc_dvd hgcd
  refine
    { factor := factor
      cofactor := cofactor
      irreducible := hirr
      factor_mul := hproduct
      represented := hrep
      normalized := hnorm
      supportNonempty :=
        directSupport_nonempty_of_represents
          hcore_primitive hval hprecision hgcd hirr hdvd hnorm hrep
      candidate_eq := directSupportCandidate_eq_of_irreducible_dvd
        hcore_primitive hcore_lc_pos hrecovery hval hprecision hgcd
        hirr hdvd hnorm hrep
      inputScale_coprime := hgcd
      scaledProduct_congr := ?_ }
  simpa [directLiftedSupport] using
    (directScaledProduct_congr_of_modP_support
      (core := core) (factor := factor) (cofactor := cofactor)
      (B := B) (data := data) (S := S)
      hval (Hex.ZPoly.size_pos_of_ne_zero core hcore_ne)
      (Hex.ZPoly.size_pos_of_ne_zero factor hfactor_ne)
      hproduct hcore_lc hgcd hgcd_factor hgcd_cofactor
      hprecision hrep)

/-- The direct-coordinate true supports seen by the CLD lattice.  The carrier
is the canonical lift of a modular support and the witness is the exact
factor certificate for that same support. -/
@[expose]
def directTrueSupports
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData) :
    Set (Set (LiftedFactorIndex (Hex.ZPoly.coreLiftData core B data))) :=
  fun U =>
    ∃ S : ModPFactorSubset data,
      Nonempty (DirectFactorCertificate core B data S) ∧
        (↑(directLiftedSupport core B data S) :
          Set (LiftedFactorIndex (Hex.ZPoly.coreLiftData core B data))) = U

namespace directTrueSupports

/-- The full direct support partition covers every lifted factor index. -/
theorem cover
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hrecovery :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    (hval : ModPFactorization core data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hpartition :
      DirectSupportPartition core B data Finset.univ core) :
    ∀ i : LiftedFactorIndex (Hex.ZPoly.coreLiftData core B data),
      ∃ U ∈ directTrueSupports core B data, i ∈ U := by
  intro i
  let d := Hex.ZPoly.coreLiftData core B data
  let hsize : d.liftedFactors.size = data.factorsModP.size :=
    henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data
  let j := modPIndexOfLiftedIndex data d hsize i
  obtain ⟨factor, S, hirr, hdvd, _hsub, hjS, hrep, hnorm, _hcandidate⟩ :=
    hpartition.cover (i := j) (by simp)
  let C : DirectFactorCertificate core B data S :=
    directFactorCertificate hcore_primitive hcore_lc_pos hrecovery
      hval hprecision hgcd hirr hdvd hnorm hrep
  refine
    ⟨(↑(directLiftedSupport core B data S) :
        Set (LiftedFactorIndex d)),
      ⟨S, ⟨C⟩, rfl⟩, ?_⟩
  have hjLift :
      liftedIndexOfModPIndex data d hsize j = i := by
    apply Fin.ext
    rfl
  rw [← hjLift]
  exact (liftedIndex_mem_liftedSubset_iff data d hsize S j).mpr hjS

/-- Two direct true supports containing the same lifted index are equal. -/
theorem eq_of_mem_inter
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hpartition :
      DirectSupportPartition core B data Finset.univ core) :
    ∀ U ∈ directTrueSupports core B data,
      ∀ V ∈ directTrueSupports core B data,
        ∀ i, i ∈ U → i ∈ V → U = V := by
  intro U hU V hV i hiU hiV
  rcases hU with ⟨S, ⟨CS⟩, rfl⟩
  rcases hV with ⟨T, ⟨CT⟩, rfl⟩
  have hSd :
      CS.factor ∣ core :=
    ⟨CS.cofactor, CS.factor_mul.symm⟩
  have hTd :
      CT.factor ∣ core :=
    ⟨CT.cofactor, CT.factor_mul.symm⟩
  by_cases hassoc :
      Associated (HexPolyZMathlib.toPolynomial CS.factor)
        (HexPolyZMathlib.toPolynomial CT.factor)
  · have hST : S = T :=
      hpartition.unique CS.irreducible hSd (Finset.subset_univ S)
        CS.represented CT.irreducible hTd (Finset.subset_univ T)
        CT.represented hassoc
    rw [hST]
  · have hdisjoint : Disjoint S T :=
      hpartition.pairwiseDisjoint CS.irreducible hSd
        (Finset.subset_univ S) CS.represented
        CT.irreducible hTd (Finset.subset_univ T) CT.represented hassoc
    have hliftDisjoint :
        Disjoint (directLiftedSupport core B data S)
          (directLiftedSupport core B data T) := by
      exact
        (liftedSubsetOfModPSubset_disjoint_iff data
          (Hex.ZPoly.coreLiftData core B data)
          (henselLiftData_liftedFactors_size_eq
            (Hex.ZPoly.monicTarget core data.p
              (Hex.precisionForCoeffBound B data.p))
            (Hex.precisionForCoeffBound B data.p) data) S T).mpr hdisjoint
    exact False.elim
      (Finset.disjoint_left.mp hliftDisjoint
        (by simpa using hiU) (by simpa using hiV))

/-- Every certified direct support is nonempty. -/
theorem nonempty
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData} :
    ∀ U ∈ directTrueSupports core B data, U.Nonempty := by
  intro U hU
  rcases hU with ⟨S, ⟨C⟩, rfl⟩
  obtain ⟨i, hi⟩ := C.supportNonempty
  refine ⟨liftedIndexOfModPIndex data
      (Hex.ZPoly.coreLiftData core B data)
      (henselLiftData_liftedFactors_size_eq
        (Hex.ZPoly.monicTarget core data.p
          (Hex.precisionForCoeffBound B data.p))
        (Hex.precisionForCoeffBound B data.p) data) i, ?_⟩
  exact liftedIndex_mem_liftedSubset_iff data
    (Hex.ZPoly.coreLiftData core B data)
    (henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data) S i |>.mpr hi

/-- Direct true supports are in bijection with the normalized irreducible
factors of the square-free core. -/
theorem ncard_eq_normalizedFactors_card
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hrecovery :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    (hval : ModPFactorization core data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hpartition :
      DirectSupportPartition core B data Finset.univ core)
    (hcore_ne : core ≠ 0) :
    (directTrueSupports core B data).ncard =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  classical
  let d := Hex.ZPoly.coreLiftData core B data
  set X := HexPolyZMathlib.toPolynomial core with hX
  have hX_ne : X ≠ 0 := by
    rw [hX]
    intro h
    exact hcore_ne (HexPolyZMathlib.equiv.injective (by simpa using h))
  set φ : Set (LiftedFactorIndex d) → Polynomial ℤ :=
    fun U => normalize (HexPolyZMathlib.toPolynomial
      (scaledRecombinationCandidate core d
        (Set.toFinite U).toFinset)) with hφdef
  have hφ :
      ∀ {S : ModPFactorSubset data}
        (C : DirectFactorCertificate core B data S),
        φ (↑(directLiftedSupport core B data S) :
            Set (LiftedFactorIndex d)) =
          normalize (HexPolyZMathlib.toPolynomial C.factor) := by
    intro S C
    have htf :
        (Set.toFinite
          (↑(directLiftedSupport core B data S) :
            Set (LiftedFactorIndex d))).toFinset =
          directLiftedSupport core B data S := by
      apply Finset.coe_injective
      rw [Set.Finite.coe_toFinset]
    simp only [hφdef]
    rw [htf]
    have hcand :
        scaledRecombinationCandidate core d
            (directLiftedSupport core B data S) = C.factor := by
      simpa [d, directSupportCandidate, directLiftedSupport] using
        C.candidate_eq
    rw [hcand]
  have hbij : Set.BijOn φ (directTrueSupports core B data)
      (↑((UniqueFactorizationMonoid.normalizedFactors X).toFinset) :
        Set (Polynomial ℤ)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro U hU
      rcases hU with ⟨S, ⟨C⟩, rfl⟩
      rw [hφ C]
      have hfactor_dvd : C.factor ∣ core :=
        ⟨C.cofactor, C.factor_mul.symm⟩
      obtain ⟨q, hq_mem, hq_assoc⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
          hX_ne C.irreducible
          (by
            rw [hX]
            exact HexPolyMathlib.toPolynomial_dvd hfactor_dvd)
      have hnorm_q : normalize q = q :=
        UniqueFactorizationMonoid.normalize_normalized_factor q hq_mem
      have heq : normalize (HexPolyZMathlib.toPolynomial C.factor) = q := by
        rw [normalize_eq_normalize_iff_associated.mpr hq_assoc, hnorm_q]
      rw [heq]
      exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr hq_mem)
    · intro U hU V hV hUV
      rcases hU with ⟨S, ⟨CS⟩, rfl⟩
      rcases hV with ⟨T, ⟨CT⟩, rfl⟩
      rw [hφ CS, hφ CT] at hUV
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial CS.factor)
            (HexPolyZMathlib.toPolynomial CT.factor) :=
        normalize_eq_normalize_iff_associated.mp hUV
      have hSd : CS.factor ∣ core :=
        ⟨CS.cofactor, CS.factor_mul.symm⟩
      have hTd : CT.factor ∣ core :=
        ⟨CT.cofactor, CT.factor_mul.symm⟩
      have hST : S = T :=
        hpartition.unique CS.irreducible hSd (Finset.subset_univ S)
          CS.represented CT.irreducible hTd (Finset.subset_univ T)
          CT.represented hassoc
      rw [hST]
    · intro p hp
      have hp_mem : p ∈ UniqueFactorizationMonoid.normalizedFactors X :=
        Multiset.mem_toFinset.mp (Finset.mem_coe.mp hp)
      have hp_irr : Irreducible p :=
        UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp_mem
      have hp_dvd : p ∣ X :=
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp_mem
      have hp_norm : normalize p = p :=
        UniqueFactorizationMonoid.normalize_normalized_factor p hp_mem
      let factor := HexPolyZMathlib.ofPolynomial p
      have hfactor_toPoly :
          HexPolyZMathlib.toPolynomial factor = p :=
        HexPolyZMathlib.toPolynomial_ofPolynomial p
      have hfactor_irr :
          Irreducible (HexPolyZMathlib.toPolynomial factor) := by
        rw [hfactor_toPoly]
        exact hp_irr
      have hfactor_dvd : factor ∣ core := by
        rw [hX] at hp_dvd
        rcases hp_dvd with ⟨r, hr⟩
        refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
        apply HexPolyZMathlib.equiv.injective
        show HexPolyZMathlib.toPolynomial core =
          HexPolyZMathlib.toPolynomial
            (factor * HexPolyZMathlib.ofPolynomial r)
        rw [HexPolyZMathlib.toPolynomial_mul, hfactor_toPoly,
          HexPolyZMathlib.toPolynomial_ofPolynomial]
        exact hr
      have hfactor_norm :
          Hex.normalizeFactorSign factor = factor := by
        apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
        have hlead_normalized : normalize p.leadingCoeff = p.leadingCoeff := by
          have hlead := congrArg Polynomial.leadingCoeff hp_norm
          rwa [Polynomial.leadingCoeff_normalize] at hlead
        have hlc :
            (HexPolyZMathlib.toPolynomial factor).leadingCoeff =
              Hex.DensePoly.leadingCoeff factor :=
          HexPolyMathlib.leadingCoeff_toPolynomial _
        rw [← hlc, hfactor_toPoly]
        exact Int.nonneg_of_normalize_eq_self hlead_normalized
      obtain ⟨S, _hsub, hrep⟩ :=
        hpartition.existsSupport hfactor_irr hfactor_dvd
      let C : DirectFactorCertificate core B data S :=
        directFactorCertificate hcore_primitive hcore_lc_pos hrecovery
          hval hprecision hgcd hfactor_irr hfactor_dvd hfactor_norm hrep
      refine
        ⟨(↑(directLiftedSupport core B data S) :
            Set (LiftedFactorIndex d)),
          ⟨S, ⟨C⟩, rfl⟩, ?_⟩
      rw [hφ C]
      change normalize (HexPolyZMathlib.toPolynomial factor) = p
      rw [hfactor_toPoly, hp_norm]
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors X).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hX_ne).mp
      (by rw [hX]; exact hpartition.targetSquarefree)
  rw [hbij.ncard_eq, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup hnodup]

end directTrueSupports

end
end HexBerlekampZassenhausMathlib
