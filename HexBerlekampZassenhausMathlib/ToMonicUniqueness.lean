/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Basic
public import HexBerlekampZassenhausMathlib.UFDPartition
public import HexHenselMathlib.Correctness
public import HexPolyZMathlib.Basic
public import HexPolyZMathlib.Mignotte
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PrincipalIdealDomain

public import HexBerlekampZassenhausMathlib.MonicCorrespondent
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.SubsetCoprimality
import all HexBerlekampZassenhausMathlib.ForwardHenselTransport
import all HexBerlekampZassenhausMathlib.RecombinationMonic
import all HexBerlekampZassenhausMathlib.PrimitivityDegreeCover
import all HexBerlekampZassenhausMathlib.ScaledSearchCoverage
import all HexBerlekampZassenhausMathlib.SmartSearchCoverage
import all HexBerlekampZassenhausMathlib.SearchAssembly
import all HexBerlekampZassenhausMathlib.MonicCorrespondent

public section
set_option backward.proofsInPublic true

/-!
This module collects the non-circular lift-stage subset-uniqueness core (#7474).
-/

namespace HexBerlekampZassenhausMathlib

/-! ### Non-circular lift-stage subset-uniqueness core (#7474)

The lemmas below establish, for `d := Hex.ZPoly.toMonicLiftData core B primeData`
on a non-monic `core` with positive leading coefficient and a prime selected by
the monic transform, that the lift-stage representation determines the selecting
subset up to the obvious constraints — *without* assuming any
`LiftedFactorSubsetPartition` / `InitialLiftedFactorSubsetPartitionEvidence`.

The argument routes a candidate divisibility through reduction modulo
`primeData.p`: each lifted-factor reduction is irreducible (the corresponding
`modPFactor`), distinct reductions are coprime, and the mod-`p` product of a
subset is coprime to the product over its complement.  A shared index would make
the corresponding mod-`p` irreducible divide both a subset product and its
complement, contradicting coprimality. -/

/-- Every lifted-factor subset is the image of a mod-`p` factor subset under
`liftedSubsetOfModPSubset`: the index embedding is a bijection between
equal-cardinality finite index types. -/
private theorem exists_modPSubset_map_eq
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (T : LiftedFactorSubset d) :
    ∃ S : ModPFactorSubset primeData,
      liftedSubsetOfModPSubset primeData d hsize S = T := by
  classical
  refine ⟨T.preimage (modPIndexToLiftedEmbedding primeData d hsize)
      ((modPIndexToLiftedEmbedding primeData d hsize).injective.injOn), ?_⟩
  unfold liftedSubsetOfModPSubset
  rw [Finset.map_eq_image, Finset.image_preimage]
  apply Finset.filter_true_of_mem
  intro x _
  simpa using modPIndexToLiftedEmbedding_surjective primeData d hsize x

/-- For `d := toMonicLiftData core B primeData` with a prime selected by the
monic transform, the mod-`p` reduction of any lifted-factor subset product is
coprime to the reduction of the complement product. -/
theorem toMonicLiftData_isCoprime_liftedFactorProduct_complement
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (T : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData)) :
    IsCoprime
      ((HexPolyZMathlib.toPolynomial
          (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) T)).map
        (Int.castRingHom (ZMod primeData.p)))
      ((HexPolyZMathlib.toPolynomial
          (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData)
            ((Finset.univ : LiftedFactorSubset
                (Hex.ZPoly.toMonicLiftData core B primeData)) \ T))).map
        (Int.castRingHom (ZMod primeData.p))) := by
  classical
  set monicCore := (Hex.ZPoly.toMonic core).monic with hmonicCore_def
  set precision := Hex.precisionForCoeffBound B primeData.p with hprec_def
  have hmonicCore_monic : Hex.DensePoly.Monic monicCore :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hmonicCore_pos : 0 < monicCore.degree?.getD 0 := by
    rw [hmonicCore_def,
      Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos hcore_pos]
    exact hcore_pos
  have hgood :
      letI := primeData.bounds
      Hex.isGoodPrime monicCore primeData.p = true :=
    hval.good
  have hp_prime : Hex.Nat.Prime primeData.p :=
    hval.prime
  have hp : 1 < primeData.p := by have := hp_prime.two_le; omega
  have hprime_root : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hp, ?_⟩
    intro m hmlt hmdvd
    rcases hp_prime.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  have hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g :=
    hval.monic
  have hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        monicCore primeData.p :=
    hval.product_congr_target hmonicCore_monic
  have hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList :=
    hval.coprime
  have hnonempty : primeData.factorsModP.toList ≠ [] :=
    hval.ne_nil
  have hinv :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p precision monicCore
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList := by
    letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
    exact Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      monicCore precision primeData
      hp_prime hp hprecision hmonicCore_monic hfactors_monic
      hproduct_mod_p hcoprime hnonempty
  have hfactors_irr :
      letI := primeData.bounds
      ∀ i : ModPFactorIndex primeData,
        Irreducible
          (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)) :=
    hval.irreducible
  have hfactors_nodup : primeData.factorsModP.toList.Nodup :=
    hval.nodup
  -- `d := toMonicLiftData core B primeData` is definitionally
  -- `henselLiftData monicCore precision primeData`.
  -- `toMonicLiftData core B primeData` is definitionally
  -- `henselLiftData monicCore precision primeData`; restate the goal over the
  -- latter so the coprimality lemma applies syntactically.
  show IsCoprime
      ((HexPolyZMathlib.toPolynomial
          (liftedFactorProduct (Hex.henselLiftData monicCore precision primeData) T)).map
        (Int.castRingHom (ZMod primeData.p)))
      ((HexPolyZMathlib.toPolynomial
          (liftedFactorProduct (Hex.henselLiftData monicCore precision primeData)
            ((Finset.univ : LiftedFactorSubset
                (Hex.henselLiftData monicCore precision primeData)) \ T))).map
        (Int.castRingHom (ZMod primeData.p)))
  obtain ⟨S, hS⟩ := exists_modPSubset_map_eq primeData
    (Hex.henselLiftData monicCore precision primeData)
    (henselLiftData_liftedFactors_size_eq monicCore precision primeData) T
  rw [← hS]
  exact henselLiftData_liftedSubset_complement_isCoprime_mod_p
    monicCore precision primeData hmonicCore_monic hprime_root hinv hp hprecision
    hfactors_monic hproduct_mod_p hfactors_irr hfactors_nodup S

/-- Each lifted factor of `toMonicLiftData core B primeData` reduces modulo
`primeData.p` to an irreducible polynomial (the corresponding `modPFactor`). -/
private theorem toMonicLiftData_liftedFactor_map_irreducible
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (i : LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData)) :
    Irreducible
      ((HexPolyZMathlib.toPolynomial
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).map
        (Int.castRingHom (ZMod primeData.p))) := by
  classical
  letI := primeData.bounds
  set monicCore := (Hex.ZPoly.toMonic core).monic with hmonicCore_def
  set precision := Hex.precisionForCoeffBound B primeData.p with hprec_def
  have hmonicCore_monic : Hex.DensePoly.Monic monicCore :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hmonicCore_pos : 0 < monicCore.degree?.getD 0 := by
    rw [hmonicCore_def,
      Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos hcore_pos]
    exact hcore_pos
  have hgood :
      letI := primeData.bounds
      Hex.isGoodPrime monicCore primeData.p = true :=
    hval.good
  have hp_prime : Hex.Nat.Prime primeData.p :=
    hval.prime
  have hp : 1 < primeData.p := by have := hp_prime.two_le; omega
  have hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g :=
    hval.monic
  have hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        monicCore primeData.p :=
    hval.product_congr_target hmonicCore_monic
  have hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList :=
    hval.coprime
  have hnonempty : primeData.factorsModP.toList ≠ [] :=
    hval.ne_nil
  have hinv :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p precision monicCore
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList := by
    letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
    exact Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      monicCore precision primeData
      hp_prime hp hprecision hmonicCore_monic hfactors_monic
      hproduct_mod_p hcoprime hnonempty
  have hfactors_irr :
      letI := primeData.bounds
      ∀ i : ModPFactorIndex primeData,
        Irreducible
          (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)) :=
    hval.irreducible
  -- `i` as a modular-factor index (same `val`; the sizes agree definitionally).
  have hival : i.val < primeData.factorsModP.size :=
    i.isLt.trans_eq
      (henselLiftData_liftedFactors_size_eq monicCore precision primeData)
  have hmodP :=
    henselLiftData_liftedFactor_modP_eq_modPFactor monicCore precision primeData
      hmonicCore_monic hinv hp hprecision hfactors_monic hproduct_mod_p
      (⟨i.val, hival⟩ : ModPFactorIndex primeData)
  have hLF :
      liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i =
        liftedFactor (Hex.henselLiftData monicCore precision primeData)
          (liftedIndexOfModPIndex primeData
            (Hex.henselLiftData monicCore precision primeData)
            (henselLiftData_liftedFactors_size_eq monicCore precision primeData)
            (⟨i.val, hival⟩ : ModPFactorIndex primeData)) := rfl
  have hbridge :
      (HexPolyZMathlib.toPolynomial
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).map
          (Int.castRingHom (ZMod primeData.p))
        = HexBerlekampMathlib.toMathlibPolynomial
            (modPFactor primeData (⟨i.val, hival⟩ : ModPFactorIndex primeData)) :=
    calc
      (HexPolyZMathlib.toPolynomial
            (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).map
            (Int.castRingHom (ZMod primeData.p))
          = (HexPolyZMathlib.toPolynomial
              (liftedFactor (Hex.henselLiftData monicCore precision primeData)
                (liftedIndexOfModPIndex primeData
                  (Hex.henselLiftData monicCore precision primeData)
                  (henselLiftData_liftedFactors_size_eq monicCore precision primeData)
                  (⟨i.val, hival⟩ : ModPFactorIndex primeData)))).map
              (Int.castRingHom (ZMod primeData.p)) := by rw [hLF]
      _ = HexBerlekampMathlib.toMathlibPolynomial
            (Hex.ZPoly.modP primeData.p
              (liftedFactor (Hex.henselLiftData monicCore precision primeData)
                (liftedIndexOfModPIndex primeData
                  (Hex.henselLiftData monicCore precision primeData)
                  (henselLiftData_liftedFactors_size_eq monicCore precision primeData)
                  (⟨i.val, hival⟩ : ModPFactorIndex primeData)))) :=
          (toMathlibPolynomial_modP_eq_map_intCast_zmod (p := primeData.p) _).symm
      _ = HexBerlekampMathlib.toMathlibPolynomial
            (modPFactor primeData (⟨i.val, hival⟩ : ModPFactorIndex primeData)) := by
          rw [hmodP]
  rw [hbridge]
  exact hfactors_irr (⟨i.val, hival⟩ : ModPFactorIndex primeData)

/-- **Clean half of the lift-stage subset core.** If the mod-`p` reduction of the
selected lifted-factor product over `S` divides that over `T`, then `S ⊆ T`.

A shared index `i ∈ S \ T` would make the irreducible mod-`p` reduction of
`liftedFactor d i` divide both the product over `T` and the product over its
complement, contradicting their coprimality. Non-circular: it assumes no
`LiftedFactorSubsetPartition`. -/
theorem toMonicLiftData_subset_of_liftedFactorProduct_map_dvd
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    {S T : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData)}
    (hdvd :
      (HexPolyZMathlib.toPolynomial
          (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) S)).map
          (Int.castRingHom (ZMod primeData.p)) ∣
        (HexPolyZMathlib.toPolynomial
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) T)).map
          (Int.castRingHom (ZMod primeData.p))) :
    S ⊆ T := by
  classical
  intro i hiS
  by_contra hiT
  have hi_compl :
      i ∈ ((Finset.univ : LiftedFactorSubset
          (Hex.ZPoly.toMonicLiftData core B primeData)) \ T) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiT⟩
  -- The mod-`p` product over any subset is the product of the per-factor
  -- reductions.
  have hprod : ∀ U : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData),
      (HexPolyZMathlib.toPolynomial
          (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) U)).map
          (Int.castRingHom (ZMod primeData.p)) =
        ∏ j ∈ U, (HexPolyZMathlib.toPolynomial
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) j)).map
          (Int.castRingHom (ZMod primeData.p)) := by
    intro U
    rw [toPolynomial_liftedFactorProduct, Polynomial.map_prod]
  have hφS :
      (HexPolyZMathlib.toPolynomial
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).map
          (Int.castRingHom (ZMod primeData.p)) ∣
        (HexPolyZMathlib.toPolynomial
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) S)).map
          (Int.castRingHom (ZMod primeData.p)) := by
    rw [hprod S]; exact Finset.dvd_prod_of_mem _ hiS
  have hφcompl :
      (HexPolyZMathlib.toPolynomial
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).map
          (Int.castRingHom (ZMod primeData.p)) ∣
        (HexPolyZMathlib.toPolynomial
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData)
              ((Finset.univ : LiftedFactorSubset
                  (Hex.ZPoly.toMonicLiftData core B primeData)) \ T))).map
          (Int.castRingHom (ZMod primeData.p)) := by
    rw [hprod _]; exact Finset.dvd_prod_of_mem _ hi_compl
  have hφT :
      (HexPolyZMathlib.toPolynomial
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).map
          (Int.castRingHom (ZMod primeData.p)) ∣
        (HexPolyZMathlib.toPolynomial
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) T)).map
          (Int.castRingHom (ZMod primeData.p)) :=
    dvd_trans hφS hdvd
  have hcop :=
    toMonicLiftData_isCoprime_liftedFactorProduct_complement core B primeData
      hcore_lc_pos hcore_pos
      hval hprecision T
  have hunit := hcop.isUnit_of_dvd' hφT hφcompl
  exact (toMonicLiftData_liftedFactor_map_irreducible core B primeData
    hcore_lc_pos hcore_pos
      hval hprecision i).not_isUnit hunit

/-- A centred lift is congruent to its input modulo the centring modulus.

A reusable transport fact for the remaining candidate-divisibility half of the
core: `centeredLiftPoly q m ≡ q (mod m)`, hence (descending the modulus)
`≡ q (mod p)` for the Hensel prime. -/
private theorem congr_centeredLiftPoly (q : Hex.ZPoly) (m : Nat) :
    Hex.ZPoly.congr (Hex.centeredLiftPoly q m) q m := by
  intro i
  rw [Hex.coeff_centeredLiftPoly]
  exact Int.emod_eq_zero_of_dvd
    (dvd_sub_comm.mp (Hex.self_sub_centeredModNat_dvd (q.coeff i) m))

/-- Sign normalisation is an associate over `Polynomial ℤ`: `normalizeFactorSign`
either fixes its argument or negates it (scaling by `-1`), and `-1` is a unit. -/
theorem toPolynomial_normalizeFactorSign_associated (q : Hex.ZPoly) :
    Associated (HexPolyZMathlib.toPolynomial (Hex.normalizeFactorSign q))
      (HexPolyZMathlib.toPolynomial q) := by
  unfold Hex.normalizeFactorSign
  split
  · rw [← Hex.ZPoly.C_mul_eq_scale, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_C]
    have huneg : IsUnit (Polynomial.C (-1 : ℤ)) :=
      Polynomial.isUnit_C.mpr (isUnit_one.neg)
    refine ⟨huneg.unit, ?_⟩
    rw [huneg.unit_spec, mul_comm, ← mul_assoc, ← Polynomial.C_mul]
    norm_num
  · exact Associated.refl _

/-- **Recovery dilation reflection.** If the primitive parts of the
`lc`-dilations of two monic integer polynomials divide one another over
`Polynomial ℤ`, then the polynomials themselves do.

Over `ℚ` the variable dilation `X ↦ lc · X` is the algebra automorphism
`algEquivCMulXAddC lc 0` (`lc ≠ 0`), so it reflects divisibility; the residual
content scalars are units there; and Gauss's lemma moves the conclusion back to
`ℤ[X]`, using that both monic inputs are primitive. -/
private theorem toPolynomial_dvd_of_primitivePart_dilate_dvd
    {a b : Hex.ZPoly} {lc : Int}
    (hlc : lc ≠ 0)
    (ha_monic : Hex.DensePoly.Monic a)
    (hb_monic : Hex.DensePoly.Monic b)
    (hdvd :
      HexPolyZMathlib.toPolynomial
          (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc a)) ∣
        HexPolyZMathlib.toPolynomial
          (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc b))) :
    HexPolyZMathlib.toPolynomial a ∣ HexPolyZMathlib.toPolynomial b := by
  classical
  set cast := Int.castRingHom ℚ with hcast
  have hA_monic : (HexPolyZMathlib.toPolynomial a).Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic a ha_monic
  have hB_monic : (HexPolyZMathlib.toPolynomial b).Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic b hb_monic
  have hA_prim : (HexPolyZMathlib.toPolynomial a).IsPrimitive := hA_monic.isPrimitive
  have hB_prim : (HexPolyZMathlib.toPolynomial b).IsPrimitive := hB_monic.isPrimitive
  have hca : cast lc ≠ 0 := by rw [eq_intCast cast lc]; exact_mod_cast hlc
  letI : Invertible (cast lc) := invertibleOfNonzero hca
  -- Per-side bridge: the primitive-part image over `ℚ` is associated to the
  -- automorphism applied to the polynomial's image.
  have key : ∀ U : Hex.ZPoly, Hex.DensePoly.Monic U →
      Associated
        ((HexPolyZMathlib.toPolynomial
            (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc U))).map cast)
        ((Polynomial.algEquivCMulXAddC (cast lc) (0 : ℚ))
          ((HexPolyZMathlib.toPolynomial U).map cast)) := by
    intro U hU
    have hU_monic : (HexPolyZMathlib.toPolynomial U).Monic :=
      HexHenselMathlib.toPolynomial_monic_of_dense_monic U hU
    have hcomp :
        HexPolyZMathlib.toPolynomial (Hex.ZPoly.dilate lc U)
          = (HexPolyZMathlib.toPolynomial U).comp (Polynomial.C lc * Polynomial.X) :=
      HexPolyZMathlib.toPolynomial_dilate lc U
    have hD0 : Hex.ZPoly.dilate lc U ≠ 0 := by
      intro hz
      have : HexPolyZMathlib.toPolynomial U ≠ 0 := hU_monic.ne_zero
      apply this
      have hcomp0 :
          (HexPolyZMathlib.toPolynomial U).comp (Polynomial.C lc * Polynomial.X) = 0 := by
        rw [← hcomp, hz, HexPolyZMathlib.toPolynomial_zero]
      rwa [Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hlc)] at hcomp0
    have hc0 : Hex.ZPoly.content (Hex.ZPoly.dilate lc U) ≠ 0 :=
      HexPolyZMathlib.content_ne_zero _ hD0
    have hcc : cast (Hex.ZPoly.content (Hex.ZPoly.dilate lc U)) ≠ 0 := by
      rw [eq_intCast cast _]; exact_mod_cast hc0
    -- Content decomposition over `ℤ`, mapped to `ℚ`.
    have hmapCF :
        (HexPolyZMathlib.toPolynomial (Hex.ZPoly.dilate lc U)).map cast
          = Polynomial.C (cast (Hex.ZPoly.content (Hex.ZPoly.dilate lc U))) *
              (HexPolyZMathlib.toPolynomial
                (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc U))).map cast := by
      rw [HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart, Polynomial.map_mul,
        Polynomial.map_C]
    -- Dilation image over `ℚ` is the automorphism applied to the base image.
    have hmapComp :
        (HexPolyZMathlib.toPolynomial (Hex.ZPoly.dilate lc U)).map cast
          = (Polynomial.algEquivCMulXAddC (cast lc) (0 : ℚ))
              ((HexPolyZMathlib.toPolynomial U).map cast) := by
      rw [hcomp, Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Polynomial.algEquivCMulXAddC_apply, ← Polynomial.comp_eq_aeval]
      simp
    have huC : IsUnit (Polynomial.C (cast (Hex.ZPoly.content (Hex.ZPoly.dilate lc U)))) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcc)
    refine ⟨huC.unit, ?_⟩
    rw [← hmapComp, hmapCF, huC.unit_spec]
    exact mul_comm _ _
  -- Push the integer-side divisibility into `ℚ[X]`.
  have hdvdQ :
      (HexPolyZMathlib.toPolynomial
          (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc a))).map cast ∣
        (HexPolyZMathlib.toPolynomial
          (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc b))).map cast := by
    have h := map_dvd (Polynomial.mapRingHom cast) hdvd
    simpa using h
  have hassocA := key a ha_monic
  have hassocB := key b hb_monic
  have heAB :
      (Polynomial.algEquivCMulXAddC (cast lc) (0 : ℚ))
          ((HexPolyZMathlib.toPolynomial a).map cast) ∣
        (Polynomial.algEquivCMulXAddC (cast lc) (0 : ℚ))
          ((HexPolyZMathlib.toPolynomial b).map cast) :=
    (hassocA.symm.dvd).trans (hdvdQ.trans hassocB.dvd)
  -- Reflect through the inverse automorphism.
  have hrefl :
      (HexPolyZMathlib.toPolynomial a).map cast ∣ (HexPolyZMathlib.toPolynomial b).map cast := by
    have h := map_dvd (Polynomial.algEquivCMulXAddC (cast lc) (0 : ℚ)).symm heAB
    simp only [AlgEquiv.symm_apply_apply] at h
    exact h
  exact (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
    (HexPolyZMathlib.toPolynomial a) (HexPolyZMathlib.toPolynomial b)
    hA_prim hB_prim).mpr hrefl

set_option maxHeartbeats 400000 in
/-- **Non-circular lifted recovery-candidate support containment.** For
`d := toMonicLiftData core B primeData` on a non-monic `core` with positive
leading coefficient and a prime selected by the monic transform, if an integer
factor `f` represented by the lifted subset `S` divides the recovered
recombination candidate over `T`, then `S ⊆ T`.

The route: exact recovery (`candidate_eq_of_monic_dvd`) identifies `f` with the
recovery candidate over `S`, so the candidate over `S` divides that over `T`;
the recovery-dilation reflection (`toPolynomial_dvd_of_primitivePart_dilate_dvd`)
and the centred-lift congruence move this to a mod-`p` divisibility of the
selected lifted-factor products; and the clean half
(`toMonicLiftData_subset_of_liftedFactorProduct_map_dvd`) concludes `S ⊆ T`.
Non-circular: it assumes no `LiftedFactorSubsetPartition`. -/
theorem toMonicLiftData_subset_of_dvd_liftedRecoveryCandidate
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    {f : Hex.ZPoly}
    {S T : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData)}
    (hfsign : Hex.normalizeFactorSign f = f)
    (hrep :
      RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) f S)
    (hdvd :
      f ∣ liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) T) :
    S ⊆ T := by
  classical
  set lc := Hex.DensePoly.leadingCoeff core with hlc_def
  set pk := (Hex.ZPoly.toMonicLiftData core B primeData).p ^
      (Hex.ZPoly.toMonicLiftData core B primeData).k with hpk
  have hlc_ne : lc ≠ 0 := ne_of_gt hcore_lc_pos
  -- Modulus facts (proved through the structure projections, not by whnf).
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k =
      Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_k _ _ _
  have hp2 : 2 ≤ primeData.p := hval.prime.two_le
  have hprec_ne : Hex.precisionForCoeffBound B primeData.p ≠ 0 := by omega
  have hpk_eq : pk = primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by
    rw [hpk, hp_eq, hk_eq]
  have hmod2 : 2 ≤ pk := by
    rw [hpk_eq]
    calc 2 ≤ primeData.p := hp2
      _ ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
          le_self_pow (by omega) hprec_ne
  have hp_dvd : primeData.p ∣ pk := by
    rw [hpk_eq]; exact dvd_pow_self primeData.p hprec_ne
  -- Exact recovery: the recovery candidate over `S` is `f`.
  have hmonic_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 := by
    intro h
    have hlcm : Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic = 1 :=
      Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
    rw [h, Hex.DensePoly.leadingCoeff_zero] at hlcm
    exact one_ne_zero hlcm.symm
  have hprec_dk :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hbound
  rcases hrep with ⟨hrec⟩
  have hrecS :
      liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S = f :=
    hrec.candidate_eq_of_monic_dvd hmonic_ne hfsign hprec_dk
  have hcand_dvd :
      liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S ∣
        liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) T := by
    rw [hrecS]; exact hdvd
  -- Lifted-factor products and their centred lifts are monic.
  have hlf_monic :
      ∀ i : Fin (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size,
        Hex.DensePoly.Monic (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData core B primeData
      hcore_lc_pos hcore_pos
      hval hprecision
  have hP_monic :
      ∀ U : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData),
        Hex.DensePoly.Monic (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) U) :=
    fun U => liftedFactorProduct_monic _ U (fun i _ => hlf_monic i)
  have hcl_monic :
      ∀ U : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData),
        Hex.DensePoly.Monic
          (Hex.centeredLiftPoly
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) U) pk) :=
    fun U => monic_centeredLiftPoly_of_monic (hP_monic U) hmod2
  -- Strip sign normalisation to a divisibility of the dilated primitive parts.
  have hcand_dvdP :
      HexPolyZMathlib.toPolynomial
          (liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S) ∣
        HexPolyZMathlib.toPolynomial
          (liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) T) :=
    HexPolyMathlib.toPolynomial_dvd hcand_dvd
  have hppST :
      HexPolyZMathlib.toPolynomial
          (Hex.ZPoly.primitivePart
            (Hex.ZPoly.dilate lc
              (Hex.centeredLiftPoly
                (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) S) pk))) ∣
        HexPolyZMathlib.toPolynomial
          (Hex.ZPoly.primitivePart
            (Hex.ZPoly.dilate lc
              (Hex.centeredLiftPoly
                (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) T) pk))) := by
    have hassS :=
      toPolynomial_normalizeFactorSign_associated
        (Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate lc
            (Hex.centeredLiftPoly
              (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) S) pk)))
    have hassT :=
      toPolynomial_normalizeFactorSign_associated
        (Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate lc
            (Hex.centeredLiftPoly
              (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) T) pk)))
    exact (hassS.symm.dvd).trans (hcand_dvdP.trans hassT.dvd)
  -- Reflect through the dilation: the centred lifts divide over `ℤ`.
  have hclST :
      HexPolyZMathlib.toPolynomial
          (Hex.centeredLiftPoly
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) S) pk) ∣
        HexPolyZMathlib.toPolynomial
          (Hex.centeredLiftPoly
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) T) pk) :=
    toPolynomial_dvd_of_primitivePart_dilate_dvd hlc_ne (hcl_monic S) (hcl_monic T) hppST
  -- Map to `ZMod primeData.p` and rewrite centred lifts to the lifted-factor products.
  have hclST_map :
      (HexPolyZMathlib.toPolynomial
          (Hex.centeredLiftPoly
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) S) pk)).map
          (Int.castRingHom (ZMod primeData.p)) ∣
        (HexPolyZMathlib.toPolynomial
          (Hex.centeredLiftPoly
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) T) pk)).map
          (Int.castRingHom (ZMod primeData.p)) := by
    have h := map_dvd (Polynomial.mapRingHom (Int.castRingHom (ZMod primeData.p))) hclST
    simpa using h
  have hmapcl :
      ∀ U : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData),
        (HexPolyZMathlib.toPolynomial
            (Hex.centeredLiftPoly
              (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) U) pk)).map
            (Int.castRingHom (ZMod primeData.p)) =
          (HexPolyZMathlib.toPolynomial
            (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) U)).map
            (Int.castRingHom (ZMod primeData.p)) := by
    intro U
    exact HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ _
      (Hex.ZPoly.congr_of_dvd_modulus _ _ hp_dvd
        (congr_centeredLiftPoly
          (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) U) pk))
  rw [hmapcl S, hmapcl T] at hclST_map
  -- Clean half.
  exact toMonicLiftData_subset_of_liftedFactorProduct_map_dvd core B primeData
    hcore_lc_pos hcore_pos
      hval hprecision hclST_map

/-- **Non-circular recovered-candidate equality.** For
`d := toMonicLiftData core B primeData` on a non-monic `core` with positive
leading coefficient and a prime selected by the monic transform, a sign-
normalised integer factor `f` represented by the lifted subset `S` is exactly
the recovered recombination candidate over `S`.

This is the recovery half of
`toMonicLiftData_subset_of_dvd_liftedRecoveryCandidate`, exposed as a standalone
identity through `RecoveredAtLift.candidate_eq_of_monic_dvd`.  Non-circular: it
assumes no `LiftedFactorSubsetPartition`. -/
theorem toMonicLiftData_liftedRecoveryCandidate_eq
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (_hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    {f : Hex.ZPoly}
    {S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData)}
    (hfsign : Hex.normalizeFactorSign f = f)
    (hrep :
      RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) f S) :
    liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S = f := by
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k =
      Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_k _ _ _
  have hmonic_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 := by
    intro h
    have hlcm : Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic = 1 :=
      Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
    rw [h, Hex.DensePoly.leadingCoeff_zero] at hlcm
    exact one_ne_zero hlcm.symm
  have hprec_dk :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hbound
  rcases hrep with ⟨hrec⟩
  exact hrec.candidate_eq_of_monic_dvd hmonic_ne hfsign hprec_dk

/--
Lifted-subset uniqueness at `toMonicLiftData`: two lifted-factor subsets that
both represent the same irreducible integer factor of `core` coincide.  This is
the `unique_subset` field of `HenselSubsetCorrespondenceHypotheses` at
`d := toMonicLiftData core B primeData`.

It is a thin mutual-inclusion wrapper over the non-circular product-divisor
lemma `toMonicLiftData_subset_of_dvd_liftedRecoveryCandidate`.  Each
representation recovers the factor exactly as its own recovery candidate
(`RecoveredAtLift.candidate_eq_of_monic_dvd`), so `factor` divides the other
subset's candidate and the product-divisor lemma yields mutual inclusion.  The
sign-normalisation `normalizeFactorSign factor = factor` that both helpers need
is not assumed: it is discharged from the representation itself via
`normalizeFactorSign_eq_of_representsAtLift` (the recovered monic witness is the
monic centred lift of a monic lifted-factor product, so the positive-leading
dilation makes `factor` positively led).
-/
theorem toMonicLiftData_unique_subset
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    {factor : Hex.ZPoly}
    {S T : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData)}
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (_hdvd : factor ∣ core)
    (hS :
      RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) factor S)
    (hT :
      RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) factor T) :
    S = T := by
  classical
  -- `(toMonic core).monic` is monic, hence nonzero.
  have hmonic_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 := by
    intro h
    have hlcm : Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic = 1 :=
      Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
    rw [h, Hex.DensePoly.leadingCoeff_zero] at hlcm
    exact one_ne_zero hlcm.symm
  -- Transport the precision bound onto the lift-data modulus `d.p ^ d.k`.
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k =
      Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_k _ _ _
  have hprec_dk :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hbound
  -- The lifted local factors are monic (good prime data).
  have hlf_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData core B primeData
      hcore_lc_pos hcore_pos
      hval hprecision
  -- The represented factor is sign-normalised (recovered monic witness ⇒ positive lead).
  have hfsign : Hex.normalizeFactorSign factor = factor :=
    normalizeFactorSign_eq_of_representsAtLift hS hcore_lc_pos hmonic_ne hlf_monic hprec_dk
  -- Each representation recovers the factor exactly as its own candidate.
  rcases hS with ⟨hrecS⟩
  rcases hT with ⟨hrecT⟩
  have hcandS :
      liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S = factor :=
    hrecS.candidate_eq_of_monic_dvd hmonic_ne hfsign hprec_dk
  have hcandT :
      liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) T = factor :=
    hrecT.candidate_eq_of_monic_dvd hmonic_ne hfsign hprec_dk
  have hdvdT :
      factor ∣ liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) T := by
    rw [hcandT]; exact Hex.DensePoly.dvd_refl_poly factor
  have hdvdS :
      factor ∣ liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S := by
    rw [hcandS]; exact Hex.DensePoly.dvd_refl_poly factor
  have hST : S ⊆ T :=
    toMonicLiftData_subset_of_dvd_liftedRecoveryCandidate core B primeData
      hcore_lc_pos hcore_pos
      hval hprecision hbound hfsign
      (RepresentsIntegerFactorAtLift.ofRecovered hrecS) hdvdT
  have hTS : T ⊆ S :=
    toMonicLiftData_subset_of_dvd_liftedRecoveryCandidate core B primeData
      hcore_lc_pos hcore_pos
      hval hprecision hbound hfsign
      (RepresentsIntegerFactorAtLift.ofRecovered hrecT) hdvdS
  exact Finset.Subset.antisymm hST hTS

/-- An irreducible integer divisor of a primitive polynomial has positive
executable degree. A degree-zero divisor is a constant, and primitivity of the
target forces that constant to be a unit, contradicting irreducibility. -/
private theorem one_le_degree_getD_of_irreducible_dvd_primitive
    {core factor : Hex.ZPoly}
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    1 ≤ factor.degree?.getD 0 := by
  have hnd :
      (HexPolyZMathlib.toPolynomial factor).natDegree =
        factor.degree?.getD 0 :=
    HexPolyMathlib.natDegree_toPolynomial factor
  rw [← hnd]
  rcases Nat.eq_zero_or_pos
      (HexPolyZMathlib.toPolynomial factor).natDegree with hzero | hpos
  · exfalso
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hzero
    have hdvd_poly :
        HexPolyZMathlib.toPolynomial factor ∣
          HexPolyZMathlib.toPolynomial core :=
      HexPolyMathlib.toPolynomial_dvd hdvd
    have hcore_poly_prim :
        (HexPolyZMathlib.toPolynomial core).IsPrimitive :=
      toPolynomial_isPrimitive_of_zpoly_primitive_basic hcore_prim
    have hCa_dvd : Polynomial.C a ∣ HexPolyZMathlib.toPolynomial core := by
      rw [ha]
      exact hdvd_poly
    have ha_unit : IsUnit a := hcore_poly_prim a hCa_dvd
    exact hirr.not_isUnit (by
      rw [← ha]
      exact Polynomial.isUnit_C.mpr ha_unit)
  · exact hpos

/--
Successful-descent sibling of the `toMonicPrimeData?` Hensel subset
correspondence surface.

The reverse descent input is the monic-correspondent carrier:
`primeData` was selected for `(Hex.ZPoly.toMonic core).monic`, so existence
of lifted representatives is produced by transporting each sign-normalized
irreducible divisor through its monic correspondent. The primitive and
positive-degree side conditions required by that producer come from the
primitive positive-degree core and Gauss. Uniqueness is discharged by the
non-circular `toMonicLiftData_unique_subset` theorem.
-/
theorem henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData_success_descent
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hdescent :
      MonicDescentHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (hB_ne_zero : B ≠ 0) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetCorrespondenceHypotheses core B primeData d True True := by
  intro d
  have hcore0 : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hdeg : 1 ≤ (Hex.ZPoly.toMonic core).degree := hcore_pos
  refine
    { lift_eq := hdescent.lift_eq
      admissible_prime := trivial
      successful_lift := hdescent.successful_lift
      exists_subset := ?_
      unique_subset := ?_ }
  · intro factor hsign hirr hdvd
    have hprim : Hex.ZPoly.Primitive factor :=
      zpoly_primitive_of_dvd_primitive_basic hcore_prim hdvd
    have hfdeg : 1 ≤ factor.degree?.getD 0 :=
      one_le_degree_getD_of_irreducible_dvd_primitive hcore_prim hirr hdvd
    exact toMonicLiftData_represents_lifted_of_modP core B primeData
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos)
      hcore0 hcore_lc_pos hdeg hB_ne_zero hirr hprim hsign hfdeg hdvd
  · intro factor S T hirr hdvd hS hT
    exact toMonicLiftData_unique_subset core B primeData
      hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprecision hbound hirr hdvd hS hT

/--
Carrier-free `toMonicPrimeData?` Hensel subset correspondence surface.

Same conclusion as
`henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData_success_descent`, but
without the `MonicDescentHypotheses` carrier: at the `True True` instantiation the
only descent fields that constructor consumed (`lift_eq`, `successful_lift`) are
`rfl`/`trivial`, and the existence/uniqueness fields come directly from the core
facts via `toMonicLiftData_represents_lifted_of_modP` and
`toMonicLiftData_unique_subset`.  This is the core-facts producer that the
partition and slow-path substrate packages route through. -/
theorem henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (hB_ne_zero : B ≠ 0) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetCorrespondenceHypotheses core B primeData d True True := by
  intro d
  have hcore0 : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hdeg : 1 ≤ (Hex.ZPoly.toMonic core).degree := hcore_pos
  refine
    { lift_eq := rfl
      admissible_prime := trivial
      successful_lift := trivial
      exists_subset := ?_
      unique_subset := ?_ }
  · intro factor hsign hirr hdvd
    have hprim : Hex.ZPoly.Primitive factor :=
      zpoly_primitive_of_dvd_primitive_basic hcore_prim hdvd
    have hfdeg : 1 ≤ factor.degree?.getD 0 :=
      one_le_degree_getD_of_irreducible_dvd_primitive hcore_prim hirr hdvd
    exact toMonicLiftData_represents_lifted_of_modP core B primeData
      hval hcore0 hcore_lc_pos hdeg hB_ne_zero hirr hprim hsign hfdeg hdvd
  · intro factor S T hirr hdvd hS hT
    exact toMonicLiftData_unique_subset core B primeData
      hcore_lc_pos hcore_pos
      hval hprecision hbound hirr hdvd hS hT

/-- Initial lifted subset partition for `toMonicPrimeData?` success.

This composes the core-fact correspondence producer
`henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData_success_descent` with
the existing partition constructor. The recovered-coordinate partition fields
come from `InitialLiftedFactorSubsetPartitionEvidence`; the monic-only unscaled
field is derived from recovered support under its side condition. -/
theorem liftedFactorSubsetPartition_of_toMonicPrimeData_success_descent
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hdescent :
      MonicDescentHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (hB_ne_zero : B ≠ 0)
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    LiftedFactorSubsetPartition core d Finset.univ core := by
  intro d
  exact liftedFactorSubsetPartition_of_toMonicPrimeData
    core B primeData
    (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos)
    (henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData_success_descent
      core B primeData hselected hdescent hcore_lc_pos hcore_pos hcore_prim
      hprecision hbound hB_ne_zero)
    hcore_sqfree hinitial

/-- **#6682 supporting lemma (HO-1 slow-path substrate constructor).**

Successful-descent variant of
`slowPathHenselSubstrate_of_toMonicChoosePrimeData`.  The `corr` field is
sourced from the non-circular `toMonicPrimeData?` correspondence constructor
above, using the monic-correspondent reverse descent carrier.  The partition
field uses the narrowed `liftedFactorSubsetPartition` wrapper with that same
correspondence; recovered partition evidence is supplied by
`InitialLiftedFactorSubsetPartitionEvidence`.
-/
theorem slowPathHenselSubstrate_of_toMonicChoosePrimeData_success_descent
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_ne_zero : B ≠ 0)
    (hdescent :
      MonicDescentHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    SlowPathHenselSubstrate core B primeData := by
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hprec_spec :
      2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne_zero
  have hmodulus :
      2 ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by
    omega
  have hprec_pos : 1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    by_contra hlt
    have hzero : Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hmodulus
    omega
  refine
    { corr := ?_
      partition := ?_
      liftedFactor_monic := ?_
      liftedFactor_natDegree_pos := ?_
      liftedFactor_inj := ?_
      modulus := ?_
      precision := ?_ }
  · exact henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData_success_descent
      core B primeData hselected hdescent hcore_lc_pos hcore_pos hcore_prim
      hprec_pos hbound hB_ne_zero
  · exact liftedFactorSubsetPartition_of_toMonicPrimeData_success_descent
      core B primeData hselected hdescent hcore_lc_pos hcore_pos hcore_prim
      hcore_sqfree hprec_pos hbound hB_ne_zero hinitial
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact hmodulus
  · exact hprec_spec

end HexBerlekampZassenhausMathlib
