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

public import HexBerlekampZassenhausMathlib.SubsetCoprimality
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.SubsetCoprimality

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects the forward Hensel transport for the canonical lifted subset.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-! ### Forward Hensel transport for the canonical lifted subset

The next theorem closes the forward `represents_lifted_of_modP` direction of
`HenselSubsetLiftHypotheses`: if `factor` is a monic integer divisor of `core`
that is represented modulo `primeData.p` by the modular-factor subset `S`,
then the canonical Hensel lift `liftedSubsetOfModPSubset` of `S` represents
`factor` modulo `primeData.p ^ B` on the integer side. The proof feeds the
packaged subset/complement product (`#4752`) and coprimality (`#4761`) inputs
into `HexHenselMathlib.hensel_unique` and converts the resulting Mathlib
`Polynomial.map` equality back to the executable `Hex.ZPoly.reduceModPow`
equality stored by `RepresentsIntegerFactorAtLift`. -/

/-- Monic integer polynomials reduce to non-`isZero` `FpPoly` images modulo
any prime `p > 1`: the leading coefficient `1` survives reduction, so the
stored size is preserved. -/
private theorem modP_isZero_false_of_monic
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    {f : Hex.ZPoly} (hf_monic : Hex.DensePoly.Monic f) (hp : 1 < p) :
    (Hex.ZPoly.modP p f).isZero = false := by
  have hf_size_pos : 0 < f.size := zpoly_size_pos_of_monic hf_monic
  have hf_lead : f.coeff (f.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last f hf_size_pos]
    exact hf_monic
  have hmod1 : 1 % p = 1 := Nat.mod_eq_of_lt hp
  have htoNat_one : (1 : Hex.ZMod64 p).toNat = 1 := by
    show Hex.ZMod64.one.toNat = 1
    rw [Hex.ZMod64.toNat_one, hmod1]
  have hone_ne_zero : (1 : Hex.ZMod64 p) ≠ (0 : Hex.ZMod64 p) := by
    intro h
    have hnat := congrArg Hex.ZMod64.toNat h
    rw [htoNat_one, show (0 : Hex.ZMod64 p) = Hex.ZMod64.zero from rfl,
        Hex.ZMod64.toNat_zero] at hnat
    exact absurd hnat (by decide)
  have hmodP_coeff_lead :
      (Hex.ZPoly.modP p f).coeff (f.size - 1) = (1 : Hex.ZMod64 p) := by
    rw [Hex.ZPoly.coeff_modP, hf_lead]
    have hintModNat : Hex.ZPoly.intModNat (1 : Int) p = 1 := by
      show Int.toNat ((1 : Int) % Int.ofNat p) = 1
      have hppos : (1 : Int) < Int.ofNat p := Int.ofNat_lt.mpr hp
      rw [Int.emod_eq_of_lt (by decide) hppos]
      rfl
    rw [hintModNat]
    rfl
  have hmodP_size_pos : 0 < (Hex.ZPoly.modP p f).size := by
    rcases Nat.eq_zero_or_pos (Hex.ZPoly.modP p f).size with hsz | hsz
    · exfalso
      have hcoeff_zero :
          (Hex.ZPoly.modP p f).coeff (f.size - 1) = 0 := by
        apply Hex.DensePoly.coeff_eq_zero_of_size_le
        omega
      rw [hcoeff_zero] at hmodP_coeff_lead
      exact hone_ne_zero hmodP_coeff_lead.symm
    · exact hsz
  exact (Hex.DensePoly.isZero_eq_false_iff _).mpr hmodP_size_pos

/-- `monicModPImage` is the identity on the mod-`p` reduction of a monic
integer polynomial, since the leading coefficient `1` reduces to `1` and
`(1 : ZMod64 p)⁻¹ = 1`. -/
private theorem monicModPImage_modP_eq_self_of_monic
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    {f : Hex.ZPoly} (hf_monic : Hex.DensePoly.Monic f)
    (hprime : Hex.Nat.Prime p) (hp : 1 < p) :
    monicModPImage (Hex.ZPoly.modP p f) = Hex.ZPoly.modP p f := by
  rw [monicModPImage_eq_monicModularImage]
  exact monicModularImage_modP_eq_of_monic f hf_monic hprime hp
    (modP_isZero_false_of_monic hf_monic hp)

/-- Forward Hensel-lift transport for the canonical lifted subset: a monic
integer factor of `core` that is represented modulo `primeData.p` by a
modular-factor subset `S` is represented modulo `primeData.p ^ B` on the
integer side by the corresponding canonical lifted subset
`liftedSubsetOfModPSubset primeData d hsize S`.

The proof packages the subset/complement product modulo `p ^ B`
(`henselLiftData_liftedFactorProduct_subset_complement_congr_core`) and the
subset/complement coprimality modulo `p`
(`henselLiftData_liftedSubset_complement_isCoprime_mod_p`) into the
hypothesis list of `HexHenselMathlib.hensel_unique`, alongside the integer
factorization `core = factor * q` derived from `factor ∣ core` and the
mod-`p` subset representation hypothesis. Converting the resulting Mathlib
`Polynomial.map` equality back to the executable
`Hex.ZPoly.reduceModPow` form via
`HexHenselMathlib.zpoly_congr_of_toPolynomial_map_eq` and
`Hex.ZPoly.reduceModPow_eq_of_congr` discharges
`RepresentsIntegerFactorAtLift`.

This is the forward `represents_lifted_of_modP` field of
`HenselSubsetLiftHypotheses` (#4733 for parent #4695); the analytic
hypotheses listed here are the inputs that the constructor successor #4697
will package from `Hex.choosePrimeData`/`Hex.henselLiftData` boundary
facts. -/
theorem henselLiftData_represents_lifted_of_modP
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime : _root_.Nat.Prime primeData.p)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hfactors_irr :
      letI := primeData.bounds
      ∀ i : ModPFactorIndex primeData,
        Irreducible
          (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)))
    (hfactors_nodup : primeData.factorsModP.toList.Nodup)
    {factor : Hex.ZPoly} {S : ModPFactorSubset primeData}
    (hfactor_monic : Hex.DensePoly.Monic factor)
    (_hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd : factor ∣ core)
    (hrepP : RepresentsIntegerFactorModP primeData factor S) :
    letI := primeData.bounds
    RepresentsIntegerFactorAtLift core (Hex.henselLiftData core B primeData) factor
      (liftedSubsetOfModPSubset primeData (Hex.henselLiftData core B primeData)
        (henselLiftData_liftedFactors_size_eq core B primeData) S) := by
  letI := primeData.bounds
  haveI hprime_fact : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime⟩
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime
      (by
        constructor
        · exact hprime.two_le
        · intro m hmdvd
          rcases hprime.eq_one_or_self_of_dvd m hmdvd with h | h
          · exact Or.inl h
          · exact Or.inr h)
  have hp : 1 < primeData.p := hprime.one_lt
  have hprime_hex : Hex.Nat.Prime primeData.p := by
    constructor
    · exact hprime.two_le
    · intro m hmdvd
      rcases hprime.eq_one_or_self_of_dvd m hmdvd with h | h
      · exact Or.inl h
      · exact Or.inr h
  obtain ⟨q, hcoreq⟩ := hfactor_dvd
  -- Mathlib aliases for the Hensel-unique inputs.
  set d := Hex.henselLiftData core B primeData with hd_def
  set hsize := henselLiftData_liftedFactors_size_eq core B primeData with hsize_def
  set liftedS := liftedSubsetOfModPSubset primeData d hsize S with hliftedS_def
  set complementS : LiftedFactorSubset d := (Finset.univ : LiftedFactorSubset d) \ liftedS
    with hcomplementS_def
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  set g := HexPolyZMathlib.toPolynomial (liftedFactorProduct d liftedS) with hg_def
  set h := HexPolyZMathlib.toPolynomial (liftedFactorProduct d complementS) with hh_def
  set g' := HexPolyZMathlib.toPolynomial factor with hg'_def
  set h' := HexPolyZMathlib.toPolynomial q with hh'_def
  -- Monicness.
  have hg_dense_monic : Hex.DensePoly.Monic (liftedFactorProduct d liftedS) :=
    henselLiftData_liftedFactorProduct_monic core B primeData
      hcore_monic hprime_invariant hp hB liftedS
  have hg_monic : g.Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hg_dense_monic
  have hg'_monic : g'.Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hfactor_monic
  -- Subset/complement product modulo `p ^ B` on the lifted side.
  have hgh_congr :
      Hex.ZPoly.congr
        (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)
        core (primeData.p ^ B) :=
    henselLiftData_liftedFactorProduct_subset_complement_congr_core
      core B primeData hprime_invariant hp hB liftedS
  have hgh_map_pB :
      (HexPolyZMathlib.toPolynomial
          (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)).map
          (Int.castRingHom (ZMod (primeData.p ^ B))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ _ hgh_congr
  have hprod :
      (g.map (Int.castRingHom (ZMod (primeData.p ^ B)))) *
          (h.map (Int.castRingHom (ZMod (primeData.p ^ B)))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) := by
    have hmul := hgh_map_pB
    rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul] at hmul
    exact hmul
  -- Integer-side product (`core = factor * q`).
  have hf_eq : f = g' * h' := by
    rw [hf_def, hg'_def, hh'_def, hcoreq, HexPolyZMathlib.toPolynomial_mul]
  have hprod' :
      (g'.map (Int.castRingHom (ZMod (primeData.p ^ B)))) *
          (h'.map (Int.castRingHom (ZMod (primeData.p ^ B)))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) := by
    rw [hf_eq, Polynomial.map_mul]
  -- Identify `RepresentsIntegerFactorModP` with the Mathlib mod-`p` map equality.
  have hg1 :
      g.map (Int.castRingHom (ZMod primeData.p)) =
        g'.map (Int.castRingHom (ZMod primeData.p)) := by
    have h1 :=
      toPolynomial_liftedSubset_map_intCast_zmod_eq_toMathlibPolynomial
        core B primeData hcore_monic hprime_invariant hp hB
        hfactors_monic hproduct_mod_p S
    have h2 : modPFactorProduct primeData S =
        monicModPImage (Hex.ZPoly.modP primeData.p factor) := hrepP
    have h3 := monicModPImage_modP_eq_self_of_monic
      (f := factor) hfactor_monic hprime_hex hp
    have h4 := toMathlibPolynomial_modP_eq_map_intCast_zmod (p := primeData.p) factor
    show (HexPolyZMathlib.toPolynomial (liftedFactorProduct d liftedS)).map
          (Int.castRingHom (ZMod primeData.p)) =
        (HexPolyZMathlib.toPolynomial factor).map (Int.castRingHom (ZMod primeData.p))
    rw [show liftedS = liftedSubsetOfModPSubset primeData d hsize S from rfl,
      h1, h2, h3, h4]
  -- Derive `hdeg` from `hg1` and monicness via `Monic.natDegree_map`.
  haveI : Nontrivial (ZMod primeData.p) := inferInstance
  have hdeg : g.natDegree = g'.natDegree := by
    have hg_map_natDeg :
        (g.map (Int.castRingHom (ZMod primeData.p))).natDegree = g.natDegree :=
      hg_monic.natDegree_map (Int.castRingHom (ZMod primeData.p))
    have hg'_map_natDeg :
        (g'.map (Int.castRingHom (ZMod primeData.p))).natDegree = g'.natDegree :=
      hg'_monic.natDegree_map (Int.castRingHom (ZMod primeData.p))
    rw [← hg_map_natDeg, ← hg'_map_natDeg, hg1]
  -- Mod-`p` map equality on the complement, via cancellation in `Polynomial (ZMod p)`.
  have hp_dvd_pB : primeData.p ∣ primeData.p ^ B := by
    have h := Nat.pow_dvd_pow primeData.p hB
    simpa using h
  have hgh_congr_p :
      Hex.ZPoly.congr
        (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)
        core primeData.p :=
    Hex.ZPoly.congr_of_dvd_modulus _ _ hp_dvd_pB hgh_congr
  have hgh_map_p :
      (HexPolyZMathlib.toPolynomial
          (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)).map
          (Int.castRingHom (ZMod primeData.p)) =
        f.map (Int.castRingHom (ZMod primeData.p)) :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ _ hgh_congr_p
  have hprod_p :
      (g.map (Int.castRingHom (ZMod primeData.p))) *
          (h.map (Int.castRingHom (ZMod primeData.p))) =
        f.map (Int.castRingHom (ZMod primeData.p)) := by
    have hmul := hgh_map_p
    rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul] at hmul
    exact hmul
  have hprod'_p :
      (g'.map (Int.castRingHom (ZMod primeData.p))) *
          (h'.map (Int.castRingHom (ZMod primeData.p))) =
        f.map (Int.castRingHom (ZMod primeData.p)) := by
    rw [hf_eq, Polynomial.map_mul]
  have hg_map_p_monic : (g.map (Int.castRingHom (ZMod primeData.p))).Monic :=
    hg_monic.map _
  have hg'_map_p_monic : (g'.map (Int.castRingHom (ZMod primeData.p))).Monic :=
    hg'_monic.map _
  have hg'_map_p_ne_zero : g'.map (Int.castRingHom (ZMod primeData.p)) ≠ 0 :=
    hg'_map_p_monic.ne_zero
  have hh1 :
      h.map (Int.castRingHom (ZMod primeData.p)) =
        h'.map (Int.castRingHom (ZMod primeData.p)) := by
    have hsame :
        (g'.map (Int.castRingHom (ZMod primeData.p))) *
            (h.map (Int.castRingHom (ZMod primeData.p))) =
          (g'.map (Int.castRingHom (ZMod primeData.p))) *
            (h'.map (Int.castRingHom (ZMod primeData.p))) := by
      calc (g'.map (Int.castRingHom (ZMod primeData.p))) *
              (h.map (Int.castRingHom (ZMod primeData.p)))
          = (g.map (Int.castRingHom (ZMod primeData.p))) *
              (h.map (Int.castRingHom (ZMod primeData.p))) := by rw [hg1]
        _ = f.map (Int.castRingHom (ZMod primeData.p)) := hprod_p
        _ = (g'.map (Int.castRingHom (ZMod primeData.p))) *
              (h'.map (Int.castRingHom (ZMod primeData.p))) := hprod'_p.symm
    exact mul_left_cancel₀ hg'_map_p_ne_zero hsame
  -- Subset/complement coprimality modulo `p` (#4761).
  have hcop :
      IsCoprime (g.map (Int.castRingHom (ZMod primeData.p)))
        (h.map (Int.castRingHom (ZMod primeData.p))) :=
    henselLiftData_liftedSubset_complement_isCoprime_mod_p
      core B primeData hcore_monic hprime hprime_invariant hp hB
      hfactors_monic hproduct_mod_p hfactors_irr hfactors_nodup S
  -- Apply `hensel_unique`.
  obtain ⟨hgg', _⟩ :=
    HexHenselMathlib.hensel_unique f g h g' h' primeData.p B hB
      hg_monic hg'_monic hdeg hprod hprod' hg1 hh1 hcop
  -- Convert back to the recovered-coordinate `RepresentsIntegerFactorAtLift`.
  have hcongr_pk :
      Hex.ZPoly.congr (liftedFactorProduct d liftedS) factor (primeData.p ^ B) :=
    HexHenselMathlib.zpoly_congr_of_toPolynomial_map_eq _ _ _ hgg'
  have hdp : d.p = primeData.p := rfl
  have hdk : d.k = B := rfl
  have hrec_congr :
      Hex.ZPoly.reduceModPow (liftedFactorProduct d liftedS) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k := by
    rw [hdp, hdk]
    exact Hex.ZPoly.reduceModPow_eq_of_congr _ _ _ _ hcongr_pk
  refine RepresentsIntegerFactorAtLift.ofRecovered ?_
  exact
    { monicFactor := factor
      congr := hrec_congr
      dilate_eq := by
        rw [show Hex.DensePoly.leadingCoeff core = (1 : Int) from hcore_monic,
          Hex.ZPoly.dilate_one]
        exact Hex.ZPoly.primitivePart_eq_self_of_primitive factor
          (zpoly_primitive_of_monic hfactor_monic)
      monic_dvd := by
        rw [Hex.ZPoly.toMonic_monic_eq_core_of_leadingCoeff_eq_one core
          (show Hex.DensePoly.leadingCoeff core = (1 : Int) from hcore_monic)]
        exact ⟨q, hcoreq⟩ }

/--
Subset-level Hensel uniqueness in additive congruence form.

This is the proof core behind the recovered-coordinate
`henselLiftData_represents_lifted_of_modP`: if a selected modular subset `S`
represents a monic integer factor `factor` modulo `p`, and `factor * cofactor`
is a second factorisation of the same monic Hensel target modulo `p ^ B`, then
the canonical lifted subset product is congruent to `factor` modulo `p ^ B`.

The statement deliberately returns only the coefficientwise congruence.  This
fits non-recovered coordinates such as the BHKS `monicTarget` M1 target, where
the product comparison is a modular target-coordinate assertion rather than an
integer equality `target = factor * cofactor`.
-/
theorem henselLiftData_liftedSubset_congr_of_modP
    (target : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (htarget_monic : Hex.DensePoly.Monic target)
    (hprime : _root_.Nat.Prime primeData.p)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B target
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        target primeData.p)
    (hfactors_irr :
      letI := primeData.bounds
      ∀ i : ModPFactorIndex primeData,
        Irreducible
          (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)))
    (hfactors_nodup : primeData.factorsModP.toList.Nodup)
    {factor cofactor : Hex.ZPoly} {S : ModPFactorSubset primeData}
    (hfactor_monic : Hex.DensePoly.Monic factor)
    (hfactor_product :
      Hex.ZPoly.congr (factor * cofactor) target (primeData.p ^ B))
    (hrepP : RepresentsIntegerFactorModP primeData factor S) :
    letI := primeData.bounds
    Hex.ZPoly.congr
      (liftedFactorProduct (Hex.henselLiftData target B primeData)
        (liftedSubsetOfModPSubset primeData (Hex.henselLiftData target B primeData)
          (henselLiftData_liftedFactors_size_eq target B primeData) S))
      factor (primeData.p ^ B) := by
  letI := primeData.bounds
  haveI hprime_fact : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime⟩
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime
      (by
        constructor
        · exact hprime.two_le
        · intro m hmdvd
          rcases hprime.eq_one_or_self_of_dvd m hmdvd with h | h
          · exact Or.inl h
          · exact Or.inr h)
  have hp : 1 < primeData.p := hprime.one_lt
  have hprime_hex : Hex.Nat.Prime primeData.p := by
    constructor
    · exact hprime.two_le
    · intro m hmdvd
      rcases hprime.eq_one_or_self_of_dvd m hmdvd with h | h
      · exact Or.inl h
      · exact Or.inr h
  set d := Hex.henselLiftData target B primeData with hd_def
  set hsize := henselLiftData_liftedFactors_size_eq target B primeData with hsize_def
  set liftedS := liftedSubsetOfModPSubset primeData d hsize S with hliftedS_def
  set complementS : LiftedFactorSubset d := (Finset.univ : LiftedFactorSubset d) \ liftedS
    with hcomplementS_def
  set f := HexPolyZMathlib.toPolynomial target with hf_def
  set g := HexPolyZMathlib.toPolynomial (liftedFactorProduct d liftedS) with hg_def
  set h := HexPolyZMathlib.toPolynomial (liftedFactorProduct d complementS) with hh_def
  set g' := HexPolyZMathlib.toPolynomial factor with hg'_def
  set h' := HexPolyZMathlib.toPolynomial cofactor with hh'_def
  have hg_dense_monic : Hex.DensePoly.Monic (liftedFactorProduct d liftedS) :=
    henselLiftData_liftedFactorProduct_monic target B primeData
      htarget_monic hprime_invariant hp hB liftedS
  have hg_monic : g.Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hg_dense_monic
  have hg'_monic : g'.Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hfactor_monic
  have hgh_congr :
      Hex.ZPoly.congr
        (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)
        target (primeData.p ^ B) :=
    henselLiftData_liftedFactorProduct_subset_complement_congr_core
      target B primeData hprime_invariant hp hB liftedS
  have hgh_map_pB :
      (HexPolyZMathlib.toPolynomial
          (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)).map
          (Int.castRingHom (ZMod (primeData.p ^ B))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ _ hgh_congr
  have hprod :
      (g.map (Int.castRingHom (ZMod (primeData.p ^ B)))) *
          (h.map (Int.castRingHom (ZMod (primeData.p ^ B)))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) := by
    have hmul := hgh_map_pB
    rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul] at hmul
    exact hmul
  have hfactor_map_pB :
      (HexPolyZMathlib.toPolynomial (factor * cofactor)).map
          (Int.castRingHom (ZMod (primeData.p ^ B))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ _ hfactor_product
  have hprod' :
      (g'.map (Int.castRingHom (ZMod (primeData.p ^ B)))) *
          (h'.map (Int.castRingHom (ZMod (primeData.p ^ B)))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) := by
    have hmul := hfactor_map_pB
    rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul] at hmul
    exact hmul
  have hg1 :
      g.map (Int.castRingHom (ZMod primeData.p)) =
        g'.map (Int.castRingHom (ZMod primeData.p)) := by
    have h1 :=
      toPolynomial_liftedSubset_map_intCast_zmod_eq_toMathlibPolynomial
        target B primeData htarget_monic hprime_invariant hp hB
        hfactors_monic hproduct_mod_p S
    have h2 : modPFactorProduct primeData S =
        monicModPImage (Hex.ZPoly.modP primeData.p factor) := hrepP
    have h3 := monicModPImage_modP_eq_self_of_monic
      (f := factor) hfactor_monic hprime_hex hp
    have h4 := toMathlibPolynomial_modP_eq_map_intCast_zmod (p := primeData.p) factor
    show (HexPolyZMathlib.toPolynomial (liftedFactorProduct d liftedS)).map
          (Int.castRingHom (ZMod primeData.p)) =
        (HexPolyZMathlib.toPolynomial factor).map (Int.castRingHom (ZMod primeData.p))
    rw [show liftedS = liftedSubsetOfModPSubset primeData d hsize S from rfl,
      h1, h2, h3, h4]
  haveI : Nontrivial (ZMod primeData.p) := inferInstance
  have hdeg : g.natDegree = g'.natDegree := by
    have hg_map_natDeg :
        (g.map (Int.castRingHom (ZMod primeData.p))).natDegree = g.natDegree :=
      hg_monic.natDegree_map (Int.castRingHom (ZMod primeData.p))
    have hg'_map_natDeg :
        (g'.map (Int.castRingHom (ZMod primeData.p))).natDegree = g'.natDegree :=
      hg'_monic.natDegree_map (Int.castRingHom (ZMod primeData.p))
    rw [← hg_map_natDeg, ← hg'_map_natDeg, hg1]
  have hp_dvd_pB : primeData.p ∣ primeData.p ^ B := by
    have h := Nat.pow_dvd_pow primeData.p hB
    simpa using h
  have hgh_congr_p :
      Hex.ZPoly.congr
        (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)
        target primeData.p :=
    Hex.ZPoly.congr_of_dvd_modulus _ _ hp_dvd_pB hgh_congr
  have hgh_map_p :
      (HexPolyZMathlib.toPolynomial
          (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)).map
          (Int.castRingHom (ZMod primeData.p)) =
        f.map (Int.castRingHom (ZMod primeData.p)) :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ _ hgh_congr_p
  have hprod_p :
      (g.map (Int.castRingHom (ZMod primeData.p))) *
          (h.map (Int.castRingHom (ZMod primeData.p))) =
        f.map (Int.castRingHom (ZMod primeData.p)) := by
    have hmul := hgh_map_p
    rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul] at hmul
    exact hmul
  have hfactor_congr_p :
      Hex.ZPoly.congr (factor * cofactor) target primeData.p :=
    Hex.ZPoly.congr_of_dvd_modulus _ _ hp_dvd_pB hfactor_product
  have hfactor_map_p :
      (HexPolyZMathlib.toPolynomial (factor * cofactor)).map
          (Int.castRingHom (ZMod primeData.p)) =
        f.map (Int.castRingHom (ZMod primeData.p)) :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ _ hfactor_congr_p
  have hprod'_p :
      (g'.map (Int.castRingHom (ZMod primeData.p))) *
          (h'.map (Int.castRingHom (ZMod primeData.p))) =
        f.map (Int.castRingHom (ZMod primeData.p)) := by
    have hmul := hfactor_map_p
    rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul] at hmul
    exact hmul
  have hg'_map_p_monic : (g'.map (Int.castRingHom (ZMod primeData.p))).Monic :=
    hg'_monic.map _
  have hg'_map_p_ne_zero : g'.map (Int.castRingHom (ZMod primeData.p)) ≠ 0 :=
    hg'_map_p_monic.ne_zero
  have hh1 :
      h.map (Int.castRingHom (ZMod primeData.p)) =
        h'.map (Int.castRingHom (ZMod primeData.p)) := by
    have hsame :
        (g'.map (Int.castRingHom (ZMod primeData.p))) *
            (h.map (Int.castRingHom (ZMod primeData.p))) =
          (g'.map (Int.castRingHom (ZMod primeData.p))) *
            (h'.map (Int.castRingHom (ZMod primeData.p))) := by
      calc (g'.map (Int.castRingHom (ZMod primeData.p))) *
              (h.map (Int.castRingHom (ZMod primeData.p)))
          = (g.map (Int.castRingHom (ZMod primeData.p))) *
              (h.map (Int.castRingHom (ZMod primeData.p))) := by rw [hg1]
        _ = f.map (Int.castRingHom (ZMod primeData.p)) := hprod_p
        _ = (g'.map (Int.castRingHom (ZMod primeData.p))) *
              (h'.map (Int.castRingHom (ZMod primeData.p))) := hprod'_p.symm
    exact mul_left_cancel₀ hg'_map_p_ne_zero hsame
  have hcop :
      IsCoprime (g.map (Int.castRingHom (ZMod primeData.p)))
        (h.map (Int.castRingHom (ZMod primeData.p))) :=
    henselLiftData_liftedSubset_complement_isCoprime_mod_p
      target B primeData htarget_monic hprime hprime_invariant hp hB
      hfactors_monic hproduct_mod_p hfactors_irr hfactors_nodup S
  obtain ⟨hgg', _⟩ :=
    HexHenselMathlib.hensel_unique f g h g' h' primeData.p B hB
      hg_monic hg'_monic hdeg hprod hprod' hg1 hh1 hcop
  exact HexHenselMathlib.zpoly_congr_of_toPolynomial_map_eq _ _ _ hgg'

/--
M1 (`monicTarget`-coordinate) subset Hensel uniqueness for `coreLiftData`.

If the modular subset `S` represents the `monicTarget` coordinate of an integer
factor, and that coordinate participates in a modular factorisation of
`monicTarget core p k`, then the canonical selected product in
`coreLiftData core B primeData` is congruent to `monicTarget factor p k` modulo
the Hensel modulus.  The modular product decomposition is an explicit premise:
it is the scale-coordinate M1 fact to be supplied by callers, not something
derived from the older dilation-coordinate recovery carrier.
-/
theorem coreLiftData_subset_congr_monicTarget
    (core factor : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.choosePrimeData? core = some primeData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_size : 0 < core.size)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hgcd_core : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (primeData.p ^ Hex.precisionForCoeffBound B primeData.p)) = 1)
    (hfactor_size : 0 < factor.size)
    (hgcd_factor : Int.gcd (Hex.DensePoly.leadingCoeff factor)
      (Int.ofNat (primeData.p ^ Hex.precisionForCoeffBound B primeData.p)) = 1)
    {cofactor : Hex.ZPoly} {S : ModPFactorSubset primeData}
    (hfactor_product :
      Hex.ZPoly.congr
        (Hex.ZPoly.monicTarget factor primeData.p
            (Hex.precisionForCoeffBound B primeData.p) * cofactor)
        (Hex.ZPoly.monicTarget core primeData.p
            (Hex.precisionForCoeffBound B primeData.p))
        (primeData.p ^ Hex.precisionForCoeffBound B primeData.p))
    (hrepP : RepresentsIntegerFactorModP primeData
      (Hex.ZPoly.monicTarget factor primeData.p
        (Hex.precisionForCoeffBound B primeData.p)) S) :
    letI := primeData.bounds
    Hex.ZPoly.congr
      (liftedFactorProduct (Hex.ZPoly.coreLiftData core B primeData)
        (liftedSubsetOfModPSubset primeData (Hex.ZPoly.coreLiftData core B primeData)
          (henselLiftData_liftedFactors_size_eq
            (Hex.ZPoly.monicTarget core primeData.p
              (Hex.precisionForCoeffBound B primeData.p))
            (Hex.precisionForCoeffBound B primeData.p) primeData) S))
      (Hex.ZPoly.monicTarget factor primeData.p
        (Hex.precisionForCoeffBound B primeData.p))
      ((Hex.ZPoly.coreLiftData core B primeData).p ^
        (Hex.ZPoly.coreLiftData core B primeData).k) := by
  letI := primeData.bounds
  set precision := Hex.precisionForCoeffBound B primeData.p with hprecision_def
  set target := Hex.ZPoly.monicTarget core primeData.p precision with htarget_def
  set monicFactor := Hex.ZPoly.monicTarget factor primeData.p precision with hfactor_def
  have hp_prime_hex : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hselected
  have hp_prime : _root_.Nat.Prime primeData.p :=
    natPrime_of_hexNatPrime hp_prime_hex
  have hp : 1 < primeData.p := hp_prime_hex.one_lt
  have hpk : 1 < primeData.p ^ precision :=
    Nat.one_lt_pow (by omega) hp
  have htarget_monic : Hex.DensePoly.Monic target := by
    rw [htarget_def]
    exact Hex.ZPoly.monicTarget_monic core primeData.p precision hpk
      (by simpa [hprecision_def] using hgcd_core) hcore_size
  have hfactor_monic : Hex.DensePoly.Monic monicFactor := by
    rw [hfactor_def]
    exact Hex.ZPoly.monicTarget_monic factor primeData.p precision hpk
      (by simpa [hprecision_def] using hgcd_factor) hfactor_size
  obtain ⟨hzeroP, heqP⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hselected
  have hform : Hex.factorsModPBerlekampForm core primeData :=
    ⟨hp_prime_hex, hzeroP, heqP⟩
  have hgood : Hex.isGoodPrime core primeData.p = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hselected
  have hfactors_monic :
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g :=
    factorsModP_monic_of_factorsModPBerlekampForm core primeData hform
  have hproduct_mod_p :
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        target primeData.p := by
    rw [htarget_def]
    exact factorsModP_polyProduct_congr_monicTarget core precision primeData hpk
      (by omega) (by simpa [hprecision_def] using hgcd_core) hform hgood
  have hcoprime :
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList :=
    factorsModP_coprime_of_factorsModPBerlekampForm core primeData hform hgood
  have hnonempty : primeData.factorsModP.toList ≠ [] :=
    factorsModP_ne_nil_of_factorsModPBerlekampForm core primeData hform
  have hinv :
      Hex.ZPoly.QuadraticMultifactorLiftInvariant primeData.p precision target
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList :=
    Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      target precision primeData hp_prime_hex hp
      (by simpa [hprecision_def] using hprecision)
      htarget_monic hfactors_monic hproduct_mod_p hcoprime hnonempty
  have hfactors_irr :
      ∀ i : ModPFactorIndex primeData,
        Irreducible
          (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)) :=
    factors_irreducible_of_factorsModPBerlekampForm
      core primeData hform hgood hcore_pos
  have hfactors_nodup : primeData.factorsModP.toList.Nodup :=
    factorsModP_nodup_of_factorsModPBerlekampForm core primeData hform hgood
  have hproduct : Hex.ZPoly.congr (monicFactor * cofactor) target
      (primeData.p ^ precision) := by
    simpa [hfactor_def, htarget_def, hprecision_def] using hfactor_product
  have hrepP' : RepresentsIntegerFactorModP primeData monicFactor S := by
    simpa [hfactor_def, hprecision_def] using hrepP
  have hcongr :=
    henselLiftData_liftedSubset_congr_of_modP target precision primeData
      htarget_monic hp_prime hinv (by simpa [hprecision_def] using hprecision)
      hfactors_monic hproduct_mod_p hfactors_irr hfactors_nodup
      hfactor_monic hproduct hrepP'
  simpa [Hex.ZPoly.coreLiftData, htarget_def, hfactor_def, hprecision_def] using hcongr

/-- **#7453.**

Monic-coordinate forward Hensel-lift transport for `toMonicLiftData`
correspondents.

For `M := (Hex.ZPoly.toMonic core).monic`, this instantiates
`henselLiftData_represents_lifted_of_modP` at Hensel precision
`Hex.precisionForCoeffBound B primeData.p`, discharging the analytic inputs
from the `toMonicPrimeData?` / `factorsModPBerlekampForm` extractors and the
`Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData` path, then
records the conclusion against `Hex.ZPoly.toMonicLiftData core B primeData`,
which is definitionally
`Hex.henselLiftData M (Hex.precisionForCoeffBound B primeData.p) primeData`.

The result is the monic-coordinate lifted representation only: a monic factor
`g ∣ M` represented modulo `primeData.p` by `S` is represented at the lift on
the monic coordinate `M`.  Recovering the original non-monic `factor` from this
(via `primitivePart ∘ dilate`) is the separate transfer of #7452; this lemma
deliberately stops at the monic coordinate.

`hcore_lc_pos` and `hcore_pos` make `M` monic
(`Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree`).  `hB_ne_zero` is required
for `1 ≤ Hex.precisionForCoeffBound B primeData.p`: with `B = 0` the
coefficient target `2 * B + 1 = 1` admits precision `0`, and
`precisionForCoeffBound_spec` only forces `2 * B < primeData.p ^ precision`. -/
theorem toMonicLiftData_represents_lifted_monicCorrespondent
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hB_ne_zero : B ≠ 0)
    {g : Hex.ZPoly} {S : ModPFactorSubset primeData}
    (hg_monic : Hex.DensePoly.Monic g)
    (hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g))
    (hg_dvd : g ∣ (Hex.ZPoly.toMonic core).monic)
    (hrepP : RepresentsIntegerFactorModP primeData g S) :
    RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
      (Hex.ZPoly.toMonicLiftData core B primeData) g
      (liftedSubsetOfModPSubset primeData
        (Hex.ZPoly.toMonicLiftData core B primeData)
        (Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData) S) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hmonicCore_monic :
      Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hform :
      Hex.factorsModPBerlekampForm (Hex.ZPoly.toMonic core).monic primeData :=
    Hex.ZPoly.toMonicPrimeData?_factorsModP_berlekamp_form core primeData hselected
  have hgood :
      Hex.isGoodPrime (Hex.ZPoly.toMonic core).monic primeData.p = true :=
    Hex.ZPoly.toMonicPrimeData?_isGoodPrime core primeData hselected
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
  have hp : 1 < primeData.p := hp_prime.two_le
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  -- Precision positivity: needs `B ≠ 0`, since `precisionForCoeffBound_spec`
  -- only bounds `2 * B < p ^ precision`.
  have hprec_spec :
      2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne_zero
  have hprec_pos : 1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    by_contra hlt
    have hzero : Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hprec_spec
    omega
  -- Analytic inputs from the Berlekamp-form extractors.
  have hfactors_monic :
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g :=
    factorsModP_monic_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hform
  have hproduct_mod_p :
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        (Hex.ZPoly.toMonic core).monic primeData.p :=
    factorsModP_polyProduct_congr_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hmonicCore_monic hform hgood
  have hcoprime :
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList :=
    factorsModP_coprime_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hform hgood
  have hnonempty : primeData.factorsModP.toList ≠ [] :=
    factorsModP_ne_nil_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hform
  have hinv :
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p (Hex.precisionForCoeffBound B primeData.p)
        (Hex.ZPoly.toMonic core).monic
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList :=
    Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      (Hex.ZPoly.toMonic core).monic
      (Hex.precisionForCoeffBound B primeData.p) primeData
      hp_prime hp hprec_pos hmonicCore_monic hfactors_monic
      hproduct_mod_p hcoprime hnonempty
  have hfactors_nodup : primeData.factorsModP.toList.Nodup :=
    factorsModP_nodup_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hform hgood
  have hmonicCore_pos :
      0 < (Hex.ZPoly.toMonic core).monic.degree?.getD 0 := by
    rw [Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos hcore_pos]
    exact hcore_pos
  have hfactors_irr :
      ∀ i : ModPFactorIndex primeData,
        Irreducible
          (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)) :=
    factors_irreducible_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hform hgood hmonicCore_pos
  have hprime_root : _root_.Nat.Prime primeData.p :=
    natPrime_of_hexNatPrime hp_prime
  exact henselLiftData_represents_lifted_of_modP
    (Hex.ZPoly.toMonic core).monic
    (Hex.precisionForCoeffBound B primeData.p) primeData
    hmonicCore_monic hprime_root hinv hprec_pos hfactors_monic hproduct_mod_p
    hfactors_irr hfactors_nodup hg_monic hg_irr hg_dvd hrepP

/-- `centeredModNat 1 m = 1` when `m ≥ 2`: the value `1` lies in the centred
half-window and is preserved by the centred-reduction operation. -/
private theorem centeredModNat_one_of_two_le {m : Nat} (hm : 2 ≤ m) :
    Hex.centeredModNat (1 : Int) m = (1 : Int) := by
  by_cases hm3 : 3 ≤ m
  · have hbound : (1 : Int).natAbs ≤ (1 : Nat) := by decide
    have hsep : 2 * (1 : Nat) < m := by omega
    have h := Hex.centeredModNat_emod_eq_of_natAbs_le (1 : Int) m 1 hbound hsep
    have h1mod : (1 : Int) % (m : Int) = 1 :=
      Int.emod_eq_of_lt (by decide) (by exact_mod_cast (show 1 < m by omega))
    rwa [h1mod] at h
  · have hm2 : m = 2 := by omega
    subst hm2
    rfl

/--
Centred-lift preserves monicness once the modulus is at least two.

The leading coefficient `1` of a monic input survives the centred-reduction
(`centeredModNat 1 m = 1` for `m ≥ 2`) and `DensePoly.ofCoeffs` does not trim
it, so the output preserves both size and leading coefficient.
-/
theorem monic_centeredLiftPoly_of_monic
    {g : Hex.ZPoly} (hg : Hex.DensePoly.Monic g) {m : Nat} (hm : 2 ≤ m) :
    Hex.DensePoly.Monic (Hex.centeredLiftPoly g m) := by
  have hg_size_pos : 0 < g.size := zpoly_size_pos_of_monic hg
  have hg_lead : g.coeff (g.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_size_pos]; exact hg
  set g' := Hex.centeredLiftPoly g m with hg'_def
  have hcoeff : ∀ i, g'.coeff i = Hex.centeredModNat (g.coeff i) m :=
    fun i => Hex.coeff_centeredLiftPoly g m i
  have hcoeff_top : g'.coeff (g.size - 1) = (1 : Int) := by
    rw [hcoeff, hg_lead]; exact centeredModNat_one_of_two_le hm
  have hg'_size_ge : g.size ≤ g'.size := by
    by_contra hlt
    have hlt' : g'.size < g.size := Nat.lt_of_not_ge hlt
    have hle : g'.size ≤ g.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g' hle
    rw [hcoeff_top] at h_zero
    exact absurd h_zero (by decide)
  have hg'_size_le : g'.size ≤ g.size := by
    rw [hg'_def]
    unfold Hex.centeredLiftPoly
    have h := Hex.DensePoly.size_ofCoeffs_le
      (g.toArray.map fun coeff => Hex.centeredModNat coeff m)
    rw [Array.size_map] at h
    -- `g.toArray.size = g.coeffs.size = g.size` definitionally
    exact h
  have hg'_size_eq : g'.size = g.size := le_antisymm hg'_size_le hg'_size_ge
  show Hex.DensePoly.leadingCoeff g' = (1 : Int)
  rw [Hex.DensePoly.leadingCoeff_eq_coeff_last g' (hg'_size_eq ▸ hg_size_pos),
    hg'_size_eq]
  exact hcoeff_top

/-- Centred-lift preserves stored size when the input is monic and the modulus
is at least two. The leading coefficient `1` survives the centred reduction
(forcing `g'.size ≥ g.size`) and `DensePoly.ofCoeffs` never grows the array
(forcing `g'.size ≤ g.size`). -/
private theorem size_centeredLiftPoly_eq_of_monic
    {g : Hex.ZPoly} (hg : Hex.DensePoly.Monic g) {m : Nat} (hm : 2 ≤ m) :
    (Hex.centeredLiftPoly g m).size = g.size := by
  have hg_size_pos : 0 < g.size := zpoly_size_pos_of_monic hg
  have hg_lead : g.coeff (g.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_size_pos]; exact hg
  set g' := Hex.centeredLiftPoly g m with hg'_def
  have hcoeff : ∀ i, g'.coeff i = Hex.centeredModNat (g.coeff i) m :=
    fun i => Hex.coeff_centeredLiftPoly g m i
  have hcoeff_top : g'.coeff (g.size - 1) = (1 : Int) := by
    rw [hcoeff, hg_lead]; exact centeredModNat_one_of_two_le hm
  have hg'_size_ge : g.size ≤ g'.size := by
    by_contra hlt
    have hlt' : g'.size < g.size := Nat.lt_of_not_ge hlt
    have hle : g'.size ≤ g.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g' hle
    rw [hcoeff_top] at h_zero
    exact absurd h_zero (by decide)
  have hg'_size_le : g'.size ≤ g.size := by
    rw [hg'_def]
    unfold Hex.centeredLiftPoly
    have h := Hex.DensePoly.size_ofCoeffs_le
      (g.toArray.map fun coeff => Hex.centeredModNat coeff m)
    rw [Array.size_map] at h
    exact h
  exact le_antisymm hg'_size_le hg'_size_ge

/--
`Array.polyProduct` of an array all of whose entries are monic is monic.

The base case is `Monic 1` (`zpoly_monic_one`); the inductive step chains
`zpoly_monic_mul` through each entry along the `foldl` accumulator.
-/
private theorem polyProduct_monic_of_all_monic
    {factors : Array Hex.ZPoly}
    (hmonic : ∀ p ∈ factors.toList, Hex.DensePoly.Monic p) :
    Hex.DensePoly.Monic (Array.polyProduct factors) := by
  unfold Array.polyProduct
  rw [← Array.foldl_toList]
  suffices h : ∀ (l : List Hex.ZPoly) (acc : Hex.ZPoly),
      Hex.DensePoly.Monic acc →
      (∀ p ∈ l, Hex.DensePoly.Monic p) →
      Hex.DensePoly.Monic (l.foldl (· * ·) acc) by
    exact h factors.toList 1 zpoly_monic_one hmonic
  intro l
  induction l with
  | nil =>
    intro acc hacc _
    simpa using hacc
  | cons x rest ih =>
    intro acc hacc hl
    simp only [List.foldl_cons]
    apply ih
    · exact zpoly_monic_mul hacc (hl x List.mem_cons_self)
    · intro p hp; exact hl p (List.mem_cons_of_mem _ hp)

/--
Derive the **dilated centered-lift** reconstruction equality from a proof-side
lifted-subset representation.  This is the producer-side bridge consumed by the
migrated fast-path BHKS recovery wrappers
(`candidatesOfDilatedCenteredLift`, `ofMignottePrecisionCandidateProducts`),
which restate the reconstruction in the executable monic-transform recovery
coordinate `dilate (leadingCoeff core) ∘ centeredLiftPoly` rather than the
additive `scale`-coordinate modular congruence removed by the fast-path
migration (#7044 / #2564).

The fast-path recovery chain is monic-gated (its producer
`bhksIndicatorCandidate?_representsIntegerFactorAtLift` carries `hcore_monic`),
so `leadingCoeff core = 1` and the dilation collapses to the identity.  The
proof routes through `RecoveredAtLift.candidate_eq_of_monic_dvd`
(`liftedRecoveryCandidate core d S = factor`) and then collapses the
`primitivePart`/`normalizeFactorSign` normalizations of `liftedRecoveryCandidate`
on the monic centred lift of the selected product.
-/
theorem dilatedCenteredLift_of_representsIntegerFactorAtLift
    {core : Hex.ZPoly} {d : Hex.LiftData} {selected : Array Hex.ZPoly}
    {expectedFactor : Hex.ZPoly} {S : LiftedFactorSubset d}
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprod_monic : Hex.DensePoly.Monic (liftedFactorProduct d S))
    (hp_two_le : 2 ≤ d.p ^ d.k)
    (hmonic_ne : (Hex.ZPoly.toMonic core).monic ≠ 0)
    (hfactor_norm : Hex.normalizeFactorSign expectedFactor = expectedFactor)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        d.p ^ d.k)
    (hselected_product :
      Array.polyProduct selected = liftedFactorProduct d S)
    (hrep : RepresentsIntegerFactorAtLift core d expectedFactor S) :
    Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
        (Hex.centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k)) =
      expectedFactor := by
  rcases hrep with ⟨hrec⟩
  have hcand : liftedRecoveryCandidate core d S = expectedFactor :=
    hrec.candidate_eq_of_monic_dvd hmonic_ne hfactor_norm hprecision
  have hlc : Hex.DensePoly.leadingCoeff core = (1 : Int) := hcore_monic
  have hcl_monic : Hex.DensePoly.Monic
      (Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)) :=
    monic_centeredLiftPoly_of_monic hprod_monic hp_two_le
  rw [hselected_product, hlc, Hex.ZPoly.dilate_one, ← hcand]
  unfold liftedRecoveryCandidate
  rw [hlc, Hex.ZPoly.dilate_one,
    Hex.ZPoly.primitivePart_eq_self_of_primitive _
      (zpoly_primitive_of_monic hcl_monic),
    zpoly_normalize_factor_sign_of_monic hcl_monic]

/--
A successful `bhksIndicatorCandidate?` call yields, under monic-core and
monic-selected-factor hypotheses, the canonical modular product equality
`reduceModPow raw p k = reduceModPow candidate p k`.

This is the per-candidate modular-product fact needed to derive the
`RepresentsIntegerFactorAtLift` certificate from a successful candidate path
(see issue #6455 / #6450). The proof routes through:

- the centred-lift round-trip identity `centeredLiftPoly_reduceModPow_eq`,
- `monic_centeredLiftPoly_of_monic` to push monicness through the centred lift,
- `zpoly_primitive_of_monic` + `primitivePart_eq_self_of_primitive` to
  collapse `normalizeCandidateFactor` to identity on monic input,
- `zpoly_normalize_factor_sign_of_monic` to collapse `normalizeFactorSign` to
  identity on monic input.
-/
theorem bhksIndicatorCandidate?_reduceModPow_eq_of_monic
    {core : Hex.ZPoly} {d : Hex.LiftData} {indicator : Array Int}
    {candidate quotient : Hex.ZPoly} {selected : Array Hex.ZPoly}
    (h : Hex.bhksIndicatorCandidate? core d indicator = some (candidate, quotient))
    (hselected :
       Hex.bhksIndicatorSelectedFactors d.liftedFactors indicator = some selected)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hselected_monic :
       ∀ p ∈ selected.toList, Hex.DensePoly.Monic p)
    (hp_two_lt : 2 ≤ d.p ^ d.k) :
    Hex.ZPoly.reduceModPow
        (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
          (Array.polyProduct selected)) d.p d.k =
      Hex.ZPoly.reduceModPow candidate d.p d.k := by
  -- Step 1: lc(core) = 1 since core is monic.
  have hlc : Hex.DensePoly.leadingCoeff core = (1 : Int) := hcore_monic
  -- Step 2: polyProduct selected is monic.
  have hprod_monic : Hex.DensePoly.Monic (Array.polyProduct selected) :=
    polyProduct_monic_of_all_monic hselected_monic
  -- Step 3: raw = scale 1 (polyProduct selected) = polyProduct selected, so raw is monic.
  set raw := Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
    (Array.polyProduct selected) with hraw_def
  have hraw_eq : raw = Array.polyProduct selected := by
    rw [hraw_def, hlc]
    -- scale 1 g = g (coefficient-wise): both sides equal Array.polyProduct selected.
    apply Hex.DensePoly.ext_coeff
    intro n
    rw [Hex.DensePoly.coeff_scale _ _ _ (by ring : (1 : Int) * 0 = 0)]
    ring
  have hraw_monic : Hex.DensePoly.Monic raw := by rw [hraw_eq]; exact hprod_monic
  -- Step 4: centeredLiftPoly raw (p^k) is monic.
  have hcl_raw_monic : Hex.DensePoly.Monic
      (Hex.centeredLiftPoly raw (d.p ^ d.k)) :=
    monic_centeredLiftPoly_of_monic hraw_monic hp_two_lt
  -- Step 5: centeredLiftPoly (reduceModPow raw p k) (p^k) = centeredLiftPoly raw (p^k).
  have hcl_eq : Hex.centeredLiftPoly (Hex.ZPoly.reduceModPow raw d.p d.k) (d.p ^ d.k) =
      Hex.centeredLiftPoly raw (d.p ^ d.k) :=
    centeredLiftPoly_reduceModPow_eq raw d.p d.k d.p_pos
  -- Step 6: The centred lift is monic, and normalize-stuff are identities on monic input.
  set cl := Hex.centeredLiftPoly (Hex.ZPoly.reduceModPow raw d.p d.k) (d.p ^ d.k)
    with hcl_def
  have hcl_monic : Hex.DensePoly.Monic cl := by rw [hcl_eq]; exact hcl_raw_monic
  have hcl_prim : Hex.ZPoly.Primitive cl := zpoly_primitive_of_monic hcl_monic
  have hpprim : Hex.ZPoly.primitivePart cl = cl :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive cl hcl_prim
  have hnorm_cand : Hex.normalizeCandidateFactor cl = cl := by
    unfold Hex.normalizeCandidateFactor
    rw [hpprim]
    have : ¬ Hex.DensePoly.leadingCoeff cl < 0 := by
      have : Hex.DensePoly.leadingCoeff cl = (1 : Int) := hcl_monic
      rw [this]; decide
    simp [this]
  have hnorm_sign : Hex.normalizeFactorSign cl = cl :=
    zpoly_normalize_factor_sign_of_monic hcl_monic
  -- Step 7: candidate = cl, using the executable-layer characterization.
  have hcand_eq : candidate = cl := by
    have hext := Hex.bhksIndicatorCandidate?_eq_normalized_dilatedCenteredLift h hselected
    have hcl_selected :
        Hex.centeredLiftPoly selected.polyProduct (d.p ^ d.k) = cl := by
      rw [hcl_eq, hraw_eq]
    rw [hext, hlc, Hex.ZPoly.dilate_one, hcl_selected, hnorm_cand, hnorm_sign]
  -- Step 8: reduceModPow raw p k = reduceModPow cl p k via the centered lift.
  rw [hcand_eq]
  -- Goal: reduceModPow raw p k = reduceModPow cl p k.
  -- cl = centeredLiftPoly (reduceModPow raw p k) (p^k).
  -- Reducing the centred lift back recovers the canonical residue.
  -- Key helper: centeredModNat x m ≡ x (mod m).
  have hcenteredModNat_emod_eq :
      ∀ (z : Int) (m : Nat), m ≠ 0 →
        (Hex.centeredModNat z m) % (Int.ofNat m) = z % (Int.ofNat m) := by
    intro z m hm
    unfold Hex.centeredModNat
    rw [if_neg hm]
    set r := z % (Int.ofNat m) with hr_def
    have hrmod : r % (Int.ofNat m) = r := by
      rw [hr_def, Int.emod_emod_of_dvd _ (dvd_refl _)]
    by_cases hc1 : 2 * r.natAbs ≤ m
    · rw [if_pos hc1]; exact hrmod
    · rw [if_neg hc1]
      by_cases hc2 : r < 0
      · rw [if_pos hc2]
        have hrwadd : (r + Int.ofNat m) % Int.ofNat m = r % Int.ofNat m := by
          rw [show r + Int.ofNat m = r + 1 * Int.ofNat m by ring,
            Int.add_mul_emod_self_right]
        rw [hrwadd, hrmod]
      · rw [if_neg hc2]
        have hrwsub : (r - Int.ofNat m) % Int.ofNat m = r % Int.ofNat m := by
          rw [show r - Int.ofNat m = r + (-1) * Int.ofNat m by ring,
            Int.add_mul_emod_self_right]
        rw [hrwsub, hrmod]
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [hcl_def, Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ (Nat.pow_pos d.p_pos),
    Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ (Nat.pow_pos d.p_pos),
    Hex.coeff_centeredLiftPoly,
    Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ (Nat.pow_pos d.p_pos)]
  -- Goal: raw.coeff n % m = centeredModNat (raw.coeff n % m) m % m.
  rw [hcenteredModNat_emod_eq _ _ (Nat.ne_of_gt (Nat.pow_pos d.p_pos))]
  exact (Int.emod_emod_of_dvd _ (dvd_refl _)).symm

/--
The Mathlib-transported `natDegree` of the executable recombination candidate
over a lifted-factor subset equals the sum of the Mathlib-transported
`natDegree`s of the selected lifted factors.

Under the modulus condition `2 ≤ d.p ^ d.k` and monicness of every lifted
factor, the candidate's `centeredLiftPoly`/`primitivePart`/`normalizeFactorSign`
chain collapses to a single monic polynomial whose stored size is the same as
the underlying lifted-factor product, so its Mathlib-side `natDegree` is the
sum over the subset.

This is the candidate-side ingredient of the reverse-coverage degree-counting
argument in the `representedFactor_dvd_recombinationCandidate_of_subset`
divisibility theorem; see issue #4439.
-/
theorem natDegree_toPolynomial_recombinationCandidate_eq_sum
    {d : Hex.LiftData}
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
      ∑ i ∈ T,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  set lp := liftedFactorProduct d T with hlp_def
  -- lp is monic from monicness of each lifted factor.
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  -- centeredLiftPoly preserves monicness under the modulus condition.
  have hcl_monic := monic_centeredLiftPoly_of_monic hlp_monic hd_modulus
  set cl := Hex.centeredLiftPoly lp (d.p ^ d.k) with hcl_def
  -- A monic poly has trivial content and trivial sign normalisation.
  have hnorm : Hex.normalizeFactorSign cl = cl :=
    zpoly_normalize_factor_sign_of_monic hcl_monic
  have hprim : Hex.ZPoly.primitivePart cl = cl :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive cl
      (zpoly_primitive_of_monic hcl_monic)
  -- Combining, the candidate is just the centered lift of the product.
  have hrec_eq : recombinationCandidate d T = cl := by
    unfold recombinationCandidate
    rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct,
      ← hlp_def, ← hcl_def, hprim, hnorm]
  rw [hrec_eq]
  -- The centered lift has the same stored size as the product.
  have hsize_eq : cl.size = lp.size :=
    size_centeredLiftPoly_eq_of_monic hlp_monic hd_modulus
  -- `natDegree (toPolynomial _)` is `size - 1` on a nonzero (monic) poly.
  have hcl_size_pos : 0 < cl.size := zpoly_size_pos_of_monic hcl_monic
  have hlp_size_pos : 0 < lp.size := zpoly_size_pos_of_monic hlp_monic
  have hcl_natDeg :
      (HexPolyZMathlib.toPolynomial cl).natDegree = cl.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hcl_size_pos]
  have hlp_natDeg :
      (HexPolyZMathlib.toPolynomial lp).natDegree = lp.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hlp_size_pos]
  rw [hcl_natDeg, hsize_eq, ← hlp_natDeg, hlp_def, toPolynomial_liftedFactorProduct]
  -- Mathlib `natDegree_prod_of_monic` over monic factors.
  apply Polynomial.natDegree_prod_of_monic
  intro i _
  -- Monicness of `toPolynomial (liftedFactor d i)` from monicness of the
  -- lifted factor itself via `HexPolyMathlib.leadingCoeff_toPolynomial`.
  show (HexPolyZMathlib.toPolynomial (liftedFactor d i)).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact hd_liftedFactor_monic i

/--
The Mathlib-transported `natDegree` of a represented integer factor equals the
sum of the Mathlib-transported `natDegree`s of the lifted factors in the
representing subset.

On a monic core, the partition pins the represented factor to its executable
recombination candidate (`LiftedFactorSubsetPartition.recombinationCandidate_eq`),
after which `natDegree_toPolynomial_recombinationCandidate_eq_sum` reads off the
degree sum. This routes through the sound partition equality rather than passing
`RepresentsIntegerFactorAtLift` to the old scaled-product recovery lemmas.
-/
theorem natDegree_toPolynomial_eq_sum_of_represents
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d}
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d factor S) :
    (HexPolyZMathlib.toPolynomial factor).natDegree =
      ∑ i ∈ S,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  have hrec_eq : recombinationCandidate d S = factor :=
    hpartition.recombinationCandidate_eq hcore_monic hfactor_irr
      hfactor_dvd_target hSJ hrep
  rw [← hrec_eq]
  exact natDegree_toPolynomial_recombinationCandidate_eq_sum
    hd_modulus hd_liftedFactor_monic S

/--
Identification of the executable `Hex.ZPoly.Primitive` predicate with Mathlib's
`Polynomial.IsPrimitive` on the transported polynomial.
-/
private theorem toPolynomial_isPrimitive_of_zpoly_primitive_basic
    {f : Hex.ZPoly} (hprim : Hex.ZPoly.Primitive f) :
    (HexPolyZMathlib.toPolynomial f).IsPrimitive := by
  intro r hdvd
  have hcoeff : ∀ n, r ∣ f.coeff n := by
    intro n
    have h :=
      (Polynomial.C_dvd_iff_dvd_coeff r (HexPolyZMathlib.toPolynomial f)).mp hdvd n
    rwa [HexPolyZMathlib.coeff_toPolynomial] at h
  have hnatAbs_dvd : ∀ n, (r.natAbs : ℤ) ∣ f.coeff n := fun n =>
    Int.natAbs_dvd.mpr (hcoeff n)
  have hr_dvd_content : (r.natAbs : ℤ) ∣ Hex.ZPoly.content f :=
    Hex.ZPoly.dvd_content_of_nat_dvd_coeff f r.natAbs hnatAbs_dvd
  rw [show Hex.ZPoly.content f = 1 from hprim] at hr_dvd_content
  have hone : r.natAbs ∣ 1 := by exact_mod_cast hr_dvd_content
  exact Int.isUnit_iff_natAbs_eq.mpr (Nat.eq_one_of_dvd_one hone)

/--
Reverse identification from Mathlib's `Polynomial.IsPrimitive` on the transported
polynomial to the executable `Hex.ZPoly.Primitive` predicate.
-/
private theorem zpoly_primitive_of_toPolynomial_isPrimitive_basic
    {f : Hex.ZPoly}
    (hprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive) :
    Hex.ZPoly.Primitive f := by
  show Hex.ZPoly.content f = 1
  have hC_dvd :
      Polynomial.C (Hex.ZPoly.content f) ∣ HexPolyZMathlib.toPolynomial f := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [HexPolyZMathlib.coeff_toPolynomial]
    exact Hex.ZPoly.content_dvd_coeff f n
  have hIsUnit : IsUnit (Hex.ZPoly.content f) := hprim _ hC_dvd
  have hcontent_nonneg : 0 ≤ Hex.ZPoly.content f := by
    show 0 ≤ Hex.DensePoly.content _
    unfold Hex.DensePoly.content
    exact Int.natCast_nonneg _
  rcases Int.isUnit_iff.mp hIsUnit with hone | hneg
  · exact hone
  · rw [hneg] at hcontent_nonneg
    omega

/-- A `Hex.ZPoly` with positive leading coefficient is nonzero. -/
theorem zpoly_ne_zero_of_pos_lc {f : Hex.ZPoly}
    (hpos : 0 < Hex.DensePoly.leadingCoeff f) : f ≠ 0 := by
  intro hf
  rw [hf] at hpos
  have hzero_lc : Hex.DensePoly.leadingCoeff (0 : Hex.ZPoly) = 0 := rfl
  rw [hzero_lc] at hpos
  omega

/-- A `Hex.ZPoly` with positive leading coefficient has positive stored size. -/
private theorem zpoly_size_pos_of_pos_lc {f : Hex.ZPoly}
    (hpos : 0 < Hex.DensePoly.leadingCoeff f) : 0 < f.size := by
  rcases Nat.eq_zero_or_pos f.coeffs.size with hcs_zero | hcs_pos
  · exfalso
    have hlc_zero : Hex.DensePoly.leadingCoeff f = (0 : Int) := by
      simp [Hex.DensePoly.leadingCoeff, hcs_zero, Array.getD] <;> rfl
    rw [hlc_zero] at hpos
    omega
  · exact hcs_pos

private theorem zpoly_eq_one_of_toPolynomial_isUnit_of_pos_lc
    {f : Hex.ZPoly}
    (hpos : 0 < Hex.DensePoly.leadingCoeff f)
    (hunit : IsUnit (HexPolyZMathlib.toPolynomial f)) :
    f = 1 := by
  have hunit_z : Hex.ZPoly.IsUnit f :=
    (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mpr hunit
  rcases hunit_z with hunit_one | hunit_neg
  · rw [hunit_one]
    rfl
  · exfalso
    rw [hunit_neg] at hpos
    change 0 < Hex.DensePoly.leadingCoeff (Hex.DensePoly.C (-1 : Int)) at hpos
    simp [Hex.DensePoly.leadingCoeff, Hex.DensePoly.coeffs_C_of_ne_zero] at hpos

private theorem zpoly_primitive_of_dvd_primitive_basic
    {factor target : Hex.ZPoly}
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (hfactor_dvd_target : factor ∣ target) :
    Hex.ZPoly.Primitive factor := by
  apply zpoly_primitive_of_toPolynomial_isPrimitive_basic
  exact isPrimitive_of_dvd
    (toPolynomial_isPrimitive_of_zpoly_primitive_basic htarget_primitive)
    (HexPolyMathlib.toPolynomial_dvd hfactor_dvd_target)

private theorem zpoly_left_pos_lc_of_mul_eq_of_pos_lc
    {left right target : Hex.ZPoly}
    (hmul : left * right = target)
    (hright_pos : 0 < Hex.DensePoly.leadingCoeff right)
    (htarget_pos : 0 < Hex.DensePoly.leadingCoeff target) :
    0 < Hex.DensePoly.leadingCoeff left := by
  have hright_ne : right ≠ 0 := zpoly_ne_zero_of_pos_lc hright_pos
  have htarget_ne : target ≠ 0 := zpoly_ne_zero_of_pos_lc htarget_pos
  have hleft_ne : left ≠ 0 := by
    intro hleft
    apply htarget_ne
    rw [← hmul, hleft, Hex.DensePoly.zero_mul]
  have hlc :=
    Hex.ZPoly.leadingCoeff_mul_of_nonzero left right hleft_ne hright_ne
  have hprod_pos :
      0 < Hex.DensePoly.leadingCoeff left *
        Hex.DensePoly.leadingCoeff right := by
    rw [← hlc, hmul]
    exact htarget_pos
  nlinarith

private theorem centeredModNat_eq_of_pos_natAbs_le
    {z : Int} {m B : Nat}
    (hz_pos : 0 < z) (hbound : z.natAbs ≤ B) (hsep : 2 * B < m) :
    Hex.centeredModNat z m = z := by
  have hz_nonneg : 0 ≤ z := le_of_lt hz_pos
  have hltNat : z.natAbs < m := by omega
  have hlt : z < (m : Int) := by
    have hz_le_abs : z ≤ (z.natAbs : Int) := by
      rw [Int.natAbs_of_nonneg hz_nonneg]
    have habs_lt : (z.natAbs : Int) < (m : Int) := by exact_mod_cast hltNat
    exact lt_of_le_of_lt hz_le_abs habs_lt
  have hmod : z % (m : Int) = z := Int.emod_eq_of_lt hz_nonneg hlt
  have hcenter :=
    Hex.centeredModNat_emod_eq_of_natAbs_le z m B hbound hsep
  rwa [hmod] at hcenter

/--
Centred-lift preserves a strictly positive leading coefficient that lies inside
the Mignotte half-window.
-/
private theorem leadingCoeff_centeredLiftPoly_of_pos_leadingCoeff_bound
    {g : Hex.ZPoly} {m B : Nat}
    (hg_lc_pos : 0 < Hex.DensePoly.leadingCoeff g)
    (hbound_lc : (Hex.DensePoly.leadingCoeff g).natAbs ≤ B)
    (hsep : 2 * B < m) :
    Hex.DensePoly.leadingCoeff (Hex.centeredLiftPoly g m) =
      Hex.DensePoly.leadingCoeff g := by
  have hg_size_pos : 0 < g.size := zpoly_size_pos_of_pos_lc hg_lc_pos
  have hg_lead :
      g.coeff (g.size - 1) = Hex.DensePoly.leadingCoeff g := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_size_pos]
  set g' := Hex.centeredLiftPoly g m with hg'_def
  have hcoeff : ∀ i, g'.coeff i = Hex.centeredModNat (g.coeff i) m :=
    fun i => Hex.coeff_centeredLiftPoly g m i
  have hcoeff_top :
      g'.coeff (g.size - 1) = Hex.DensePoly.leadingCoeff g := by
    rw [hcoeff, hg_lead]
    exact centeredModNat_eq_of_pos_natAbs_le hg_lc_pos hbound_lc hsep
  have hg'_size_ge : g.size ≤ g'.size := by
    by_contra hlt
    have hlt' : g'.size < g.size := Nat.lt_of_not_ge hlt
    have hle : g'.size ≤ g.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g' hle
    rw [hcoeff_top] at h_zero
    exact (ne_of_gt hg_lc_pos) h_zero
  have hg'_size_le : g'.size ≤ g.size := by
    rw [hg'_def]
    unfold Hex.centeredLiftPoly
    have h := Hex.DensePoly.size_ofCoeffs_le
      (g.toArray.map fun coeff => Hex.centeredModNat coeff m)
    rw [Array.size_map] at h
    exact h
  have hg'_size_eq : g'.size = g.size := le_antisymm hg'_size_le hg'_size_ge
  show Hex.DensePoly.leadingCoeff g' = Hex.DensePoly.leadingCoeff g
  rw [Hex.DensePoly.leadingCoeff_eq_coeff_last g' (hg'_size_eq ▸ hg_size_pos),
    hg'_size_eq]
  exact hcoeff_top

/-- Scaling a monic integer polynomial by a nonzero constant preserves its
stored size: the leading coefficient becomes `c * 1 = c ≠ 0`, and `scale` never
grows the array. -/
private theorem size_scale_eq_of_monic_of_ne_zero
    {c : Int} (hc : c ≠ 0) {f : Hex.ZPoly} (hmonic : Hex.DensePoly.Monic f) :
    (Hex.DensePoly.scale c f).size = f.size := by
  have hf_size_pos : 0 < f.size := zpoly_size_pos_of_monic hmonic
  have hf_lead : f.coeff (f.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last f hf_size_pos]; exact hmonic
  set g := Hex.DensePoly.scale c f with hg_def
  have hcoeff_top : g.coeff (f.size - 1) = c := by
    rw [hg_def, Hex.DensePoly.coeff_scale (R := Int) c f _ (Int.mul_zero _),
      hf_lead]; ring
  have hg_size_ge : f.size ≤ g.size := by
    by_contra hlt
    have hlt' : g.size < f.size := Nat.lt_of_not_ge hlt
    have hle : g.size ≤ f.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g hle
    rw [hcoeff_top] at h_zero
    exact hc h_zero
  have hg_size_le : g.size ≤ f.size := by
    rw [hg_def]
    unfold Hex.DensePoly.scale
    have h := Hex.DensePoly.size_ofCoeffs_le
      ((f.toArray.toList.map fun a => c * a).toArray)
    rw [List.size_toArray, List.length_map] at h
    simpa [Hex.DensePoly.size] using h
  exact le_antisymm hg_size_le hg_size_ge

/-- Variable dilation by a nonzero integer preserves stored size for monic
integer polynomials. -/
private theorem size_dilate_eq_of_monic_of_ne_zero
    {c : Int} (hc : c ≠ 0) {f : Hex.ZPoly} (hmonic : Hex.DensePoly.Monic f) :
    (Hex.ZPoly.dilate c f).size = f.size := by
  have hf_size_pos : 0 < f.size := zpoly_size_pos_of_monic hmonic
  have hf_lead : f.coeff (f.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last f hf_size_pos]
    exact hmonic
  set g := Hex.ZPoly.dilate c f with hg_def
  have hcoeff_top : g.coeff (f.size - 1) = c ^ (f.size - 1) := by
    rw [hg_def, Hex.ZPoly.coeff_dilate, hf_lead, Int.mul_one]
  have hpow_ne : c ^ (f.size - 1) ≠ 0 := pow_ne_zero _ hc
  have hg_size_ge : f.size ≤ g.size := by
    by_contra hlt
    have hlt' : g.size < f.size := Nat.lt_of_not_ge hlt
    have hle : g.size ≤ f.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g hle
    rw [hcoeff_top] at h_zero
    exact hpow_ne h_zero
  have hg_size_le : g.size ≤ f.size := by
    rw [hg_def]
    unfold Hex.ZPoly.dilate
    have h := Hex.DensePoly.size_ofCoeffs_le
      ((List.range f.size).map fun i => c ^ i * f.coeff i).toArray
    rw [List.size_toArray, List.length_map, List.length_range] at h
    simpa [Hex.DensePoly.size] using h
  exact le_antisymm hg_size_le hg_size_ge

/-- Centred-lift preserves stored size when the leading coefficient is strictly
positive and lies inside the Mignotte half-window. Companion to
`leadingCoeff_centeredLiftPoly_of_pos_leadingCoeff_bound`. -/
private theorem size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound
    {g : Hex.ZPoly} {m B : Nat}
    (hg_lc_pos : 0 < Hex.DensePoly.leadingCoeff g)
    (hbound_lc : (Hex.DensePoly.leadingCoeff g).natAbs ≤ B)
    (hsep : 2 * B < m) :
    (Hex.centeredLiftPoly g m).size = g.size := by
  have hg_size_pos : 0 < g.size := zpoly_size_pos_of_pos_lc hg_lc_pos
  have hg_lead :
      g.coeff (g.size - 1) = Hex.DensePoly.leadingCoeff g := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_size_pos]
  set g' := Hex.centeredLiftPoly g m with hg'_def
  have hcoeff : ∀ i, g'.coeff i = Hex.centeredModNat (g.coeff i) m :=
    fun i => Hex.coeff_centeredLiftPoly g m i
  have hcoeff_top : g'.coeff (g.size - 1) = Hex.DensePoly.leadingCoeff g := by
    rw [hcoeff, hg_lead]
    exact centeredModNat_eq_of_pos_natAbs_le hg_lc_pos hbound_lc hsep
  have hg'_size_ge : g.size ≤ g'.size := by
    by_contra hlt
    have hlt' : g'.size < g.size := Nat.lt_of_not_ge hlt
    have hle : g'.size ≤ g.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g' hle
    rw [hcoeff_top] at h_zero
    exact (ne_of_gt hg_lc_pos) h_zero
  have hg'_size_le : g'.size ≤ g.size := by
    rw [hg'_def]
    unfold Hex.centeredLiftPoly
    have h := Hex.DensePoly.size_ofCoeffs_le
      (g.toArray.map fun coeff => Hex.centeredModNat coeff m)
    rw [Array.size_map] at h
    exact h
  exact le_antisymm hg'_size_le hg'_size_ge

/-- `Hex.normalizeFactorSign` preserves stored size: it either returns the input
unchanged or negates every coefficient via `DensePoly.scale (-1)`, and scaling by
the nonzero integer `-1` preserves stored size. -/
private theorem size_normalizeFactorSign_eq (f : Hex.ZPoly) :
    (Hex.normalizeFactorSign f).size = f.size := by
  unfold Hex.normalizeFactorSign
  by_cases hneg : Hex.DensePoly.leadingCoeff f < 0
  · rw [if_pos hneg]
    exact Hex.ZPoly.scale_size_of_nonzero (-1 : Int) f (by decide)
  · rw [if_neg hneg]

/-- `Hex.ZPoly.primitivePart` preserves stored size on nonzero inputs.

Reconstruct `f = scale (content f) (primitivePart f)` via
`content_mul_primitivePart`, then apply `Hex.ZPoly.scale_size_of_nonzero` with
the fact that `content f ≠ 0` whenever `f ≠ 0`. -/
private theorem size_primitivePart_eq_of_ne_zero {f : Hex.ZPoly} (hf : f ≠ 0) :
    (Hex.ZPoly.primitivePart f).size = f.size := by
  have hcontent_ne : (Hex.ZPoly.content f : Int) ≠ 0 := by
    intro hcontent
    apply hf
    have hpart_zero : Hex.ZPoly.primitivePart f = 0 := by
      simpa [Hex.ZPoly.primitivePart] using
        Hex.DensePoly.primitivePart_eq_zero_of_content_eq_zero f
          (by simpa [Hex.ZPoly.content] using hcontent)
    have hreconstruct := Hex.ZPoly.content_mul_primitivePart f
    rw [hcontent, hpart_zero] at hreconstruct
    have : Hex.DensePoly.scale (0 : Int) (0 : Hex.ZPoly) = (0 : Hex.ZPoly) := by
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_scale (R := Int) (0 : Int) (0 : Hex.ZPoly) n
        (Int.zero_mul 0), Hex.DensePoly.coeff_zero]
      exact Int.zero_mul _
    rw [this] at hreconstruct
    exact hreconstruct.symm
  have h_rec := Hex.ZPoly.content_mul_primitivePart f
  have h_scale_size :
      (Hex.DensePoly.scale (Hex.ZPoly.content f) (Hex.ZPoly.primitivePart f)).size =
        (Hex.ZPoly.primitivePart f).size :=
    Hex.ZPoly.scale_size_of_nonzero (Hex.ZPoly.content f)
      (Hex.ZPoly.primitivePart f) hcontent_ne
  calc (Hex.ZPoly.primitivePart f).size
      = (Hex.DensePoly.scale (Hex.ZPoly.content f)
          (Hex.ZPoly.primitivePart f)).size := h_scale_size.symm
    _ = f.size := by rw [h_rec]

/-- Abstract-bound variant of
`natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum`: takes
`B' : Nat`, `hcore_lc_le : (lc core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.

The single precision caller in the proof body is
`size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound`, which requires a
leading-coefficient bound on `scaledLiftedFactorProduct core d T`. That
leading coefficient is `lc core`, so the hypothesis-supplied
`hcore_lc_le` discharges the precondition directly.

Follows the `(B', hcore_lc_le, hprecision)` parameter ordering
established by `representsIntegerFactorAtLift_primitive_of_bound`,
`natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound`,
and `zpoly_primitive_scaledRecombinationCandidate_of_bound`. -/
theorem natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (_hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hprecision : 2 * B' < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T)).natDegree =
      ∑ i ∈ T,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  set lp := liftedFactorProduct d T with hlp_def
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  have hlp_size_pos : 0 < lp.size := zpoly_size_pos_of_monic hlp_monic
  have hcore_lc_ne : Hex.DensePoly.leadingCoeff core ≠ (0 : Int) :=
    ne_of_gt hcore_lc_pos
  have hslp_size :
      (scaledLiftedFactorProduct core d T).size = lp.size := by
    unfold scaledLiftedFactorProduct
    exact size_scale_eq_of_monic_of_ne_zero hcore_lc_ne hlp_monic
  have hslp_lc :
      Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T) =
        Hex.DensePoly.leadingCoeff core := by
    unfold scaledLiftedFactorProduct
    rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero
      (Hex.DensePoly.leadingCoeff core) lp hcore_lc_ne,
      show Hex.DensePoly.leadingCoeff lp = (1 : Int) from hlp_monic]
    ring
  have hslp_lc_pos :
      0 < Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T) := by
    rw [hslp_lc]; exact hcore_lc_pos
  have hslp_lc_bound :
      (Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T)).natAbs ≤
        B' := by
    rwa [hslp_lc]
  have hcl_size :
      (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
          (d.p ^ d.k)).size =
        (scaledLiftedFactorProduct core d T).size :=
    size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound
      hslp_lc_pos hslp_lc_bound hprecision
  have hcl_size_pos :
      0 < (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
          (d.p ^ d.k)).size := by
    rw [hcl_size, hslp_size]; exact hlp_size_pos
  have hcl_ne :
      Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T) (d.p ^ d.k)
        ≠ 0 := by
    intro h
    have h0 :
        (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)).size = 0 := by
      rw [h]; rfl
    omega
  have hpp_size :
      (Hex.ZPoly.primitivePart
          (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k))).size =
        (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)).size :=
    size_primitivePart_eq_of_ne_zero hcl_ne
  have hsc_size :
      (scaledRecombinationCandidate core d T).size = lp.size := by
    show (Hex.normalizeFactorSign
        (Hex.ZPoly.primitivePart
          (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)))).size = lp.size
    rw [size_normalizeFactorSign_eq, hpp_size, hcl_size, hslp_size]
  have hsc_size_pos : 0 < (scaledRecombinationCandidate core d T).size := by
    rw [hsc_size]; exact hlp_size_pos
  have hsc_natDeg :
      (HexPolyZMathlib.toPolynomial
          (scaledRecombinationCandidate core d T)).natDegree =
        (scaledRecombinationCandidate core d T).size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hsc_size_pos]
  have hlp_natDeg :
      (HexPolyZMathlib.toPolynomial lp).natDegree = lp.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hlp_size_pos]
  rw [hsc_natDeg, hsc_size, ← hlp_natDeg, hlp_def, toPolynomial_liftedFactorProduct]
  apply Polynomial.natDegree_prod_of_monic
  intro i _
  show (HexPolyZMathlib.toPolynomial (liftedFactor d i)).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact hd_liftedFactor_monic i

/-- The Mathlib-transported `natDegree` of the scaled recombination candidate
over a lifted-factor subset equals the sum of the Mathlib-transported
`natDegree`s of the selected lifted factors, given primitive + positive-leading
`core` and the Mignotte precision bound.

The candidate goes through `centeredLiftPoly ∘ primitivePart ∘ normalizeFactorSign`
on top of `scaledLiftedFactorProduct = scale (lc core) (liftedFactorProduct)`.
Each step preserves stored size: scaling by the nonzero leading coefficient,
centred-lift under the positive-leading bound, primitive part on a nonzero
input, and sign normalisation. Combined with `lp.size = ∑ + 1` for the monic
lifted-factor product, the candidate's natDegree decomposes as a sum.

Thin wrapper over
`natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum_of_bound` that
instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and discharges
`hcore_lc_le` via `defaultFactorCoeffBound_valid core hcore_ne core
hcore_dvd_self` at index `core.size - 1`, converted to the leading
coefficient via `leadingCoeff_eq_coeff_last`.

Companion scaled variant of `natDegree_toPolynomial_recombinationCandidate_eq_sum`.
Consumed by the scaled cover-at-min chain for the primitive recursive
recombination coverage proof (#4647 / #4737). -/
theorem natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T)).natDegree =
      ∑ i ∈ T,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_ne hcore_lc_pos hd_liftedFactor_monic hcore_lc_le hprecision T

/-- The Mathlib-transported `natDegree` of the corrected recovered candidate
equals the sum of the selected lifted-factor degrees.  The selected product is
centred while monic, then variable-dilated by a nonzero leading coefficient;
both operations preserve the stored degree before primitive/sign
normalisation. -/
theorem natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial
        (liftedRecoveryCandidate core d T)).natDegree =
      ∑ i ∈ T,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  set lp := liftedFactorProduct d T with hlp_def
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  set cl := Hex.centeredLiftPoly lp (d.p ^ d.k) with hcl_def
  have hcl_monic : Hex.DensePoly.Monic cl := by
    rw [hcl_def]
    exact monic_centeredLiftPoly_of_monic hlp_monic hd_modulus
  have hcl_size : cl.size = lp.size := by
    rw [hcl_def]
    exact size_centeredLiftPoly_eq_of_monic hlp_monic hd_modulus
  have hcore_lc_ne : Hex.DensePoly.leadingCoeff core ≠ (0 : Int) :=
    ne_of_gt hcore_lc_pos
  have hdil_size :
      (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl).size =
        cl.size :=
    size_dilate_eq_of_monic_of_ne_zero hcore_lc_ne hcl_monic
  have hcl_size_pos : 0 < cl.size := zpoly_size_pos_of_monic hcl_monic
  have hdil_ne :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl ≠ 0 := by
    intro h
    have h0 :
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl).size = 0 := by
      rw [h]; rfl
    omega
  have hpp_size :
      (Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl)).size =
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl).size :=
    size_primitivePart_eq_of_ne_zero hdil_ne
  have hrec_size :
      (liftedRecoveryCandidate core d T).size = lp.size := by
    show (Hex.normalizeFactorSign
        (Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
            (Hex.centeredLiftPoly (liftedFactorProduct d T) (d.p ^ d.k))))).size =
        lp.size
    rw [← hlp_def, ← hcl_def, size_normalizeFactorSign_eq, hpp_size,
      hdil_size, hcl_size]
  have hrec_size_pos : 0 < (liftedRecoveryCandidate core d T).size := by
    rw [hrec_size, ← hcl_size]
    exact hcl_size_pos
  have hlp_size_pos : 0 < lp.size := by
    rw [← hcl_size]
    exact hcl_size_pos
  have hrec_natDeg :
      (HexPolyZMathlib.toPolynomial
          (liftedRecoveryCandidate core d T)).natDegree =
        (liftedRecoveryCandidate core d T).size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hrec_size_pos]
  have hlp_natDeg :
      (HexPolyZMathlib.toPolynomial lp).natDegree = lp.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hlp_size_pos]
  rw [hrec_natDeg, hrec_size, ← hlp_natDeg, hlp_def, toPolynomial_liftedFactorProduct]
  apply Polynomial.natDegree_prod_of_monic
  intro i _
  show (HexPolyZMathlib.toPolynomial (liftedFactor d i)).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact hd_liftedFactor_monic i

/-- Abstract-bound wrapper for
`natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum`.  The bound and
precision hypotheses are used only to derive the modulus lower bound from the
positive leading coefficient. -/
theorem natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial
        (liftedRecoveryCandidate core d T)).natDegree =
      ∑ i ∈ T,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  have hB_pos : 0 < B' := by
    have hlc_nat_pos :
        0 < (Hex.DensePoly.leadingCoeff core).natAbs :=
      Int.natAbs_pos.mpr (ne_of_gt hcore_lc_pos)
    omega
  have hd_modulus : 2 ≤ d.p ^ d.k := by
    have htwo_le : 2 ≤ 2 * B' := by omega
    omega
  exact natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum
    hcore_lc_pos hd_modulus hd_liftedFactor_monic T

/-- Abstract-bound variant of
`natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`,
`hcore_lc_le : (lc core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.

The unscaled `_hrec_scaled` step from the existing proof is dropped
entirely — its result was never consumed — and the centred-lift
recovery call is routed through
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound`
in place of the core-shape recovery. Both changes make this sibling
independent of `scaledRecombinationCandidate_eq_factor_of_recovery`
and hence of the scaled recovery-candidate `_of_bound` chain (#4882).

Note: this sibling needs `hcore_lc_le` in addition to `hvalid`
because the size-preservation step
`size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound` consumes a
leading-coefficient bound on `scaledLiftedFactorProduct core d S`,
whose leading coefficient is `lc core`. Without a `B'`-shape bound
on `lc core` itself, the abstract-precision hypothesis cannot
discharge that lemma's separation requirement. The existing
core-shape wrapper supplies this from
`defaultFactorCoeffBound_valid core hcore_ne core hcore_dvd_self`.
-/
theorem natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d}
    (B' : Nat)
    (_hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    (HexPolyZMathlib.toPolynomial factor).natDegree =
      ∑ i ∈ S,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  -- The partition pins the represented factor to its sound recovered candidate.
  have hrec_eq : liftedRecoveryCandidate core d S = factor :=
    hpartition.liftedRecoveryCandidate_eq hfactor_irr hfactor_dvd_target hSJ hrep
  rw [← hrec_eq]
  exact natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum_of_bound
    B' hcore_lc_pos hcore_lc_le hd_liftedFactor_monic hprecision S

/--
Primitive + positive-leading-core variant of
`natDegree_toPolynomial_eq_sum_of_represents` (#4646).

For primitive non-monic `core`, the represented factor's natDegree equals the
sum of natDegrees of the selected lifted factors. The proof routes through the
scaled recovery identity `scaledRecombinationCandidate core d S = factor`
(#4652) and the size identities
`factor.size = (scaledLiftedFactorProduct core d S).size =
 (liftedFactorProduct d S).size`. Scaling by `C (lc core)` and the centred lift
both preserve stored size under the Mignotte half-window bound on `lc core`,
so the sum decomposition `natDegree_prod_of_monic` over `liftedFactorProduct`
applies unchanged. The `hcore_primitive` and `hfactor_irr` hypotheses are
threaded for API uniformity with the monic variant but are not used by the
proof; the natDegree extraction depends only on the leading-coefficient bound
and the primitive/sign-normalised facts on `factor` consumed by #4652.

This is a thin wrapper over
`natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd` and the
leading-coefficient bound via
`defaultFactorCoeffBound_valid core hcore_ne core hcore_dvd_self`.
-/
theorem natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hdvd : factor ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d factor S) :
    (HexPolyZMathlib.toPolynomial factor).natDegree =
      ∑ i ∈ S,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos hd_liftedFactor_monic
    hpartition hfactor_irr hfactor_dvd_target hSJ hrep hprecision

/-- Converse to `toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord`: if the
transported polynomial is non-zero and a non-unit, then the executable
`shouldRecordPolynomialFactor` check passes.  Used to package executable
witnesses for one recombination split from Mathlib-side irreducibility. -/
theorem shouldRecordPolynomialFactor_of_toPolynomial_ne_zero_not_isUnit
    {f : Hex.ZPoly}
    (hne_zero : HexPolyZMathlib.toPolynomial f ≠ 0)
    (hnonunit : ¬ IsUnit (HexPolyZMathlib.toPolynomial f)) :
    Hex.shouldRecordPolynomialFactor f = true := by
  have hf_ne_zero : f ≠ 0 := fun hf => hne_zero (by
    rw [hf]; exact HexPolyZMathlib.toPolynomial_zero)
  have hf_ne_one : f ≠ 1 := fun hf => hnonunit
    ((HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mp (by rw [hf]; left; rfl))
  have hf_ne_neg_one : f ≠ Hex.DensePoly.C (-1) := fun hf => hnonunit
    ((HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mp (by rw [hf]; right; rfl))
  unfold Hex.shouldRecordPolynomialFactor
  simp [hf_ne_zero, hf_ne_one, hf_ne_neg_one]

/-- An irreducible (after transport) `Hex.ZPoly` value passes the executable
`shouldRecordPolynomialFactor` check.  Combines the previous lemma with
`Irreducible`'s structural projections. -/
theorem shouldRecordPolynomialFactor_of_irreducible_toPolynomial
    {f : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f)) :
    Hex.shouldRecordPolynomialFactor f = true :=
  shouldRecordPolynomialFactor_of_toPolynomial_ne_zero_not_isUnit
    hirr.ne_zero hirr.not_isUnit

/-- One-step `shouldRecord` discharge for a recombination split: when the
candidate equals an irreducible integer factor, the executable check passes. -/
theorem shouldRecord_recombinationCandidate_of_eq_factor
    {factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    Hex.shouldRecordPolynomialFactor (recombinationCandidate d S) = true := by
  rw [heq]
  exact shouldRecordPolynomialFactor_of_irreducible_toPolynomial hirr

/-- One-step `exactQuotient?` discharge for a recombination split: when the
candidate equals an integer divisor of `core` and is monic of positive degree,
the executable exact-division check returns `some` of the proof-side cofactor. -/
theorem exactQuotient?_recombinationCandidate_eq_some_of_eq_factor
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (heq : recombinationCandidate d S = factor)
    (hmonic : Hex.DensePoly.Monic factor)
    (hpos : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ core) :
    ∃ quotient,
      Hex.exactQuotient? core (recombinationCandidate d S) = some quotient ∧
        quotient * recombinationCandidate d S = core := by
  obtain ⟨q, hq⟩ := hdvd
  -- hq : core = factor * q
  have hmul : q * factor = core := by
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hq.symm
  refine ⟨q, ?_, ?_⟩
  · rw [heq]
    exact Hex.exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree hmonic hpos hmul
  · rw [heq]; exact hmul

/-- Scaled-candidate counterpart of `shouldRecord_recombinationCandidate_of_eq_factor`.
When the scaled candidate equals an irreducible integer factor, the executable
record check passes. -/
theorem shouldRecord_scaledRecombinationCandidate_of_eq_factor
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (heq : scaledRecombinationCandidate core d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    Hex.shouldRecordPolynomialFactor (scaledRecombinationCandidate core d S) =
      true := by
  rw [heq]
  exact shouldRecordPolynomialFactor_of_irreducible_toPolynomial hirr

/-- Scaled-candidate counterpart of `exactQuotient?_recombinationCandidate_eq_some_of_eq_factor`.
When the scaled candidate equals a monic integer divisor of `target` of
positive degree, the executable exact-division check on `target` returns
`some` of the proof-side cofactor.

Used by the primitive recursive coverage proof in #4647 against the new
`Hex.scaledRecombinationSearchModAux` executable, paired with the recovery
identity `scaledRecombinationCandidate_eq_factor_of_recovery` from #4652. -/
theorem exactQuotient?_scaledRecombinationCandidate_eq_some_of_eq_factor
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (heq : scaledRecombinationCandidate core d S = factor)
    (hmonic : Hex.DensePoly.Monic factor)
    (hpos : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ target) :
    ∃ quotient,
      Hex.exactQuotient? target (scaledRecombinationCandidate core d S) =
        some quotient ∧
        quotient * scaledRecombinationCandidate core d S = target := by
  obtain ⟨q, hq⟩ := hdvd
  -- hq : target = factor * q
  have hmul : q * factor = target := by
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hq.symm
  refine ⟨q, ?_, ?_⟩
  · rw [heq]
    exact Hex.exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree hmonic hpos hmul
  · rw [heq]; exact hmul

/-- Non-monic counterpart of
`exactQuotient?_scaledRecombinationCandidate_eq_some_of_eq_factor`.
When the scaled candidate equals an integer divisor of `target` with positive
leading coefficient and positive degree, the executable exact-division check
on `target` returns `some` of the proof-side cofactor.

Drops `Monic factor` in favour of `0 < lc factor`, routing through
`exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq` instead of the
monic-only `exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree`.  Consumed
by the primitive recursive coverage proof in #4647, paired with the recovery
identity `scaledRecombinationCandidate_eq_factor_of_recovery` from #4652 and
the primitive + positive-leading bound from
`representsIntegerFactorAtLift_primitive` (#4644). -/
theorem exactQuotient?_scaledRecombinationCandidate_eq_some_of_eq_factor_of_primitive_pos_lc
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (heq : scaledRecombinationCandidate core d S = factor)
    (hpos_lc : 0 < Hex.DensePoly.leadingCoeff factor)
    (hpos : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ target) :
    ∃ quotient,
      Hex.exactQuotient? target (scaledRecombinationCandidate core d S) =
        some quotient ∧
        quotient * scaledRecombinationCandidate core d S = target := by
  obtain ⟨q, hq⟩ := hdvd
  -- hq : target = factor * q
  have hmul : q * factor = target := by
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hq.symm
  refine ⟨q, ?_, ?_⟩
  · rw [heq]
    exact Hex.exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq hpos_lc hpos hmul
  · rw [heq]; exact hmul

/--
Executable recombination-search success for one lifted subset.

Once a proof-side lifted subset is known to contain the first remaining local
factor, its ordered `(selected, rest)` partition is one of the splits traversed
by `recombinationSearchMod`.  If the subset's executable candidate is an
irreducible integer divisor of the current target and the recursive search on
the quotient/rest problem succeeds, the surface recombination search succeeds.
-/
theorem recombinationSearchMod_isSome_of_liftedSubset_candidate_eq_factor
    {core factor quotient : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (hcore_ne_one : core ≠ 1)
    (hsize_pos : 0 < d.liftedFactors.size)
    (hfirst : (⟨0, hsize_pos⟩ : LiftedFactorIndex d) ∈ S)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hsearch_rest :
      (Hex.recombinationSearchModAux quotient (d.p ^ d.k)
        (liftedSubsetRejectedList d S) d.liftedFactors.toList.length).isSome = true)
    (hquot :
      Hex.exactQuotient? core (recombinationCandidate d S) = some quotient) :
    (Hex.recombinationSearchMod core (d.p ^ d.k)
        d.liftedFactors.toList).isSome = true := by
  refine
    Hex.recombinationSearchMod_isSome_of_step
      (target := core)
      (candidate := factor)
      (quotient := quotient)
      (modulus := d.p ^ d.k)
      (localFactors := d.liftedFactors.toList)
      (selected := liftedSubsetSelectedList d S)
      (rest := liftedSubsetRejectedList d S)
      hcore_ne_one
      (liftedSubsetSplit_mem_subsetSplitsWithFirst d S hsize_pos hfirst)
      ?_
      (by
        simpa [heq] using
          shouldRecord_recombinationCandidate_of_eq_factor heq hirr)
      ?_
      hsearch_rest
  · simpa [recombinationCandidate] using heq.symm
  · simpa [heq] using hquot

/--
Matched-rest variant of
`recombinationSearchMod_isSome_of_liftedSubset_candidate_eq_factor`.

At a recursive recombination state, `localFactors` is no longer the full
lifted-factor list; it is the order-preserving list of the remaining proof-side
indices `J`.  If a represented subset `S ⊆ J` contains the current minimum
remaining index, the matching predicate identifies its executable split and
the ordinary one-step search lemma applies.
-/
theorem recombinationSearchModAux_isSome_of_liftedSubset_candidate_eq_factor_of_matches
    {target factor quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    (htarget_ne_one : target ≠ 1)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hSJ : S ⊆ J)
    (hne : J.Nonempty)
    (hmin : J.min' hne ∈ S)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hsearch_rest :
      (Hex.recombinationSearchModAux quotient (d.p ^ d.k)
        (liftedSubsetSelectedList d (J \ S)) fuel).isSome = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d S) = some quotient) :
    (Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors (fuel + 1)).isSome =
      true := by
  refine
    Hex.recombinationSearchModAux_isSome_of_step
      (target := target)
      (candidate := factor)
      (quotient := quotient)
      (modulus := d.p ^ d.k)
      (localFactors := localFactors)
      (selected := liftedSubsetSelectedList d S)
      (rest := liftedSubsetSelectedList d (J \ S))
      (fuel := fuel)
      htarget_ne_one
      (liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
        hmatches hSJ hne hmin)
      ?_
      (by
        simpa [heq] using
          shouldRecord_recombinationCandidate_of_eq_factor heq hirr)
      ?_
      hsearch_rest
  · simpa [recombinationCandidate] using heq.symm
  · simpa [heq] using hquot

/--
Exact-output matched-rest variant of
`recombinationSearchModAux_isSome_of_liftedSubset_candidate_eq_factor_of_matches`.

When the split selected from a matched remaining-index set is the first
successful executable split, the returned factor list has the represented
factor at its head. This is the local first-success lemma needed by the
recursive coverage proof before it reasons about earlier successful splits.
-/
theorem recombinationSearchModAux_first_success_witness_of_liftedSubset_candidate_eq_factor_of_matches
    {target factor quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat} {restFactors : List Hex.ZPoly}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (htarget_ne_one : target ≠ 1)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hSJ : S ⊆ J)
    (hne : J.Nonempty)
    (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S)) ::
            suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          Hex.normalizeFactorSign <|
            Hex.ZPoly.primitivePart <|
              Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
                (d.p ^ d.k)
        if Hex.shouldRecordPolynomialFactor candidate' then
          match Hex.exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match Hex.recombinationSearchModAux quotient' (d.p ^ d.k) split.2 fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hsearch_rest :
      Hex.recombinationSearchModAux quotient (d.p ^ d.k)
        (liftedSubsetSelectedList d (J \ S)) fuel = some restFactors)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d S) = some quotient) :
    ∃ result,
      Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors (fuel + 1) =
          some result ∧
        ∃ emitted ∈ result,
          Associated (HexPolyZMathlib.toPolynomial emitted)
            (HexPolyZMathlib.toPolynomial factor) := by
  have _hsplit_mem :
      (liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S)) ∈
        Hex.subsetSplitsWithFirst localFactors :=
    liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
      hmatches hSJ hne hmin
  refine ⟨factor :: restFactors, ?_, ?_⟩
  · exact
      Hex.recombinationSearchModAux_eq_some_of_step_of_prefix_none
        (target := target)
        (candidate := factor)
        (quotient := quotient)
        (modulus := d.p ^ d.k)
        (localFactors := localFactors)
        (selected := liftedSubsetSelectedList d S)
        (rest := liftedSubsetSelectedList d (J \ S))
        (restFactors := restFactors)
        (pre := pre)
        (suffix := suffix)
        (fuel := fuel)
        htarget_ne_one hsplits hprefix
        (by simpa [recombinationCandidate] using heq.symm)
        (by
          simpa [heq] using
            shouldRecord_recombinationCandidate_of_eq_factor heq hirr)
        (by simpa [heq] using hquot)
        hsearch_rest
  · refine ⟨factor, by simp, ?_⟩
    exact Associated.refl (HexPolyZMathlib.toPolynomial factor)

/--
Variant of
`recombinationSearchMod_isSome_of_liftedSubset_candidate_eq_factor` that
discharges the executable quotient check from ordinary divisibility plus the
monic positive-degree hypotheses required by `exactQuotient?`.
-/
theorem recombinationSearchMod_isSome_of_liftedSubset_factor_dvd
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne_one : core ≠ 1)
    (hsize_pos : 0 < d.liftedFactors.size)
    (hfirst : (⟨0, hsize_pos⟩ : LiftedFactorIndex d) ∈ S)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hmonic : Hex.DensePoly.Monic factor)
    (hdegree : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ core)
    (hsearch_rest :
      ∀ quotient,
        Hex.exactQuotient? core (recombinationCandidate d S) = some quotient →
        (Hex.recombinationSearchModAux quotient (d.p ^ d.k)
          (liftedSubsetRejectedList d S) d.liftedFactors.toList.length).isSome = true) :
    (Hex.recombinationSearchMod core (d.p ^ d.k)
        d.liftedFactors.toList).isSome = true := by
  rcases
    exactQuotient?_recombinationCandidate_eq_some_of_eq_factor
      (core := core) (factor := factor) (d := d) (S := S)
      heq hmonic hdegree hdvd with
    ⟨quotient, hquot, _hmul⟩
  exact
    recombinationSearchMod_isSome_of_liftedSubset_candidate_eq_factor
      (core := core) (factor := factor) (quotient := quotient) (d := d)
      (S := S) hcore_ne_one hsize_pos hfirst heq hirr
      (hsearch_rest quotient hquot) hquot

/--
Matched-rest variant of
`recombinationSearchMod_isSome_of_liftedSubset_factor_dvd`: discharges the
executable quotient check from divisibility plus monic positive-degree
hypotheses at the recursive recombination state, where the running
`localFactors` list matches an arbitrary remaining-index set `J` and the
candidate subset `S ⊆ J` contains the current minimum remaining index.
-/
theorem recombinationSearchModAux_isSome_of_liftedSubset_factor_dvd_of_matches
    {target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    (htarget_ne_one : target ≠ 1)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hSJ : S ⊆ J)
    (hne : J.Nonempty)
    (hmin : J.min' hne ∈ S)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hmonic : Hex.DensePoly.Monic factor)
    (hdegree : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ target)
    (hsearch_rest :
      ∀ quotient,
        Hex.exactQuotient? target (recombinationCandidate d S) = some quotient →
        (Hex.recombinationSearchModAux quotient (d.p ^ d.k)
          (liftedSubsetSelectedList d (J \ S)) fuel).isSome = true) :
    (Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors
        (fuel + 1)).isSome = true := by
  rcases
    exactQuotient?_recombinationCandidate_eq_some_of_eq_factor
      (core := target) (factor := factor) (d := d) (S := S)
      heq hmonic hdegree hdvd with
    ⟨quotient, hquot, _hmul⟩
  exact
    recombinationSearchModAux_isSome_of_liftedSubset_candidate_eq_factor_of_matches
      (target := target) (factor := factor) (quotient := quotient) (d := d)
      (J := J) (S := S) (localFactors := localFactors) (fuel := fuel)
      htarget_ne_one hmatches hSJ hne hmin heq hirr
      (hsearch_rest quotient hquot) hquot

/--
Proof-facing package for a first successful recombination split.

The executable theorem in `HexBerlekampZassenhaus.Basic` returns an exact
`some (candidate :: restFactors)` value.  This wrapper exposes the pieces that
Mathlib-side coverage proofs need without requiring downstream statements to
mention the internals of `firstSome`: the returned list, head membership,
`shouldRecord`, exact quotient witness, and recursive-rest success.
-/
theorem recombinationSearchMod_first_success_witness_of_step_of_prefix_none
    {target candidate quotient : Hex.ZPoly} {modulus : Nat}
    {localFactors selected rest restFactors : List Hex.ZPoly}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (htarget_ne_one : target ≠ 1)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors = pre ++ (selected, rest) :: suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          Hex.normalizeFactorSign <|
            Hex.ZPoly.primitivePart <|
              Hex.centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        if Hex.shouldRecordPolynomialFactor candidate' then
          match Hex.exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match Hex.recombinationSearchModAux quotient' modulus split.2
                  localFactors.length with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (hcandidate_def :
      candidate = Hex.normalizeFactorSign
        (Hex.ZPoly.primitivePart
          (Hex.centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : Hex.shouldRecordPolynomialFactor candidate = true)
    (hquot : Hex.exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      Hex.recombinationSearchModAux quotient modulus rest localFactors.length =
        some restFactors) :
    ∃ factors,
      Hex.recombinationSearchMod target modulus localFactors = some factors ∧
        candidate ∈ factors ∧
        Hex.shouldRecordPolynomialFactor candidate = true ∧
        (∃ quotient,
          Hex.exactQuotient? target candidate = some quotient ∧
            Hex.recombinationSearchModAux quotient modulus rest
                localFactors.length = some restFactors) := by
  refine ⟨candidate :: restFactors, ?_, ?_, hrecord, ?_⟩
  · exact
      Hex.recombinationSearchMod_eq_some_of_step_of_prefix_none
        htarget_ne_one hsplits hprefix hcandidate_def hrecord hquot
        hsearch_rest
  · simp
  · exact ⟨quotient, hquot, hsearch_rest⟩


/-- A `Hex.ZPoly` factor that passes the executable `shouldRecordPolynomialFactor`
check is non-zero and not a unit after transport to `Polynomial ℤ`.  The
executable check rejects `0`, `1`, and `-1`, which are exactly the zero
and unit constants on the Mathlib side. -/
theorem toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
    {f : Hex.ZPoly} (h : Hex.shouldRecordPolynomialFactor f = true) :
    HexPolyZMathlib.toPolynomial f ≠ 0 ∧
      ¬ IsUnit (HexPolyZMathlib.toPolynomial f) := by
  rw [Hex.shouldRecordPolynomialFactor] at h
  -- `h : (f ≠ 0 && f ≠ 1 && f ≠ DensePoly.C (-1)) = true`
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hne_zero, hne_one⟩, hne_neg_one⟩ := h
  have hne_zero' : f ≠ 0 := by simpa using hne_zero
  have hne_one' : f ≠ 1 := by simpa using hne_one
  have hne_neg_one' : f ≠ Hex.DensePoly.C (-1) := by simpa using hne_neg_one
  refine ⟨?_, ?_⟩
  · intro hpoly
    apply hne_zero'
    apply HexPolyZMathlib.equiv.injective
    simpa using hpoly
  · intro hunit
    have hisUnit : Hex.ZPoly.IsUnit f :=
      (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mpr hunit
    rcases hisUnit with hone | hneg_one
    · exact hne_one' hone
    · exact hne_neg_one' hneg_one

/--
Forward lemma carrying a successful executable recombination candidate quotient
to a proof-side irreducible divisor of `target` together with its representing
subset under a `LiftedFactorSubsetPartition`.

Given a `LiftedFactorSubsetPartition core d J target` and an arbitrary lifted
subset `T`, the hypotheses

* `Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true`, and
* `Hex.exactQuotient? target (recombinationCandidate d T) = some quotient`

are the two executable facts that any "non-`none` body" of one step in the
recombination search produces.  The lemma packages from these:

* the explicit product witness `quotient * recombinationCandidate d T = target`
  (via `Hex.exactQuotient?_product`),
* the proof-side divisibility `recombinationCandidate d T ∣ target`, and
* an irreducible factor `g` of the candidate (via UFD existence in
  `Polynomial ℤ`) that, via the partition's inherited
  `HenselSubsetCorrespondenceRest.exists_subset`, is itself an irreducible
  divisor of `target` with representing subset `S ⊆ J`.

Used by the prefix-none assembler in the recursive coverage proof for
`Hex.recombinationSearchModAux` (#4367/#4301) to compare an earlier executable
split's selected subset against the partition's representing subsets using
`pairwise_disjoint` / `unique_up_to_associated`.
-/
theorem exists_representingSubset_dvd_recombinationCandidate_of_exactQuotient
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    quotient * recombinationCandidate d T = target ∧
      recombinationCandidate d T ∣ target ∧
        ∃ (g : Hex.ZPoly) (S : LiftedFactorSubset d),
          Irreducible (HexPolyZMathlib.toPolynomial g) ∧
          g ∣ target ∧
          g ∣ recombinationCandidate d T ∧
          S ⊆ J ∧
          RepresentsIntegerFactorAtLift core d g S := by
  -- Quotient equation and divisibility from `exactQuotient?_product`.
  have hmul : quotient * recombinationCandidate d T = target :=
    Hex.exactQuotient?_product hquot
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  -- Candidate is nonzero and not a unit after transport to `Polynomial ℤ`.
  obtain ⟨hcand_poly_ne_zero, hcand_poly_nonunit⟩ :=
    toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord
  -- UFD existence: extract an irreducible factor of the candidate in
  -- `Polynomial ℤ`.
  -- Extract a sign-normalized irreducible factor of the candidate, so the
  -- narrowed `exists_subset` (restricted to sign-normalized representatives)
  -- applies.
  obtain ⟨g, hg_irr_toPoly, hg_dvd_cand, hg_norm_sign⟩ :=
    exists_signNormalized_irreducible_factor hcand_poly_nonunit hcand_poly_ne_zero
  have hg_dvd_target : g ∣ target := zpoly_dvd_trans hg_dvd_cand hcand_dvd_target
  -- Apply the partition's inherited `exists_subset` to obtain the representing
  -- subset for `g`.
  obtain ⟨S, hSJ, hSrep⟩ :=
    hpartition.exists_subset hg_norm_sign hg_irr_toPoly hg_dvd_target
  exact ⟨hmul, hcand_dvd_target, g, S, hg_irr_toPoly, hg_dvd_target, hg_dvd_cand,
    hSJ, hSrep⟩

end

end HexBerlekampZassenhausMathlib
