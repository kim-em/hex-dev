/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.ModularPolynomial
public import HexBerlekampZassenhausMathlib.Factorization


public section
set_option backward.proofsInPublic true

/-!
# Integer polynomial irreducibility certificates

Soundness of the modular subset-degree and linear irreducibility
certificates.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/--
`hasSubsetDegreeAux` is the recursive subset-sum check used by
`Hex.PrimeFactorData.hasSubsetDegree`. If some sub-multiset of `L` sums to
`target`, the recursive procedure detects it.
-/
private theorem hasSubsetDegreeAux_eq_true_of_exists_subMultiset
    {L : List Nat} {target : Nat}
    {S : Multiset Nat} (hS : S ≤ (L : Multiset Nat)) (hsum : S.sum = target) :
    Hex.PrimeFactorData.hasSubsetDegreeAux L target = true := by
  induction L generalizing target S with
  | nil =>
    have hS_zero : S = 0 := by
      have : S ≤ 0 := by simpa using hS
      exact Multiset.le_zero.mp this
    rw [hS_zero] at hsum
    simp [Hex.PrimeFactorData.hasSubsetDegreeAux, ← hsum]
  | cons d L ih =>
    rw [← Multiset.cons_coe] at hS
    by_cases hd_mem : d ∈ S
    · -- d ∈ S; remove it and recurse on (target - d)
      have hd_le_target : d ≤ target := by
        rw [← hsum]
        exact Multiset.single_le_sum (fun _ _ => Nat.zero_le _) d hd_mem
      have hS_eq : S = d ::ₘ S.erase d := (Multiset.cons_erase hd_mem).symm
      have hT_le_L : S.erase d ≤ (L : Multiset Nat) := by
        have herase : S.erase d ≤ (d ::ₘ (L : Multiset Nat)).erase d :=
          Multiset.erase_le_erase d hS
        rwa [Multiset.erase_cons_head] at herase
      have hT_sum : (S.erase d).sum = target - d := by
        have hsum' : (d ::ₘ S.erase d).sum = target := hS_eq ▸ hsum
        rw [Multiset.sum_cons] at hsum'
        omega
      have hrec := ih (S := S.erase d) hT_le_L hT_sum
      simp [Hex.PrimeFactorData.hasSubsetDegreeAux, hd_le_target, hrec]
    · -- d ∉ S; reduce to L
      have hS_le_L : S ≤ (L : Multiset Nat) := (Multiset.le_cons_of_notMem hd_mem).mp hS
      have hrec := ih (S := S) hS_le_L hsum
      simp [Hex.PrimeFactorData.hasSubsetDegreeAux, hrec]

/-- Helper: extract `checkCertAtFactor` at a specific index from `checkFactorCerts`. -/
private theorem checkCertAtFactor_of_checkFactorCerts
    (primeData : Hex.PrimeFactorData)
    (hcheck : primeData.checkFactorCerts = true)
    (i : Nat) (hi_deg : i < primeData.factorDegrees.size)
    (hi_polys : i < primeData.factorPolys.size)
    (hi_certs : i < primeData.factorCerts.size) :
    Hex.PrimeFactorData.checkCertAtFactor primeData
      primeData.factorDegrees[i] primeData.factorPolys[i] primeData.factorCerts[i] = true := by
  simp only [Hex.PrimeFactorData.checkFactorCerts, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hcheck
  obtain ⟨_, hall⟩ := hcheck
  have hmem :
      (primeData.factorDegrees[i],
        (primeData.factorPolys[i], primeData.factorCerts[i])) ∈
      primeData.factorDegrees.toList.zip
        (primeData.factorPolys.toList.zip primeData.factorCerts.toList) := by
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · simp only [List.length_zip, Array.length_toList]
      omega
    · simp only [List.getElem_zip, Array.getElem_toList]
  exact hall _ hmem

/--
The Mathlib transport of an executable factor recorded in a
`PrimeFactorData` block has natural degree equal to the recorded factor
degree. This follows directly from the executable `degree?` slot and the
Mathlib basis-size identification.
-/
private theorem natDegree_toMathlibPolynomial_factorPolys_eq
    (primeData : Hex.PrimeFactorData)
    (hcheck : primeData.checkFactorCerts = true)
    (i : Nat) (hi_polys : i < primeData.factorPolys.size)
    (hi_deg : i < primeData.factorDegrees.size)
    (hi_certs : i < primeData.factorCerts.size) :
    letI := primeData.bounds
    (HexBerlekampMathlib.toMathlibPolynomial primeData.factorPolys[i]).natDegree =
      primeData.factorDegrees[i] := by
  letI := primeData.bounds
  have hpair :=
    checkCertAtFactor_of_checkFactorCerts primeData hcheck i hi_deg hi_polys hi_certs
  have hdegree :
      primeData.factorPolys[i].degree? = some primeData.factorDegrees[i] := by
    simp only [Hex.PrimeFactorData.checkCertAtFactor, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hpair
    exact hpair.1.2
  rw [HexBerlekampMathlib.natDegree_toMathlibPolynomial_eq_basisSize]
  show primeData.factorPolys[i].degree?.getD 0 = _
  rw [hdegree]
  rfl

/--
The executable integer-polynomial irreducibility checker is sound after
transport to Mathlib's polynomial model, under the standard certificate
side-conditions: each per-prime block uses a prime modulus, the input is
primitive, and the input is non-constant. Primality is needed for Rabin
irreducibility lifting and `(ZMod p)[X]` UFD reasoning; primitivity and
non-constancy rule out trivially reducible inputs whose recorded obstructions
would otherwise be vacuous.
-/
theorem checkIrreducibleCert_sound
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hprime : ∀ primeData ∈ cert.perPrime.toList, Nat.Prime primeData.p)
    (hprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive)
    (hpos : 0 < (HexPolyZMathlib.toPolynomial f).natDegree) :
    Hex.checkIrreducibleCert f cert = true →
      Irreducible (HexPolyZMathlib.toPolynomial f) := by
  intro hcert
  set F := HexPolyZMathlib.toPolynomial f with hF_def
  have hF_ne : F ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hpos; exact absurd hpos (lt_irrefl 0)
  refine ⟨?_, ?_⟩
  · intro hunit
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · intro a b hab
    by_contra hcontra
    push Not at hcontra
    obtain ⟨ha_not_unit, hb_not_unit⟩ := hcontra
    have ha_ne : a ≠ 0 := fun h => hF_ne (by rw [hab, h, zero_mul])
    have hb_ne : b ≠ 0 := fun h => hF_ne (by rw [hab, h, mul_zero])
    have ha_dvd : a ∣ F := ⟨b, hab⟩
    have hb_dvd : b ∣ F := ⟨a, by rw [hab]; ring⟩
    have ha_prim : a.IsPrimitive := isPrimitive_of_dvd hprim ha_dvd
    have hb_prim : b.IsPrimitive := isPrimitive_of_dvd hprim hb_dvd
    have hdegSum : a.natDegree + b.natDegree = F.natDegree := by
      rw [hab, Polynomial.natDegree_mul ha_ne hb_ne]
    -- Helper: from a non-unit primitive divisor with positive natDegree, contradict.
    have hcontradict :
        ∀ (c d : Polynomial ℤ), c * d = F → c ≠ 0 → d ≠ 0 →
          c.IsPrimitive → ¬ IsUnit c →
          c.natDegree ≤ d.natDegree → False := by
      intro c d hcd_eq hc_ne hd_ne hc_prim hc_not_unit hcd_le
      -- c has positive natDegree (non-unit primitive)
      have hc_natDeg_pos : 0 < c.natDegree := by
        rcases Nat.eq_zero_or_pos c.natDegree with hzero | hposc
        · exfalso
          have hc_const : c = Polynomial.C (c.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero hzero
          have hc_coeff_unit : IsUnit (c.coeff 0) := by
            apply hc_prim
            rw [← hc_const]
          rw [hc_const] at hc_not_unit
          exact hc_not_unit (Polynomial.isUnit_C.mpr hc_coeff_unit)
        · exact hposc
      -- natDegree c ≤ F.natDegree / 2
      have hcd_sum : c.natDegree + d.natDegree = F.natDegree := by
        rw [← hcd_eq, Polynomial.natDegree_mul hc_ne hd_ne]
      have hc_le_half : c.natDegree ≤ F.natDegree / 2 := by omega
      -- c.natDegree ∈ candidateFactorDegrees f
      have hF_natDeg : F.natDegree = f.degree?.getD 0 :=
        HexPolyMathlib.natDegree_toPolynomial f
      have htarget_mem :
          c.natDegree ∈ Hex.ZPolyIrreducibilityCertificate.candidateFactorDegrees f := by
        unfold Hex.ZPolyIrreducibilityCertificate.candidateFactorDegrees
        rw [List.mem_map]
        refine ⟨c.natDegree - 1, ?_, ?_⟩
        · rw [List.mem_range, ← hF_natDeg]
          omega
        · omega
      -- Extract obstruction → primeData with hasSubsetDegree false
      have hobsFor :=
        Hex.checkIrreducibleCert_obstructs_candidate_degrees f cert hcert _ htarget_mem
      simp only [Hex.ZPolyIrreducibilityCertificate.hasObstructionFor, List.any_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hobsFor
      obtain ⟨obs, _, ⟨hobs_target_eq, hobs_valid⟩⟩ := hobsFor
      -- Get the primeData referenced by this obstruction
      have hobs_primeIndex :
          ∃ primeData : Hex.PrimeFactorData,
            cert.primeDataAt? obs.primeIndex = some primeData := by
        simp only [Hex.DegreeObstruction.checkForCertificate, Bool.and_eq_true,
          decide_eq_true_eq] at hobs_valid
        rcases hpa : cert.primeDataAt? obs.primeIndex with _ | primeData
        · simp [hpa] at hobs_valid
        · exact ⟨primeData, rfl⟩
      obtain ⟨primeData, hpa⟩ := hobs_primeIndex
      have hno_subset :
          primeData.hasSubsetDegree obs.targetDegree = false :=
        Hex.degreeObstruction_no_subset_degree f cert obs primeData hobs_valid hpa
      -- primeData is in cert.perPrime.toList
      have hpd_mem : primeData ∈ cert.perPrime.toList := by
        have hpa' := hpa
        unfold Hex.ZPolyIrreducibilityCertificate.primeDataAt? at hpa'
        rcases hdrop : cert.perPrime.toList.drop obs.primeIndex with _ | ⟨head, tail⟩
        · rw [hdrop] at hpa'; simp at hpa'
        · rw [hdrop] at hpa'
          rw [Option.some.injEq] at hpa'
          have hmem_drop : head ∈ cert.perPrime.toList.drop obs.primeIndex := by
            rw [hdrop]; exact List.mem_cons_self
          rw [← hpa']
          exact List.mem_of_mem_drop hmem_drop
      -- Extract `Nat.Prime primeData.p` from hypothesis
      have hp_prime : Nat.Prime primeData.p := hprime primeData hpd_mem
      haveI : Fact (Nat.Prime primeData.p) := ⟨hp_prime⟩
      letI := primeData.bounds
      -- Extract checkForPolynomial fact
      have hcheckPoly := Hex.checkIrreducibleCert_prime_data f cert hcert primeData hpd_mem
      have hgood := Hex.checkIrreducibleCert_isGoodPrime f cert hcert primeData hpd_mem
      have hfacts_align :=
        Hex.checkIrreducibleCert_certificate_alignment f cert hcert primeData hpd_mem
      -- leading coefficient ≠ 0 mod p (from isGoodPrime)
      have hlc_modP_ne : Hex.ZPoly.leadingCoeffModP f primeData.p ≠ 0 := by
        have := Hex.isGoodPrime_leadingCoeffAdmissible f primeData.p hgood
        unfold Hex.leadingCoeffAdmissible at this
        exact this
      -- Identify `(Int.castRingHom (ZMod p)) F.leadingCoeff = toZMod (leadingCoeffModP f p)`
      have hF_lc_eq :
          (Int.castRingHom (ZMod primeData.p)) F.leadingCoeff =
            HexModArithMathlib.ZMod64.toZMod (Hex.ZPoly.leadingCoeffModP f primeData.p) := by
        rw [HexPolyMathlib.leadingCoeff_toPolynomial]
        show ((Hex.DensePoly.leadingCoeff f : ℤ) : ZMod primeData.p) = _
        rw [← HexPolyZMathlib.toZMod_ZMod64_ofNat_intModNat_eq_intCast primeData.p
              (Hex.DensePoly.leadingCoeff f)]
        rfl
      have hF_lc_map_ne :
          (Int.castRingHom (ZMod primeData.p)) F.leadingCoeff ≠ 0 := by
        rw [hF_lc_eq]
        intro heq
        apply hlc_modP_ne
        have hinj := (HexModArithMathlib.ZMod64.equiv (p := primeData.p)).injective
        apply hinj
        simpa using heq.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
      -- F.leadingCoeff = a.leadingCoeff * b.leadingCoeff (over Z, integral domain)
      have hlc_F : F.leadingCoeff = a.leadingCoeff * b.leadingCoeff := by
        rw [hab, Polynomial.leadingCoeff_mul]
      -- Then c.leadingCoeff mod p ≠ 0 (using p prime → ZMod p domain)
      have hc_lc_map_ne :
          (Int.castRingHom (ZMod primeData.p)) c.leadingCoeff ≠ 0 := by
        haveI : IsDomain (ZMod primeData.p) := inferInstance
        intro heq
        apply hF_lc_map_ne
        have : F.leadingCoeff = c.leadingCoeff * d.leadingCoeff := by
          rw [← hcd_eq, Polynomial.leadingCoeff_mul]
        rw [this, map_mul, heq, zero_mul]
      -- natDegree c is preserved mod p
      have hc_natDeg_modP :
          (c.map (Int.castRingHom (ZMod primeData.p))).natDegree = c.natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hc_lc_map_ne
      -- c divides F, so (c mod p) divides (F mod p)
      have hc_modP_dvd_F_modP :
          c.map (Int.castRingHom (ZMod primeData.p)) ∣
            F.map (Int.castRingHom (ZMod primeData.p)) := by
        refine ⟨d.map (Int.castRingHom (ZMod primeData.p)), ?_⟩
        rw [← Polynomial.map_mul, hcd_eq]
      -- (F mod p) = (factorPolys list).prod
      have hF_modP_eq :=
        map_intCast_zmod_toPolynomial_eq_factorPolys_product f primeData hcheckPoly
      rw [hF_modP_eq] at hc_modP_dvd_F_modP
      -- Construct Hex.ZMod64.PrimeModulus from Mathlib primality
      haveI hpm : Hex.ZMod64.PrimeModulus primeData.p :=
        Hex.ZMod64.primeModulusOfPrime
          ⟨hp_prime.two_le, fun m hdvd => hp_prime.eq_one_or_self_of_dvd m hdvd⟩
      -- Each factor in factorPolys is irreducible (via Rabin)
      have hfactor_irr :
          ∀ q ∈ (primeData.factorPolys.toList.map
                  HexBerlekampMathlib.toMathlibPolynomial),
            Irreducible q := by
        intro q hq
        rw [List.mem_map] at hq
        obtain ⟨factor, hfactor_mem, rfl⟩ := hq
        rw [List.mem_iff_getElem] at hfactor_mem
        obtain ⟨i, hi, hfactor_eq⟩ := hfactor_mem
        have hi_polys : i < primeData.factorPolys.size := by simpa using hi
        have hfactor_eq' : primeData.factorPolys[i] = factor := by
          rw [← hfactor_eq]; simp
        have hsizes :
            primeData.factorDegrees.size = primeData.factorCerts.size ∧
              primeData.factorDegrees.size = primeData.factorPolys.size := by
          simp only [Hex.PrimeFactorData.checkFactorCerts, Bool.and_eq_true, beq_iff_eq]
            at hfacts_align
          exact hfacts_align.1
        have hi_deg : i < primeData.factorDegrees.size := by
          rw [hsizes.2]; exact hi_polys
        have hi_cert : i < primeData.factorCerts.size := by
          rw [hsizes.1] at hi_deg; exact hi_deg
        have hpair :=
          checkCertAtFactor_of_checkFactorCerts primeData hfacts_align i
            hi_deg hi_polys hi_cert
        -- factor is monic; extract Rabin cert acceptance
        have hmonic : Hex.DensePoly.Monic primeData.factorPolys[i] := by
          by_cases hmon : primeData.factorPolys[i].leadingCoeff = 1
          · exact hmon
          · exfalso; simp [Hex.PrimeFactorData.checkCertAtFactor, hmon] at hpair
        have hcheck : Hex.Berlekamp.checkIrreducibilityCertificate
            primeData.factorPolys[i] hmonic primeData.factorCerts[i] = true := by
          have hp := hpair
          simp only [Hex.PrimeFactorData.checkCertAtFactor, Bool.and_eq_true] at hp
          obtain ⟨_, hif⟩ := hp
          have hmonic' : Hex.DensePoly.leadingCoeff primeData.factorPolys[i] = 1 := hmonic
          rw [dif_pos hmonic'] at hif
          exact hif
        have hrabin :=
          Hex.Berlekamp.checkIrreducibilityCertificate_rabinTest
            (p := primeData.p) primeData.factorPolys[i] hmonic _ hcheck
        rw [← hfactor_eq']
        exact HexBerlekampMathlib.rabinTest_true_irreducible _ hmonic hrabin
      -- Apply UFD subset-degree lemma to (c mod p)
      have hc_modP_ne :
          c.map (Int.castRingHom (ZMod primeData.p)) ≠ 0 := by
        intro hzero
        apply hc_lc_map_ne
        have hlc_eq : (c.map (Int.castRingHom (ZMod primeData.p))).leadingCoeff = 0 := by
          rw [hzero, Polynomial.leadingCoeff_zero]
        rw [Polynomial.leadingCoeff, Polynomial.coeff_map] at hlc_eq
        rw [hc_natDeg_modP] at hlc_eq
        exact hlc_eq
      -- Restate the divisibility with Multiset for the UFD lemma
      have hc_modP_dvd_prod :
          c.map (Int.castRingHom (ZMod primeData.p)) ∣
            (↑(primeData.factorPolys.toList.map
                HexBerlekampMathlib.toMathlibPolynomial) : Multiset (Polynomial (ZMod primeData.p))).prod := by
        rw [Multiset.prod_coe]
        exact hc_modP_dvd_F_modP
      have hfactor_irr_ms :
          ∀ q ∈ (↑(primeData.factorPolys.toList.map
                  HexBerlekampMathlib.toMathlibPolynomial) :
              Multiset (Polynomial (ZMod primeData.p))),
            Irreducible q := by
        intro q hq
        rw [Multiset.mem_coe] at hq
        exact hfactor_irr q hq
      obtain ⟨S, hS_le, hS_sum⟩ :=
        UFDPartition.natDegree_eq_sum_subset_of_dvd_prod_irreducibles
          hc_modP_ne hfactor_irr_ms hc_modP_dvd_prod
      -- The subset sum equals natDegree (c mod p) = natDegree c
      have hS_sum' : S.sum = c.natDegree := by
        rw [← hS_sum]; exact hc_natDeg_modP
      -- The "degrees of factor polys" equal `factorDegrees`
      have hsizes :
          primeData.factorDegrees.size = primeData.factorCerts.size ∧
            primeData.factorDegrees.size = primeData.factorPolys.size := by
        simp only [Hex.PrimeFactorData.checkFactorCerts, Bool.and_eq_true, beq_iff_eq]
          at hfacts_align
        exact hfacts_align.1
      have hmap_eq :
          (primeData.factorPolys.toList.map
              HexBerlekampMathlib.toMathlibPolynomial).map Polynomial.natDegree =
            primeData.factorDegrees.toList := by
        rw [List.map_map]
        apply List.ext_getElem
        · simp only [List.length_map, Array.length_toList]
          omega
        · intro i hi₁ hi₂
          simp only [List.length_map, Array.length_toList] at hi₁ hi₂
          have hi_polys : i < primeData.factorPolys.size := by simpa using hi₁
          have hi_deg : i < primeData.factorDegrees.size := by rw [hsizes.2]; exact hi_polys
          have hi_cert : i < primeData.factorCerts.size := by rw [hsizes.1] at hi_deg; exact hi_deg
          rw [List.getElem_map]
          simp only [Function.comp]
          show (HexBerlekampMathlib.toMathlibPolynomial
            primeData.factorPolys.toList[i]).natDegree = _
          rw [Array.getElem_toList]
          have := natDegree_toMathlibPolynomial_factorPolys_eq primeData hfacts_align i
            hi_polys hi_deg hi_cert
          rw [this, Array.getElem_toList]
      have hS_le' : S ≤ (primeData.factorDegrees.toList : Multiset Nat) := by
        have hmapcoe :
            Multiset.map Polynomial.natDegree
              (↑(primeData.factorPolys.toList.map
                HexBerlekampMathlib.toMathlibPolynomial) :
              Multiset (Polynomial (ZMod primeData.p))) =
            ↑(List.map Polynomial.natDegree
              (List.map HexBerlekampMathlib.toMathlibPolynomial
                primeData.factorPolys.toList)) :=
          Multiset.map_coe _ _
        rw [hmapcoe] at hS_le
        rw [hmap_eq] at hS_le
        exact hS_le
      -- Apply subset-sum spec
      have hsubsetTrue := hasSubsetDegreeAux_eq_true_of_exists_subMultiset hS_le' hS_sum'
      -- This contradicts hasSubsetDegree = false
      have hsubsetEq : primeData.hasSubsetDegree c.natDegree = true := hsubsetTrue
      rw [hobs_target_eq] at hno_subset
      rw [hsubsetEq] at hno_subset
      exact absurd hno_subset (by decide)
    -- Apply to either (a, b) or (b, a) based on which has smaller natDegree
    rcases le_or_gt a.natDegree b.natDegree with hle | hgt
    · exact hcontradict a b hab.symm ha_ne hb_ne ha_prim ha_not_unit hle
    · exact hcontradict b a (by rw [hab]; ring) hb_ne ha_ne hb_prim hb_not_unit (le_of_lt hgt)

/--
The executable integer-polynomial irreducibility checker is sound for the
Mathlib-free irreducibility predicate as well.
-/
theorem checkIrreducibleCert_sound_zpoly
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hprime : ∀ primeData ∈ cert.perPrime.toList, Nat.Prime primeData.p)
    (hprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive)
    (hpos : 0 < (HexPolyZMathlib.toPolynomial f).natDegree) :
    Hex.checkIrreducibleCert f cert = true → Hex.ZPoly.Irreducible f := by
  intro hcert
  exact
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible f).mpr
      (checkIrreducibleCert_sound f cert hprime hprim hpos hcert)

/--
Soundness of the kernel-reducible integer checker: a certificate accepted by
`checkIrreducibleCertLinear` on literal data certifies irreducibility of the
transported polynomial. The primality hypothesis feeds both the
Linear→committed checker implication and the committed checker's own
soundness theorem.
-/
theorem checkIrreducibleCertLinear_sound
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hprime : ∀ primeData ∈ cert.perPrime.toList, Nat.Prime primeData.p)
    (hprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive)
    (hpos : 0 < (HexPolyZMathlib.toPolynomial f).natDegree) :
    Hex.checkIrreducibleCertLinear f cert = true →
      Irreducible (HexPolyZMathlib.toPolynomial f) := by
  intro hcert
  refine checkIrreducibleCert_sound f cert hprime hprim hpos ?_
  refine Hex.checkIrreducibleCert_of_linear f cert ?_ hcert
  intro primeData hmem
  exact ⟨(hprime primeData hmem).two_le,
    fun m hm => (hprime primeData hmem).eq_one_or_self_of_dvd m hm⟩

/--
`checkIrreducibleCertLinear_sound` with every side condition stated as a
kernel-decidable Boolean check: primality of the recorded primes, content one,
and positive executable degree. This is the exact consumption shape of the
multi-prime arm of the `factor_poly`/`irreducibility` extension: it applies
this theorem (through `zpolyIrreducible_of_checkIrreducibleCertLinear` and
`checkMultiPrimeCert`) to a reified literal certificate with an
`Eq.refl true` proof in each hypothesis slot, so the whole obligation is
discharged by kernel reduction on literal data.
-/
theorem irreducible_of_checkIrreducibleCertLinear
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hprime : cert.perPrime.all (fun primeData => decide (Nat.Prime primeData.p)) = true)
    (hcontent : decide (Hex.ZPoly.content f = 1) = true)
    (hpos : decide (0 < f.degree?.getD 0) = true)
    (hcert : Hex.checkIrreducibleCertLinear f cert = true) :
    Irreducible (HexPolyZMathlib.toPolynomial f) := by
  have hprime' : ∀ primeData ∈ cert.perPrime.toList, Nat.Prime primeData.p := by
    rw [Array.all_eq_true] at hprime
    intro primeData hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hi, hget⟩ := hmem
    have hiArray : i < cert.perPrime.size := by simpa using hi
    have hdec := hprime i hiArray
    rw [← hget]
    simpa [Array.getElem_toList] using of_decide_eq_true hdec
  have hcontent' : Hex.ZPoly.content f = 1 := of_decide_eq_true hcontent
  have hdeg : (HexPolyZMathlib.toPolynomial f).natDegree = f.degree?.getD 0 :=
    HexPolyMathlib.natDegree_toPolynomial f
  exact checkIrreducibleCertLinear_sound f cert hprime'
    (HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive f hcontent')
    (by rw [hdeg]; exact of_decide_eq_true hpos) hcert


end

end HexBerlekampZassenhausMathlib
