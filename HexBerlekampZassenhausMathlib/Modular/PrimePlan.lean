/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Modular.PrimePlan
public import HexBerlekampZassenhausMathlib.ModPFactorization
public import HexBerlekampZassenhausMathlib.ModPPartition
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.ModPPartition
import all HexBerlekampZassenhausMathlib.IntReductionMod.Descent

public section
set_option backward.proofsInPublic true

/-!
# Correctness of the direct prime plan

Two things are proved here beyond the selected trial's semantic bundle.

The subset-degree bitset a probe records is given its meaning: index `i` is
true exactly when some sub-multiset of the recorded modular factor degrees
sums to `i`.  The planner scores primes with these Booleans, and anything that
*rejects* on them needs the specification, not the fold.

The retained trials -- the selected one and every other successful trial the
planner kept -- then get the same modular facts as the selected one, and from
those follows the statement a degree filter would consume: reduction at a
retained good prime preserves the degree of an integer divisor of the input
and factors it as a subproduct of that prime's modular irreducibles, so the
divisor's degree is marked reachable at *every* retained probe.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/-! ## The subset-degree bitset -/

/-- One `directDegreeBitsStep` entry, at any index the step records. -/
private theorem directDegreeBitsStep_getElem?
    (maxDegree : Nat) (reachable : Array Bool) (degree i : Nat)
    (hi : i ≤ maxDegree) :
    (Hex.directDegreeBitsStep maxDegree reachable degree)[i]?.getD false =
      (reachable[i]?.getD false ||
        (decide (degree ≤ i) && reachable[i - degree]?.getD false)) := by
  have hlt : i < (List.range (maxDegree + 1)).length := by simp; omega
  simp only [Hex.directDegreeBitsStep, Array.getElem?_map, List.getElem?_toArray]
  rw [List.getElem?_eq_getElem hlt]
  simp

/-- A sub-multiset of `degree ::ₘ pre` either avoids the new degree entirely or
uses it once and leaves a sub-multiset of `pre` summing to the remainder. -/
private theorem exists_le_cons_iff (pre : List Nat) (degree i : Nat) :
    (∃ S ≤ (degree ::ₘ (pre : Multiset Nat)), S.sum = i) ↔
      ((∃ S ≤ (pre : Multiset Nat), S.sum = i) ∨
        (degree ≤ i ∧ ∃ S ≤ (pre : Multiset Nat), S.sum = i - degree)) := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    by_cases hmem : degree ∈ S
    · refine Or.inr ⟨?_, S.erase degree, ?_, ?_⟩
      · exact Multiset.single_le_sum (fun _ _ => Nat.zero_le _) degree hmem
      · have herase : S.erase degree ≤ (degree ::ₘ (pre : Multiset Nat)).erase degree :=
          Multiset.erase_le_erase degree hS
        rwa [Multiset.erase_cons_head] at herase
      · have hcons : (degree ::ₘ S.erase degree).sum = S.sum := by
          rw [Multiset.cons_erase hmem]
        rw [Multiset.sum_cons] at hcons
        omega
    · exact Or.inl ⟨S, (Multiset.le_cons_of_notMem hmem).mp hS, rfl⟩
  · rintro (⟨S, hS, rfl⟩ | ⟨hle, S, hS, hsum⟩)
    · exact ⟨S, hS.trans (Multiset.le_cons_self _ _), rfl⟩
    · refine ⟨degree ::ₘ S, Multiset.cons_le_cons _ hS, ?_⟩
      rw [Multiset.sum_cons, hsum]
      omega

/-- The fold invariant: an array recording the sub-multiset sums of a processed
prefix records the sums of that prefix extended by the whole remaining list. -/
private theorem foldl_directDegreeBitsStep_spec (maxDegree : Nat) :
    ∀ (degrees : List Nat) (reachable : Array Bool) (pre : List Nat),
      (∀ i ≤ maxDegree,
        (reachable[i]?.getD false = true ↔
          ∃ S ≤ (pre : Multiset Nat), S.sum = i)) →
      ∀ i ≤ maxDegree,
        ((degrees.foldl (Hex.directDegreeBitsStep maxDegree) reachable)[i]?.getD
            false = true ↔
          ∃ S ≤ ((pre ++ degrees : List Nat) : Multiset Nat), S.sum = i) := by
  intro degrees
  induction degrees with
  | nil => intro reachable pre hpre i hi; simpa using hpre i hi
  | cons degree degrees ih =>
      intro reachable pre hpre i hi
      have hstep : ∀ j ≤ maxDegree,
          ((Hex.directDegreeBitsStep maxDegree reachable degree)[j]?.getD false =
              true ↔
            ∃ S ≤ ((pre ++ [degree] : List Nat) : Multiset Nat), S.sum = j) := by
        intro j hj
        rw [directDegreeBitsStep_getElem? maxDegree reachable degree j hj]
        have hcoe : ((pre ++ [degree] : List Nat) : Multiset Nat) =
            degree ::ₘ (pre : Multiset Nat) := by
          simp [← Multiset.coe_add, Multiset.cons_coe]
          exact Multiset.add_comm _ _
        rw [hcoe, exists_le_cons_iff]
        rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact or_congr (hpre j hj)
          (and_congr_right fun _ => hpre (j - degree) (by omega))
      have := ih (Hex.directDegreeBitsStep maxDegree reachable degree)
        (pre ++ [degree]) hstep i hi
      simpa using this

/-- The initial bitset records exactly the empty sub-multiset. -/
private theorem directDegreeBits_init_spec (maxDegree : Nat) :
    ∀ i ≤ maxDegree,
      (((#[true] ++ Array.replicate maxDegree false) : Array Bool)[i]?.getD
          false = true ↔
        ∃ S ≤ (([] : List Nat) : Multiset Nat), S.sum = i) := by
  intro i hi
  have hnil : (∃ S ≤ (([] : List Nat) : Multiset Nat), S.sum = i) ↔ i = 0 := by
    constructor
    · rintro ⟨S, hS, rfl⟩
      simpa using congrArg Multiset.sum (Multiset.le_zero.mp (by simpa using hS))
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
  rw [hnil]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · have hfalse :
        ((#[true] ++ Array.replicate maxDegree false : Array Bool))[i]?.getD
          false = false := by
      rcases Nat.lt_or_ge i (maxDegree + 1) with hlt | hge
      · rw [Array.getElem?_eq_getElem (by simp; omega)]
        simp [Array.getElem_append, Nat.not_lt.mpr hpos]
      · rw [Array.getElem?_eq_none (by simp; omega)]
        rfl
    simp [hfalse]
    omega

/-- `Hex.directDegreeBits` means what its name says: index `i` is true exactly
when some sub-multiset of the recorded degrees sums to `i`.

The bound `i ≤ maxDegree` is the array's own range; outside it the fold records
nothing, and no degree of a divisor of a degree-`maxDegree` polynomial lands
there. -/
theorem directDegreeBits_getElem?_iff
    (maxDegree : Nat) (degrees : Array Nat) (i : Nat) (hi : i ≤ maxDegree) :
    (Hex.directDegreeBits maxDegree degrees)[i]?.getD false = true ↔
      ∃ S ≤ (degrees.toList : Multiset Nat), S.sum = i := by
  have := foldl_directDegreeBitsStep_spec maxDegree degrees.toList
    (#[true] ++ Array.replicate maxDegree false) []
    (directDegreeBits_init_spec maxDegree) i hi
  simpa [Hex.directDegreeBits, Array.foldl_toList] using this

/-! ## An integer divisor's degree is a modular subset sum -/

/-- A nonzero modular image divides its own monic normalization: the
normalization scales by the inverse of a nonzero leading coefficient. -/
private theorem modP_dvd_monicModularImage
    {p : Nat} [Hex.ZMod64.Bounds p]
    {f : Hex.FpPoly p} (hf : f.isZero = false) :
    f ∣ Hex.monicModularImage f := by
  rw [monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hf]
  refine ⟨Hex.DensePoly.C (Hex.DensePoly.leadingCoeff f)⁻¹, ?_⟩
  calc
    Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)⁻¹ f
        = Hex.DensePoly.C (Hex.DensePoly.leadingCoeff f)⁻¹ * f := by
          rw [Hex.FpPoly.C_mul_eq_scale]
    _ = f * Hex.DensePoly.C (Hex.DensePoly.leadingCoeff f)⁻¹ :=
          Hex.DensePoly.mul_comm_poly _ _

/-- The recorded factor degrees are the Mathlib natural degrees of the
transported modular factors. -/
private theorem map_natDegree_factorsModP
    {core : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hval : ModPFactorization core data) :
    letI := data.bounds
    data.factorsModP.toList.map
        (fun g => (HexBerlekampMathlib.toMathlibPolynomial g).natDegree) =
      (Hex.directFactorDegrees data).toList := by
  letI := data.bounds
  haveI : Fact (_root_.Nat.Prime data.p) := ⟨natPrime_of_hexNatPrime hval.prime⟩
  haveI : Nontrivial (ZMod data.p) := inferInstance
  simp only [Hex.directFactorDegrees, Array.toList_map]
  refine List.map_congr_left ?_
  intro g hg
  have hmonic : Hex.DensePoly.Monic g := hval.monic g (by simpa using hg)
  rw [HexBerlekampMathlib.natDegree_toMathlibPolynomial_eq_basisSize g hmonic]
  rfl

/-- Reduction at a good prime sends an integer divisor of the input to a
subproduct of that prime's modular irreducible factors and preserves its
degree, so the divisor's degree is one of the subset sums of the recorded
modular factor degrees.

This is the whole content of a degree filter that consults a prime other than
the one recombination enumerates: a support whose degree is not such a subset
sum cannot be the support of a genuine integer factor. -/
theorem exists_subMultiset_directFactorDegrees_of_dvd
    {core : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hval : ModPFactorization core data)
    {c : Hex.ZPoly} (hdvd : c ∣ core) :
    ∃ S ≤ ((Hex.directFactorDegrees data).toList : Multiset Nat),
      S.sum = c.degree?.getD 0 := by
  letI := data.bounds
  haveI : Fact (_root_.Nat.Prime data.p) := ⟨natPrime_of_hexNatPrime hval.prime⟩
  letI : Hex.ZMod64.PrimeModulus data.p :=
    Hex.ZMod64.primeModulusOfPrime hval.prime
  have hcore_modP_nz :
      (@Hex.ZPoly.modP data.p data.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core data.p hval.good
  have hadm : Hex.ZPoly.leadingCoeffModP core data.p ≠ 0 := by
    have := Hex.isGoodPrime_leadingCoeffAdmissible core data.p hval.good
    unfold Hex.leadingCoeffAdmissible at this
    exact this
  -- The divisor's leading coefficient survives reduction, so its degree does.
  have hF_lc :
      (Int.castRingHom (ZMod data.p))
          (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0 :=
    (IntReductionMod.intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero
      (p := data.p) (f := core)).mpr hadm
  obtain ⟨d, hd⟩ :
      HexPolyZMathlib.toPolynomial c ∣ HexPolyZMathlib.toPolynomial core :=
    HexPolyMathlib.toPolynomial_dvd hdvd
  have hC_lc :
      (Int.castRingHom (ZMod data.p))
          (HexPolyZMathlib.toPolynomial c).leadingCoeff ≠ 0 := by
    intro h
    apply hF_lc
    rw [hd, Polynomial.leadingCoeff_mul, map_mul, h, zero_mul]
  have hCmap_natDegree :
      ((HexPolyZMathlib.toPolynomial c).map
          (Int.castRingHom (ZMod data.p))).natDegree =
        (HexPolyZMathlib.toPolynomial c).natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hC_lc
  have hCmap_ne :
      (HexPolyZMathlib.toPolynomial c).map (Int.castRingHom (ZMod data.p)) ≠ 0 := by
    intro hzero
    apply hC_lc
    have hlc :
        ((HexPolyZMathlib.toPolynomial c).map
          (Int.castRingHom (ZMod data.p))).leadingCoeff = 0 := by
      rw [hzero, Polynomial.leadingCoeff_zero]
    rw [Polynomial.leadingCoeff, Polynomial.coeff_map, hCmap_natDegree] at hlc
    exact hlc
  -- The reduced divisor divides the product of the recorded modular factors.
  have hchain :
      @Hex.ZPoly.modP data.p data.bounds c ∣
        Hex.monicModularImage (@Hex.ZPoly.modP data.p data.bounds core) :=
    fpPoly_dvd_trans (modP_dvd_modP_of_dvd data.p hdvd)
      (modP_dvd_monicModularImage hcore_modP_nz)
  have hprod :
      (HexPolyZMathlib.toPolynomial c).map (Int.castRingHom (ZMod data.p)) ∣
        ((data.factorsModP.toList : Multiset _).map
          HexBerlekampMathlib.toMathlibPolynomial).prod := by
    have h := toMathlibPolynomial_dvd hchain
    rw [toMathlibPolynomial_modP_eq_map_intCast_zmod,
      ← toMathlibPolynomial_factorsModP_product_eq_monicModularImage hval] at h
    exact h
  have hirr :
      ∀ q ∈ ((data.factorsModP.toList : Multiset (Hex.FpPoly data.p)).map
          HexBerlekampMathlib.toMathlibPolynomial), Irreducible q := by
    intro q hq
    rw [← univ_val_map_modPFactor_eq_factorsModP_map data, Multiset.mem_map] at hq
    obtain ⟨i, -, rfl⟩ := hq
    exact hval.irreducible i
  obtain ⟨S, hS, hsum⟩ :=
    UFDPartition.natDegree_eq_sum_subset_of_dvd_prod_irreducibles hCmap_ne hirr
      hprod
  have hdegmap :
        ((data.factorsModP.toList : Multiset (Hex.FpPoly data.p)).map
          HexBerlekampMathlib.toMathlibPolynomial).map Polynomial.natDegree =
        ((Hex.directFactorDegrees data).toList : Multiset Nat) := by
    rw [Multiset.map_coe, Multiset.map_coe, List.map_map]
    exact congrArg _ (map_natDegree_factorsModP hval)
  refine ⟨S, ?_, ?_⟩
  · rw [← hdegmap]
    exact hS
  · rw [← hsum, hCmap_natDegree, HexPolyMathlib.natDegree_toPolynomial]

/-- No false rejection.  A probe that is its own good-prime trial marks the
degree of every genuine integer divisor of the input as reachable, so a
traversal that discards a support whose degree is *not* marked discards no
genuine factor. -/
theorem reachableDegrees_of_dvd
    {core : Hex.SquareFreeInput} {probe : Hex.DirectPrimeProbe core}
    (hrec : probe = Hex.DirectPrimeProbe.ofData core probe.candidate probe.data)
    (hval : ModPFactorization core.poly probe.data)
    {c : Hex.ZPoly} (hdvd : c ∣ core.poly) :
    probe.reachableDegrees[c.degree?.getD 0]?.getD false = true := by
  have hcore_ne : core.poly ≠ 0 := core_ne_zero_of_modPFactorization core.poly probe.data hval
  have hFne : HexPolyZMathlib.toPolynomial core.poly ≠ 0 := by
    intro hzero
    exact hcore_ne (HexPolyZMathlib.equiv.injective (by simpa using hzero))
  have hle : c.degree?.getD 0 ≤ core.poly.degree?.getD 0 := by
    have hdeg :=
      Polynomial.natDegree_le_of_dvd (HexPolyMathlib.toPolynomial_dvd hdvd) hFne
    rwa [HexPolyMathlib.natDegree_toPolynomial,
      HexPolyMathlib.natDegree_toPolynomial] at hdeg
  have hbits : probe.reachableDegrees =
      Hex.directDegreeBits (core.poly.degree?.getD 0)
        (Hex.directFactorDegrees probe.data) :=
    congrArg Hex.DirectPrimeProbe.reachableDegrees hrec
  rw [hbits, directDegreeBits_getElem?_iff _ _ _ hle]
  exact exists_subMultiset_directFactorDegrees_of_dvd hval hdvd

/-! ## The retained trials -/

/-- The complete proof-facing contract of a direct prime probe.  Consumers
need the semantic factorization, the cached Berlekamp form for the singleton
certificate, and the small-prime bound used by the CLD resultant estimate. -/
structure DirectPrimeFacts
    (core : Hex.ZPoly) (data : Hex.PrimeChoiceData) : Prop where
  /-- The cached modular factorization is mathematically valid. -/
  factorization : ModPFactorization core data
  /-- The cached factors have the required Berlekamp certificate form. -/
  berlekampForm : Hex.factorsModPBerlekampForm core data
  /-- The prime lies within the range used by the resultant estimate. -/
  p_le : data.p ≤ 500

/-- Every retained trial -- not only the selected one -- describes the
normalized modular image of the plan's own indexed polynomial. -/
theorem directPrimePlan_probes_modPFactorization
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    ∀ probe ∈ plan.probes, ModPFactorization core.poly probe.data := by
  intro probe hmem
  exact modPFactorization_of_probePrimeData
    (Hex.directPrimePlan?_probes_trial core plan hplan probe hmem).1
    hprim hlc_pos hpos

/-- Every retained trial supplies exactly the modular facts the classical and
lattice proof cones consume. -/
theorem directPrimePlan_probes_facts
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    ∀ probe ∈ plan.probes, DirectPrimeFacts core.poly probe.data := by
  intro probe hmem
  exact
    { factorization :=
        directPrimePlan_probes_modPFactorization core plan hplan hprim hlc_pos
          hpos probe hmem
      berlekampForm :=
        Hex.probePrimeData?_form core.poly probe.candidate probe.data
          (Hex.directPrimePlan?_probes_trial core plan hplan probe hmem).1
      p_le := Hex.directPrimePlan?_probes_p_le_500 core plan hplan probe hmem }

/-- The statement a degree filter over a whole plan consumes: the degree of a
genuine integer divisor of the input is marked reachable at *every* trial the
planner retained, so intersecting the retained bitsets rejects no genuine
factor. -/
theorem directPrimePlan_probes_reachableDegrees
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0)
    {c : Hex.ZPoly} (hdvd : c ∣ core.poly) :
    ∀ probe ∈ plan.probes,
      probe.reachableDegrees[c.degree?.getD 0]?.getD false = true := by
  intro probe hmem
  exact reachableDegrees_of_dvd
    (Hex.directPrimePlan?_probes_trial core plan hplan probe hmem).2
    (directPrimePlan_probes_modPFactorization core plan hplan hprim hlc_pos hpos
      probe hmem)
    hdvd

/-- A selected direct plan describes the normalized modular image of its own
indexed polynomial. -/
theorem directPrimePlan_modPFactorization
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    ModPFactorization core.poly plan.data :=
  directPrimePlan_probes_modPFactorization core plan hplan hprim hlc_pos hpos
    plan.selected plan.selected_mem_probes

/-- A successful direct plan supplies exactly the modular facts used by the
classical and lattice proof cones. -/
theorem directPrimePlan_facts
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    DirectPrimeFacts core.poly plan.data :=
  directPrimePlan_probes_facts core plan hplan hprim hlc_pos hpos
    plan.selected plan.selected_mem_probes

end HexBerlekampZassenhausMathlib
