/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Lattice.DirectAdequacy

import all HexBerlekampZassenhausMathlib.RecombinationSplit

public section
set_option backward.proofsInPublic true

/-!
# Direct-coordinate van Hoeij / CLD factorization

The classical and lattice tiers share one modular plan:
`Hex.directPrimePlan?` factors the primitive square-free core directly, and
each tier uses `Hex.ZPoly.coreLiftData` at its required precision. No
dilation-coordinate factorization or coordinate correspondence appears in
this module.

`DirectAdequacy` supplies the forward and exact span theorems.  This module only
assembles their executable consequences: singleton descent, split
irreducibility, all-ones certification, totality, and public reassembly.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- A one-factor direct modular plan certifies irreducibility of a primitive
positive-degree input. -/
theorem irreducible_of_directSingleton
    (core : Hex.ZPoly) (data : Hex.PrimeChoiceData)
    (prime : DirectPrimeFacts core data)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hsmall : data.factorsModP.size ≤ 1) :
    Hex.ZPoly.Irreducible core := by
  letI := data.bounds
  have hadm :
      Hex.leadingCoeffAdmissible core data.p :=
    Hex.isGoodPrime_leadingCoeffAdmissible core data.p
      prime.factorization.good
  have hcast :
      (Int.castRingHom (ZMod data.p))
          (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0 := by
    have hdense :=
      (IntReductionMod.intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero
        (p := data.p) (f := core)).mpr hadm
    simpa [HexPolyMathlib.leadingCoeff_toPolynomial] using hdense
  exact IntReductionMod.irreducible_of_smallMod core data
    prime.factorization.prime prime.factorization.good prime.berlekampForm
    hcore_pos hsmall
    (HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive core hcore_prim)
    hcast

/-- A successful forward-adequate CLD split emits exactly one candidate for
each normalized irreducible factor. -/
theorem bhksRecoveryCoreWithBound_factorCount
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hval : ModPFactorization core data)
    (coreFactors : Array Hex.ZPoly)
    (hfast : Hex.bhksRecoveryCoreWithBound core B data
        (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) = some coreFactors) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hle :=
    bhksRecoveryCoreWithBound_some_factor_count_le hcore_ne hfast
  obtain ⟨k, hrows, hcandidates, _hdegen, _hproduct, hfloor⟩ :=
    Hex.bhksRecoveryCoreWithBound_some_indicatorCandidates hfast
  have hk_ne : k ≠ 0 := by
    have hbound_pos :=
      Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
    have hbound_le :=
      Hex.defaultFactorCoeffBound_le_bhksRecoveryFloor core
    omega
  have hcandidateSize :=
    Hex.bhksIndicatorCandidates?_size_eq hcandidates
  have hge :=
    directFactorCount_le_classCount core k data hcore_lc_pos hcore_pos
      hcore_prim hcore_sqfree hval hfloor hk_ne hrows
  rw [List.length_map, Array.length_toList] at hle ⊢
  omega

/-- At a forward-adequate precision, the executable single-all-ones
certificate implies that the primitive square-free core is irreducible. -/
theorem irreducible_of_directSingleClass
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hval : ModPFactorization core data)
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B)
    (hB_ne : B ≠ 0)
    (hsingle : Hex.bhksSingleAllOnesPartition core
      (Hex.ZPoly.coreLiftData core B data) = true) :
    Hex.ZPoly.Irreducible core := by
  let d := Hex.ZPoly.coreLiftData core B data
  rw [Hex.bhksSingleAllOnesPartition] at hsingle
  split at hsingle
  · rename_i hrows
    let L := Hex.bhksLatticeBasis core d.p d.k d.liftedFactors
    let projected := Hex.bhksProjectedRows L hrows
    let indicators := Hex.bhksEquivalenceClassIndicators projected
    have hsize : indicators.size = 1 := by
      change (!indicators.isEmpty && !projected.projectedRows.isEmpty &&
        indicators.size == 1 &&
        Hex.bhksIndicatorAllOnes projected.factorCount
          (indicators.getD 0 #[])) = true at hsingle
      simp only [Bool.and_eq_true, beq_iff_eq] at hsingle
      exact hsingle.1.2
    have hle :
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card ≤ 1 := by
      have hcount :=
        directFactorCount_le_classCount core B data hcore_lc_pos hcore_pos
          hcore_prim hcore_sqfree hval hB_floor hB_ne
          (by simpa only [L, d] using hrows)
      simpa only [L, projected, indicators, d, hsize] using hcount
    have hcore_ne : core ≠ 0 :=
      zpoly_ne_zero_of_pos_lc hcore_lc_pos
    have hpoly_ne : HexPolyZMathlib.toPolynomial core ≠ 0 := by
      intro hzero
      exact hcore_ne (HexPolyZMathlib.equiv.injective (by simpa using hzero))
    have hnonunit :
        ¬ IsUnit (HexPolyZMathlib.toPolynomial core) :=
      not_isUnit_of_natDegree_pos_of_isReduced _
        (by simpa [HexPolyMathlib.natDegree_toPolynomial] using hcore_pos)
    have hpos :
        0 < (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card :=
      Multiset.card_pos.mpr
        ((UniqueFactorizationMonoid.normalizedFactors_pos _ hpoly_ne).mpr
          hnonunit).ne'
    have hcard :
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card = 1 := by
      omega
    obtain ⟨factor, hfactorization⟩ := Multiset.card_eq_one.mp hcard
    have hfactor_mem :
        factor ∈ UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core) := by
      rw [hfactorization]
      exact Multiset.mem_singleton_self _
    have hirr : Irreducible factor :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor
        factor hfactor_mem
    have hassoc :
        Associated factor (HexPolyZMathlib.toPolynomial core) := by
      have hproduct :=
        UniqueFactorizationMonoid.prod_normalizedFactors hpoly_ne
      rwa [hfactorization, Multiset.prod_singleton] at hproduct
    rw [Hex.ZPoly.Irreducible_iff_polynomialIrreducible]
    exact hassoc.irreducible_iff.mp hirr
  · simp at hsingle

/-- Every factor returned by the direct-coordinate CLD core tier is
irreducible.  Split success uses the forward count theorem; either all-ones
arm uses the forward irreducibility certificate. -/
theorem latticeCoreFactorsWithBound_factor_irreducible
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (prime : DirectPrimeFacts core data)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B)
    (hB_ne : B ≠ 0)
    {coreFactors : Array Hex.ZPoly}
    (hlattice :
      Hex.latticeCoreFactorsWithBound core B data = some coreFactors) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hsingleton :
      ∀ factor ∈ (#[core] : Array Hex.ZPoly).toList,
        Hex.ZPoly.Irreducible core → Hex.ZPoly.Irreducible factor := by
    intro factor hfactor hirr
    have : factor = core := by simpa using hfactor
    exact this ▸ hirr
  rw [Hex.latticeCoreFactorsWithBound] at hlattice
  split at hlattice
  · rename_i hsmall
    obtain rfl := Option.some.inj hlattice
    exact fun factor hfactor =>
      hsingleton factor hfactor
        (irreducible_of_directSingleton core data prime
          hcore_pos hcore_prim hsmall)
  · split at hlattice
    · rename_i recovered hloop
      obtain rfl := Option.some.inj hlattice
      rcases Hex.latticeCoreWithBound_some_spec hloop with
        hfast | ⟨rfl, k, hk_floor, hk_single⟩
      · exact bhksFactors_zpolyIrreducible_of_count hcore_ne hfast
          (bhksRecoveryCoreWithBound_factorCount core B data
            hcore_lc_pos hcore_pos hcore_prim hcore_sqfree
            prime.factorization recovered hfast)
      · have hk_ne : k ≠ 0 := by
          have hbound_pos :=
            Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
          have hbound_le :=
            Hex.defaultFactorCoeffBound_le_bhksRecoveryFloor core
          omega
        exact fun factor hfactor =>
          hsingleton factor hfactor
            (irreducible_of_directSingleClass core k data
              hcore_lc_pos hcore_pos hcore_prim hcore_sqfree
              prime.factorization hk_floor hk_ne hk_single)
    · split at hlattice
      · split at hlattice
        · rename_i hsingle
          obtain rfl := Option.some.inj hlattice
          exact fun factor hfactor =>
            hsingleton factor hfactor
              (irreducible_of_directSingleClass core B data
                hcore_lc_pos hcore_pos hcore_prim hcore_sqfree
                prime.factorization hB_floor hB_ne hsingle)
        · exact absurd hlattice.symm (Option.some_ne_none coreFactors)
      · exact absurd hlattice.symm (Option.some_ne_none coreFactors)

/-- At full resultant-adequate precision, the direct-coordinate CLD core tier
is total for every successful prime plan.  Exact span yields either a genuine
multi-class recovery on the scheduled cap visit or the single-all-ones
certificate. -/
theorem latticeCoreFactorsWithBound_ne_none
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (prime : DirectPrimeFacts core data)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B)
    (hB_ne : B ≠ 0)
    (hresultant :
      2 * Hex.bhksBound core <
        (Hex.ZPoly.coreLiftData core B data).p ^
          (Hex.ZPoly.coreLiftData core B data).k) :
    Hex.latticeCoreFactorsWithBound core B data ≠ none := by
  classical
  let d := Hex.ZPoly.coreLiftData core B data
  let A := directAdequacy core B data hcore_lc_pos hcore_pos
    hcore_prim hcore_sqfree prime.factorization hB_floor hB_ne
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hrows :
      1 ≤
        (Hex.bhksLatticeBasis core
          d.p d.k d.liftedFactors).factorCount +
        (Hex.bhksLatticeBasis core
          d.p d.k d.liftedFactors).coeffWidth := by
    change 1 ≤ d.liftedFactors.size + core.degree?.getD 0
    omega
  have hspan :
      BHKS.projectedRowSpanInt
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors) hrows) =
        BHKS.trueSupportSpanInt (directTrueSupports core B data) := by
    simpa only [d] using
      (directProjectedSpan_eq core B data hcore_lc_pos hcore_pos
        hcore_prim hcore_sqfree prime.factorization prime.p_le
        hB_floor hB_ne hresultant (by simpa only [d] using hrows))
  let classes :=
    BHKS.supportPartitionByMinColumn (directTrueSupports core B data)
  have hcover := A.cover hcore_prim hcore_lc_pos prime.factorization
  have hdisjoint := A.disjoint
  have hcard :=
    A.factorCount hcore_prim hcore_lc_pos prime.factorization hcore_ne
  have hclassesCount :
      classes.length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card := by
    calc
      classes.length =
          (directTrueSupports core B data).ncard := by
        exact BHKS.supportPartitionByMinColumn_length_eq_ncard_of_partition
          _ hcover hdisjoint directTrueSupports.nonempty
      _ = _ := hcard
  have hclasses_pos : 0 < classes.length := by
    have hpoly_ne : HexPolyZMathlib.toPolynomial core ≠ 0 := by
      intro hzero
      exact hcore_ne (HexPolyZMathlib.equiv.injective (by simpa using hzero))
    have hnonunit :
        ¬ IsUnit (HexPolyZMathlib.toPolynomial core) :=
      not_isUnit_of_natDegree_pos_of_isReduced _
        (by simpa [HexPolyMathlib.natDegree_toPolynomial] using hcore_pos)
    rw [hclassesCount]
    exact Multiset.card_pos.mpr
      ((UniqueFactorizationMonoid.normalizedFactors_pos _ hpoly_ne).mpr
        hnonunit).ne'
  rw [Hex.latticeCoreFactorsWithBound]
  by_cases hsmall : data.factorsModP.size ≤ 1
  · rw [if_pos hsmall]
    simp
  · rw [if_neg hsmall]
    cases hlattice :
        Hex.latticeCoreWithBound core B data
          (Hex.initialHenselPrecision B)
          (Hex.ZPoly.quadraticDoublingSteps B + 2) with
    | some factors => simp
    | none =>
        by_cases hsingle : classes.length = 1
        · have hallones :
              Hex.bhksSingleAllOnesPartition core d = true :=
            BHKS.bhksSingleAllOnesPartition_eq_true_of_span_eq
              hcover hdisjoint (by simpa only [d] using hrows)
              (by simpa only [d] using hspan)
              (by simpa only [classes] using hsingle)
          rw [Hex.bhksRecoveryFloorGate_eq, if_pos hB_floor]
          rw [show Hex.ZPoly.coreLiftData core B data = d by rfl,
            if_pos hallones]
          simp
        · have hclasses_two : 2 ≤ classes.length := by omega
          have hrecover :
              Hex.bhksRecover? core d =
                some (BHKS.recoveredClassFactors core B data) :=
            BHKS.bhksRecover_eq_some_of_span_eq
              hcore_ne hcore_prim hcore_lc_pos A.partition hcover
              hdisjoint hcard (by simpa only [d] using hrows)
              (by simpa only [d] using hspan)
              (by simpa only [classes] using hclasses_two)
          have hloop_ne :
              Hex.latticeCoreWithBound core B data
                  (Hex.initialHenselPrecision B)
                  (Hex.ZPoly.quadraticDoublingSteps B + 2) ≠ none :=
            Hex.latticeCoreWithBound_ne_none_of_recovery_on_schedule
              core B data hB_floor
              (Hex.cap_mem_henselPrecisionSchedule B)
              (by simpa only [d] using hrecover)
          exact absurd hlattice hloop_ne

/-- Reassembling a successful direct CLD core factorization covers the original
input exactly. -/
theorem reassemblyExpansionComplete_latticeCore
    (f : Hex.ZPoly) (hf : f ≠ 0) (B : Nat)
    (data : Hex.PrimeChoiceData)
    (prime :
      DirectPrimeFacts (Hex.normalizeForFactor f).squareFreeCore data)
    (hcore_pos :
      0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0)
    (hB_floor :
      Hex.bhksRecoveryFloor
        (Hex.normalizeForFactor f).squareFreeCore ≤ B)
    (hB_ne : B ≠ 0)
    {coreFactors : Array Hex.ZPoly}
    (hlattice :
      Hex.latticeCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore B data =
          some coreFactors) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors := by
  let core := (Hex.normalizeForFactor f).squareFreeCore
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim : Hex.ZPoly.Primitive core :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  have hcore_sqfree :
      Squarefree (HexPolyZMathlib.toPolynomial core) :=
    IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree
      f hf
  exact
    IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm
      f hf coreFactors
      (latticeCoreFactorsWithBound_factor_irreducible core B data prime
        hcore_lc_pos hcore_pos hcore_prim hcore_sqfree hB_floor hB_ne
        hlattice)
      (Hex.latticeCoreFactorsWithBound_polyProduct core B data hlattice)
      (Hex.latticeCoreFactorsWithBound_normalizeFactorSign core B data
        hcore_lc_pos hlattice)
      (Hex.latticeCoreFactorsWithBound_degree_pos core B data
        hcore_pos hlattice)

/-- Every recorded raw factor returned by CLD from a selected direct prime is
irreducible. -/
theorem factorLatticeFactorsWithPlan_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (modular : Hex.DirectPrimePlan
      ⟨(Hex.normalizeForFactor f).squareFreeCore⟩)
    (hplan :
      Hex.directPrimePlan?
          ⟨(Hex.normalizeForFactor f).squareFreeCore⟩ =
        some modular)
    {factors : Array Hex.ZPoly}
    (hresult :
      Hex.factorLatticeFactorsWithPlan
          (Hex.normalizeForFactor f) (Hex.latticePrecisionCap f) modular =
        some factors)
    {raw : Hex.ZPoly}
    (hraw : raw ∈ factors.toList)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
        (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  have hcore_lc_pos :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  rw [Hex.factorLatticeFactorsWithPlan] at hresult
  by_cases hdegree :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdegree] at hresult
    obtain rfl := Option.some.inj hresult
    have hcomplete :=
      Hex.reassemblyExpansionComplete_constant_of_ne_zero f hf hdegree
    rcases Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
        _ _ raw hcomplete hraw with hx | hcore
    · exact Hex.xPowerFactorArray_irreducible _ raw hx
    · exfalso
      have hraw_one : raw = 1 := by
        have hraw_core :
            raw = (Hex.normalizeForFactor f).squareFreeCore := by
          simpa using hcore
        rw [hraw_core,
          Hex.squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdegree]
      rw [hraw_one, Hex.normalizeFactorSign_one,
        Hex.shouldRecordPolynomialFactor_one] at hrecord
      exact absurd hrecord (by decide)
  · rw [if_neg hdegree] at hresult
    by_cases hcap : Hex.latticePrecisionCap f = 0
    · rw [if_pos hcap] at hresult
      exact absurd hresult.symm (Option.some_ne_none factors)
    · rw [if_neg hcap] at hresult
      cases hquadratic :
          Hex.quadraticIntegerRootFactors?
            (Hex.normalizeForFactor f).squareFreeCore with
      | some coreFactors =>
          simp only [hquadratic] at hresult
          obtain rfl := Option.some.inj hresult
          refine
            Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
              _ _ ?_ ?_ hraw
          · exact
              IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
                f hf hquadratic
          · intro factor hfactor
            exact
              Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
                hcore_lc_pos hcore_prim hquadratic hfactor
      | none =>
          rw [hquadratic] at hresult
          rw [Option.map_eq_some_iff] at hresult
          obtain ⟨coreFactors, hlattice, rfl⟩ := hresult
          have hcore_pos :
              0 <
                (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 :=
            Nat.pos_of_ne_zero hdegree
          let prime :=
            directPrimePlan_facts
              ⟨(Hex.normalizeForFactor f).squareFreeCore⟩
              modular hplan hcore_prim hcore_lc_pos hcore_pos
          refine
            Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
              (Hex.normalizeForFactor f) coreFactors ?_ ?_ hraw
          · exact reassemblyExpansionComplete_latticeCore
              f hf (Hex.latticePrecisionCap f) modular.data prime
              hcore_pos
              (Hex.bhksRecoveryFloor_squareFreeCore_le_latticePrecisionCap f)
              hcap hlattice
          · exact latticeCoreFactorsWithBound_factor_irreducible
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.latticePrecisionCap f) modular.data prime
              hcore_lc_pos hcore_pos hcore_prim
              (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree
                f hf)
              (Hex.bhksRecoveryFloor_squareFreeCore_le_latticePrecisionCap f)
              hcap hlattice

/-- Every recorded raw factor returned by the standalone direct CLD branch is
irreducible. -/
theorem factorLatticeFactorsWithBound_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {factors : Array Hex.ZPoly}
    (hresult :
      Hex.factorLatticeFactorsWithBound f (Hex.latticePrecisionCap f) =
        some factors)
    {raw : Hex.ZPoly}
    (hraw : raw ∈ factors.toList)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
        (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  have hcore_lc_pos :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  rw [Hex.factorLatticeFactorsWithBound] at hresult
  by_cases hdegree :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdegree] at hresult
    obtain rfl := Option.some.inj hresult
    have hcomplete :=
      Hex.reassemblyExpansionComplete_constant_of_ne_zero f hf hdegree
    rcases Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
        _ _ raw hcomplete hraw with hx | hcore
    · exact Hex.xPowerFactorArray_irreducible _ raw hx
    · exfalso
      have hraw_one : raw = 1 := by
        have hraw_core :
            raw = (Hex.normalizeForFactor f).squareFreeCore := by
          simpa using hcore
        rw [hraw_core,
          Hex.squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdegree]
      rw [hraw_one, Hex.normalizeFactorSign_one,
        Hex.shouldRecordPolynomialFactor_one] at hrecord
      exact absurd hrecord (by decide)
  · rw [if_neg hdegree] at hresult
    by_cases hcap : Hex.latticePrecisionCap f = 0
    · rw [if_pos hcap] at hresult
      exact absurd hresult.symm (Option.some_ne_none factors)
    · rw [if_neg hcap] at hresult
      cases hquadratic :
          Hex.quadraticIntegerRootFactors?
            (Hex.normalizeForFactor f).squareFreeCore with
      | some coreFactors =>
          simp only [hquadratic] at hresult
          obtain rfl := Option.some.inj hresult
          refine
            Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
              _ _ ?_ ?_ hraw
          · exact
              IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
                f hf hquadratic
          · intro factor hfactor
            exact
              Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
                hcore_lc_pos hcore_prim hquadratic hfactor
      | none =>
          rw [hquadratic] at hresult
          cases hplan :
              Hex.directPrimePlan?
                ⟨(Hex.normalizeForFactor f).squareFreeCore⟩ with
          | none =>
              rw [hplan] at hresult
              exact absurd hresult.symm (Option.some_ne_none factors)
          | some modular =>
              rw [hplan] at hresult
              exact factorLatticeFactorsWithPlan_factor_irreducible
                f hf modular hplan hresult hraw hrecord

end

end HexBerlekampZassenhausMathlib
