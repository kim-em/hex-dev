/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Lattice.DirectSupport
public import HexBerlekampZassenhausMathlib.PartitionRefinement
import all HexBerlekampZassenhausMathlib.RecombinationSplit

public section
set_option backward.proofsInPublic true

/-!
# Direct-coordinate recovery from CLD signature classes

The RREF signature partition is interpreted using the same direct supports as
the classical engine.  Each class selects one canonical Hensel support and its
`DirectFactorCertificate`; the executable scaled candidate is therefore the
corresponding normalized irreducible factor.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

namespace BHKS

/-- Proof-side lifted support selected by one canonical signature class. -/
@[expose]
def liftedSubsetOfClass
    (d : Hex.LiftData) (members : List Nat) : LiftedFactorSubset d :=
  Finset.univ.filter fun i : LiftedFactorIndex d => i.val ∈ members

/-- Membership rule for `liftedSubsetOfClass`. -/
@[simp] theorem mem_liftedSubsetOfClass
    (d : Hex.LiftData) (members : List Nat) (i : LiftedFactorIndex d) :
    i ∈ liftedSubsetOfClass d members ↔ i.val ∈ members := by
  simp [liftedSubsetOfClass]

/-- Executable selected-factor array for one canonical signature class. -/
@[expose]
def selectedFactorsOfClass
    (liftedFactors : Array Hex.ZPoly) (members : List Nat) : Array Hex.ZPoly :=
  Hex.bhksIndicatorSelectedFactorsArray liftedFactors
    (classIndicatorArray liftedFactors.size members)

private theorem filterMap_if_eq_map_filter
    {α β : Type _} (l : List α) (p : α → Bool) (f : α → β) :
    l.filterMap (fun x => if p x then some (f x) else none) =
      (l.filter p).map f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x <;> simp [hp, ih]

private theorem liftedSubsetSelectedList_liftedSubsetOfClass
    (d : Hex.LiftData) (members : List Nat) :
    liftedSubsetSelectedList d (liftedSubsetOfClass d members) =
      ((List.finRange d.liftedFactors.size).filter
          fun i : Fin d.liftedFactors.size => i.val ∈ members).map
        (liftedFactor d) := by
  unfold liftedSubsetSelectedList liftedSubsetMask
  have hxs : d.liftedFactors.toList =
      (List.finRange d.liftedFactors.size).map
        (fun i => d.liftedFactors[i]) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [List.getElem_finRange]
  rw [hxs, List.zip_map', List.filterMap_map]
  simp only [Function.comp_def]
  rw [filterMap_if_eq_map_filter]
  simp [liftedFactor, liftedSubsetOfClass]

/-- Executable and proof-side selected products agree. -/
theorem selectedFactorsOfClass_polyProduct
    (d : Hex.LiftData) (members : List Nat) :
    Array.polyProduct (selectedFactorsOfClass d.liftedFactors members) =
      liftedFactorProduct d (liftedSubsetOfClass d members) := by
  rw [← polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial
      (Array.polyProduct (selectedFactorsOfClass d.liftedFactors members)) =
    HexPolyZMathlib.toPolynomial
      (Array.polyProduct
        (liftedSubsetSelectedList d
          (liftedSubsetOfClass d members)).toArray)
  rw [polyProduct_toPolynomial, polyProduct_toPolynomial]
  have hselected :=
    bhksIndicatorSelectedFactorsArray_classIndicatorArray_toList
      d.liftedFactors members
  rw [selectedFactorsOfClass, hselected, List.toList_toArray,
    liftedSubsetSelectedList_liftedSubsetOfClass]
  have hmap :
      ((List.finRange d.liftedFactors.size).filter
          fun i : Fin d.liftedFactors.size => i.val ∈ members).map
        (fun i => i.val) =
        (List.range d.liftedFactors.size).filter fun i => i ∈ members := by
    have hcoe_inj :
        Function.Injective
          (fun i : Fin d.liftedFactors.size => i.val) := by
      intro a b h
      exact Fin.ext h
    rw [List.map_filter
      (f := fun i : Fin d.liftedFactors.size => i.val)
      (p := fun i : Fin d.liftedFactors.size => i.val ∈ members)
      hcoe_inj (List.finRange d.liftedFactors.size)]
    rw [List.map_coe_finRange_eq_range]
    apply List.filter_congr
    intro i hi
    have hi_size : i < d.liftedFactors.size := List.mem_range.mp hi
    by_cases hmem : i ∈ members
    · rw [show decide (i ∈ members) = true from decide_eq_true hmem]
      apply decide_eq_true
      exact ⟨⟨i, hi_size⟩, by simp [hmem], rfl⟩
    · rw [show decide (i ∈ members) = false from decide_eq_false hmem]
      apply decide_eq_false
      intro hx
      rcases hx with ⟨x, hxmem, hxi⟩
      exact hmem (by
        have hxmem' : x.val ∈ members := of_decide_eq_true hxmem
        simpa [hxi] using hxmem')
  rw [← hmap]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  simp [liftedFactor, Array.getD, i.isLt]

/-- A canonical signature class is the carrier of one member of a genuine
support partition. -/
theorem liftedSubsetOfClass_mem
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcover : ∀ i : Fin r, ∃ S ∈ trueSupports, i ∈ S)
    (hdisjoint :
      ∀ S ∈ trueSupports, ∀ T ∈ trueSupports,
        ∀ i : Fin r, i ∈ S → i ∈ T → S = T)
    (d : Hex.LiftData) (hr : d.liftedFactors.size = r)
    {members : List Nat}
    (hmem : members ∈ supportPartitionByMinColumn trueSupports) :
    (↑(liftedSubsetOfClass d members) :
        Set (LiftedFactorIndex d)) ∈
      (hr ▸ trueSupports) := by
  subst r
  unfold supportPartitionByMinColumn at hmem
  rw [List.mem_map] at hmem
  obtain ⟨rep, hrep, rfl⟩ := hmem
  obtain ⟨S, hS, hmembers⟩ :=
    supportClassMembers_eq_support_of_partition
      trueSupports hcover hdisjoint hrep
  have hset :
      (↑(liftedSubsetOfClass d
          (supportClassMembers trueSupports rep)) :
        Set (LiftedFactorIndex d)) = S := by
    ext i
    simp only [SetLike.mem_coe, mem_liftedSubsetOfClass]
    exact (hmembers i.val).trans (by
      constructor
      · rintro ⟨_, hi⟩
        exact hi
      · intro hi
        exact ⟨i.isLt, hi⟩)
  rw [hset]
  exact hS

/-- The executable direct candidate attached to one signature class. -/
@[expose]
def recoveredClassFactor
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (members : List Nat) : Hex.ZPoly :=
  scaledRecombinationCandidate core (Hex.ZPoly.directLiftData core B data)
    (liftedSubsetOfClass (Hex.ZPoly.directLiftData core B data) members)

/-- Recovered factors in canonical signature-class order. -/
noncomputable def recoveredClassFactors
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData) :
    Array Hex.ZPoly :=
  ((supportPartitionByMinColumn (directTrueSupports core B data)).map
    (recoveredClassFactor core B data)).toArray

/-- Certificate selected by one canonical signature class. -/
structure RecoveredClassCertificate
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (members : List Nat) where
  /-- The modular support represented by the signature class. -/
  support : ModPFactorSubset data
  /-- The recovered irreducible factor and its direct-support proof. -/
  certificate : DirectFactorCertificate core B data support
  /-- The direct lifted support is exactly the selected signature class. -/
  support_eq :
    directLiftedSupport core B data support =
      liftedSubsetOfClass (Hex.ZPoly.directLiftData core B data) members

/-- Select the unique direct factor certificate carried by a canonical class. -/
noncomputable def recoveredClassCertificate
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcover : ∀ i, ∃ U ∈ directTrueSupports core B data, i ∈ U)
    (hdisjoint :
      ∀ U ∈ directTrueSupports core B data,
        ∀ V ∈ directTrueSupports core B data,
          ∀ i, i ∈ U → i ∈ V → U = V)
    {members : List Nat}
    (hmem : members ∈
      supportPartitionByMinColumn (directTrueSupports core B data)) :
    RecoveredClassCertificate core B data members := by
  let d := Hex.ZPoly.directLiftData core B data
  have hcarrier :
      (↑(liftedSubsetOfClass d members) : Set (LiftedFactorIndex d)) ∈
        directTrueSupports core B data :=
    liftedSubsetOfClass_mem
      (directTrueSupports core B data) hcover hdisjoint d rfl hmem
  let S := Classical.choose hcarrier
  have hS := Classical.choose_spec hcarrier
  let C := Classical.choice hS.1
  refine
    { support := S
      certificate := C
      support_eq := ?_ }
  apply Finset.coe_injective
  exact hS.2

/-- The executable factor of a signature class is exactly the normalized
irreducible factor in its direct certificate. -/
theorem recoveredClassFactor_eq
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcover : ∀ i, ∃ U ∈ directTrueSupports core B data, i ∈ U)
    (hdisjoint :
      ∀ U ∈ directTrueSupports core B data,
        ∀ V ∈ directTrueSupports core B data,
          ∀ i, i ∈ U → i ∈ V → U = V)
    {members : List Nat}
    (hmem : members ∈
      supportPartitionByMinColumn (directTrueSupports core B data)) :
    recoveredClassFactor core B data members =
      (recoveredClassCertificate hcover hdisjoint hmem).certificate.factor := by
  let R := recoveredClassCertificate hcover hdisjoint hmem
  unfold recoveredClassFactor
  rw [← R.support_eq]
  simpa [directSupportCandidate, directLiftedSupport] using
    R.certificate.candidate_eq

/-- Canonical recovered class factors multiply back to the primitive,
positive-leading primitive square-free part. -/
theorem recoveredClassFactors_polyProduct
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hpartition :
      DirectSupportPartition core B data Finset.univ core)
    (hcover : ∀ i, ∃ U ∈ directTrueSupports core B data, i ∈ U)
    (hdisjoint :
      ∀ U ∈ directTrueSupports core B data,
        ∀ V ∈ directTrueSupports core B data,
          ∀ i, i ∈ U → i ∈ V → U = V)
    (hcard :
      (directTrueSupports core B data).ncard =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    Array.polyProduct (recoveredClassFactors core B data) = core := by
  classical
  let supports := directTrueSupports core B data
  let classes := supportPartitionByMinColumn supports
  let factor := recoveredClassFactor core B data
  let gs : List (Polynomial ℤ) :=
    classes.map fun members => HexPolyZMathlib.toPolynomial (factor members)
  have hspec : ∀ (members : List Nat) (hmem : members ∈ classes),
      let R := recoveredClassCertificate hcover hdisjoint
        (by simpa only [classes, supports] using hmem)
      factor members = R.certificate.factor ∧
        Irreducible (HexPolyZMathlib.toPolynomial R.certificate.factor) ∧
        R.certificate.factor ∣ core ∧
        0 < Hex.DensePoly.leadingCoeff R.certificate.factor := by
    intro members hmem
    let R := recoveredClassCertificate hcover hdisjoint
      (by simpa only [classes, supports] using hmem)
    exact
      ⟨recoveredClassFactor_eq hcover hdisjoint
          (by simpa only [classes, supports] using hmem),
        R.certificate.irreducible,
        R.certificate.factor_dvd,
        R.certificate.leadingCoeff_pos⟩
  have hclasses_nodup : classes.Nodup := by
    unfold classes supportPartitionByMinColumn
    refine List.Nodup.map_on ?_ ((List.nodup_range).filter _)
    intro rep₁ hrep₁ rep₂ hrep₂ heq
    have hrep₁' : rep₁ ∈ supportRepresentativeColumns supports := hrep₁
    have hrep₂' : rep₂ ∈ supportRepresentativeColumns supports := hrep₂
    have h₁ : rep₁ ∈ supportClassMembers supports rep₂ := by
      rw [← heq]
      exact supportClassMembers_rep_mem supports hrep₁'
    have h₂ : rep₂ ∈ supportClassMembers supports rep₁ := by
      rw [heq]
      exact supportClassMembers_rep_mem supports hrep₂'
    rcases lt_trichotomy rep₁ rep₂ with hlt | heq' | hgt
    · exact absurd
        ((mem_supportClassMembers_iff supports rep₂ rep₁).mp h₁ |>.2)
        (supportRepresentativeColumns_min supports hrep₂' rep₁ hlt)
    · exact heq'
    · exact absurd
        ((mem_supportClassMembers_iff supports rep₁ rep₂).mp h₂ |>.2)
        (supportRepresentativeColumns_min supports hrep₁' rep₂ hgt)
  have hfactor_inj :
      ∀ m₁ ∈ classes, ∀ m₂ ∈ classes,
        HexPolyZMathlib.toPolynomial (factor m₁) =
          HexPolyZMathlib.toPolynomial (factor m₂) →
        m₁ = m₂ := by
    intro m₁ hm₁ m₂ hm₂ heq
    let R₁ := recoveredClassCertificate hcover hdisjoint
      (by simpa only [classes, supports] using hm₁)
    let R₂ := recoveredClassCertificate hcover hdisjoint
      (by simpa only [classes, supports] using hm₂)
    have hs₁ := hspec m₁ hm₁
    have hs₂ := hspec m₂ hm₂
    have hfactor_eq :
        HexPolyZMathlib.toPolynomial R₁.certificate.factor =
          HexPolyZMathlib.toPolynomial R₂.certificate.factor := by
      rw [← hs₁.1, ← hs₂.1]
      exact heq
    have hsupport :
        R₁.support = R₂.support :=
      hpartition.unique R₁.certificate.irreducible
        R₁.certificate.factor_dvd (Finset.subset_univ _)
        R₁.certificate.represented
        R₂.certificate.irreducible R₂.certificate.factor_dvd
        (Finset.subset_univ _) R₂.certificate.represented
        (Associated.of_eq hfactor_eq)
    have hsub :
        liftedSubsetOfClass (Hex.ZPoly.directLiftData core B data) m₁ =
          liftedSubsetOfClass (Hex.ZPoly.directLiftData core B data) m₂ := by
      rw [← R₁.support_eq, ← R₂.support_eq, hsupport]
    unfold classes supportPartitionByMinColumn at hm₁ hm₂
    rw [List.mem_map] at hm₁ hm₂
    obtain ⟨rep₁, hrep₁, rfl⟩ := hm₁
    obtain ⟨rep₂, hrep₂, rfl⟩ := hm₂
    have hrep₁' : rep₁ ∈ supportRepresentativeColumns supports := hrep₁
    have hrep₂' : rep₂ ∈ supportRepresentativeColumns supports := hrep₂
    have hmem₁ : rep₁ ∈ supportClassMembers supports rep₂ := by
      have hi : (⟨rep₁,
          supportRepresentativeColumns_lt supports hrep₁'⟩ :
          LiftedFactorIndex (Hex.ZPoly.directLiftData core B data)) ∈
          liftedSubsetOfClass (Hex.ZPoly.directLiftData core B data)
            (supportClassMembers supports rep₁) := by
        simp only [mem_liftedSubsetOfClass]
        exact supportClassMembers_rep_mem supports hrep₁'
      rw [hsub] at hi
      exact (mem_liftedSubsetOfClass _ _ _).mp hi
    have hmem₂ : rep₂ ∈ supportClassMembers supports rep₁ := by
      have hi : (⟨rep₂,
          supportRepresentativeColumns_lt supports hrep₂'⟩ :
          LiftedFactorIndex (Hex.ZPoly.directLiftData core B data)) ∈
          liftedSubsetOfClass (Hex.ZPoly.directLiftData core B data)
            (supportClassMembers supports rep₂) := by
        simp only [mem_liftedSubsetOfClass]
        exact supportClassMembers_rep_mem supports hrep₂'
      rw [← hsub] at hi
      exact (mem_liftedSubsetOfClass _ _ _).mp hi
    rcases lt_trichotomy rep₁ rep₂ with hlt | heq' | hgt
    · exact absurd
        ((mem_supportClassMembers_iff supports rep₂ rep₁).mp hmem₁ |>.2)
        (supportRepresentativeColumns_min supports hrep₂' rep₁ hlt)
    · rw [heq']
    · exact absurd
        ((mem_supportClassMembers_iff supports rep₁ rep₂).mp hmem₂ |>.2)
        (supportRepresentativeColumns_min supports hrep₁' rep₂ hgt)
  have hgs_nodup : gs.Nodup :=
    List.Nodup.map_on hfactor_inj hclasses_nodup
  let X := HexPolyZMathlib.toPolynomial core
  have hX_ne : X ≠ 0 := by
    intro h
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    show HexPolyZMathlib.toPolynomial core =
      HexPolyZMathlib.toPolynomial 0
    rw [HexPolyZMathlib.toPolynomial_zero]
    exact h
  have hsubset :
      (gs : Multiset (Polynomial ℤ)) ⊆
        UniqueFactorizationMonoid.normalizedFactors X := by
    intro p hp
    rw [Multiset.mem_coe, List.mem_map] at hp
    obtain ⟨members, hmembers, rfl⟩ := hp
    let R := recoveredClassCertificate hcover hdisjoint
      (by simpa only [classes, supports] using hmembers)
    have hs := hspec members hmembers
    change factor members = R.certificate.factor ∧
      Irreducible (HexPolyZMathlib.toPolynomial R.certificate.factor) ∧
      R.certificate.factor ∣ core ∧
      0 < Hex.DensePoly.leadingCoeff R.certificate.factor at hs
    rw [hs.1]
    have hdvd_poly :
        HexPolyZMathlib.toPolynomial R.certificate.factor ∣ X := by
      change HexPolyZMathlib.toPolynomial R.certificate.factor ∣
        HexPolyZMathlib.toPolynomial core
      exact HexPolyMathlib.toPolynomial_dvd R.certificate.factor_dvd
    obtain ⟨q, hq, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
        hX_ne R.certificate.irreducible hdvd_poly
    have hq_norm : normalize q = q :=
      UniqueFactorizationMonoid.normalize_normalized_factor q hq
    have hp_norm :
        normalize (HexPolyZMathlib.toPolynomial R.certificate.factor) =
          HexPolyZMathlib.toPolynomial R.certificate.factor := by
      have hlc :
          0 ≤ (HexPolyZMathlib.toPolynomial
            R.certificate.factor).leadingCoeff := by
        rw [HexPolyMathlib.leadingCoeff_toPolynomial]
        exact le_of_lt R.certificate.leadingCoeff_pos
      rw [normalize_apply, Polynomial.coe_normUnit, Int.normUnit_eq,
        ite_eq_left hlc, Units.val_one, Polynomial.C_1, mul_one]
    have heq :
        HexPolyZMathlib.toPolynomial R.certificate.factor = q := by
      rw [← hp_norm, ← hq_norm]
      exact normalize_eq_normalize_iff_associated.mpr hassoc
    rw [heq]
    exact hq
  have hle :
      (gs : Multiset (Polynomial ℤ)) ≤
        UniqueFactorizationMonoid.normalizedFactors X :=
    (Multiset.le_iff_subset (Multiset.coe_nodup.mpr hgs_nodup)).2 hsubset
  have hlength :
      gs.length =
        (UniqueFactorizationMonoid.normalizedFactors X).card := by
    have hpartition_length :=
      supportPartitionByMinColumn_length_eq_ncard_of_partition supports
        hcover hdisjoint
        (directTrueSupports.nonempty (core := core) (B := B) (data := data))
    simpa [gs, classes, X] using hpartition_length.trans hcard
  have hmultiset :
      (gs : Multiset (Polynomial ℤ)) =
        UniqueFactorizationMonoid.normalizedFactors X :=
    Multiset.eq_of_le_of_card_le hle (by
      change (UniqueFactorizationMonoid.normalizedFactors X).card ≤ gs.length
      omega)
  have hX_norm : normalize X = X := by
    have hlc : 0 ≤ X.leadingCoeff := by
      change 0 ≤ (HexPolyZMathlib.toPolynomial core).leadingCoeff
      rw [HexPolyMathlib.leadingCoeff_toPolynomial]
      exact le_of_lt hcore_lc_pos
    rw [normalize_apply, Polynomial.coe_normUnit, Int.normUnit_eq,
      ite_eq_left hlc, Units.val_one, Polynomial.C_1, mul_one]
  have hprod_norm :
      (UniqueFactorizationMonoid.normalizedFactors X).prod = X := by
    have h := UniqueFactorizationMonoid.prod_normalizedFactors_eq hX_ne
    rw [hX_norm] at h
    exact h
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial
      (Array.polyProduct (recoveredClassFactors core B data)) =
    HexPolyZMathlib.toPolynomial core
  rw [polyProduct_toPolynomial]
  simp only [recoveredClassFactors, List.toList_toArray, List.map_map,
    Function.comp_def]
  change gs.prod = X
  change (gs : Multiset (Polynomial ℤ)).prod = X
  rw [hmultiset]
  exact hprod_norm

/-- Exact projected span makes every executable signature-class candidate the
factor in its direct certificate. -/
theorem bhksIndicatorCandidates_eq_some_of_span_eq
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcover : ∀ i, ∃ U ∈ directTrueSupports core B data, i ∈ U)
    (hdisjoint :
      ∀ U ∈ directTrueSupports core B data,
        ∀ V ∈ directTrueSupports core B data,
          ∀ i, i ∈ U → i ∈ V → U = V)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).factorCount +
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).coeffWidth)
    (hspan :
      projectedRowSpanInt
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis core
              (Hex.ZPoly.directLiftData core B data).p
              (Hex.ZPoly.directLiftData core B data).k
              (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows) =
        trueSupportSpanInt (directTrueSupports core B data)) :
    Hex.bhksIndicatorCandidates? core
        (Hex.ZPoly.directLiftData core B data)
        (Hex.bhksEquivalenceClassIndicators
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis core
              (Hex.ZPoly.directLiftData core B data).p
              (Hex.ZPoly.directLiftData core B data).k
              (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows)) =
      some (recoveredClassFactors core B data) := by
  classical
  let d := Hex.ZPoly.directLiftData core B data
  let supports := directTrueSupports core B data
  let classes := supportPartitionByMinColumn supports
  let projected :=
    Hex.bhksProjectedRows
      (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors) hrows
  let indicators := Hex.bhksEquivalenceClassIndicators projected
  let candidates := recoveredClassFactors core B data
  have hfactorCount : projected.factorCount = d.liftedFactors.size := by
    rfl
  have hspan' :
      projectedRowSpanInt projected = trueSupportSpanInt supports := by
    simpa only [projected, supports, d] using hspan
  have hindicators :
      indicators =
        (classes.map (classIndicatorArray projected.factorCount)).toArray :=
    bhksEquivalenceClassIndicators_eq_supportPartition
      projected supports hspan'
  refine Hex.bhksIndicatorCandidates?_eq_some_of_getD
    core d indicators candidates ?_ ?_
  · rw [hindicators]
    simp [candidates, recoveredClassFactors, classes, supports]
  · intro i hi
    have hi_classes : i < classes.length := by
      rw [hindicators] at hi
      simpa using hi
    let members := classes[i]
    have hmembers : members ∈ classes := List.getElem_mem ..
    have hindicator :
        indicators.getD i #[] =
          classIndicatorArray d.liftedFactors.size members := by
      rw [hindicators]
      simp [Array.getD, hi_classes, members, hfactorCount]
    have hcandidate :
        candidates.getD i 0 = recoveredClassFactor core B data members := by
      simp [candidates, recoveredClassFactors, classes, supports,
        Array.getD, hi_classes, members]
    have hnonempty :
        ∃ j, j < (classIndicatorArray d.liftedFactors.size members).size ∧
          (classIndicatorArray d.liftedFactors.size members).getD j 0 = 1 := by
      have hmapped : members ∈
          (supportRepresentativeColumns supports).map
            (supportClassMembers supports) := by
        simpa only [classes, supportPartitionByMinColumn] using hmembers
      rw [List.mem_map] at hmapped
      obtain ⟨rep, hrep, hmembers_eq⟩ := hmapped
      have hrep_mem : rep ∈ members := by
        rw [← hmembers_eq]
        exact supportClassMembers_rep_mem supports hrep
      refine ⟨rep, ?_, ?_⟩
      · simpa [d] using supportRepresentativeColumns_lt supports hrep
      · exact classIndicatorArray_has_one_of_mem
          d.liftedFactors.size members
          (by simpa [d] using supportRepresentativeColumns_lt supports hrep)
          hrep_mem
    let selected := selectedFactorsOfClass d.liftedFactors members
    have hselected :
        Hex.bhksIndicatorSelectedFactors d.liftedFactors
            (classIndicatorArray d.liftedFactors.size members) =
          some selected :=
      Hex.bhksIndicatorSelectedFactors_eq_some_selectedArray_of_getD
        d.liftedFactors
        (classIndicatorArray d.liftedFactors.size members)
        (classIndicatorArray_size _ _)
        (classIndicatorArray_bits _ _) hnonempty
    let R := recoveredClassCertificate
      (by simpa only [supports, d] using hcover)
      (by simpa only [supports, d] using hdisjoint)
      (by simpa only [classes, supports] using hmembers)
    have hfactor_eq :
        recoveredClassFactor core B data members = R.certificate.factor :=
      recoveredClassFactor_eq
        (by simpa only [supports, d] using hcover)
        (by simpa only [supports, d] using hdisjoint)
        (by simpa only [classes, supports] using hmembers)
    have hrecovered :
        Hex.normalizeFactorSign
            (Hex.ZPoly.primitivePart
              (Hex.centeredLiftPoly
                (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
                  (liftedFactorProduct d
                    (liftedSubsetOfClass d members)))
                (d.p ^ d.k))) =
          R.certificate.factor := by
      simpa [recoveredClassFactor, scaledRecombinationCandidate,
        scaledLiftedFactorProduct, d] using hfactor_eq
    rw [hindicator, hcandidate, hfactor_eq]
    exact Hex.bhksIndicatorCandidate?_eq_some_of_scaledCandidate
      core d
      (classIndicatorArray d.liftedFactors.size members)
      selected R.certificate.factor
      (liftedFactorProduct d (liftedSubsetOfClass d members))
      hselected
      (selectedFactorsOfClass_polyProduct d members)
      R.certificate.factor_dvd
      R.certificate.leadingCoeff_pos
      (R.certificate.degree_pos hcore_primitive)
      hrecovered

/-- A nonempty genuine support partition cannot have exact projected span with
an empty executable row array. -/
theorem projectedRows_isEmpty_eq_false_of_span_eq
    (L : Hex.BhksProjectedRows)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hspan : projectedRowSpanInt L = trueSupportSpanInt trueSupports)
    (hcover : ∀ i : Fin L.factorCount, ∃ S ∈ trueSupports, i ∈ S)
    (hclasses : supportPartitionByMinColumn trueSupports ≠ []) :
    L.projectedRows.isEmpty = false := by
  classical
  by_contra hfalse
  have hempty : L.projectedRows.isEmpty = true := by
    cases h : L.projectedRows.isEmpty <;> simp_all
  have hsize : L.projectedRows.size = 0 :=
    Array.isEmpty_iff_size_eq_zero.mp hempty
  have hspan_bot : projectedRowSpanInt L = ⊥ := by
    unfold projectedRowSpanInt
    have hrange :
        Set.range (fun i : Fin L.projectedRows.size =>
          Matrix.row (projectedRowsIntMatrix L) i) = ∅ := by
      ext v
      simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨i, rfl⟩
      have hi := i.isLt
      omega
    rw [hrange, Submodule.span_empty]
  obtain ⟨members, hmembers⟩ :=
    List.exists_mem_of_ne_nil _ hclasses
  unfold supportPartitionByMinColumn at hmembers
  rw [List.mem_map] at hmembers
  obtain ⟨rep, hrep, _⟩ := hmembers
  have hreplt := supportRepresentativeColumns_lt trueSupports hrep
  obtain ⟨S, hS, hrepS⟩ := hcover ⟨rep, hreplt⟩
  let support : trueSupports := ⟨S, hS⟩
  have hindicator :
      indicatorVector support.1 ∈ projectedRowSpanInt L := by
    rw [hspan]
    exact indicatorVector_mem_trueSupportSpanInt trueSupports support
  rw [hspan_bot] at hindicator
  have hzero : indicatorVector S = 0 := hindicator
  have hcoord := congrFun hzero ⟨rep, hreplt⟩
  rw [indicatorVector_apply_mem S hrepS] at hcoord
  norm_num at hcoord

/-- With at least two true supports, exact span recovery passes every
fixed-precision BHKS check. -/
theorem bhksRecover_eq_some_of_span_eq
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hpartition :
      DirectSupportPartition core B data Finset.univ core)
    (hcover : ∀ i, ∃ U ∈ directTrueSupports core B data, i ∈ U)
    (hdisjoint :
      ∀ U ∈ directTrueSupports core B data,
        ∀ V ∈ directTrueSupports core B data,
          ∀ i, i ∈ U → i ∈ V → U = V)
    (hcard :
      (directTrueSupports core B data).ncard =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).factorCount +
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).coeffWidth)
    (hspan :
      projectedRowSpanInt
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis core
              (Hex.ZPoly.directLiftData core B data).p
              (Hex.ZPoly.directLiftData core B data).k
              (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows) =
        trueSupportSpanInt (directTrueSupports core B data))
    (hclasses : 2 ≤
      (supportPartitionByMinColumn
        (directTrueSupports core B data)).length) :
    Hex.bhksRecover? core (Hex.ZPoly.directLiftData core B data) =
      some (recoveredClassFactors core B data) := by
  let d := Hex.ZPoly.directLiftData core B data
  let L := Hex.bhksLatticeBasis core d.p d.k d.liftedFactors
  let projected := Hex.bhksProjectedRows L hrows
  let supports := directTrueSupports core B data
  let indicators := Hex.bhksEquivalenceClassIndicators projected
  let candidates := recoveredClassFactors core B data
  have hfactorCount : projected.factorCount = d.liftedFactors.size := by
    rfl
  have hspan' : projectedRowSpanInt projected =
      trueSupportSpanInt supports := by
    simpa only [projected, L, supports, d] using hspan
  have hindicators :
      indicators =
        ((supportPartitionByMinColumn supports).map
          (classIndicatorArray projected.factorCount)).toArray :=
    bhksEquivalenceClassIndicators_eq_supportPartition
      projected supports hspan'
  have hind_size :
      indicators.size =
        (supportPartitionByMinColumn supports).length := by
    rw [hindicators]
    simp
  have hind_nonempty : indicators.isEmpty = false := by
    cases he : indicators.isEmpty with
    | false => rfl
    | true =>
        have hz : indicators.size = 0 :=
          Array.isEmpty_iff_size_eq_zero.mp he
        rw [hind_size] at hz
        have hc : 2 ≤ (supportPartitionByMinColumn supports).length := by
          simpa only [supports] using hclasses
        omega
  have hclasses_ne :
      supportPartitionByMinColumn (directTrueSupports core B data) ≠ [] := by
    intro hnil
    have hz :=
      congrArg List.length hnil
    simp only [List.length_nil] at hz
    omega
  have hprojected_nonempty : projected.projectedRows.isEmpty = false := by
    simpa only [projected, L, supports, d] using
      (projectedRows_isEmpty_eq_false_of_span_eq
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis core
            (Hex.ZPoly.directLiftData core B data).p
            (Hex.ZPoly.directLiftData core B data).k
            (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows)
        (directTrueSupports core B data) hspan hcover hclasses_ne)
  have hind_not_one : (indicators.size == 1) = false := by
    simp only [beq_eq_false_iff_ne]
    rw [hind_size]
    have hc : 2 ≤ (supportPartitionByMinColumn supports).length := by
      simpa only [supports] using hclasses
    omega
  have hnondeg :
      Hex.bhksDegenerateIndicatorPartition projected indicators = false :=
    Hex.bhksDegenerateIndicatorPartition_eq_false
      projected indicators hind_nonempty hprojected_nonempty hind_not_one
  have hcandidates :
      Hex.bhksIndicatorCandidates? core d indicators = some candidates := by
    simpa only [d, L, projected, indicators, candidates] using
      (bhksIndicatorCandidates_eq_some_of_span_eq
        hcore_primitive hcover hdisjoint hrows hspan)
  have hproduct : Array.polyProduct candidates = core := by
    simpa only [candidates] using
      (recoveredClassFactors_polyProduct hcore_ne hcore_primitive
        hcore_lc_pos hpartition hcover hdisjoint hcard)
  exact Hex.bhksRecover?_eq_some_of_checks core d hrows
    (by simpa only [L, projected, indicators] using hnondeg)
    (by simpa only [candidates] using hcandidates)
    hproduct

/-- With exactly one true support, exact span recovery yields the executable
single-all-ones irreducibility certificate. -/
theorem bhksSingleAllOnesPartition_eq_true_of_span_eq
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcover : ∀ i, ∃ U ∈ directTrueSupports core B data, i ∈ U)
    (hdisjoint :
      ∀ U ∈ directTrueSupports core B data,
        ∀ V ∈ directTrueSupports core B data,
          ∀ i, i ∈ U → i ∈ V → U = V)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).factorCount +
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).coeffWidth)
    (hspan :
      projectedRowSpanInt
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis core
              (Hex.ZPoly.directLiftData core B data).p
              (Hex.ZPoly.directLiftData core B data).k
              (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows) =
        trueSupportSpanInt (directTrueSupports core B data))
    (hclasses :
      (supportPartitionByMinColumn
        (directTrueSupports core B data)).length = 1) :
    Hex.bhksSingleAllOnesPartition core
      (Hex.ZPoly.directLiftData core B data) = true := by
  classical
  let d := Hex.ZPoly.directLiftData core B data
  let L := Hex.bhksLatticeBasis core d.p d.k d.liftedFactors
  let projected := Hex.bhksProjectedRows L hrows
  let supports := directTrueSupports core B data
  let classes := supportPartitionByMinColumn supports
  let indicators := Hex.bhksEquivalenceClassIndicators projected
  have hfactorCount : projected.factorCount = d.liftedFactors.size := by
    rfl
  have hspan' : projectedRowSpanInt projected =
      trueSupportSpanInt supports := by
    simpa only [projected, L, supports, d] using hspan
  have hindicators :
      indicators =
        (classes.map
          (classIndicatorArray projected.factorCount)).toArray :=
    bhksEquivalenceClassIndicators_eq_supportPartition
      projected supports hspan'
  have hclasses' : classes.length = 1 := by
    simpa only [classes, supports] using hclasses
  obtain ⟨members, hclasses_list⟩ :=
    List.length_eq_one_iff.mp hclasses'
  have hmembers : members ∈ classes := by
    rw [hclasses_list]
    simp
  have hmapped : members ∈
      (supportRepresentativeColumns supports).map
        (supportClassMembers supports) := by
    simpa only [classes, supportPartitionByMinColumn] using hmembers
  rw [List.mem_map] at hmapped
  obtain ⟨rep, hrep, hmembers_eq⟩ := hmapped
  obtain ⟨classSupport, hclassSupport, hmember_iff⟩ :=
    supportClassMembers_eq_support_of_partition supports
      (by simpa only [supports, d] using hcover)
      (by simpa only [supports, d] using hdisjoint)
      hrep
  have hncard : supports.ncard = 1 := by
    rw [← supportPartitionByMinColumn_length_eq_ncard_of_partition
      supports
      (by simpa only [supports, d] using hcover)
      (by simpa only [supports, d] using hdisjoint)
      (by
        simpa only [supports, d] using
          (directTrueSupports.nonempty
            (core := core) (B := B) (data := data)))]
    exact hclasses'
  obtain ⟨onlySupport, hsupports⟩ := Set.ncard_eq_one.mp hncard
  have hclass_only : classSupport = onlySupport := by
    rw [hsupports] at hclassSupport
    simpa using hclassSupport
  have hall_members :
      ∀ i, i < projected.factorCount → i ∈ members := by
    intro i hi
    have hi' : i < d.liftedFactors.size := by
      rw [hfactorCount] at hi
      exact hi
    obtain ⟨T, hT, hiT⟩ := hcover ⟨i, hi'⟩
    have hT_only : T = onlySupport := by
      have hT' : T ∈ supports := by simpa only [supports] using hT
      rw [hsupports] at hT'
      simpa using hT'
    have hi_class : (⟨i, hi'⟩ : LiftedFactorIndex d) ∈ classSupport := by
      simpa only [hT_only, hclass_only] using hiT
    have himem :
        i ∈ supportClassMembers supports rep :=
      (hmember_iff i).2 ⟨hi', hi_class⟩
    rw [hmembers_eq] at himem
    exact himem
  have hindicator_zero :
      indicators.getD 0 #[] =
        classIndicatorArray projected.factorCount members := by
    rw [hindicators, hclasses_list]
    simp [Array.getD]
  have hallones :
      Hex.bhksIndicatorAllOnes projected.factorCount
          (indicators.getD 0 #[]) = true := by
    apply Hex.bhksIndicatorAllOnes_eq_true_of_getD
    · rw [hindicator_zero, classIndicatorArray_size]
    · intro i hi
      rw [hindicator_zero, classIndicatorArray_getD]
      simp [hi, hall_members i hi]
  have hind_nonempty : indicators.isEmpty = false := by
    cases he : indicators.isEmpty with
    | false => rfl
    | true =>
        have hz : indicators.size = 0 :=
          Array.isEmpty_iff_size_eq_zero.mp he
        have hone : indicators.size = 1 := by
          rw [hindicators, hclasses_list]
          simp
        omega
  have hclasses_ne :
      supportPartitionByMinColumn (directTrueSupports core B data) ≠ [] := by
    intro hnil
    rw [hnil] at hclasses
    simp at hclasses
  have hprojected_nonempty : projected.projectedRows.isEmpty = false := by
    simpa only [projected, L, supports, d] using
      (projectedRows_isEmpty_eq_false_of_span_eq
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis core
            (Hex.ZPoly.directLiftData core B data).p
            (Hex.ZPoly.directLiftData core B data).k
            (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows)
        (directTrueSupports core B data) hspan hcover hclasses_ne)
  rw [Hex.bhksSingleAllOnesPartition, dite_eq_left hrows]
  change (!indicators.isEmpty && !projected.projectedRows.isEmpty &&
    indicators.size == 1 &&
      Hex.bhksIndicatorAllOnes projected.factorCount
        (indicators.getD 0 #[])) = true
  have hind_size : indicators.size = 1 := by
    rw [hindicators, hclasses_list]
    simp
  have hzero_lt : 0 < indicators.size := by omega
  have hallones_get :
      Hex.bhksIndicatorAllOnes projected.factorCount indicators[0] = true := by
    simpa [Array.getD, hzero_lt] using hallones
  simp [hind_nonempty, hprojected_nonempty, hind_size, hallones_get]

end BHKS

end
end HexBerlekampZassenhausMathlib
