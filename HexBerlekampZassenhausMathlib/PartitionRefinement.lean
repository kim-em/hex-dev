import HexBerlekampZassenhausMathlib.Recovery
import HexBerlekampZassenhausMathlib.Basic
import HexBerlekampZassenhausMathlib.CLDColumnBound
import HexBerlekampZassenhausMathlib.IntReductionMod
import HexBerlekampZassenhausMathlib.BHKSIndependent

/-!
BHKS B8 partition-refinement step.

The fast-core success branch certified by
`factorFastCoreWithBound_some_factor_count_ge_of_irreducible` consumes an
irreducibility witness for every emitted factor. This module derives that
witness from the BHKS recovery side data: the support-driven canonical
indicator array `BHKS.expectedIndicatorArrayOfSupports trueSupports` has one
row per support-equivalence class, and
`BHKS.ForwardRecoveryInputs.ExpectedTrueFactors` transports that class count
to the polynomial-side factor list length. Under the B8 partition-refinement
hypothesis (the class count matches `normalizedFactors.card`), the existing
UFD partition argument upgrades the count equality to factor irreducibility.

The B8 partition-refinement hypothesis itself is the deeper BHKS Lemma 3.4
obligation discharged elsewhere; this module supplies the count and
irreducibility derivation that consumes it.
-/

namespace HexBerlekampZassenhausMathlib

namespace BHKS

/-- The expected indicator array has one row per support-equivalence class. -/
theorem expectedIndicatorArrayOfSupports_size {r : Nat}
    (trueSupports : Set (Set (Fin r))) :
    (expectedIndicatorArrayOfSupports trueSupports).size =
      (supportPartitionByMinColumn trueSupports).length := by
  simp [expectedIndicatorArrayOfSupports]

/-! ### Support-partition length from a genuine partition

The B8 partition-refinement hypothesis `hpartition` consumed by the fast-core
irreducibility wrappers is an equality
`(supportPartitionByMinColumn trueSupports).length = normalizedFactors.card`.
The lemma below supplies the provider-agnostic combinatorial half of that
discharge: when `trueSupports` is a genuine partition of `Fin r` into nonempty
parts (each column lies in exactly one part), the support-equivalence partition
has exactly one class per part, so its length is the number of parts.  A
`trueSupports`-builder pairs this with a bijection from the parts to
`normalizedFactors (toPolynomial core)`. -/

/-- The chosen part of a covered column. -/
private noncomputable def partOf {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcover : ∀ i : Fin r, ∃ S ∈ trueSupports, i ∈ S) (i : Fin r) :
    Set (Fin r) :=
  (hcover i).choose

private theorem partOf_mem {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcover : ∀ i : Fin r, ∃ S ∈ trueSupports, i ∈ S) (i : Fin r) :
    partOf trueSupports hcover i ∈ trueSupports :=
  (hcover i).choose_spec.1

private theorem mem_partOf {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcover : ∀ i : Fin r, ∃ S ∈ trueSupports, i ∈ S) (i : Fin r) :
    i ∈ partOf trueSupports hcover i :=
  (hcover i).choose_spec.2

private theorem partOf_eq_of_mem {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcover : ∀ i : Fin r, ∃ S ∈ trueSupports, i ∈ S)
    (hdisj : ∀ S ∈ trueSupports, ∀ T ∈ trueSupports, ∀ i : Fin r,
      i ∈ S → i ∈ T → S = T)
    {i : Fin r} {S : Set (Fin r)} (hS : S ∈ trueSupports) (hi : i ∈ S) :
    partOf trueSupports hcover i = S :=
  hdisj _ (partOf_mem trueSupports hcover i) _ hS i (mem_partOf trueSupports hcover i) hi

/-- For a partition `trueSupports`, the support-equivalence partition has exactly
one class per part: its length equals the number of parts `trueSupports.ncard`. -/
theorem supportPartitionByMinColumn_length_eq_ncard_of_partition {r : Nat}
    (trueSupports : Set (Set (Fin r)))
    (hcover : ∀ i : Fin r, ∃ S ∈ trueSupports, i ∈ S)
    (hdisj : ∀ S ∈ trueSupports, ∀ T ∈ trueSupports, ∀ i : Fin r,
      i ∈ S → i ∈ T → S = T)
    (hne : ∀ S ∈ trueSupports, S.Nonempty) :
    (supportPartitionByMinColumn trueSupports).length = trueSupports.ncard := by
  classical
  set L := supportRepresentativeColumns trueSupports with hL
  -- The partition length is the number of class representatives.
  have hlen : (supportPartitionByMinColumn trueSupports).length = L.length := by
    unfold supportPartitionByMinColumn
    rw [List.length_map]
  rw [hlen]
  -- `L` is nodup (a filter of `List.range r`).
  have hLnodup : L.Nodup := by
    rw [hL]
    unfold supportRepresentativeColumns
    exact (List.nodup_range).filter _
  -- Two columns lying in the same part are support-equivalent, and conversely.
  have hpart_equiv : ∀ {i j : Fin r},
      partOf trueSupports hcover i = partOf trueSupports hcover j →
      supportEquivalent trueSupports i j := by
    intro i j hij T hT
    constructor
    · intro hiT
      have : partOf trueSupports hcover i = T :=
        partOf_eq_of_mem trueSupports hcover hdisj hT hiT
      have hjT : j ∈ partOf trueSupports hcover j := mem_partOf trueSupports hcover j
      rw [← hij, this] at hjT
      exact hjT
    · intro hjT
      have : partOf trueSupports hcover j = T :=
        partOf_eq_of_mem trueSupports hcover hdisj hT hjT
      have hiT : i ∈ partOf trueSupports hcover i := mem_partOf trueSupports hcover i
      rw [hij, this] at hiT
      exact hiT
  -- The representative-to-part map.
  let F : Nat → Set (Fin r) :=
    fun rep => if h : rep < r then partOf trueSupports hcover ⟨rep, h⟩ else ∅
  have hF_mem : ∀ rep ∈ L, F rep ∈ trueSupports := by
    intro rep hrep
    have hlt : rep < r := supportRepresentativeColumns_lt trueSupports (hL ▸ hrep)
    simp only [F, dif_pos hlt]
    exact partOf_mem trueSupports hcover _
  -- Bijection between the representative finset and the parts.
  have hbij : Set.BijOn F (↑L.toFinset) trueSupports := by
    refine ⟨?_, ?_, ?_⟩
    · -- MapsTo
      intro rep hrep
      rw [Finset.mem_coe, List.mem_toFinset] at hrep
      exact hF_mem rep hrep
    · -- InjOn
      intro rep1 hrep1 rep2 hrep2 hFeq
      rw [Finset.mem_coe, List.mem_toFinset] at hrep1 hrep2
      have hlt1 : rep1 < r := supportRepresentativeColumns_lt trueSupports (hL ▸ hrep1)
      have hlt2 : rep2 < r := supportRepresentativeColumns_lt trueSupports (hL ▸ hrep2)
      simp only [F, dif_pos hlt1, dif_pos hlt2] at hFeq
      have hequiv : supportEquivalent trueSupports ⟨rep1, hlt1⟩ ⟨rep2, hlt2⟩ :=
        hpart_equiv hFeq
      have hequivAt : supportEquivalentAt trueSupports rep1 rep2 :=
        (supportEquivalentAt_iff trueSupports hlt1 hlt2).mpr hequiv
      rcases lt_trichotomy rep1 rep2 with hlt | heq | hgt
      · exact absurd hequivAt
          (supportRepresentativeColumns_min trueSupports (hL ▸ hrep2) rep1 hlt)
      · exact heq
      · exact absurd (supportEquivalentAt_symm trueSupports hequivAt)
          (supportRepresentativeColumns_min trueSupports (hL ▸ hrep1) rep2 hgt)
    · -- SurjOn
      intro S hS
      obtain ⟨i, hi⟩ := hne S hS
      -- The least column equivalent to `i` is a representative.
      let C : Finset Nat :=
        (Finset.range r).filter (fun k => supportEquivalentAt trueSupports k i.val)
      have hiC : i.val ∈ C := by
        simp only [C, Finset.mem_filter, Finset.mem_range]
        exact ⟨i.isLt, supportEquivalentAt_refl trueSupports i.isLt⟩
      have hCne : C.Nonempty := ⟨i.val, hiC⟩
      set m := C.min' hCne with hm
      have hmC : m ∈ C := C.min'_mem hCne
      have hm_lt : m < r := by
        simp only [C, Finset.mem_filter, Finset.mem_range] at hmC
        exact hmC.1
      have hm_equiv_i : supportEquivalentAt trueSupports m i.val := by
        simp only [C, Finset.mem_filter, Finset.mem_range] at hmC
        exact hmC.2
      -- `m` is fresh: no smaller column is equivalent to it.
      have hm_fresh : ∀ k, k < m → ¬ supportEquivalentAt trueSupports k m := by
        intro k hk hke
        have hk_equiv_i : supportEquivalentAt trueSupports k i.val :=
          supportEquivalentAt_trans trueSupports hke hm_equiv_i
        have hk_lt : k < r := by
          rcases hk_equiv_i with ⟨hk_lt, _, _⟩; exact hk_lt
        have hkC : k ∈ C := by
          simp only [C, Finset.mem_filter, Finset.mem_range]
          exact ⟨hk_lt, hk_equiv_i⟩
        exact absurd (C.min'_le k hkC) (by omega)
      have hm_rep : m ∈ L := by
        rw [hL, mem_supportRepresentativeColumns_iff]
        exact ⟨hm_lt, hm_fresh⟩
      refine ⟨m, by rw [Finset.mem_coe, List.mem_toFinset]; exact hm_rep, ?_⟩
      -- `F m = S`.
      have hmi : supportEquivalent trueSupports ⟨m, hm_lt⟩ i :=
        (supportEquivalentAt_iff trueSupports hm_lt i.isLt).mp
          (by simpa using hm_equiv_i)
      have hmS : (⟨m, hm_lt⟩ : Fin r) ∈ S := (hmi S hS).mpr hi
      simp only [F, dif_pos hm_lt]
      exact partOf_eq_of_mem trueSupports hcover hdisj hS hmS
  -- Conclude via the bijection.
  have hncard : trueSupports.ncard = L.length := by
    rw [← hbij.image_eq, Set.InjOn.ncard_image hbij.injOn,
      Set.ncard_coe_finset, List.toFinset_card_of_nodup hLnodup]
  rw [hncard]

/--
Concrete lifted-support partition count for the true supports represented by a
`LiftedFactorSubsetPartition core d Finset.univ core`.

This composes the lifted-index cover/disjoint/nonempty facts with the generic
support-equivalence partition spine above. The remaining arithmetic count
identifying this `ncard` with `normalizedFactors (toPolynomial core).card` is
kept separate.
-/
theorem supportPartitionByMinColumn_length_eq_liftedTrueSupports_ncard
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    (supportPartitionByMinColumn (liftedTrueSupports core d)).length =
      (liftedTrueSupports core d).ncard :=
  supportPartitionByMinColumn_length_eq_ncard_of_partition
    (liftedTrueSupports core d)
    (liftedTrueSupports.cover_of_partition hpartition)
    (liftedTrueSupports.eq_of_mem_inter_of_partition hpartition)
    (liftedTrueSupports.nonempty_of_partition
      hpartition hcore_ne hcore_primitive hcore_lc_pos hprecision)

/--
B8 partition-refinement equality for the lifted true-support family: the
support-equivalence partition length matches the number of normalized
irreducible factors of `core`.

This composes the lifted-support partition count
(`supportPartitionByMinColumn_length_eq_liftedTrueSupports_ncard`) with the
support-to-factor bijection (`liftedTrueSupports.ncard_eq_normalizedFactors_card`),
exposing exactly the `hpartition` hypothesis consumed by
`factorFastCoreWithBound_some_factor_zpolyIrreducible`.
-/
theorem supportPartitionByMinColumn_length_eq_normalizedFactors_card
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    (supportPartitionByMinColumn (liftedTrueSupports core d)).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  rw [supportPartitionByMinColumn_length_eq_liftedTrueSupports_ncard
      hpartition hcore_ne hcore_primitive hcore_lc_pos hprecision,
    liftedTrueSupports.ncard_eq_normalizedFactors_card hpartition hcore_ne]

/--
Fast-path B8 partition-refinement count from core facts alone.

Composes the carrier-free `toMonicPrimeData?` partition producer
`liftedFactorSubsetPartition_of_toMonicPrimeData_complete` -- which derives the
full `LiftedFactorSubsetPartition core (toMonicLiftData core B primeData)
Finset.univ core` from the executable selection witness and the standard core
side conditions, without routing through slow exhaustive enumeration -- with the
generic count theorem
`supportPartitionByMinColumn_length_eq_normalizedFactors_card`.

The result discharges the exact `hpartition` length-equality shape threaded
through the fast-BHKS irreducibility wrappers, for the lifted true-support family
`liftedTrueSupports core (toMonicLiftData core B primeData)`, with no free
partition hypothesis.  `hbound` is the monic-coordinate Mignotte precision the
producer consumes; `hcore_bound` is the corresponding core-coordinate precision
that the count theorem needs (the two refer to distinct default coefficient
bounds, so both are supplied by the caller).
-/
theorem supportPartitionByMinColumn_length_eq_normalizedFactors_card_of_toMonicPrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (hcore_bound :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p) :
    (supportPartitionByMinColumn
        (liftedTrueSupports core
          (Hex.ZPoly.toMonicLiftData core B primeData))).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  have hcore_ne : core ≠ 0 := by
    intro h
    rw [h, Hex.DensePoly.leadingCoeff_zero] at hcore_lc_pos
    exact lt_irrefl 0 hcore_lc_pos
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k =
      Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_k _ _ _
  have hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hcore_bound
  exact supportPartitionByMinColumn_length_eq_normalizedFactors_card
    (liftedFactorSubsetPartition_of_toMonicPrimeData_complete
      core B primeData hselected hcore_lc_pos hcore_pos hcore_prim hcore_sqfree
      hB_ne_zero hbound)
    hcore_ne hcore_prim hcore_lc_pos hprecision

namespace ForwardRecoveryInputs

/-- Under an `ExpectedTrueFactors` package whose indicators are the
support-driven canonical indicator array, the expected factor count equals
the support-equivalence partition length. -/
theorem ExpectedTrueFactors.size_eq_supportPartitionByMinColumn_length
    {f : Hex.ZPoly} {r : Nat} (trueSupports : Set (Set (Fin r)))
    {expectedFactors : Array Hex.ZPoly}
    (htrue : ExpectedTrueFactors f
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors) :
    expectedFactors.size =
      (supportPartitionByMinColumn trueSupports).length := by
  rw [htrue.size_eq, expectedIndicatorArrayOfSupports_size]

/-- The polynomial-transported expected factor list has length equal to the
support-equivalence partition length. -/
theorem ExpectedTrueFactors.polynomial_length_eq_supportPartitionByMinColumn_length
    {f : Hex.ZPoly} {r : Nat} (trueSupports : Set (Set (Fin r)))
    {expectedFactors : Array Hex.ZPoly}
    (htrue : ExpectedTrueFactors f
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors) :
    (expectedFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (supportPartitionByMinColumn trueSupports).length := by
  rw [List.length_map, Array.length_toList,
    ExpectedTrueFactors.size_eq_supportPartitionByMinColumn_length trueSupports htrue]

/-- Under the B8 partition-refinement hypothesis (the support-equivalence
partition has the same length as `normalizedFactors`), the polynomial-
transported expected factor list has length `normalizedFactors.card`. -/
theorem ExpectedTrueFactors.polynomial_length_eq_normalizedFactors_card
    {f : Hex.ZPoly} {r : Nat} (trueSupports : Set (Set (Fin r)))
    {expectedFactors : Array Hex.ZPoly}
    (htrue : ExpectedTrueFactors f
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hpartition :
      (supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial f)).card) :
    (expectedFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial f)).card := by
  rw [ExpectedTrueFactors.polynomial_length_eq_supportPartitionByMinColumn_length
    trueSupports htrue, hpartition]

/-- Under the B8 partition-refinement hypothesis, every polynomial-transported
expected factor is irreducible. This is the B8 partition-refinement output
the downstream fast-core irreducibility argument consumes. -/
theorem ExpectedTrueFactors.irreducible_of_partition_count
    {f : Hex.ZPoly} {r : Nat} (trueSupports : Set (Set (Fin r)))
    {expectedFactors : Array Hex.ZPoly}
    (htrue : ExpectedTrueFactors f
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hf_ne : f ≠ 0)
    (hpartition :
      (supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial f)).card) :
    ∀ g ∈ expectedFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial g) := by
  set fpoly := HexPolyZMathlib.toPolynomial f with hf_def
  have hfpoly_ne : fpoly ≠ 0 := by
    intro hzero
    apply hf_ne
    apply HexPolyZMathlib.equiv.injective
    simpa using hzero
  set gs : List (Polynomial ℤ) :=
    expectedFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  have hpos_factor : ∀ g ∈ expectedFactors,
      0 < (HexPolyZMathlib.toPolynomial g).natDegree := by
    intro g hg
    obtain ⟨i, hi_lt, hget⟩ := Array.mem_iff_getElem.mp hg
    have hi_lt' : i < (expectedIndicatorArrayOfSupports trueSupports).size := by
      rw [← htrue.size_eq]; exact hi_lt
    have hdeg := htrue.positive_degree i hi_lt'
    have hgetD : expectedFactors.getD i 0 = g := by
      have := Array.getElem_eq_getD (xs := expectedFactors) (i := i) (h := hi_lt) 0
      rw [← this]; exact hget
    rw [HexPolyMathlib.natDegree_toPolynomial, ← hgetD]
    exact hdeg
  have hne_all : ∀ g ∈ gs, g ≠ 0 := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [Array.mem_toList_iff] at hfactor_mem
    rw [← hg_eq]
    exact Polynomial.ne_zero_of_natDegree_gt (hpos_factor factor hfactor_mem)
  have hnonunit_all : ∀ g ∈ gs, ¬ IsUnit g := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [Array.mem_toList_iff] at hfactor_mem
    rw [← hg_eq]
    exact Polynomial.not_isUnit_of_natDegree_pos _ (hpos_factor factor hfactor_mem)
  have hprod : Associated gs.prod fpoly := by
    have hp_factor : Array.polyProduct expectedFactors = f := htrue.product_eq
    have hp_poly :
        (expectedFactors.toList.map HexPolyZMathlib.toPolynomial).prod =
          HexPolyZMathlib.toPolynomial f := by
      rw [← polyProduct_toPolynomial, hp_factor]
    rw [hgs_def, hp_poly, hf_def]
  have hcount :
      gs.length =
        (UniqueFactorizationMonoid.normalizedFactors fpoly).card := by
    rw [hgs_def, hf_def]
    exact ExpectedTrueFactors.polynomial_length_eq_normalizedFactors_card
      trueSupports htrue hpartition
  intro g hg
  have hg_arr : g ∈ expectedFactors := Array.mem_toList_iff.mp hg
  have hgmem : HexPolyZMathlib.toPolynomial g ∈ gs := by
    rw [hgs_def, List.mem_map]
    exact ⟨g, hg, rfl⟩
  exact UFDPartition.irreducible_of_partition_card_eq_normalizedFactors_card
    hfpoly_ne gs hne_all hnonunit_all hprod hcount _ hgmem

end ForwardRecoveryInputs

end BHKS

namespace BHKS

/--
Candidate-size producer for the forward-cut `hsize` hypothesis.

This is the fixed-lift core fact behind fast-branch forward-cut callers: a
successful `bhksIndicatorCandidates?` run over the canonical
`equivalenceClassIndicatorsOfLiftData` emits exactly one candidate per
equivalence-class indicator row.
-/
theorem size_eq_indicators_of_candidates
    {core : Hex.ZPoly} {d : Hex.LiftData} {coreFactors : Array Hex.ZPoly}
    {rows_pos : HasPositiveDimension core d}
    (hcandidates :
      Hex.bhksIndicatorCandidates? core d
          (equivalenceClassIndicatorsOfLiftData core d rows_pos) =
        some coreFactors) :
    coreFactors.size =
      (Hex.bhksEquivalenceClassIndicators
        (projectedRowsOfLiftData core d rows_pos)).size := by
  simpa [equivalenceClassIndicatorsOfLiftData] using
    Hex.bhksIndicatorCandidates?_size_eq hcandidates

end BHKS

/--
Fast-core loop `hsize` producer for forward-cut irreducibility endpoints.

Given a successful `factorFastCoreWithBound` call and the candidate equality
exposed by `Hex.factorFastCoreWithBound_some_indicatorCandidates`, this returns
the exact size equality consumed by
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut`.
-/
theorem factorFastCoreWithBound_some_size_eq_indicators
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel target : Nat} {coreFactors : Array Hex.ZPoly}
    {rows_pos : BHKS.HasPositiveDimension core
      (Hex.ZPoly.toMonicLiftData core target primeData)}
    (_h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hcandidates :
      Hex.bhksIndicatorCandidates? core
          (Hex.ZPoly.toMonicLiftData core target primeData)
          (BHKS.equivalenceClassIndicatorsOfLiftData core
            (Hex.ZPoly.toMonicLiftData core target primeData) rows_pos) =
        some coreFactors) :
    coreFactors.size =
      (Hex.bhksEquivalenceClassIndicators
        (BHKS.projectedRowsOfLiftData core
          (Hex.ZPoly.toMonicLiftData core target primeData) rows_pos)).size :=
  BHKS.size_eq_indicators_of_candidates hcandidates

/--
Fast-core loop `hpartition` producer for forward-cut irreducibility endpoints.

Specializes the canonical lifted-support partition count
`BHKS.supportPartitionByMinColumn_length_eq_normalizedFactors_card_of_toMonicPrimeData`
to the accepted `toMonicLiftData` precision, presenting the canonical lifted
true-support family `liftedTrueSupports core (toMonicLiftData core B primeData)`
at the projected-row index type so it lines up directly with the `hpartition`
hypothesis consumed by `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut`.
This is the partition-equality sibling of
`factorFastCoreWithBound_some_size_eq_indicators`; the projected-row factor count
is definitionally the lift-data factor-array size, so no transport is needed.
-/
theorem factorFastCoreWithBound_some_partition_eq_normalizedFactors_card
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    {rows_pos : BHKS.HasPositiveDimension core
      (Hex.ZPoly.toMonicLiftData core B primeData)}
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (hcore_bound :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p) :
    (BHKS.supportPartitionByMinColumn
        (liftedTrueSupports core
            (Hex.ZPoly.toMonicLiftData core B primeData) :
          Set (Set (Fin (BHKS.projectedRowsOfLiftData core
            (Hex.ZPoly.toMonicLiftData core B primeData) rows_pos).factorCount)))).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card :=
  BHKS.supportPartitionByMinColumn_length_eq_normalizedFactors_card_of_toMonicPrimeData
    core B primeData hselected hcore_lc_pos hcore_pos hcore_prim hcore_sqfree
    hB_ne_zero hbound hcore_bound

/--
Forward-recovery loop-identification wrapper.

If the target precision is on the executable fast-core schedule, the supplied
`ForwardRecoveryInputs` package proves recovery at that target, and every other
scheduled precision before the target has no `bhksRecover?` result, then the
first-success loop returns exactly the package's expected factors.
-/
theorem factorFastCoreWithBound_eq_expected_of_forwardInputs_on_schedule_of_no_prior_recovery
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {start fuel target : Nat}
    (hfloor : Hex.cldCoeffFloor core ≤ target)
    (hinputs :
      BHKS.ForwardRecoveryInputs core
        (Hex.ZPoly.toMonicLiftData core target primeData))
    (hmem : target ∈ Hex.henselPrecisionSchedule B start fuel)
    (hno :
      ∀ k, k ∈ Hex.henselPrecisionSchedule B start fuel → k ≠ target →
        Hex.bhksRecover? core (Hex.ZPoly.toMonicLiftData core k primeData) = none) :
    Hex.factorFastCoreWithBound core B primeData start fuel =
      some hinputs.expectedFactors :=
  Hex.factorFastCoreWithBound_eq_some_of_recovery_on_schedule_of_no_prior_recovery
    core B primeData hfloor hmem hno
    (BHKS.bhksRecover_eq_some_of_forwardInputs core
      (Hex.ZPoly.toMonicLiftData core target primeData) hinputs)

/--
Canonical-cap specialization of
`factorFastCoreWithBound_eq_expected_of_forwardInputs_on_schedule_of_no_prior_recovery`.

The only remaining non-executable hypothesis is `hno`: no scheduled precision
other than the cap recovers before the loop reaches the cap.  The intended BHKS
precision-soundness theorem should discharge `hno` by proving success implies
Mignotte/cap precision.
-/
theorem factorFastCoreWithBound_eq_expected_of_forwardInputs_at_cap_of_no_prior_recovery
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    (hfloor : Hex.cldCoeffFloor core ≤ B)
    (hinputs :
      BHKS.ForwardRecoveryInputs core
        (Hex.ZPoly.toMonicLiftData core B primeData))
    (hno :
      ∀ k,
        k ∈ Hex.henselPrecisionSchedule B (Hex.initialHenselPrecision B)
          (Hex.ZPoly.quadraticDoublingSteps B + 2) →
        k ≠ B →
        Hex.bhksRecover? core (Hex.ZPoly.toMonicLiftData core k primeData) = none) :
    Hex.factorFastCoreWithBound core B primeData
        (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
      some hinputs.expectedFactors :=
  factorFastCoreWithBound_eq_expected_of_forwardInputs_on_schedule_of_no_prior_recovery
    hfloor hinputs (Hex.cap_mem_henselPrecisionSchedule B) hno

/-- Lower cardinality bound for a successful BHKS fast-core branch whose
emitted candidates have been certified through the B8 partition-refinement
package: the recovery side data provides an `ExpectedTrueFactors` witness
matching the support-driven indicator array, and the partition cardinality
matches the integer-factor count. Together these supply the irreducibility
hypothesis required by `factorFastCoreWithBound_some_factor_count_ge_of_irreducible`. -/
theorem factorFastCoreWithBound_some_factor_count_ge
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (htrue : BHKS.ForwardRecoveryInputs.ExpectedTrueFactors core
      (BHKS.expectedIndicatorArrayOfSupports trueSupports) coreFactors)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    (UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial core)).card ≤
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length :=
  factorFastCoreWithBound_some_factor_count_ge_of_irreducible h
    (BHKS.ForwardRecoveryInputs.ExpectedTrueFactors.irreducible_of_partition_count
      trueSupports htrue hcore_ne hpartition)

/-- Forward-inclusion lower count bound for a successful fast-core branch.

This derives the `count_ge` half from the *forward* inclusion `W ⊆ L'`
(`CutProjectionHypotheses`) through the partition-refinement argument
(`supportPartitionByMinColumn_length_le_bhksEquivalenceClassIndicators_size`),
with no reverse `L' = W` separation and hence no bad-vector resultant valuation.
Unlike `factorFastCoreWithBound_some_factor_count_ge`, it does not route through
an `ExpectedTrueFactors` package (whose construction needs the full `L' = W`).

The two executable-success facts it consumes isolate the remaining plumbing: the
emitted factor count equals the equivalence-class count (`hsize`) and the
support-partition length equals the integer-factor count (`hpartition`).  The
successful-branch premise `_h` is retained to mark the eventual source of those
facts once the executable recovery wiring discharges them. -/
theorem factorFastCoreWithBound_some_factor_count_ge_of_cut
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {L : Hex.BhksProjectedRows}
    (trueSupports : Set (Set (Fin L.factorCount)))
    (_h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hcut : BHKS.CutProjectionHypotheses L trueSupports)
    (hsize : coreFactors.size = (Hex.bhksEquivalenceClassIndicators L).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    (UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial core)).card ≤
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length := by
  rw [List.length_map, Array.length_toList, hsize, ← hpartition]
  exact
    BHKS.supportPartitionByMinColumn_length_le_bhksEquivalenceClassIndicators_size
      L trueSupports hcut

/-- Forward-cut cardinality equality for a successful BHKS fast-core branch.

Pairs the executable upper bound `factorFastCoreWithBound_some_factor_count_le`
with the forward-inclusion lower bound
`factorFastCoreWithBound_some_factor_count_ge_of_cut`, so the count equality is
established from the forward inclusion `W ⊆ L'`
(`BHKS.CutProjectionHypotheses`) alone.  Unlike
`factorFastCoreWithBound_some_factor_count_eq`, it routes through no
`ExpectedTrueFactors` package, and hence through no reverse `L' = W` separation
or bad-vector resultant valuation.  The two executable-success facts `hsize`
and `hpartition` isolate the remaining plumbing. -/
theorem factorFastCoreWithBound_some_factor_count_eq_of_cut
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {L : Hex.BhksProjectedRows}
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hcut : BHKS.CutProjectionHypotheses L trueSupports)
    (hsize : coreFactors.size = (Hex.bhksEquivalenceClassIndicators L).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  apply le_antisymm
  · exact factorFastCoreWithBound_some_factor_count_le hcore_ne h
  · exact factorFastCoreWithBound_some_factor_count_ge_of_cut trueSupports h hcut
      hsize hpartition

/-- Irreducibility of every emitted factor from the forward-cut count equality.

This is the forward-inclusion analogue of
`factorFastCoreWithBound_some_factor_irreducible`: it feeds the forward count
equality `factorFastCoreWithBound_some_factor_count_eq_of_cut` into the UFD
partition scaffold `factorFastCoreWithBound_some_factor_irreducible_of_count`,
with no dependency on the reverse `L' = W` separation. -/
theorem factorFastCoreWithBound_some_factor_irreducible_of_cut
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {L : Hex.BhksProjectedRows}
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hcut : BHKS.CutProjectionHypotheses L trueSupports)
    (hsize : coreFactors.size = (Hex.bhksEquivalenceClassIndicators L).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial factor) :=
  factorFastCoreWithBound_some_factor_irreducible_of_count hcore_ne h
    (factorFastCoreWithBound_some_factor_count_eq_of_cut trueSupports hcore_ne h
      hcut hsize hpartition)

/-- `Hex.ZPoly`-predicate form of
`factorFastCoreWithBound_some_factor_irreducible_of_cut`: the forward-inclusion
irreducibility wrapper used by fast-core callers that already carry a forward
cut certificate. -/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {L : Hex.BhksProjectedRows}
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hcut : BHKS.CutProjectionHypotheses L trueSupports)
    (hsize : coreFactors.size = (Hex.bhksEquivalenceClassIndicators L).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor :=
  factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count hcore_ne h
    (factorFastCoreWithBound_some_factor_count_eq_of_cut trueSupports hcore_ne h
      hcut hsize hpartition)

/--
Irreducibility wrapper that discharges the forward cut hypothesis directly from
the true-factor CLD-vector certificates and their tight norm bounds, via the
BHKS prefix survivor-span lemma.  This replaces the retired `CutRetention`
route.
-/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_trueFactors
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {L : Hex.BhksLatticeBasis} {hrows : 1 ≤ L.factorCount + L.coeffWidth}
    (trueSupports :
      Set (Set (Fin (Hex.bhksProjectedRows L hrows).factorCount)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hbasis : L.basis.independent)
    (data : ∀ S : trueSupports, BHKS.TrueFactorCLDVectorData L S.1)
    (tight : ∀ S : trueSupports, BHKS.TrueFactorCLDTightNormBound L S.1)
    (hsize :
      coreFactors.size =
        (Hex.bhksEquivalenceClassIndicators (Hex.bhksProjectedRows L hrows)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor :=
  factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut trueSupports
    hcore_ne h
    (BHKS.cutProjectionHypotheses_of_trueFactors L hrows hbasis trueSupports data tight)
    hsize hpartition

/--
Capstone composition for the fast `h_raw` disjunct: per-candidate irreducibility
of the first successful BHKS fast-core recovery, with the forward cut
certificates discharged from genuine true-factor lift data rather than taken as
opaque hypotheses.

For each true support `S`, the per-support lift package `lift S`
(`BHKS.TrueFactorLift`) and its semantic facts `sem S`
(`BHKS.TrueFactorLiftSemantics`), together with the prime, Hensel-precision, and
per-column CLD separation hypotheses, produce the tight per-column bound via
`BHKS.tightColumnBound_of_lift`.  That feeds `BHKS.tightNormBound_of_lift` to the
tight cut-radius certificate `TrueFactorCLDTightNormBound`; its loose companion
(`toNormBound`) and the structural block-form coordinate identities assemble the
`TrueFactorCLDVectorData` arm.  Both arms drive
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_trueFactors`.

This is the first consumer to wire the analytic stack (#7650 product CLD
identity, #7674 semantic lift facts, #7712 tight column bound producer) through
to the irreducibility endpoint.  The remaining residual is supplying the
per-support `TrueFactorLift`/semantics/separation family for the first
successful recovery; the separation hypotheses `hp`, `hk`, `hsep` are the BHKS
Lemma 5.7 inputs at the first-success lift precision, threaded here verbatim
rather than re-derived from the global Mignotte recovery bound. -/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_lift
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {L : Hex.BhksLatticeBasis} {hrows : 1 ≤ L.factorCount + L.coeffWidth}
    (trueSupports :
      Set (Set (Fin (Hex.bhksProjectedRows L hrows).factorCount)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hbasis : L.basis.independent)
    (lift : ∀ S : trueSupports, BHKS.TrueFactorLift L S.1)
    (sem : ∀ S : trueSupports, BHKS.TrueFactorLiftSemantics (lift S))
    (hp : ∀ S : trueSupports, 2 ≤ (lift S).p)
    (hk : ∀ S : trueSupports, 1 < (lift S).p ^ (lift S).a)
    (hsep : ∀ S : trueSupports,
      ∀ j, 2 * Hex.bhksCoeffBound (lift S).f j < (lift S).p ^ (lift S).a)
    (hsize :
      coreFactors.size =
        (Hex.bhksEquivalenceClassIndicators (Hex.bhksProjectedRows L hrows)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  have tight : ∀ S : trueSupports, BHKS.TrueFactorCLDTightNormBound L S.1 :=
    fun S =>
      BHKS.tightNormBound_of_lift (lift S)
        (BHKS.tightColumnBound_of_lift (lift S) (sem S) (hp S) (hk S) (hsep S))
  have data : ∀ S : trueSupports, BHKS.TrueFactorCLDVectorData L S.1 :=
    fun S =>
      { project_eq := fun i =>
          BHKS.trueFactorCLDVector_project_of_blockForm S.1 (lift S).blockForm i
        coeff_eq := fun j =>
          BHKS.trueFactorCLDVector_coeff_of_blockForm S.1 (lift S).blockForm j
        norm_bound := (tight S).toNormBound }
  exact factorFastCoreWithBound_some_factor_zpolyIrreducible_of_trueFactors
    trueSupports hcore_ne h hbasis data tight hsize hpartition

/--
Capstone composition for the fast `h_raw` disjunct via the **aggregate-tail CLD
lattice path** (issue #7876).  Where
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_lift` needs a
`TrueFactorLift` (raw per-factor integer divisibility), this consumes the weaker
`RecoveredLift` that the executable fast-core recovery actually exposes: each
support's `RecoveredLift` produces a period-adjusted `SupportShortVectorData`
(`BHKS.supportShortVectorData_of_recoveredLift`, in the monic coordinate), which
`BHKS.cutProjectionHypotheses_of_shortVectors` turns into the forward cut
certificate.  This is the route that survives the CLD period trap
(#7866/#7867): the per-factor column bound is unavailable, but the
period-reduced aggregate column is bounded by the aggregate residue alone.

The monic-coordinate hypothesis `hf_lc` (`leadingCoeff f = 1`) and the
precision/threshold separations `hk`/`hsep`/`hthr` are the BHKS Lemma 5.7 inputs
at the first-success lift precision, threaded here verbatim; `hfac` is the
Hensel-factorisation datum `∏ gᵢ ≡ f (mod pᵃ)` per selected factor. -/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {L : Hex.BhksLatticeBasis} {hrows : 1 ≤ L.factorCount + L.coeffWidth}
    (trueSupports :
      Set (Set (Fin (Hex.bhksProjectedRows L hrows).factorCount)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hbasis : L.basis.independent)
    (lift : ∀ S : trueSupports, BHKS.RecoveredLift L S.1)
    (hf_lc : ∀ S : trueSupports, Hex.DensePoly.leadingCoeff (lift S).f = 1)
    (hfactor_monic : ∀ S : trueSupports,
      (HexPolyMathlib.toPolynomial (lift S).factor).Monic)
    (hp : ∀ S : trueSupports, 2 ≤ (lift S).p)
    (hk : ∀ S : trueSupports, 1 < (lift S).p ^ (lift S).a)
    (hsep : ∀ S : trueSupports,
      ∀ j, 2 * Hex.bhksCoeffBound (lift S).f j < (lift S).p ^ (lift S).a)
    (hthr : ∀ S : trueSupports,
      ∀ j, Hex.bhksCoeffCutThreshold (lift S).p (lift S).f j ≤ (lift S).a)
    (hfac : ∀ S : trueSupports, ∀ i : Fin L.factorCount, i ∈ S.1 →
        ∃ g : Hex.ZPoly,
          Hex.DensePoly.Monic (L.liftedFactors.getD i.val 1) ∧
          0 < (L.liftedFactors.getD i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr (lift S).f ((L.liftedFactors.getD i.val 1) * g)
            ((lift S).p ^ (lift S).a))
    (hsize :
      coreFactors.size =
        (Hex.bhksEquivalenceClassIndicators (Hex.bhksProjectedRows L hrows)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  have hcut := BHKS.cutProjectionHypotheses_of_recoveredLift L hrows hbasis trueSupports
    lift hf_lc hfactor_monic hp hk hsep hthr hfac
  exact factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut trueSupports
    hcore_ne h hcut hsize hpartition

/--
Non-monic sibling of
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift`: the
fast-core irreducibility endpoint discharged over the executable's **core**
(non-monic) basis `bhksLatticeBasis core d.p d.k d.liftedFactors`, issue #8290.

Where the monic version consumes a `RecoveredLift` per true support, this consumes
the `RecoveredAtLiftM1` recovery witness the fast-core path actually exposes,
together with the abstract/concrete support-product identification
`hsupp : liftedFactorProduct d (subset S) = supportProduct L S`.  The forward cut
is built by `BHKS.cutProjectionHypotheses_of_recoveredM1` (recovery proportionality
→ logarithmic-derivative bridge → non-monic aggregate residue), bypassing the
type-impossible monic `RecoveredLift` (#8288).  `hgcd` is the good-prime condition
`p ∤ leadingCoeff core`; `hp`/`hk`/`hsep`/`hthr` are the BHKS Lemma 5.7 separation
inputs at the recovery precision; `hfac` is the per-selected-factor Hensel datum
`gᵢ ∣ core (mod pᵃ)`; `hfactor` is the genuine integer factorisation
`core = factorₛ · cofₛ`. -/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredM1
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {d : Hex.LiftData}
    {hrows :
      1 ≤ (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).factorCount +
        (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).coeffWidth}
    (trueSupports :
      Set (Set (Fin
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors) hrows).factorCount)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hbasis : (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).basis.independent)
    (hp : 2 ≤ d.p)
    (hk : 1 < d.p ^ d.k)
    (hsep : ∀ j, 2 * Hex.bhksCoeffBound core j < d.p ^ d.k)
    (hthr : ∀ j, Hex.bhksCoeffCutThreshold d.p core j ≤ d.k)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core) (Int.ofNat (d.p ^ d.k)) = 1)
    (factor cof : trueSupports → Hex.ZPoly)
    (subset : trueSupports → LiftedFactorSubset d)
    (hrec : ∀ S : trueSupports, RecoveredAtLiftM1 core d (factor S) (subset S))
    (hsupp : ∀ S : trueSupports,
      liftedFactorProduct d (subset S)
        = BHKS.supportProduct (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors) S.1)
    (hfac : ∀ S : trueSupports,
      ∀ i : Fin (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).factorCount, i ∈ S.1 →
        ∃ g : Hex.ZPoly,
          Hex.DensePoly.Monic
            ((Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).liftedFactors.getD i.val 1) ∧
          0 < ((Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).liftedFactors.getD
            i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr core
            (((Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).liftedFactors.getD i.val 1) * g)
            (d.p ^ d.k))
    (hfactor : ∀ S : trueSupports,
      HexPolyMathlib.toPolynomial core
        = HexPolyMathlib.toPolynomial (factor S) * HexPolyMathlib.toPolynomial (cof S))
    (hsize :
      coreFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors) hrows)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  have hcut := BHKS.cutProjectionHypotheses_of_recoveredM1 core d hrows hbasis
    trueSupports hp hk hsep hthr hgcd factor cof subset hrec hsupp hfac hfactor
  exact factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut trueSupports
    hcore_ne h hcut hsize hpartition

/--
M1 recovery-data form of the fast-core irreducibility endpoint.

This is the `coreLiftData` call-site for the subset congruence / honest-scale
bridge: callers supply, for each true support, the subset product congruence to
`monicTarget (factor S)` (the #8327 output) and the leading-coefficient split
through `cofactorLc`.  The proof builds the honest proportional congruence with
`honestCongr_of_product_congr_monicTarget` (#8328) and feeds it directly to
`BHKS.cutProjectionHypotheses_of_recoveryData`; it does not read any
scale-coordinate congruence from a dilation-coordinate `RecoveredAtLift` witness.
-/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveryData
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {d : Hex.LiftData}
    {hrows :
      1 ≤ (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).factorCount +
        (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).coeffWidth}
    (trueSupports :
      Set (Set (Fin
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors) hrows).factorCount)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hbasis : (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).basis.independent)
    (hp : 2 ≤ d.p)
    (hk : 1 < d.p ^ d.k)
    (hsep : ∀ j, 2 * Hex.bhksCoeffBound core j < d.p ^ d.k)
    (hthr : ∀ j, Hex.bhksCoeffCutThreshold d.p core j ≤ d.k)
    (hgcd_core : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (d.p ^ d.k)) = 1)
    (factor cof : trueSupports → Hex.ZPoly)
    (subset : trueSupports → LiftedFactorSubset d)
    (cofactorLc : trueSupports → Int)
    (hcofactorLc_pos : ∀ S : trueSupports, 0 < cofactorLc S)
    (hlc : ∀ S : trueSupports,
      Hex.DensePoly.leadingCoeff core =
        Hex.DensePoly.leadingCoeff (factor S) * cofactorLc S)
    (hprod : ∀ S : trueSupports,
      Hex.ZPoly.congr
        (liftedFactorProduct d (subset S))
        (Hex.ZPoly.monicTarget (factor S) d.p d.k)
        (d.p ^ d.k))
    (hgcd_factor : ∀ S : trueSupports,
      Int.gcd (Hex.DensePoly.leadingCoeff (factor S))
        (Int.ofNat (d.p ^ d.k)) = 1)
    (hmonic_dvd : ∀ S : trueSupports,
      Hex.ZPoly.monicTarget (factor S) d.p d.k ∣
        Hex.ZPoly.monicTarget core d.p d.k)
    (hfactor_prim : ∀ S : trueSupports,
      Hex.ZPoly.primitivePart (factor S) = factor S)
    (coeffBound : trueSupports → Nat)
    (hvalid : ∀ S : trueSupports, ∀ i,
      ((Hex.DensePoly.scale (cofactorLc S) (factor S)).coeff i).natAbs ≤ coeffBound S)
    (hprecision : ∀ S : trueSupports, 2 * coeffBound S < d.p ^ d.k)
    (hsupp : ∀ S : trueSupports,
      liftedFactorProduct d (subset S)
        = BHKS.supportProduct (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors) S.1)
    (hfac : ∀ S : trueSupports,
      ∀ i : Fin (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).factorCount, i ∈ S.1 →
        ∃ g : Hex.ZPoly,
          Hex.DensePoly.Monic
            ((Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).liftedFactors.getD i.val 1) ∧
          0 < ((Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).liftedFactors.getD
            i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr core
            (((Hex.bhksLatticeBasis core d.p d.k d.liftedFactors).liftedFactors.getD i.val 1) * g)
            (d.p ^ d.k))
    (hfactor : ∀ S : trueSupports,
      HexPolyMathlib.toPolynomial core
        = HexPolyMathlib.toPolynomial (factor S) * HexPolyMathlib.toPolynomial (cof S))
    (hsize :
      coreFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors) hrows)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  have hcut := BHKS.cutProjectionHypotheses_of_recoveryData core d hrows hbasis
    trueSupports hp hk hsep hthr hgcd_core factor cof subset
    (fun S => Hex.ZPoly.monicTarget (factor S) d.p d.k)
    cofactorLc hcofactorLc_pos
    (fun S => Hex.ZPoly.reduceModPow_eq_of_congr _ _ d.p d.k (hprod S))
    hmonic_dvd
    (fun S => honestCongr_of_product_congr_monicTarget
      (cofactorLc S) (hlc S) (hprod S) (hgcd_factor S) hk)
    hfactor_prim coeffBound hvalid hprecision hsupp hfac hfactor
  exact factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut trueSupports
    hcore_ne h hcut hsize hpartition

/--
`coreLiftData` specialization of
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveryData`.

This is the fully threaded M1 call-site: for each support, the modular subset
representation of `monicTarget (factor S)` is lifted through
`coreLiftData_subset_congr_monicTarget` (#8327), then the resulting product
congruence is converted to the honest scale-coordinate congruence by
`honestCongr_of_product_congr_monicTarget` through the recovery-data wrapper
above (#8328).
-/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_coreLiftDataRecoveryData
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {hrows :
      1 ≤ (Hex.bhksLatticeBasis core
          (Hex.ZPoly.coreLiftData core B primeData).p
          (Hex.ZPoly.coreLiftData core B primeData).k
          (Hex.ZPoly.coreLiftData core B primeData).liftedFactors).factorCount +
        (Hex.bhksLatticeBasis core
          (Hex.ZPoly.coreLiftData core B primeData).p
          (Hex.ZPoly.coreLiftData core B primeData).k
          (Hex.ZPoly.coreLiftData core B primeData).liftedFactors).coeffWidth}
    (trueSupports :
      Set (Set (Fin
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis core
            (Hex.ZPoly.coreLiftData core B primeData).p
            (Hex.ZPoly.coreLiftData core B primeData).k
            (Hex.ZPoly.coreLiftData core B primeData).liftedFactors) hrows).factorCount)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hbasis :
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.coreLiftData core B primeData).p
        (Hex.ZPoly.coreLiftData core B primeData).k
        (Hex.ZPoly.coreLiftData core B primeData).liftedFactors).basis.independent)
    (hp : 2 ≤ (Hex.ZPoly.coreLiftData core B primeData).p)
    (hk :
      1 <
        (Hex.ZPoly.coreLiftData core B primeData).p ^
          (Hex.ZPoly.coreLiftData core B primeData).k)
    (hsep : ∀ j,
      2 * Hex.bhksCoeffBound core j <
        (Hex.ZPoly.coreLiftData core B primeData).p ^
          (Hex.ZPoly.coreLiftData core B primeData).k)
    (hthr : ∀ j,
      Hex.bhksCoeffCutThreshold (Hex.ZPoly.coreLiftData core B primeData).p core j ≤
        (Hex.ZPoly.coreLiftData core B primeData).k)
    (hselected : Hex.choosePrimeData? core = some primeData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_size : 0 < core.size)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hgcd_core : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (primeData.p ^ Hex.precisionForCoeffBound B primeData.p)) = 1)
    (factor cof : trueSupports → Hex.ZPoly)
    (modPSubset : trueSupports → ModPFactorSubset primeData)
    (cofactor : trueSupports → Hex.ZPoly)
    (cofactorLc : trueSupports → Int)
    (hcofactorLc_pos : ∀ S : trueSupports, 0 < cofactorLc S)
    (hlc : ∀ S : trueSupports,
      Hex.DensePoly.leadingCoeff core =
        Hex.DensePoly.leadingCoeff (factor S) * cofactorLc S)
    (hfactor_size : ∀ S : trueSupports, 0 < (factor S).size)
    (hgcd_factor : ∀ S : trueSupports,
      Int.gcd (Hex.DensePoly.leadingCoeff (factor S))
        (Int.ofNat (primeData.p ^ Hex.precisionForCoeffBound B primeData.p)) = 1)
    (hfactor_product : ∀ S : trueSupports,
      Hex.ZPoly.congr
        (Hex.ZPoly.monicTarget (factor S) primeData.p
            (Hex.precisionForCoeffBound B primeData.p) * cofactor S)
        (Hex.ZPoly.monicTarget core primeData.p
            (Hex.precisionForCoeffBound B primeData.p))
        (primeData.p ^ Hex.precisionForCoeffBound B primeData.p))
    (hrepP : ∀ S : trueSupports,
      RepresentsIntegerFactorModP primeData
        (Hex.ZPoly.monicTarget (factor S) primeData.p
          (Hex.precisionForCoeffBound B primeData.p))
        (modPSubset S))
    (hmonic_dvd : ∀ S : trueSupports,
      Hex.ZPoly.monicTarget (factor S)
          (Hex.ZPoly.coreLiftData core B primeData).p
          (Hex.ZPoly.coreLiftData core B primeData).k ∣
        Hex.ZPoly.monicTarget core
          (Hex.ZPoly.coreLiftData core B primeData).p
          (Hex.ZPoly.coreLiftData core B primeData).k)
    (hfactor_prim : ∀ S : trueSupports,
      Hex.ZPoly.primitivePart (factor S) = factor S)
    (coeffBound : trueSupports → Nat)
    (hvalid : ∀ S : trueSupports, ∀ i,
      ((Hex.DensePoly.scale (cofactorLc S) (factor S)).coeff i).natAbs ≤ coeffBound S)
    (hprecision_factor : ∀ S : trueSupports,
      2 * coeffBound S <
        (Hex.ZPoly.coreLiftData core B primeData).p ^
          (Hex.ZPoly.coreLiftData core B primeData).k)
    (hsupp : ∀ S : trueSupports,
      liftedFactorProduct (Hex.ZPoly.coreLiftData core B primeData)
          (liftedSubsetOfModPSubset primeData (Hex.ZPoly.coreLiftData core B primeData)
            (henselLiftData_liftedFactors_size_eq
              (Hex.ZPoly.monicTarget core primeData.p
                (Hex.precisionForCoeffBound B primeData.p))
              (Hex.precisionForCoeffBound B primeData.p) primeData)
            (modPSubset S))
        = BHKS.supportProduct
            (Hex.bhksLatticeBasis core
              (Hex.ZPoly.coreLiftData core B primeData).p
              (Hex.ZPoly.coreLiftData core B primeData).k
              (Hex.ZPoly.coreLiftData core B primeData).liftedFactors) S.1)
    (hfac : ∀ S : trueSupports,
      ∀ i : Fin
          (Hex.bhksLatticeBasis core
            (Hex.ZPoly.coreLiftData core B primeData).p
            (Hex.ZPoly.coreLiftData core B primeData).k
            (Hex.ZPoly.coreLiftData core B primeData).liftedFactors).factorCount,
        i ∈ S.1 →
        ∃ g : Hex.ZPoly,
          Hex.DensePoly.Monic
            ((Hex.bhksLatticeBasis core
              (Hex.ZPoly.coreLiftData core B primeData).p
              (Hex.ZPoly.coreLiftData core B primeData).k
              (Hex.ZPoly.coreLiftData core B primeData).liftedFactors).liftedFactors.getD
                i.val 1) ∧
          0 <
            ((Hex.bhksLatticeBasis core
              (Hex.ZPoly.coreLiftData core B primeData).p
              (Hex.ZPoly.coreLiftData core B primeData).k
              (Hex.ZPoly.coreLiftData core B primeData).liftedFactors).liftedFactors.getD
                i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr core
            (((Hex.bhksLatticeBasis core
              (Hex.ZPoly.coreLiftData core B primeData).p
              (Hex.ZPoly.coreLiftData core B primeData).k
              (Hex.ZPoly.coreLiftData core B primeData).liftedFactors).liftedFactors.getD
                i.val 1) * g)
            ((Hex.ZPoly.coreLiftData core B primeData).p ^
              (Hex.ZPoly.coreLiftData core B primeData).k))
    (hfactor : ∀ S : trueSupports,
      HexPolyMathlib.toPolynomial core
        = HexPolyMathlib.toPolynomial (factor S) * HexPolyMathlib.toPolynomial (cof S))
    (hsize :
      coreFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis core
              (Hex.ZPoly.coreLiftData core B primeData).p
              (Hex.ZPoly.coreLiftData core B primeData).k
              (Hex.ZPoly.coreLiftData core B primeData).liftedFactors) hrows)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  let d := Hex.ZPoly.coreLiftData core B primeData
  let hsize_d :
      d.liftedFactors.size = primeData.factorsModP.size :=
    henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core primeData.p
        (Hex.precisionForCoeffBound B primeData.p))
      (Hex.precisionForCoeffBound B primeData.p) primeData
  refine
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveryData
      (core := core) (B := B) (primeData := primeData) (k := k) (fuel := fuel)
      (coreFactors := coreFactors) (d := d) (hrows := hrows)
      trueSupports hcore_ne h hbasis hp hk hsep hthr ?_ factor cof
      (fun S => liftedSubsetOfModPSubset primeData d hsize_d (modPSubset S))
      cofactorLc hcofactorLc_pos hlc ?_ ?_ hmonic_dvd hfactor_prim coeffBound
      hvalid hprecision_factor hsupp hfac hfactor hsize hpartition
  · simpa [d, Hex.ZPoly.coreLiftData] using hgcd_core
  · intro S
    simpa [d] using
      coreLiftData_subset_congr_monicTarget core (factor S) B primeData
        hselected hcore_pos hcore_size hprecision hgcd_core
        (hfactor_size S) (hgcd_factor S) (hfactor_product S) (hrepP S)
  · intro S
    simpa [d, Hex.ZPoly.coreLiftData] using hgcd_factor S

/--
Fast-core irreducibility wrapper from a monic recovered-lift family produced by
`recoveredLift_subtypeFamily_of_indicatorCandidates`.

The theorem keeps the deep BHKS residuals explicit (`hindicators`, monic-lattice
`hsize`, `hpartition`, and the CLD separation/threshold hypotheses), but derives
`hp`, `hk`, and the per-index Hensel congruence side condition from the
`toMonicPrimeData?` witness and the success precision `k'`.
-/
theorem factorFastCore_irreducible_of_monicRecoveredLift
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hvalid : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (k' : Nat)
    (rows_pos :
      BHKS.HasPositiveDimension core (Hex.ZPoly.toMonicLiftData core k' primeData))
    (hprecision : 1 ≤ Hex.precisionForCoeffBound k' primeData.p)
    (monicRows :
      1 ≤
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core k' primeData).p
          (Hex.ZPoly.toMonicLiftData core k' primeData).k
          (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).factorCount +
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core k' primeData).p
          (Hex.ZPoly.toMonicLiftData core k' primeData).k
          (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).coeffWidth)
    (hbasis :
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core k' primeData).p
        (Hex.ZPoly.toMonicLiftData core k' primeData).k
        (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).basis.independent)
    (trueSupports :
      Set (Set (Fin
        (BHKS.projectedRowsOfLiftData core
          (Hex.ZPoly.toMonicLiftData core k' primeData) rows_pos).factorCount)))
    (hindicators :
      BHKS.equivalenceClassIndicatorsOfLiftData core
          (Hex.ZPoly.toMonicLiftData core k' primeData) rows_pos =
        BHKS.expectedIndicatorArrayOfSupports trueSupports)
    (hcandidates :
      Hex.bhksIndicatorCandidates? core (Hex.ZPoly.toMonicLiftData core k' primeData)
          (BHKS.equivalenceClassIndicatorsOfLiftData core
            (Hex.ZPoly.toMonicLiftData core k' primeData) rows_pos) =
        some coreFactors)
    (lift :
      ∀ S : BHKS.ForwardRecoveryInputs.emittedSupports (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core k' primeData) trueSupports,
        BHKS.RecoveredLift
          (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
            (Hex.ZPoly.toMonicLiftData core k' primeData).p
            (Hex.ZPoly.toMonicLiftData core k' primeData).k
            (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors) S.1)
    (hlift :
      lift =
        BHKS.ForwardRecoveryInputs.recoveredLift_subtypeFamily_of_indicatorCandidates
          rows_pos trueSupports hindicators hcandidates hcore_lc_pos hcore_pos
          (fun i =>
            Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
              core k' primeData hcore_lc_pos hcore_pos hvalid hprecision i)
          (BHKS.toMonicLiftData_one_lt_modulus core k' primeData hvalid hprecision))
    (hf_lc : ∀ S, Hex.DensePoly.leadingCoeff (lift S).f = 1)
    (hfactor_monic : ∀ S, (HexPolyMathlib.toPolynomial (lift S).factor).Monic)
    (hsep : ∀ S, ∀ j, 2 * Hex.bhksCoeffBound (lift S).f j < (lift S).p ^ (lift S).a)
    (hthr : ∀ S, ∀ j, Hex.bhksCoeffCutThreshold (lift S).p (lift S).f j ≤ (lift S).a)
    (hfac : ∀ S, ∀ i : Fin
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core k' primeData).p
          (Hex.ZPoly.toMonicLiftData core k' primeData).k
          (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).factorCount,
        i ∈ S.1 →
          ∃ g : Hex.ZPoly,
            Hex.DensePoly.Monic
              ((Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
                (Hex.ZPoly.toMonicLiftData core k' primeData).p
                (Hex.ZPoly.toMonicLiftData core k' primeData).k
                (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).liftedFactors.getD
                  i.val 1) ∧
            0 < ((Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
                (Hex.ZPoly.toMonicLiftData core k' primeData).p
                (Hex.ZPoly.toMonicLiftData core k' primeData).k
                (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).liftedFactors.getD
                  i.val 1).degree?.getD 0 ∧
            Hex.ZPoly.congr (lift S).f
              (((Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
                (Hex.ZPoly.toMonicLiftData core k' primeData).p
                (Hex.ZPoly.toMonicLiftData core k' primeData).k
                (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).liftedFactors.getD
                  i.val 1) * g)
              ((lift S).p ^ (lift S).a))
    (hsize :
      coreFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
              (Hex.ZPoly.toMonicLiftData core k' primeData).p
              (Hex.ZPoly.toMonicLiftData core k' primeData).k
              (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors)
            monicRows)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn
        (BHKS.ForwardRecoveryInputs.emittedSupports (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core k' primeData) trueSupports)).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  classical
  let d := Hex.ZPoly.toMonicLiftData core k' primeData
  let L := Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic d.p d.k d.liftedFactors
  let emitted :=
    BHKS.ForwardRecoveryInputs.emittedSupports (Hex.ZPoly.toMonic core).monic d trueSupports
  subst lift
  -- The `hp`/`hk` side conditions are stated about the recovered-lift family's
  -- own `.p`/`.a` fields; rewrite those to the underlying lift data's `d.p`/`d.k`
  -- (the family preserves them, #7923) before discharging from `toMonicPrimeData`.
  refine
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift
      (core := core) (B := B) (primeData := primeData) (k := k) (fuel := fuel)
      (coreFactors := coreFactors) (L := L) (hrows := monicRows) emitted
      hcore_ne h hbasis
      (BHKS.ForwardRecoveryInputs.recoveredLift_subtypeFamily_of_indicatorCandidates
        rows_pos trueSupports hindicators hcandidates hcore_lc_pos hcore_pos
        (fun i =>
          Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
            core k' primeData hcore_lc_pos hcore_pos hvalid hprecision i)
        (BHKS.toMonicLiftData_one_lt_modulus core k' primeData hvalid hprecision))
      hf_lc hfactor_monic ?_ ?_ hsep hthr hfac hsize hpartition
  · intro S
    rw [BHKS.ForwardRecoveryInputs.recoveredLift_subtypeFamily_of_indicatorCandidates_p]
    exact BHKS.toMonicLiftData_two_le_p core k' primeData hvalid
  · intro S
    rw [BHKS.ForwardRecoveryInputs.recoveredLift_subtypeFamily_of_indicatorCandidates_p,
        BHKS.ForwardRecoveryInputs.recoveredLift_subtypeFamily_of_indicatorCandidates_a]
    exact BHKS.toMonicLiftData_one_lt_modulus core k' primeData hvalid hprecision

/--
**Centered `RecoveredLift` for a genuine lifted true support (#8068 keystone).**

For any support `U` in the genuine `liftedTrueSupports core (toMonicLiftData core
B primeData)` family, the centered recovered lift over the monic basis exists.

Unlike `recoveredLift_subtypeFamily_of_indicatorCandidates`, this consumes **no**
`hindicators` (`L' = W`) hypothesis: the witnessing integer factor `f` carried by
the `liftedTrueSupports` membership is descended to its monic correspondent `gf`
(via `IntReductionMod.monicCorrespondentDescent_of_representsAtLift`), whose
monic-coordinate representation feeds `recoveredLiftOfToMonicRepresents`.  The
support is then transported back along the membership's coercion `↑S = U`.  This
is the separation-free producer of the `lift` family consumed by
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift`.
-/
noncomputable def recoveredLiftOfLiftedTrueSupport
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (U : Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData)))
    (hU : U ∈ liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core B primeData)) :
    BHKS.RecoveredLift
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData).p
        (Hex.ZPoly.toMonicLiftData core B primeData).k
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors) U := by
  classical
  have hsize_d :
      (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size =
        primeData.factorsModP.size :=
    Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k =
      Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_k _ _ _
  have hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hbound
  -- Extract the witnessing integer factor and its representing subset (Prop → data: `choose`).
  have hf_irr : Irreducible (HexPolyZMathlib.toPolynomial hU.choose) :=
    hU.choose_spec.choose_spec.1
  have hf_dvd : hU.choose ∣ core := hU.choose_spec.choose_spec.2.1
  have hrep :
      RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData)
        hU.choose hU.choose_spec.choose :=
    hU.choose_spec.choose_spec.2.2.1
  have hcoe :
      (↑hU.choose_spec.choose :
          Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData))) = U :=
    hU.choose_spec.choose_spec.2.2.2
  -- Descend to the monic correspondent.
  have hdesc :=
    IntReductionMod.monicCorrespondentDescent_of_representsAtLift core B primeData hselected
      hcore_lc_pos hcore_pos hcore_prim hB_ne_zero hbound hf_irr hf_dvd hrep
  have hgf_monic := hdesc.choose_spec.choose_spec.1
  have hgf_dvd := hdesc.choose_spec.choose_spec.2.1
  have hgf_irr := hdesc.choose_spec.choose_spec.2.2.1
  have hmodP := hdesc.choose_spec.choose_spec.2.2.2.1
  have hSeq := hdesc.choose_spec.choose_spec.2.2.2.2.2
  -- Monic-coordinate lifted representation of the correspondent.
  have hliftM :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) hdesc.choose
        (liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
          hsize_d hdesc.choose_spec.choose) :=
    toMonicLiftData_represents_lifted_monicCorrespondent core B primeData hcore_lc_pos
      hcore_pos hselected hB_ne_zero hgf_monic hgf_irr hgf_dvd hmodP
  -- Build the recovered lift over the monic basis, then transport the support to `U`.
  have hsupp :
      BHKS.supportOfSubset (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core B primeData)
          (liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
            hsize_d hdesc.choose_spec.choose) = U := by
    show (↑(liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
        hsize_d hdesc.choose_spec.choose) :
        Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData))) = U
    rw [← hSeq]; exact hcoe
  exact hsupp ▸ BHKS.recoveredLiftOfToMonicRepresents core B primeData
    (liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
      hsize_d hdesc.choose_spec.choose)
    hdesc.choose hgf_dvd.choose hcore_lc_pos hcore_pos hgf_dvd.choose_spec.symm hprecision hliftM

/-- The lift modulus base `p` of the separation-free keystone recovered lift is
the underlying `toMonicLiftData`'s prime base. -/
@[simp] theorem recoveredLiftOfLiftedTrueSupport_p
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (U : Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData)))
    (hU : U ∈ liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core B primeData)) :
    (recoveredLiftOfLiftedTrueSupport core B primeData hselected hcore_lc_pos hcore_pos
      hcore_prim hB_ne_zero hbound U hU).p =
        (Hex.ZPoly.toMonicLiftData core B primeData).p := by
  unfold recoveredLiftOfLiftedTrueSupport
  simp only [BHKS.ForwardRecoveryInputs.RecoveredLift.p_eqRec, BHKS.recoveredLiftOfToMonicRepresents_p]

/-- The lift precision `a` of the separation-free keystone recovered lift is the
underlying `toMonicLiftData`'s precision. -/
@[simp] theorem recoveredLiftOfLiftedTrueSupport_a
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (U : Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData)))
    (hU : U ∈ liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core B primeData)) :
    (recoveredLiftOfLiftedTrueSupport core B primeData hselected hcore_lc_pos hcore_pos
      hcore_prim hB_ne_zero hbound U hU).a =
        (Hex.ZPoly.toMonicLiftData core B primeData).k := by
  unfold recoveredLiftOfLiftedTrueSupport
  simp only [BHKS.ForwardRecoveryInputs.RecoveredLift.a_eqRec, BHKS.recoveredLiftOfToMonicRepresents_a]

/-- The lift target `f` of the separation-free keystone recovered lift is the
monic transform `(toMonic core).monic`. -/
@[simp] theorem recoveredLiftOfLiftedTrueSupport_f
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (U : Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData)))
    (hU : U ∈ liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core B primeData)) :
    (recoveredLiftOfLiftedTrueSupport core B primeData hselected hcore_lc_pos hcore_pos
      hcore_prim hB_ne_zero hbound U hU).f = (Hex.ZPoly.toMonic core).monic := by
  unfold recoveredLiftOfLiftedTrueSupport
  simp only [BHKS.ForwardRecoveryInputs.RecoveredLift.f_eqRec, BHKS.recoveredLiftOfToMonicRepresents_f]

/-- The recovered integer factor of the separation-free keystone lift is the
monic correspondent descended from the witnessing factor, hence monic. -/
theorem recoveredLiftOfLiftedTrueSupport_factor_denseMonic
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (U : Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData)))
    (hU : U ∈ liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core B primeData)) :
    Hex.DensePoly.Monic
      (recoveredLiftOfLiftedTrueSupport core B primeData hselected hcore_lc_pos hcore_pos
        hcore_prim hB_ne_zero hbound U hU).factor := by
  classical
  have hf_irr : Irreducible (HexPolyZMathlib.toPolynomial hU.choose) :=
    hU.choose_spec.choose_spec.1
  have hf_dvd : hU.choose ∣ core := hU.choose_spec.choose_spec.2.1
  have hrep :
      RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData)
        hU.choose hU.choose_spec.choose :=
    hU.choose_spec.choose_spec.2.2.1
  have hdesc :=
    IntReductionMod.monicCorrespondentDescent_of_representsAtLift core B primeData hselected
      hcore_lc_pos hcore_pos hcore_prim hB_ne_zero hbound hf_irr hf_dvd hrep
  have hval :
      (recoveredLiftOfLiftedTrueSupport core B primeData hselected hcore_lc_pos hcore_pos
        hcore_prim hB_ne_zero hbound U hU).factor = hdesc.choose := by
    unfold recoveredLiftOfLiftedTrueSupport
    simp only [BHKS.ForwardRecoveryInputs.RecoveredLift.factor_eqRec,
      BHKS.recoveredLiftOfToMonicRepresents_factor]
  rw [hval]
  exact hdesc.choose_spec.choose_spec.1

/-- Mathlib-monic form of `recoveredLiftOfLiftedTrueSupport_factor_denseMonic`,
the `hfactor_monic` leaf of the separation-free fast-core endpoint. -/
theorem recoveredLiftOfLiftedTrueSupport_factor_monic
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (U : Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData)))
    (hU : U ∈ liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core B primeData)) :
    (HexPolyMathlib.toPolynomial
      (recoveredLiftOfLiftedTrueSupport core B primeData hselected hcore_lc_pos hcore_pos
        hcore_prim hB_ne_zero hbound U hU).factor).Monic :=
  HexHenselMathlib.toPolynomial_monic_of_dense_monic _
    (recoveredLiftOfLiftedTrueSupport_factor_denseMonic core B primeData hselected
      hcore_lc_pos hcore_pos hcore_prim hB_ne_zero hbound U hU)

/--
Separation-free fast-core multi-factor irreducibility at the loop **success**
precision, built on the keystone `recoveredLiftOfLiftedTrueSupport`.

The success precision `k'` and the CLD floor gate `cldCoeffFloor core ≤ k'` are
extracted from the loop success via
`Hex.factorFastCoreWithBound_some_indicatorCandidates`; the monic Mignotte gate
`BHKS.defaultFactorCoeffBound_toMonic_le_cldCoeffFloor` and the un-monic core
recovery gate `two_mul_defaultFactorCoeffBound_core_lt_pow_of_cldCoeffFloor_le`
turn it into the keystone's `hbound` and the partition lemma's `hcore_bound`.
The monicity, prime, Hensel-precision, separation, threshold, per-index Hensel
congruence (`hfac`), and partition-count leaves all discharge from the keystone
field projections and the CLD-floor producers.

The single remaining hypothesis `hsize` is the genuine residual, because the
keystone recovers over `(toMonic core).monic` while the executable loop emits
`coreFactors` over the **core** basis (first argument `core`): `hsize` asks that
`coreFactors.size` equals the **monic**-basis equivalence-class indicator count.
The executable instead gives `coreFactors.size = (core-basis indicators).size`
(`factorFastCoreWithBound_some_size_eq_indicators`), and
`Hex.bhksEquivalenceClassIndicators` size is basis-dependent
(`bhksEquivalenceClassIndicators_size_eq` reduces it to the rref column-signature
partition length of the projected rows, and `Hex.cldCoeffs f` depends on `f`).
Discharging it needs a core ↔ monic equivalence-class-indicator-size bridge that
the codebase does not yet provide; supplying that bridge closes the multi-factor
arm of `factor_irreducible_of_nonUnit`. -/
theorem factorFastCore_irreducible_of_liftedTrueSupport
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hconst : core.coeff 0 ≠ 0)
    (hn : 2 ≤ core.degree?.getD 0)
    (hvalid : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hsize : ∀ k'
        (coreRows :
          1 ≤
            (Hex.bhksLatticeBasis core
              (Hex.ZPoly.toMonicLiftData core k' primeData).p
              (Hex.ZPoly.toMonicLiftData core k' primeData).k
              (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).factorCount +
            (Hex.bhksLatticeBasis core
              (Hex.ZPoly.toMonicLiftData core k' primeData).p
              (Hex.ZPoly.toMonicLiftData core k' primeData).k
              (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).coeffWidth)
        (monicRows :
          1 ≤
            (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
              (Hex.ZPoly.toMonicLiftData core k' primeData).p
              (Hex.ZPoly.toMonicLiftData core k' primeData).k
              (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).factorCount +
            (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
              (Hex.ZPoly.toMonicLiftData core k' primeData).p
              (Hex.ZPoly.toMonicLiftData core k' primeData).k
              (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).coeffWidth),
        Hex.bhksIndicatorCandidates? core (Hex.ZPoly.toMonicLiftData core k' primeData)
            (Hex.bhksEquivalenceClassIndicators
              (Hex.bhksProjectedRows
                (Hex.bhksLatticeBasis core (Hex.ZPoly.toMonicLiftData core k' primeData).p
                  (Hex.ZPoly.toMonicLiftData core k' primeData).k
                  (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors)
                coreRows)) =
          some coreFactors →
        coreFactors.size =
          (Hex.bhksEquivalenceClassIndicators
            (Hex.bhksProjectedRows
              (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
                (Hex.ZPoly.toMonicLiftData core k' primeData).p
                (Hex.ZPoly.toMonicLiftData core k' primeData).k
                (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors)
              monicRows)).size) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  classical
  obtain ⟨k', hrows, hcandidates, _hdegen, _hprod, hfloor⟩ :=
    Hex.factorFastCoreWithBound_some_indicatorCandidates h
  have hp : 2 ≤ primeData.p :=
    (Hex.ZPoly.toMonicPrimeData?_prime core primeData hvalid).two_le
  have hcore_bound :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        primeData.p ^ Hex.precisionForCoeffBound k' primeData.p :=
    BHKS.two_mul_defaultFactorCoeffBound_core_lt_pow_of_cldCoeffFloor_le
      core k' primeData hp hfloor hconst hn
  have hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound k' primeData.p := by
    have hle : Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic ≤ k' :=
      le_trans (BHKS.defaultFactorCoeffBound_toMonic_le_cldCoeffFloor core hcore_pos) hfloor
    have hspec := Hex.precisionForCoeffBound_spec hp k'
    omega
  have hk'_ne : k' ≠ 0 := by
    have h1 : 0 < Hex.ZPoly.defaultFactorCoeffBound core :=
      Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
    have h2 : Hex.ZPoly.defaultFactorCoeffBound core ≤ Hex.cldCoeffFloor core :=
      BHKS.defaultFactorCoeffBound_le_cldCoeffFloor core hconst hn
    omega
  have hprecision : 1 ≤ Hex.precisionForCoeffBound k' primeData.p := by
    rcases Nat.eq_zero_or_pos (Hex.precisionForCoeffBound k' primeData.p) with h0 | h0
    · exfalso
      have hspec := Hex.precisionForCoeffBound_spec hp k'
      rw [h0, pow_zero] at hspec
      omega
    · exact h0
  have hmonic_one : Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic = 1 :=
    Hex.DensePoly.leadingCoeff_eq_one_of_monic
      (Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos)
  -- monic-basis positive dimension from the core-basis one (degrees agree).
  have monicRows :
      1 ≤
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core k' primeData).p
          (Hex.ZPoly.toMonicLiftData core k' primeData).k
          (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).factorCount +
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core k' primeData).p
          (Hex.ZPoly.toMonicLiftData core k' primeData).k
          (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).coeffWidth := by
    have hfc :
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core k' primeData).p
          (Hex.ZPoly.toMonicLiftData core k' primeData).k
          (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).factorCount =
        (Hex.bhksLatticeBasis core
          (Hex.ZPoly.toMonicLiftData core k' primeData).p
          (Hex.ZPoly.toMonicLiftData core k' primeData).k
          (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).factorCount := rfl
    have hcw :
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core k' primeData).p
          (Hex.ZPoly.toMonicLiftData core k' primeData).k
          (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).coeffWidth =
        (Hex.bhksLatticeBasis core
          (Hex.ZPoly.toMonicLiftData core k' primeData).p
          (Hex.ZPoly.toMonicLiftData core k' primeData).k
          (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).coeffWidth :=
      Hex.ZPoly.toMonic_monic_degree_getD core
    rw [hfc, hcw]; exact hrows
  refine factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift
    (core := core) (B := B) (primeData := primeData) (k := k) (fuel := fuel)
    (coreFactors := coreFactors)
    (L := Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
      (Hex.ZPoly.toMonicLiftData core k' primeData).p
      (Hex.ZPoly.toMonicLiftData core k' primeData).k
      (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors)
    (hrows := monicRows)
    (trueSupports := liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core k' primeData))
    hcore_ne h
    (Hex.bhksLatticeBasis_independent _ _ _ _
      (Hex.ZPoly.toMonicLiftData core k' primeData).p_pos)
    (fun S => recoveredLiftOfLiftedTrueSupport core k' primeData hvalid hcore_lc_pos
      hcore_pos hcore_prim hk'_ne hbound S.1 S.2)
    ?hf_lc ?hfactor_monic ?hp2 ?hk2 ?hsep ?hthr ?hfac ?hsize ?hpartition
  case hf_lc =>
    intro S
    rw [recoveredLiftOfLiftedTrueSupport_f]
    exact hmonic_one
  case hfactor_monic =>
    intro S
    exact recoveredLiftOfLiftedTrueSupport_factor_monic core k' primeData hvalid
      hcore_lc_pos hcore_pos hcore_prim hk'_ne hbound S.1 S.2
  case hp2 =>
    intro S
    rw [recoveredLiftOfLiftedTrueSupport_p]
    exact BHKS.toMonicLiftData_two_le_p core k' primeData hvalid
  case hk2 =>
    intro S
    rw [recoveredLiftOfLiftedTrueSupport_p, recoveredLiftOfLiftedTrueSupport_a]
    exact BHKS.toMonicLiftData_one_lt_modulus core k' primeData hvalid hprecision
  case hsep =>
    intro S j
    rw [recoveredLiftOfLiftedTrueSupport_f, recoveredLiftOfLiftedTrueSupport_p,
      recoveredLiftOfLiftedTrueSupport_a]
    exact BHKS.two_mul_bhksCoeffBound_lt_pow_of_cldCoeffFloor_le core k' primeData hp hfloor j
  case hthr =>
    intro S j
    rw [recoveredLiftOfLiftedTrueSupport_p, recoveredLiftOfLiftedTrueSupport_f,
      recoveredLiftOfLiftedTrueSupport_a]
    exact BHKS.bhksCoeffCutThreshold_le_of_cldCoeffFloor_le core k' primeData hp hfloor j
  case hfac =>
    intro S i hi
    obtain ⟨g, hg_monic, hg_deg, hg_congr⟩ :=
      BHKS.toMonicLiftData_liftedFactor_hensel_semantics core k' primeData
        hcore_lc_pos hcore_pos hvalid hprecision i
    have hib :
        (i : Nat) <
          (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
            (Hex.ZPoly.toMonicLiftData core k' primeData).p
            (Hex.ZPoly.toMonicLiftData core k' primeData).k
            (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).liftedFactors.size :=
      i.isLt
    have hlf :
        liftedFactor (Hex.ZPoly.toMonicLiftData core k' primeData) i =
          (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
            (Hex.ZPoly.toMonicLiftData core k' primeData).p
            (Hex.ZPoly.toMonicLiftData core k' primeData).k
            (Hex.ZPoly.toMonicLiftData core k' primeData).liftedFactors).liftedFactors.getD
            i.val 1 := by
      rw [liftedFactor, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hib,
        Option.getD_some]
      rfl
    rw [recoveredLiftOfLiftedTrueSupport_f, recoveredLiftOfLiftedTrueSupport_p,
      recoveredLiftOfLiftedTrueSupport_a]
    refine ⟨g, ?_, ?_, ?_⟩
    · rw [← hlf]; exact hg_monic
    · rw [← hlf]; exact hg_deg
    · rw [← hlf]; exact hg_congr
  case hpartition =>
    exact factorFastCoreWithBound_some_partition_eq_normalizedFactors_card
      core k' primeData (rows_pos := hrows) hvalid hcore_lc_pos hcore_pos hcore_prim
      hcore_sqfree hk'_ne hbound hcore_bound
  case hsize =>
    exact hsize k' hrows monicRows hcandidates

/-- Cardinality equality for a successful BHKS fast-core branch under the B8
partition-refinement package.  Pairs `factorFastCoreWithBound_some_factor_count_le`
with `factorFastCoreWithBound_some_factor_count_ge`, exposing the count
equality requested by #4030 / #4055 in a form directly usable as the `hcount`
hypothesis of `factorFastCoreWithBound_some_factor_irreducible_of_count` and
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count`. -/
theorem factorFastCoreWithBound_some_factor_count_eq
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (htrue : BHKS.ForwardRecoveryInputs.ExpectedTrueFactors core
      (BHKS.expectedIndicatorArrayOfSupports trueSupports) coreFactors)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  apply le_antisymm
  · exact factorFastCoreWithBound_some_factor_count_le hcore_ne h
  · exact factorFastCoreWithBound_some_factor_count_ge trueSupports hcore_ne h
      htrue hpartition

/-- Irreducibility for every factor emitted by a successful BHKS fast-core
branch under the partition-refinement package.

This packages the count equality from
`factorFastCoreWithBound_some_factor_count_eq` into the older
`factorFastCoreWithBound_some_factor_irreducible_of_count` scaffold, giving
downstream factorization assembly a branch theorem that no longer has to
thread the count equality manually. -/
theorem factorFastCoreWithBound_some_factor_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (htrue : BHKS.ForwardRecoveryInputs.ExpectedTrueFactors core
      (BHKS.expectedIndicatorArrayOfSupports trueSupports) coreFactors)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial factor) :=
  factorFastCoreWithBound_some_factor_irreducible_of_count hcore_ne h
    (factorFastCoreWithBound_some_factor_count_eq trueSupports hcore_ne h
      htrue hpartition)

/-- `Hex.ZPoly`-predicate form of
`factorFastCoreWithBound_some_factor_irreducible`. -/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (htrue : BHKS.ForwardRecoveryInputs.ExpectedTrueFactors core
      (BHKS.expectedIndicatorArrayOfSupports trueSupports) coreFactors)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor :=
  factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count hcore_ne h
    (factorFastCoreWithBound_some_factor_count_eq trueSupports hcore_ne h
      htrue hpartition)

/-- Forward-recovery-input form of the fast-core irreducibility wrapper, routed
through the forward inclusion `W ⊆ L'`.

This is the proof-facing API for fast-branch callers that carry the BHKS
recovery package at the successful lift together with a forward cut certificate.
It obtains the lower count bound through
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut`, so it depends only
on the forward `BHKS.CutProjectionHypotheses` (certified by the cut-survival
argument) — not on the `ForwardRecoveryInputs.lattice_eq_indicators` field, the
reverse `L' = W` separation that requires the bad-vector resultant valuation.
The recovery package supplies only the executable identification: the
`hsize` plumbing fact is discharged from its `candidates_eq` / `indicators_match`
fields, with no appeal to the lattice separation. -/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_forwardInputs
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat}
    (hcore_ne : core ≠ 0)
    (hinputs :
      BHKS.ForwardRecoveryInputs core (Hex.ZPoly.toMonicLiftData core k primeData))
    (h :
      Hex.factorFastCoreWithBound core B primeData k fuel =
        some hinputs.expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData core
          (Hex.ZPoly.toMonicLiftData core k primeData) hinputs.rows_pos)
        hinputs.trueSupports)
    (hpartition :
      (BHKS.supportPartitionByMinColumn hinputs.trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ hinputs.expectedFactors.toList,
      Hex.ZPoly.Irreducible factor := by
  have hsize :
      hinputs.expectedFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (BHKS.projectedRowsOfLiftData core
            (Hex.ZPoly.toMonicLiftData core k primeData) hinputs.rows_pos)).size := by
    have hcandidates :
        Hex.bhksIndicatorCandidates? core
            (Hex.ZPoly.toMonicLiftData core k primeData)
            (BHKS.equivalenceClassIndicatorsOfLiftData core
              (Hex.ZPoly.toMonicLiftData core k primeData) hinputs.rows_pos) =
          some hinputs.expectedFactors := by
      simpa [hinputs.indicators_match] using hinputs.candidates_eq
    exact BHKS.size_eq_indicators_of_candidates hcandidates
  exact
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut
      hinputs.trueSupports hcore_ne h hcut hsize hpartition

set_option maxHeartbeats 800000 in
/--
Default-bound fast-BHKS direct-core specialization via the forward-count route.

The BHKS core is the normalized square-free core and the coefficient bound is
`Hex.ZPoly.defaultFactorCoeffBound f`; callers still choose the concrete lift
precision `k` and fuel for the core loop.  The proof is the general
forward-input wrapper specialized to the public default-bound core.
-/
theorem factorFastCoreDefault_factor_zpolyIrreducible_of_forwardInputs
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (primeData : Hex.PrimeChoiceData) {k fuel : Nat}
    (hinputs :
      BHKS.ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore k primeData))
    (h :
      Hex.factorFastCoreWithBound
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData k fuel =
        some hinputs.expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore k primeData)
          hinputs.rows_pos)
        hinputs.trueSupports)
    (hpartition :
      (BHKS.supportPartitionByMinColumn hinputs.trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card) :
    ∀ factor ∈ hinputs.expectedFactors.toList,
      Hex.ZPoly.Irreducible factor := by
  have hcore_lc_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  exact
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_forwardInputs
      hcore_ne hinputs h hcut hpartition

/-- Scheduled-loop form of
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_forwardInputs`.

The executable fast dispatcher does not start the core loop at the recovery
precision: it starts at `Hex.initialHenselPrecision a` and walks the Hensel
schedule, so the loop's `start` argument differs from the precision `target` at
which the caller carries the `BHKS.ForwardRecoveryInputs` package.  This wrapper
decouples the two: the loop-success hypothesis `h` is stated at an arbitrary
`start`/`fuel`, while the forward package, cut certificate, and partition count
all sit at the scheduled `target`.

The decoupling is sound because the count argument routes through
`factorFastCoreWithBound_some_factor_count_eq_of_cut`, whose loop-result
parameters (`k`, `fuel`) and cut-precision parameters (`L`) are already
independent — they meet only at the size identity `hsize`, which is derived
purely from the package fields (`candidates_eq` / `indicators_match`) at
`target`.  The hypothesis `h` pins the loop output to the package's
`expectedFactors`; supplying that equality for the actual executable start
`Hex.initialHenselPrecision a` is the scheduled-loop determinism obligation left
to the caller (it is *not* implied by the package at `target` alone, since the
loop returns the first schedule success and an earlier precision could exit with
a different array). -/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_forwardInputs_on_schedule
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {start fuel target : Nat}
    (hcore_ne : core ≠ 0)
    (hinputs :
      BHKS.ForwardRecoveryInputs core
        (Hex.ZPoly.toMonicLiftData core target primeData))
    (h :
      Hex.factorFastCoreWithBound core B primeData start fuel =
        some hinputs.expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData core
          (Hex.ZPoly.toMonicLiftData core target primeData) hinputs.rows_pos)
        hinputs.trueSupports)
    (hpartition :
      (BHKS.supportPartitionByMinColumn hinputs.trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ hinputs.expectedFactors.toList,
      Hex.ZPoly.Irreducible factor := by
  have hsize :
      hinputs.expectedFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (BHKS.projectedRowsOfLiftData core
            (Hex.ZPoly.toMonicLiftData core target primeData)
            hinputs.rows_pos)).size := by
    have hcandidates :
        Hex.bhksIndicatorCandidates? core
            (Hex.ZPoly.toMonicLiftData core target primeData)
            (BHKS.equivalenceClassIndicatorsOfLiftData core
              (Hex.ZPoly.toMonicLiftData core target primeData) hinputs.rows_pos) =
          some hinputs.expectedFactors := by
      simpa [hinputs.indicators_match] using hinputs.candidates_eq
    exact BHKS.size_eq_indicators_of_candidates hcandidates
  exact
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut
      hinputs.trueSupports hcore_ne h hcut hsize hpartition

set_option maxHeartbeats 800000 in
/--
Default-bound scheduled-loop fast-BHKS direct-core specialization.

Same as `factorFastCoreDefault_factor_zpolyIrreducible_of_forwardInputs`, but
with the loop-success hypothesis `h` decoupled from the recovery precision
`target` so that it matches the executable schedule walk (which starts the core
loop at `Hex.initialHenselPrecision a`, not at `target`).  The forward package,
cut certificate, and partition count are all carried at the scheduled `target`;
`h` is the loop-output equality at the actual `start`/`fuel`, supplied by the
scheduled-loop determinism obligation.
-/
theorem factorFastCoreDefault_factor_zpolyIrreducible_of_forwardInputs_on_schedule
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (primeData : Hex.PrimeChoiceData) {start fuel target : Nat}
    (hinputs :
      BHKS.ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore target primeData))
    (h :
      Hex.factorFastCoreWithBound
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData start fuel =
        some hinputs.expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore target primeData)
          hinputs.rows_pos)
        hinputs.trueSupports)
    (hpartition :
      (BHKS.supportPartitionByMinColumn hinputs.trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card) :
    ∀ factor ∈ hinputs.expectedFactors.toList,
      Hex.ZPoly.Irreducible factor := by
  have hcore_lc_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  exact
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_forwardInputs_on_schedule
      hcore_ne hinputs h hcut hpartition

/--
Recorded-entry irreducibility for the BHKS fast-core success arm.

The executable reassembly array is intentionally private to
`HexBerlekampZassenhaus.Basic`, so this public theorem works through the
existing branch-shape lemma: each recorded `factorWithBound` entry is the
sign-normalisation of some raw factor in the fast-core reassembly.  The
forward-input/cut certificates prove each successful core output irreducible,
and the supplied reassembly-completeness certificate lifts that proof across the
normalization reassembly.
-/
theorem factorWithBound_fastCore_entry_irreducible_of_forwardInputs
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hB_pos : 1 ≤ B)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hmulti : 1 < primeData.factorsModP.size)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (hinputs :
      BHKS.ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some hinputs.expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          hinputs.rows_pos)
        hinputs.trueSupports)
    (hpartition :
      (BHKS.supportPartitionByMinColumn hinputs.trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card)
    (hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
        hinputs.expectedFactors) :
    ∀ entry ∈ (Hex.factorWithBound f B).factors.toList,
      Hex.ZPoly.Irreducible entry.1 := by
  have hcore_lc_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_irr :
      ∀ factor ∈ hinputs.expectedFactors.toList,
        Hex.ZPoly.Irreducible factor :=
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_forwardInputs_on_schedule
      hcore_ne hinputs hcore hcut hpartition
  intro entry hentry
  obtain ⟨raw, hraw_mem, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_fast_core_success_raw f B entry
      primeData hB_pos hdeg hchoose hmulti hquadratic hcore hentry
  have hraw_irr : Hex.ZPoly.Irreducible raw :=
    Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
      (Hex.normalizeForFactor f) hinputs.expectedFactors
      hcomplete hcore_irr hraw_mem
  rw [hentry_eq]
  exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible hraw_irr

private theorem dvd_acc_foldl_mul_zpoly (x : Hex.ZPoly) :
    ∀ (l : List Hex.ZPoly) (acc : Hex.ZPoly),
      x ∣ acc → x ∣ l.foldl (· * ·) acc := by
  intro l
  induction l with
  | nil =>
      intro acc hacc
      simpa using hacc
  | cons head tail ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      refine ih (acc * head) ?_
      have hcomm : acc * head = head * acc := Hex.DensePoly.mul_comm_poly (S := Int) acc head
      rw [hcomm]
      exact Hex.DensePoly.dvd_mul_left_poly head hacc

private theorem mem_dvd_foldl_mul_zpoly
    (l : List Hex.ZPoly) (acc : Hex.ZPoly) (x : Hex.ZPoly) (hx : x ∈ l) :
    x ∣ l.foldl (· * ·) acc := by
  induction l generalizing acc with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons head tail ih =>
      rw [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with rfl | hx
      · refine dvd_acc_foldl_mul_zpoly x tail (acc * x) ?_
        have hcomm : acc * x = x * acc := Hex.DensePoly.mul_comm_poly (S := Int) acc x
        rw [hcomm]
        exact ⟨acc, rfl⟩
      · exact ih (acc * head) hx

private theorem factorPower_size_lower_bound
    {q : Hex.ZPoly} (hq_deg : 0 < q.degree?.getD 0) (e : Nat) :
    e + 1 ≤ (Hex.Factorization.factorPower q e).size := by
  induction e with
  | zero =>
      show 1 ≤ (1 : Hex.ZPoly).size
      rfl
  | succ e ih =>
      rw [Hex.Factorization.factorPower_succ]
      have hq_size_ge_two : 2 ≤ q.size := by
        have hdeg_unfold : q.degree?.getD 0 =
            (if q.size = 0 then 0 else q.size - 1) := by
          unfold Hex.DensePoly.degree?
          by_cases h : q.size = 0 <;> simp [h]
        rw [hdeg_unfold] at hq_deg
        by_cases h : q.size = 0
        · simp [h] at hq_deg
        · simp [h] at hq_deg
          omega
      have hprev_size_pos : 0 < (Hex.Factorization.factorPower q e).size := by
        omega
      have hq_size_pos : 0 < q.size := by
        omega
      have hmul_size :
          (Hex.Factorization.factorPower q e * q).size =
            (Hex.Factorization.factorPower q e).size + q.size - 1 :=
        Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_size_pos hq_size_pos
      omega

/--
Successful BHKS fast-core reassembly consumes the normalized repeated-part
residual.  This is the reassembly-completeness producer for the public fast
branch: the same forward/cut certificates that prove emitted core factors
irreducible also supply the square-free-cover hypothesis consumed by the
existing repeated-part assembler.
-/
theorem fastCoreComplete_of_forwardInputs
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hinputs :
      BHKS.ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some hinputs.expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          hinputs.rows_pos)
        hinputs.trueSupports)
    (hpartition :
      (BHKS.supportPartitionByMinColumn hinputs.trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      hinputs.expectedFactors := by
  have hcore_lc_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hirr : ∀ q ∈ hinputs.expectedFactors.toList, Hex.ZPoly.Irreducible q :=
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_forwardInputs_on_schedule
      hcore_ne hinputs hcore hcut hpartition
  have hprod :
      Array.polyProduct hinputs.expectedFactors =
        (Hex.normalizeForFactor f).squareFreeCore := by
    simpa using
      Hex.factorFastCoreWithBound_product
        (Hex.normalizeForFactor f).squareFreeCore B primeData
        (Hex.initialHenselPrecision B) (Hex.ZPoly.quadraticDoublingSteps B + 2)
        hinputs.expectedFactors hcore
  have hnorm :
      ∀ q ∈ hinputs.expectedFactors.toList, Hex.normalizeFactorSign q = q := by
    intro q hq
    exact Hex.factorFastCoreWithBound_some_normalizeFactorSign hcore q hq
  have hdegree :
      ∀ q ∈ hinputs.expectedFactors.toList, 0 < q.degree?.getD 0 := by
    intro q hq
    exact Hex.factorFastCoreWithBound_some_degree_pos hcore q hq
  have hpos_lc :
      ∀ q ∈ hinputs.expectedFactors.toList,
        0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm : Hex.normalizeFactorSign q = q := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      rw [← hq_norm]
      exact leadingCoeff_normalizeFactorSign_nonneg q
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  have hrp_ne :
      (Hex.normalizeForFactor f).repeatedPart ≠ 0 :=
    Hex.repeatedPart_ne_zero_of_ne_zero f hf_ne
  have hfuel :
      ∀ exponents : List Nat,
        exponents.length = hinputs.expectedFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((hinputs.expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ hinputs.expectedFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro exponents _ hdecomp qe hqe
    have hq_mem : qe.1 ∈ hinputs.expectedFactors.toList :=
      (List.of_mem_zip hqe).1
    have hq_deg : 0 < qe.1.degree?.getD 0 := hdegree qe.1 hq_mem
    have hfp_size_lb : qe.2 + 1 ≤
        (Hex.Factorization.factorPower qe.1 qe.2).size :=
      factorPower_size_lower_bound hq_deg qe.2
    have hfp_ne : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
      intro h0
      have : (Hex.Factorization.factorPower qe.1 qe.2).size = 0 := by
        rw [h0]
        rfl
      omega
    have hfp_in_map :
        Hex.Factorization.factorPower qe.1 qe.2 ∈
          (hinputs.expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2) := by
      rw [List.mem_map]
      exact ⟨qe, hqe, rfl⟩
    have hfp_dvd :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          ((hinputs.expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
      mem_dvd_foldl_mul_zpoly _ 1 _ hfp_in_map
    have hfp_dvd_rp :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          (Hex.normalizeForFactor f).repeatedPart := by
      rw [hdecomp]
      exact hfp_dvd
    have hsize_le : (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
      Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne hrp_ne hfp_dvd_rp
    omega
  exact IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    f hf_ne hinputs.expectedFactors hirr hprod hnorm hpos_lc hdegree hfuel

/--
Fast `h_raw` disjunct producer for the BHKS fast-core success arm.

This is the fast half of the `h_raw` hypothesis consumed by
`HexBerlekampZassenhausMathlib.factorWithBound_entries_irreducible` /
`factor_entries_irreducible` (#3987 / #4170) and by the #6672 capstone:
whenever the public fast factor function `Hex.factorFastFactorsWithBound f B`
returns `some rawFactors`, every raw factor in that array is
`Hex.ZPoly.Irreducible`.  Instantiating `B` at `Hex.ZPoly.defaultFactorCoeffBound f`
yields exactly the first disjunct of `factor_entries_irreducible`'s `h_raw`.

Unlike the #7738 entry-level theorem `factorWithBound_fastCore_entry_irreducible_of_forwardInputs`,
which proves the *recorded* `factorWithBound` entries irreducible, this exposes
the *raw* fast-factor array directly: it identifies that array as the
normalization reassembly of the successful core output `hinputs.expectedFactors`
(`Hex.factorFastFactorsWithBound_eq_some_of_core_success`), proves each core
factor irreducible through the scheduled-loop forward-input wrapper
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_forwardInputs_on_schedule`,
and lifts that across the reassembly via
`Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`.

The first-success certificates are threaded as hypotheses at the precision the
caller carries them: `hcore` pins the *actual* executable loop output (started
at `Hex.initialHenselPrecision a`, not at a cap precision) to
`hinputs.expectedFactors`.  This does not force equality with any cap recovery
array, and the cut certificate `hcut` runs through the true-factor lift/cut
stack rather than the refuted no-early-success or cap-determinism shortcuts. -/
theorem factorFastFactorsWithBound_raw_zpolyIrreducible_of_forwardInputs
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hB_pos : 1 ≤ B)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hmulti : 1 < primeData.factorsModP.size)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (hinputs :
      BHKS.ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some hinputs.expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          hinputs.rows_pos)
        hinputs.trueSupports)
    (hpartition :
      (BHKS.supportPartitionByMinColumn hinputs.trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card)
    (hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
        hinputs.expectedFactors)
    {rawFactors : Array Hex.ZPoly}
    (hfast : Hex.factorFastFactorsWithBound f B = some rawFactors) :
    ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw := by
  have hcore_lc_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_irr :
      ∀ factor ∈ hinputs.expectedFactors.toList,
        Hex.ZPoly.Irreducible factor :=
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_forwardInputs_on_schedule
      hcore_ne hinputs hcore hcut hpartition
  have hfast_eq :=
    Hex.factorFastFactorsWithBound_eq_some_of_core_success f B primeData
      hinputs.expectedFactors hB_pos hchoose hdeg (by omega) hquadratic hcore
  rw [hfast] at hfast_eq
  have hraw_eq := (Option.some.inj hfast_eq)
  intro raw hraw_mem
  rw [hraw_eq] at hraw_mem
  exact
    Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
      (Hex.normalizeForFactor f) hinputs.expectedFactors hcomplete hcore_irr
      hraw_mem

/--
No-`hcomplete` sibling of
`factorFastFactorsWithBound_raw_zpolyIrreducible_of_forwardInputs`.

The successful fast-core branch itself proves
`Hex.reassemblyExpansionComplete` via
`fastCoreComplete_of_forwardInputs`, so callers carrying
the same forward/cut certificates no longer have to supply reassembly
completeness separately.
-/
theorem rawIrreducible_of_forwardInputs
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hB_pos : 1 ≤ B)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hmulti : 1 < primeData.factorsModP.size)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (hinputs :
      BHKS.ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some hinputs.expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          hinputs.rows_pos)
        hinputs.trueSupports)
    (hpartition :
      (BHKS.supportPartitionByMinColumn hinputs.trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card)
    {rawFactors : Array Hex.ZPoly}
    (hfast : Hex.factorFastFactorsWithBound f B = some rawFactors) :
    ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw :=
  factorFastFactorsWithBound_raw_zpolyIrreducible_of_forwardInputs
    f hf_ne B primeData hB_pos hchoose hdeg hmulti hquadratic
    hinputs hcore hcut hpartition
    (fastCoreComplete_of_forwardInputs
      f hf_ne B primeData hinputs hcore hcut hpartition)
    hfast

/--
Direct-cut variant of
`fastCoreComplete_of_forwardInputs`.  This matches the
lower-level wrapper that avoids constructing a `BHKS.ForwardRecoveryInputs`
value and carries the cut, size, and partition certificates directly.
-/
theorem fastCoreComplete_of_cut
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      BHKS.HasPositiveDimension (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
    (trueSupports :
      Set (Set (Fin
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          rows_pos).factorCount)))
    {expectedFactors : Array Hex.ZPoly}
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          rows_pos)
        trueSupports)
    (hsize :
      expectedFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (BHKS.projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              B primeData)
            rows_pos)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      expectedFactors := by
  have hcore_lc_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hirr : ∀ q ∈ expectedFactors.toList, Hex.ZPoly.Irreducible q :=
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut
      trueSupports hcore_ne hcore hcut hsize hpartition
  have hprod :
      Array.polyProduct expectedFactors =
        (Hex.normalizeForFactor f).squareFreeCore := by
    simpa using
      Hex.factorFastCoreWithBound_product
        (Hex.normalizeForFactor f).squareFreeCore B primeData
        (Hex.initialHenselPrecision B) (Hex.ZPoly.quadraticDoublingSteps B + 2)
        expectedFactors hcore
  have hnorm :
      ∀ q ∈ expectedFactors.toList, Hex.normalizeFactorSign q = q := by
    intro q hq
    exact Hex.factorFastCoreWithBound_some_normalizeFactorSign hcore q hq
  have hdegree :
      ∀ q ∈ expectedFactors.toList, 0 < q.degree?.getD 0 := by
    intro q hq
    exact Hex.factorFastCoreWithBound_some_degree_pos hcore q hq
  have hpos_lc :
      ∀ q ∈ expectedFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm : Hex.normalizeFactorSign q = q := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      rw [← hq_norm]
      exact leadingCoeff_normalizeFactorSign_nonneg q
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  have hrp_ne :
      (Hex.normalizeForFactor f).repeatedPart ≠ 0 :=
    Hex.repeatedPart_ne_zero_of_ne_zero f hf_ne
  have hfuel :
      ∀ exponents : List Nat,
        exponents.length = expectedFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ expectedFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro exponents _ hdecomp qe hqe
    have hq_mem : qe.1 ∈ expectedFactors.toList :=
      (List.of_mem_zip hqe).1
    have hq_deg : 0 < qe.1.degree?.getD 0 := hdegree qe.1 hq_mem
    have hfp_size_lb : qe.2 + 1 ≤
        (Hex.Factorization.factorPower qe.1 qe.2).size :=
      factorPower_size_lower_bound hq_deg qe.2
    have hfp_ne : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
      intro h0
      have : (Hex.Factorization.factorPower qe.1 qe.2).size = 0 := by
        rw [h0]
        rfl
      omega
    have hfp_in_map :
        Hex.Factorization.factorPower qe.1 qe.2 ∈
          (expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2) := by
      rw [List.mem_map]
      exact ⟨qe, hqe, rfl⟩
    have hfp_dvd :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          ((expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
      mem_dvd_foldl_mul_zpoly _ 1 _ hfp_in_map
    have hfp_dvd_rp :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          (Hex.normalizeForFactor f).repeatedPart := by
      rw [hdecomp]
      exact hfp_dvd
    have hsize_le : (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
      Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne hrp_ne hfp_dvd_rp
    omega
  exact IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    f hf_ne expectedFactors hirr hprod hnorm hpos_lc hdegree hfuel

/--
Forward `factorFastFactorsWithBound`-level raw irreducibility that takes the
forward cut certificates **directly**, with no `BHKS.ForwardRecoveryInputs`
parameter.

Sibling of `factorFastFactorsWithBound_raw_zpolyIrreducible_of_forwardInputs`,
but routed through `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut`
rather than reconstructing a `ForwardRecoveryInputs` value.  This deliberately
avoids the structure's `lattice_eq_indicators` field — the dead reverse
`L' = W` separation (route-blocked behind #6779 / #2564) that nothing
downstream reads — so a forward-only producer never has to inhabit it.  The
`expectedFactors`, `trueSupports`, dimension positivity (`rows_pos`),
indicator-size, and partition-count certificates are supplied directly; the
forward cut hypothesis `hcut` (over `projectedRowsOfLiftData`) is the only
lattice obligation, and the first-success loop pin `hcore` is threaded at the
actual executable `start = initialHenselPrecision a` (not at a cap precision),
exactly as in the `_of_forwardInputs` sibling.

This closes deliverable 1 of #7786.  Deliverable 2 — a producer that discharges
the per-support `BHKS.TrueFactorLift` / `TrueFactorLiftSemantics` /
Lemma-5.7 separation family (and hence `hcut`) for the actual first-success
recovery — remains open on a missing coverage substrate (see the issue
comment). -/
theorem factorFastFactorsWithBound_raw_zpolyIrreducible_of_cut
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hB_pos : 1 ≤ B)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hmulti : 1 < primeData.factorsModP.size)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (rows_pos :
      BHKS.HasPositiveDimension (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
    (trueSupports :
      Set (Set (Fin
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          rows_pos).factorCount)))
    {expectedFactors : Array Hex.ZPoly}
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          rows_pos)
        trueSupports)
    (hsize :
      expectedFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (BHKS.projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              B primeData)
            rows_pos)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card)
    (hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
        expectedFactors)
    {rawFactors : Array Hex.ZPoly}
    (hfast : Hex.factorFastFactorsWithBound f B = some rawFactors) :
    ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw := by
  have hcore_lc_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_irr :
      ∀ factor ∈ expectedFactors.toList,
        Hex.ZPoly.Irreducible factor :=
    factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut
      trueSupports hcore_ne hcore hcut hsize hpartition
  have hfast_eq :=
    Hex.factorFastFactorsWithBound_eq_some_of_core_success f B primeData
      expectedFactors hB_pos hchoose hdeg (by omega) hquadratic hcore
  rw [hfast] at hfast_eq
  have hraw_eq := (Option.some.inj hfast_eq)
  intro raw hraw_mem
  rw [hraw_eq] at hraw_mem
  exact
    Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
      (Hex.normalizeForFactor f) expectedFactors hcomplete hcore_irr
      hraw_mem

/--
No-`hcomplete` sibling of `factorFastFactorsWithBound_raw_zpolyIrreducible_of_cut`.
The direct cut certificates plus fast-core success prove the required
`Hex.reassemblyExpansionComplete` internally.
-/
theorem rawIrreducible_of_cut
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hB_pos : 1 ≤ B)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hmulti : 1 < primeData.factorsModP.size)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (rows_pos :
      BHKS.HasPositiveDimension (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
    (trueSupports :
      Set (Set (Fin
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          rows_pos).factorCount)))
    {expectedFactors : Array Hex.ZPoly}
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some expectedFactors)
    (hcut :
      BHKS.CutProjectionHypotheses
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          rows_pos)
        trueSupports)
    (hsize :
      expectedFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (BHKS.projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              B primeData)
            rows_pos)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card)
    {rawFactors : Array Hex.ZPoly}
    (hfast : Hex.factorFastFactorsWithBound f B = some rawFactors) :
    ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw :=
  factorFastFactorsWithBound_raw_zpolyIrreducible_of_cut
    f hf_ne B primeData hB_pos hchoose hdeg hmulti hquadratic
    rows_pos trueSupports hcore hcut hsize hpartition
    (fastCoreComplete_of_cut
      f hf_ne B primeData rows_pos trueSupports hcore hcut hsize hpartition)
    hfast

/--
Fast-branch raw irreducibility capstone from the #8051 recovered-lift cut
package.

This is the raw `factorFastFactorsWithBound` analogue of the core-level
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift`: instead
of taking the forward cut certificate `hcut` as an opaque hypothesis, it
consumes the per-support `BHKS.RecoveredLift` family (the data the executable
fast-core recovery actually exposes) together with its monicity, prime,
Hensel-precision, threshold, and per-index congruence side conditions, and
builds `hcut` through the #8051 producer
`BHKS.cutProjectionHypotheses_of_recoveredLift` (period-adjusted short vectors →
retained projected-row span).  The count-equality / UFD-partition plumbing is
not re-derived here — it is routed through `rawIrreducible_of_cut`, which
discharges `reassemblyExpansionComplete` and the factor-count refinement from
`hsize`/`hpartition`.

Scoped to the fast-core success disjunct: the slow modular branch, the
trial-division branch, and the public `factor_irreducible_of_nonUnit` assembly
are left to later issues. -/
theorem factorFastFactorsWithBound_raw_zpolyIrreducible_of_recoveredLift
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hB_pos : 1 ≤ B)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hmulti : 1 < primeData.factorsModP.size)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (rows_pos :
      BHKS.HasPositiveDimension (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
    (trueSupports :
      Set (Set (Fin
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          rows_pos).factorCount)))
    {expectedFactors : Array Hex.ZPoly}
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some expectedFactors)
    (hbasis :
      (BHKS.latticeBasisOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData)).basis.independent)
    (lift : ∀ S : trueSupports,
      BHKS.RecoveredLift
        (BHKS.latticeBasisOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)) S.1)
    (hf_lc : ∀ S : trueSupports,
      Hex.DensePoly.leadingCoeff (lift S).f = 1)
    (hfactor_monic : ∀ S : trueSupports,
      (HexPolyMathlib.toPolynomial (lift S).factor).Monic)
    (hp : ∀ S : trueSupports, 2 ≤ (lift S).p)
    (hk : ∀ S : trueSupports, 1 < (lift S).p ^ (lift S).a)
    (hsep : ∀ S : trueSupports,
      ∀ j, 2 * Hex.bhksCoeffBound (lift S).f j < (lift S).p ^ (lift S).a)
    (hthr : ∀ S : trueSupports,
      ∀ j, Hex.bhksCoeffCutThreshold (lift S).p (lift S).f j ≤ (lift S).a)
    (hfac : ∀ S : trueSupports,
      ∀ i : Fin (BHKS.latticeBasisOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)).factorCount, i ∈ S.1 →
        ∃ g : Hex.ZPoly,
          Hex.DensePoly.Monic
            ((BHKS.latticeBasisOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                B primeData)).liftedFactors.getD i.val 1) ∧
          0 < ((BHKS.latticeBasisOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                B primeData)).liftedFactors.getD i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr (lift S).f
            ((BHKS.latticeBasisOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                B primeData)).liftedFactors.getD i.val 1 * g)
            ((lift S).p ^ (lift S).a))
    (hsize :
      expectedFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (BHKS.projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              B primeData)
            rows_pos)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card)
    {rawFactors : Array Hex.ZPoly}
    (hfast : Hex.factorFastFactorsWithBound f B = some rawFactors) :
    ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw :=
  rawIrreducible_of_cut
    f hf_ne B primeData hB_pos hchoose hdeg hmulti hquadratic
    rows_pos trueSupports hcore
    (BHKS.cutProjectionHypotheses_of_recoveredLift
      (BHKS.latticeBasisOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
      rows_pos hbasis trueSupports lift hf_lc hfactor_monic hp hk hsep hthr hfac)
    hsize hpartition hfast

/--
Recorded-entry (guarded) form of
`factorFastFactorsWithBound_raw_zpolyIrreducible_of_recoveredLift`.

The corrected fast-branch irreducibility contract (#8079) guards each raw
obligation with `Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw)
= true`, excluding the unit/constant raw outputs the public factorization never
records.  On the BHKS core-success disjunct every raw factor is unconditionally
irreducible, so the guard is simply dropped and the obligation routes through the
#8058 capstone `factorFastFactorsWithBound_raw_zpolyIrreducible_of_recoveredLift`
— no cut, partition-count, or support-family proof is re-derived here.  The
companion constant/unit early-return disjunct is
`Hex.factorFastFactorsWithBound_raw_irreducible_of_constant`. -/
theorem factorFastFactorsWithBound_raw_guardedIrreducible_of_recoveredLift
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hB_pos : 1 ≤ B)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hmulti : 1 < primeData.factorsModP.size)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (rows_pos :
      BHKS.HasPositiveDimension (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData))
    (trueSupports :
      Set (Set (Fin
        (BHKS.projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)
          rows_pos).factorCount)))
    {expectedFactors : Array Hex.ZPoly}
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some expectedFactors)
    (hbasis :
      (BHKS.latticeBasisOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          B primeData)).basis.independent)
    (lift : ∀ S : trueSupports,
      BHKS.RecoveredLift
        (BHKS.latticeBasisOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)) S.1)
    (hf_lc : ∀ S : trueSupports,
      Hex.DensePoly.leadingCoeff (lift S).f = 1)
    (hfactor_monic : ∀ S : trueSupports,
      (HexPolyMathlib.toPolynomial (lift S).factor).Monic)
    (hp : ∀ S : trueSupports, 2 ≤ (lift S).p)
    (hk : ∀ S : trueSupports, 1 < (lift S).p ^ (lift S).a)
    (hsep : ∀ S : trueSupports,
      ∀ j, 2 * Hex.bhksCoeffBound (lift S).f j < (lift S).p ^ (lift S).a)
    (hthr : ∀ S : trueSupports,
      ∀ j, Hex.bhksCoeffCutThreshold (lift S).p (lift S).f j ≤ (lift S).a)
    (hfac : ∀ S : trueSupports,
      ∀ i : Fin (BHKS.latticeBasisOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            B primeData)).factorCount, i ∈ S.1 →
        ∃ g : Hex.ZPoly,
          Hex.DensePoly.Monic
            ((BHKS.latticeBasisOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                B primeData)).liftedFactors.getD i.val 1) ∧
          0 < ((BHKS.latticeBasisOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                B primeData)).liftedFactors.getD i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr (lift S).f
            ((BHKS.latticeBasisOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                B primeData)).liftedFactors.getD i.val 1 * g)
            ((lift S).p ^ (lift S).a))
    (hsize :
      expectedFactors.size =
        (Hex.bhksEquivalenceClassIndicators
          (BHKS.projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              B primeData)
            rows_pos)).size)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card)
    {rawFactors : Array Hex.ZPoly}
    (hfast : Hex.factorFastFactorsWithBound f B = some rawFactors) :
    ∀ raw ∈ rawFactors.toList,
      Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true →
        Hex.ZPoly.Irreducible raw :=
  fun raw hmem _hrecord =>
    factorFastFactorsWithBound_raw_zpolyIrreducible_of_recoveredLift
      f hf_ne B primeData hB_pos hchoose hdeg hmulti hquadratic
      rows_pos trueSupports hcore hbasis lift hf_lc hfactor_monic hp hk hsep hthr hfac
      hsize hpartition hfast raw hmem

end HexBerlekampZassenhausMathlib
