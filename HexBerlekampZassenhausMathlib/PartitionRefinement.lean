import HexBerlekampZassenhausMathlib.Recovery
import HexBerlekampZassenhausMathlib.Basic

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
    core B primeData hmem hno
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
    hinputs (Hex.cap_mem_henselPrecisionSchedule B) hno

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
    rw [Hex.bhksIndicatorCandidates?_size_eq hinputs.candidates_eq]
    exact congrArg Array.size hinputs.indicators_match.symm
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
    rw [Hex.bhksIndicatorCandidates?_size_eq hinputs.candidates_eq]
    exact congrArg Array.size hinputs.indicators_match.symm
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

end HexBerlekampZassenhausMathlib
