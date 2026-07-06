/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Recovery
public import HexBerlekampZassenhausMathlib.ToMonicUniqueness

public section
set_option backward.proofsInPublic true

/-!
Support-partition counting for the BHKS class-count lower bound (#8519).

Resurrected from the pre-#8411 `PartitionRefinement.lean` (6bf20977^): when
the true supports genuinely partition the lifted-factor indices (cover,
uniqueness, nonemptiness — supplied by `LiftedFactorSubsetPartition`), the
support-equivalence partition has exactly one class per support, so its
length is `(liftedTrueSupports core d).ncard`, which the #8413 machinery
identifies with `(normalizedFactors (toPolynomial core)).card`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

namespace BHKS

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
`bhksRecoveryCoreWithBound_some_factor_zpolyIrreducible`.
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

end BHKS

end

end HexBerlekampZassenhausMathlib
