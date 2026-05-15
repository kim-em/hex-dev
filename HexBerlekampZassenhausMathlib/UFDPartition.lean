import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
Abstract UFD partition-cardinality bound used by the BHKS Group B
certification chain.

The bridge layer needs to convert "the algorithm returned a list of non-unit
divisors that multiply back to `f`" into "each divisor is irreducible." The
UFD half of that argument is independent of the BHKS lattice machinery: in any
unique factorization monoid, if `gs.length = (normalizedFactors f).card` then
each `g ∈ gs` accounts for exactly one irreducible factor of `f`, hence is
irreducible.

This module isolates the Mathlib UFD reasoning so the algorithm-specific work
(certifying the cardinality equality from BHKS lattice success state) can be
treated separately.
-/

namespace HexBerlekampZassenhausMathlib

open UniqueFactorizationMonoid

namespace UFDPartition

/--
The cardinality of the sum of a multiset of multisets equals the sum of the
cardinalities. This is the multiset version of `Multiset.card_add` applied
under `Multiset.sum`.
-/
private lemma card_multiset_sum {α : Type*} (s : Multiset (Multiset α)) :
    s.sum.card = (s.map Multiset.card).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons x xs ih =>
      simp [Multiset.sum_cons, Multiset.card_add, ih]

/--
For a multiset of naturals with every element at least one, the cardinality of
the multiset is bounded above by its sum.
-/
private lemma card_le_sum_of_one_le {M : Multiset ℕ}
    (h : ∀ c ∈ M, 1 ≤ c) : M.card ≤ M.sum := by
  induction M using Multiset.induction with
  | empty => simp
  | cons c cs ih =>
      simp only [Multiset.sum_cons, Multiset.card_cons]
      have hc : 1 ≤ c := h c (Multiset.mem_cons_self c cs)
      have hcs : ∀ c' ∈ cs, 1 ≤ c' :=
        fun c' hc' => h c' (Multiset.mem_cons_of_mem hc')
      have hcs_le := ih hcs
      omega

/--
A multiset of naturals whose sum equals its cardinality, with every element at
least one, has every element exactly equal to one.
-/
private lemma eq_one_of_one_le_of_sum_eq_card {M : Multiset ℕ}
    (hge : ∀ c ∈ M, 1 ≤ c) (hsum : M.sum = M.card) :
    ∀ c ∈ M, c = 1 := by
  induction M using Multiset.induction with
  | empty =>
      intro c hc
      exact absurd hc (Multiset.notMem_zero c)
  | cons c cs ih =>
      intro c' hc'
      have hc_ge : 1 ≤ c := hge c (Multiset.mem_cons_self c cs)
      have hcs_ge : ∀ x ∈ cs, 1 ≤ x :=
        fun x hx => hge x (Multiset.mem_cons_of_mem hx)
      have hcs_le : cs.card ≤ cs.sum := card_le_sum_of_one_le hcs_ge
      simp only [Multiset.sum_cons, Multiset.card_cons] at hsum
      have hc_one : c = 1 := by omega
      have hcs_sum : cs.sum = cs.card := by omega
      rcases Multiset.mem_cons.mp hc' with rfl | h
      · exact hc_one
      · exact ih hcs_ge hcs_sum c' h

/--
Upper cardinality bound for a product partition in a UFD.

If a non-zero element `f` is associated to the product of a list of non-zero
non-unit factors, then that list cannot have more entries than the multiset of
normalized irreducible factors of `f`. Each list entry contributes at least one
normalized factor.
-/
theorem length_le_normalizedFactors_card
    {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α]
    [UniqueFactorizationMonoid α]
    {f : α} (_hf : f ≠ 0)
    (gs : List α)
    (hne : ∀ g ∈ gs, g ≠ 0)
    (hnonunit : ∀ g ∈ gs, ¬ IsUnit g)
    (hprod : Associated gs.prod f) :
    gs.length ≤ (normalizedFactors f).card := by
  let s : Multiset α := (gs : Multiset α)
  have hszero : (0 : α) ∉ s := by
    intro h
    exact hne 0 (Multiset.mem_coe.mp h) rfl
  have hs_prod : s.prod = gs.prod := by
    simp [s, Multiset.prod_coe]
  have hsum_factors :
      (normalizedFactors gs.prod) = (s.map normalizedFactors).sum := by
    rw [← hs_prod]
    exact normalizedFactors_multiset_prod s hszero
  have heq : (normalizedFactors f) = (s.map normalizedFactors).sum := by
    rw [← hsum_factors]
    exact hprod.normalizedFactors_eq.symm
  have hcard_sum :
      (normalizedFactors f).card =
        ((s.map normalizedFactors).map Multiset.card).sum := by
    rw [heq, card_multiset_sum]
  have hge_one :
      ∀ c ∈ (s.map normalizedFactors).map Multiset.card, 1 ≤ c := by
    intro c hc
    rcases Multiset.mem_map.mp hc with ⟨m, hm, rfl⟩
    rcases Multiset.mem_map.mp hm with ⟨g, hg, rfl⟩
    have hg_mem_gs : g ∈ gs := Multiset.mem_coe.mp hg
    have hne_g : g ≠ 0 := hne g hg_mem_gs
    have hnonunit_g : ¬ IsUnit g := hnonunit g hg_mem_gs
    have hfactors_ne : normalizedFactors g ≠ 0 :=
      (normalizedFactors_eq_zero_iff hne_g).not.mpr hnonunit_g
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    exact hfactors_ne (Multiset.card_eq_zero.mp hzero)
  have hM_card :
      ((s.map normalizedFactors).map Multiset.card).card = gs.length := by
    simp [s]
  calc
    gs.length = ((s.map normalizedFactors).map Multiset.card).card := hM_card.symm
    _ ≤ ((s.map normalizedFactors).map Multiset.card).sum :=
      card_le_sum_of_one_le hge_one
    _ = (normalizedFactors f).card := hcard_sum.symm

/--
If a list of irreducible factors has product associated to `f`, then the
multiset of normalized factors of `f` has exactly the length of the list.

This is the converse cardinality direction to
`length_le_normalizedFactors_card` for the already-certified irreducible
partition case.
-/
theorem normalizedFactors_card_eq_length_of_irreducible_partition
    {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    [NormalizationMonoid α] [UniqueFactorizationMonoid α]
    {f : α} (gs : List α)
    (hirr : ∀ g ∈ gs, Irreducible g)
    (hprod : Associated gs.prod f) :
    (normalizedFactors f).card = gs.length := by
  let s : Multiset α := (gs : Multiset α)
  have hs_prod : s.prod = gs.prod := by
    simp [s, Multiset.prod_coe]
  have hnorm_prod :
      normalizedFactors gs.prod = s.map normalize := by
    rw [← hs_prod]
    exact normalizedFactors_prod_eq s (by
      intro g hg
      exact hirr g (Multiset.mem_coe.mp hg))
  have heq : normalizedFactors f = s.map normalize := by
    rw [← hnorm_prod]
    exact hprod.normalizedFactors_eq.symm
  calc
    (normalizedFactors f).card = (s.map normalize).card := by rw [heq]
    _ = s.card := Multiset.card_map normalize s
    _ = gs.length := by simp [s]

/--
Lower cardinality bound for an irreducible product partition.

When every emitted factor is already known irreducible and the product is
associated to `f`, `f` cannot have more normalized irreducible factors than
the emitted list.
-/
theorem normalizedFactors_card_le_length_of_irreducible_partition
    {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    [NormalizationMonoid α] [UniqueFactorizationMonoid α]
    {f : α} (gs : List α)
    (hirr : ∀ g ∈ gs, Irreducible g)
    (hprod : Associated gs.prod f) :
    (normalizedFactors f).card ≤ gs.length := by
  rw [normalizedFactors_card_eq_length_of_irreducible_partition gs hirr hprod]

/--
**Group B partition-cardinality bound (Mathlib-only UFD argument).**

In any unique factorization monoid, a non-zero element `f` admitting a list of
non-unit divisors `gs` whose product is associated to `f` and whose length
equals the cardinality of `normalizedFactors f` must consist entirely of
irreducible elements.

This isolates the UFD half of the BHKS Group B / B8 certification theorem:
the algorithm-specific work (establishing the cardinality equality from BHKS
lattice success state) is handled separately and supplies the `hcount`
hypothesis to this lemma.
-/
theorem irreducible_of_partition_card_eq_normalizedFactors_card
    {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α]
    [UniqueFactorizationMonoid α]
    {f : α} (_hf : f ≠ 0)
    (gs : List α)
    (hne : ∀ g ∈ gs, g ≠ 0)
    (hnonunit : ∀ g ∈ gs, ¬ IsUnit g)
    (hprod : Associated gs.prod f)
    (hcount : gs.length = (normalizedFactors f).card) :
    ∀ g ∈ gs, Irreducible g := by
  -- View `gs` as a Multiset so we can use `normalizedFactors_multiset_prod`.
  let s : Multiset α := (gs : Multiset α)
  have hszero : (0 : α) ∉ s := by
    intro h
    exact hne 0 (Multiset.mem_coe.mp h) rfl
  have hs_prod : s.prod = gs.prod := by
    simp [s, Multiset.prod_coe]
  have hsum_factors :
      (normalizedFactors gs.prod) = (s.map normalizedFactors).sum := by
    rw [← hs_prod]
    exact normalizedFactors_multiset_prod s hszero
  have heq : (normalizedFactors f) = (s.map normalizedFactors).sum := by
    rw [← hsum_factors]
    exact hprod.normalizedFactors_eq.symm
  -- Take cardinalities.
  have hcard_sum :
      (normalizedFactors f).card =
        ((s.map normalizedFactors).map Multiset.card).sum := by
    rw [heq, card_multiset_sum]
  -- Each `(normalizedFactors g).card ≥ 1` (g non-zero, non-unit).
  have hge_one :
      ∀ c ∈ (s.map normalizedFactors).map Multiset.card, 1 ≤ c := by
    intro c hc
    rcases Multiset.mem_map.mp hc with ⟨m, hm, rfl⟩
    rcases Multiset.mem_map.mp hm with ⟨g, hg, rfl⟩
    have hg_mem_gs : g ∈ gs := Multiset.mem_coe.mp hg
    have hne_g : g ≠ 0 := hne g hg_mem_gs
    have hnonunit_g : ¬ IsUnit g := hnonunit g hg_mem_gs
    have hfactors_ne : normalizedFactors g ≠ 0 :=
      (normalizedFactors_eq_zero_iff hne_g).not.mpr hnonunit_g
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    exact hfactors_ne (Multiset.card_eq_zero.mp hzero)
  -- The map `card ∘ normalizedFactors` has the same length as `gs`.
  have hM_card :
      ((s.map normalizedFactors).map Multiset.card).card = gs.length := by
    simp [s]
  -- Combine: sum of cardinalities equals length of list of cardinalities.
  have hsum_eq_card :
      ((s.map normalizedFactors).map Multiset.card).sum =
        ((s.map normalizedFactors).map Multiset.card).card := by
    rw [← hcard_sum, ← hcount, ← hM_card]
  -- Hence each cardinality equals one.
  have heach_one :
      ∀ c ∈ (s.map normalizedFactors).map Multiset.card, c = 1 :=
    eq_one_of_one_le_of_sum_eq_card hge_one hsum_eq_card
  -- Apply to a specific `g ∈ gs`.
  intro g hg
  have hg_in_s : g ∈ s := Multiset.mem_coe.mpr hg
  have hcard_g :
      (normalizedFactors g).card = 1 := by
    refine heach_one (normalizedFactors g).card ?_
    refine Multiset.mem_map.mpr ⟨normalizedFactors g, ?_, rfl⟩
    exact Multiset.mem_map.mpr ⟨g, hg_in_s, rfl⟩
  -- `(normalizedFactors g).card = 1` ⟹ `Irreducible g`.
  obtain ⟨p, hp⟩ := Multiset.card_eq_one.mp hcard_g
  have hp_mem : p ∈ normalizedFactors g := by
    rw [hp]
    exact Multiset.mem_singleton_self _
  have hp_irr : Irreducible p := irreducible_of_normalized_factor p hp_mem
  have hg_ne : g ≠ 0 := hne g hg
  have hassoc : Associated (normalizedFactors g).prod g :=
    prod_normalizedFactors hg_ne
  rw [hp, Multiset.prod_singleton] at hassoc
  exact hassoc.irreducible hp_irr

/--
**UFD subset-factor lemma.**

In a unique factorization monoid, if a non-zero element `g` divides the
product of a multiset of irreducibles `qs`, then the normalized factorization
of `g` is a sub-multiset of `qs` up to normalization.

This is the UFD half of the BZ certificate degree-obstruction argument:
once an integer factor reduces to a divisor of the recorded modular factor
product, its modular factorization is drawn from the recorded irreducibles.
-/
theorem normalizedFactors_le_map_normalize_of_dvd_prod_irreducibles
    {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α]
    [UniqueFactorizationMonoid α]
    {g : α} (hg : g ≠ 0)
    {qs : Multiset α}
    (hirr : ∀ q ∈ qs, Irreducible q)
    (hdvd : g ∣ qs.prod) :
    normalizedFactors g ≤ qs.map normalize := by
  rcases qs.empty_or_exists_mem with rfl | ⟨b, hb⟩
  · rw [Multiset.prod_zero] at hdvd
    have hunit : IsUnit g := isUnit_of_dvd_one hdvd
    rw [normalizedFactors_of_isUnit hunit]
    exact Multiset.zero_le _
  · haveI : Nontrivial α := nontrivial_of_ne b 0 (hirr b hb).ne_zero
    have hprod_ne : qs.prod ≠ 0 :=
      Multiset.prod_ne_zero fun hmem => (hirr 0 hmem).ne_zero rfl
    have hnorm_prod : normalizedFactors qs.prod = qs.map normalize :=
      normalizedFactors_prod_eq qs hirr
    have hle : normalizedFactors g ≤ normalizedFactors qs.prod :=
      (dvd_iff_normalizedFactors_le_normalizedFactors hg hprod_ne).mp hdvd
    rw [hnorm_prod] at hle
    exact hle

/--
**Polynomial subset-degree lemma.**

Over a field `K`, if `g : K[X]` is non-zero and divides the product of a
multiset of irreducible polynomials `qs`, then `g.natDegree` is the sum of
some sub-multiset of `qs.map natDegree`.

This is the degree-subset-sum packaging of
`normalizedFactors_le_map_normalize_of_dvd_prod_irreducibles` that the BZ
certificate degree-obstruction consumer needs: the recorded modular factor
degrees are the `qs.map natDegree` values, and the contradiction with a
"no subset sums to `g.natDegree`" obstruction comes from this lemma.
-/
theorem natDegree_eq_sum_subset_of_dvd_prod_irreducibles
    {K : Type*} [Field K] [DecidableEq K]
    {g : Polynomial K} (hg : g ≠ 0)
    {qs : Multiset (Polynomial K)}
    (hirr : ∀ q ∈ qs, Irreducible q)
    (hdvd : g ∣ qs.prod) :
    ∃ S : Multiset Nat, S ≤ qs.map Polynomial.natDegree ∧ g.natDegree = S.sum := by
  have hle : normalizedFactors g ≤ qs.map normalize :=
    normalizedFactors_le_map_normalize_of_dvd_prod_irreducibles hg hirr hdvd
  refine ⟨(normalizedFactors g).map Polynomial.natDegree,
    ?_, ?_⟩
  · -- (normalizedFactors g).map natDegree ≤ qs.map natDegree
    have hsub :
        (normalizedFactors g).map Polynomial.natDegree ≤
          (qs.map normalize).map Polynomial.natDegree :=
      Multiset.map_le_map hle
    have hcong :
        (qs.map normalize).map Polynomial.natDegree =
          qs.map Polynomial.natDegree := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl ?_
      intro q _
      exact Polynomial.natDegree_eq_of_degree_eq Polynomial.degree_normalize
    rw [hcong] at hsub
    exact hsub
  · -- g.natDegree = ((normalizedFactors g).map natDegree).sum
    have hassoc : Associated (normalizedFactors g).prod g :=
      prod_normalizedFactors hg
    have hdeg_assoc :
        ((normalizedFactors g).prod).natDegree = g.natDegree :=
      Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated hassoc)
    have hprod_deg :
        ((normalizedFactors g).prod).natDegree =
          ((normalizedFactors g).map Polynomial.natDegree).sum :=
      Polynomial.natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)
    rw [hprod_deg] at hdeg_assoc
    exact hdeg_assoc.symm

end UFDPartition

end HexBerlekampZassenhausMathlib
