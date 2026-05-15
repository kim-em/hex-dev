import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.Polynomial.UniqueFactorization

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
The normalized factors of a list product of irreducibles are exactly the
normalizations of the list entries, viewed as a multiset.
-/
theorem normalizedFactors_list_prod_eq_of_irreducible
    {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    [NormalizationMonoid α] [UniqueFactorizationMonoid α]
    (gs : List α) (hirr : ∀ g ∈ gs, Irreducible g) :
    normalizedFactors gs.prod = ((gs : Multiset α).map normalize) := by
  let s : Multiset α := (gs : Multiset α)
  have hs_prod : s.prod = gs.prod := by
    simp [s, Multiset.prod_coe]
  rw [← hs_prod]
  exact normalizedFactors_prod_eq s (by
    intro g hg
    exact hirr g (Multiset.mem_coe.mp hg))

private theorem polynomial_list_prod_monic
    (gs : List (Polynomial ℤ)) (hmonic : ∀ g ∈ gs, g.Monic) :
    gs.prod.Monic := by
  induction gs with
  | nil =>
      exact Polynomial.leadingCoeff_one
  | cons g gs ih =>
      rw [List.prod_cons]
      exact (hmonic g (by simp)).mul
        (ih (fun q hq => hmonic q (by simp [hq])))

/--
Uniqueness for scalar-prefixed products of flattened monic irreducible integer
polynomial factors.

If two nonzero integer scalars multiply products of monic irreducible factors
to the same polynomial, the scalars agree and the flattened products have the
same normalized-factor multiset. This is the Mathlib/UFD core needed by the
factorization uniqueness bridge after executable factor entries have been
expanded by multiplicity.
-/
theorem scalar_eq_and_normalizedFactors_eq_of_monic_irreducible_product_eq
    (c d : ℤ) (xs ys : List (Polynomial ℤ))
    (hc : c ≠ 0)
    (hxirr : ∀ x ∈ xs, Irreducible x)
    (hyirr : ∀ y ∈ ys, Irreducible y)
    (hxmonic : ∀ x ∈ xs, x.Monic)
    (hymonic : ∀ y ∈ ys, y.Monic)
    (hprod :
      Polynomial.C c * xs.prod = Polynomial.C d * ys.prod) :
    c = d ∧
      normalizedFactors xs.prod = normalizedFactors ys.prod := by
  have hxprod_monic : xs.prod.Monic :=
    polynomial_list_prod_monic xs hxmonic
  have hyprod_monic : ys.prod.Monic :=
    polynomial_list_prod_monic ys hymonic
  have hscalar : c = d := by
    have hlead := congrArg Polynomial.leadingCoeff hprod
    rw [hxprod_monic.leadingCoeff_C_mul c,
      hyprod_monic.leadingCoeff_C_mul d] at hlead
    exact hlead
  have hprod_eq : xs.prod = ys.prod := by
    have hcancel :
        Polynomial.C c * xs.prod = Polynomial.C c * ys.prod := by
      simpa [hscalar] using hprod
    exact mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hc) hcancel
  refine ⟨hscalar, ?_⟩
  have hxnorm := normalizedFactors_list_prod_eq_of_irreducible xs hxirr
  have hynorm := normalizedFactors_list_prod_eq_of_irreducible ys hyirr
  simpa [hxnorm, hynorm] using congrArg normalizedFactors hprod_eq

/--
Variant of `scalar_eq_and_normalizedFactors_eq_of_monic_irreducible_product_eq`
for nonconstant `normalize`-fixed irreducible integer polynomial factors, which
is what the BZ uniqueness bridge actually has (the executable
`normalizeFactorSign` only enforces a nonnegative leading coefficient, not a
unit leading coefficient).

If two nonzero integer scalars multiply products of nonconstant `normalize`-fixed
irreducible integer polynomial factors to the same polynomial, the scalars
agree and the flattened factor lists agree as multisets. Constant factors are
ruled out by the `natDegree ≠ 0` hypothesis, so they cannot leak between the
scalar prefix and the factor list.
-/
theorem scalar_eq_and_coe_eq_of_normalize_fixed_nonconst_irreducible_product_eq
    (c d : ℤ) (xs ys : List (Polynomial ℤ))
    (hc : c ≠ 0)
    (hxirr : ∀ x ∈ xs, Irreducible x)
    (hyirr : ∀ y ∈ ys, Irreducible y)
    (hxnorm : ∀ x ∈ xs, normalize x = x)
    (hynorm : ∀ y ∈ ys, normalize y = y)
    (hxnonconst : ∀ x ∈ xs, x.natDegree ≠ 0)
    (hynonconst : ∀ y ∈ ys, y.natDegree ≠ 0)
    (hprod : Polynomial.C c * xs.prod = Polynomial.C d * ys.prod) :
    c = d ∧ (xs : Multiset (Polynomial ℤ)) = (ys : Multiset _) := by
  have hCc_ne : (Polynomial.C c : Polynomial ℤ) ≠ 0 := Polynomial.C_ne_zero.mpr hc
  have hxs_zero_notMem : (0 : Polynomial ℤ) ∉ xs := fun h =>
    (hxirr 0 h).ne_zero rfl
  have hys_zero_notMem : (0 : Polynomial ℤ) ∉ ys := fun h =>
    (hyirr 0 h).ne_zero rfl
  have hxprod_ne : xs.prod ≠ 0 := List.prod_ne_zero hxs_zero_notMem
  have hys_prod_ne : ys.prod ≠ 0 := List.prod_ne_zero hys_zero_notMem
  have hd_ne : d ≠ 0 := by
    intro hd0
    rw [hd0, Polynomial.C_0, zero_mul] at hprod
    exact mul_ne_zero hCc_ne hxprod_ne hprod
  have hCd_ne : (Polynomial.C d : Polynomial ℤ) ≠ 0 := Polynomial.C_ne_zero.mpr hd_ne
  -- The (multiset-of) flattened factors equals normalizedFactors of the product.
  have hxnorm_factors :
      normalizedFactors xs.prod = (xs : Multiset (Polynomial ℤ)) := by
    rw [normalizedFactors_list_prod_eq_of_irreducible xs hxirr]
    refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id _)
    intro x hx
    simpa using hxnorm x (Multiset.mem_coe.mp hx)
  have hynorm_factors :
      normalizedFactors ys.prod = (ys : Multiset (Polynomial ℤ)) := by
    rw [normalizedFactors_list_prod_eq_of_irreducible ys hyirr]
    refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id _)
    intro y hy
    simpa using hynorm y (Multiset.mem_coe.mp hy)
  -- Split off the constant scalar contribution on each side.
  have hsplit_x :
      normalizedFactors (Polynomial.C c * xs.prod) =
        normalizedFactors (Polynomial.C c) + (xs : Multiset (Polynomial ℤ)) := by
    rw [normalizedFactors_mul hCc_ne hxprod_ne, hxnorm_factors]
  have hsplit_y :
      normalizedFactors (Polynomial.C d * ys.prod) =
        normalizedFactors (Polynomial.C d) + (ys : Multiset (Polynomial ℤ)) := by
    rw [normalizedFactors_mul hCd_ne hys_prod_ne, hynorm_factors]
  have hfact_eq :
      normalizedFactors (Polynomial.C c) + (xs : Multiset (Polynomial ℤ)) =
        normalizedFactors (Polynomial.C d) + (ys : Multiset (Polynomial ℤ)) := by
    rw [← hsplit_x, ← hsplit_y, hprod]
  -- Each irreducible divisor of `C c` has `natDegree = 0`.
  have hCc_factors_const :
      ∀ q ∈ normalizedFactors (Polynomial.C c), q.natDegree = 0 := by
    intro q hq
    have hq_dvd : q ∣ Polynomial.C c := dvd_of_mem_normalizedFactors hq
    have hbound : q.natDegree ≤ (Polynomial.C c).natDegree :=
      Polynomial.natDegree_le_of_dvd hq_dvd hCc_ne
    rw [Polynomial.natDegree_C] at hbound
    exact Nat.le_zero.mp hbound
  have hCd_factors_const :
      ∀ q ∈ normalizedFactors (Polynomial.C d), q.natDegree = 0 := by
    intro q hq
    have hq_dvd : q ∣ Polynomial.C d := dvd_of_mem_normalizedFactors hq
    have hbound : q.natDegree ≤ (Polynomial.C d).natDegree :=
      Polynomial.natDegree_le_of_dvd hq_dvd hCd_ne
    rw [Polynomial.natDegree_C] at hbound
    exact Nat.le_zero.mp hbound
  -- Filter both sides by `natDegree ≠ 0` to isolate the nonconstant factors.
  have hfilter :
      (xs : Multiset (Polynomial ℤ)) = (ys : Multiset _) := by
    have key := congrArg
      (Multiset.filter (fun p : Polynomial ℤ => p.natDegree ≠ 0)) hfact_eq
    rw [Multiset.filter_add, Multiset.filter_add] at key
    have hL1 :
        (normalizedFactors (Polynomial.C c)).filter
            (fun p : Polynomial ℤ => p.natDegree ≠ 0) = 0 := by
      refine Multiset.filter_eq_nil.mpr ?_
      intro q hq
      simp [hCc_factors_const q hq]
    have hL2 :
        ((xs : Multiset (Polynomial ℤ))).filter
            (fun p : Polynomial ℤ => p.natDegree ≠ 0) = xs := by
      refine Multiset.filter_eq_self.mpr ?_
      intro q hq
      exact hxnonconst q (Multiset.mem_coe.mp hq)
    have hR1 :
        (normalizedFactors (Polynomial.C d)).filter
            (fun p : Polynomial ℤ => p.natDegree ≠ 0) = 0 := by
      refine Multiset.filter_eq_nil.mpr ?_
      intro q hq
      simp [hCd_factors_const q hq]
    have hR2 :
        ((ys : Multiset (Polynomial ℤ))).filter
            (fun p : Polynomial ℤ => p.natDegree ≠ 0) = ys := by
      refine Multiset.filter_eq_self.mpr ?_
      intro q hq
      exact hynonconst q (Multiset.mem_coe.mp hq)
    rw [hL1, hL2, hR1, hR2, zero_add, zero_add] at key
    exact key
  -- Reduce to scalar equality via cancellation on the polynomial part.
  have hprod_eq : xs.prod = ys.prod := by
    have hms := congrArg Multiset.prod hfilter
    simpa [Multiset.prod_coe] using hms
  have hCcd : (Polynomial.C c : Polynomial ℤ) = Polynomial.C d := by
    have heq : Polynomial.C c * xs.prod = Polynomial.C d * xs.prod := by
      conv_rhs => rw [hprod_eq]
      exact hprod
    exact mul_right_cancel₀ hxprod_ne heq
  exact ⟨Polynomial.C_injective hCcd, hfilter⟩

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

end UFDPartition

end HexBerlekampZassenhausMathlib
