/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
Abstract UFD partition-cardinality bound used by the BHKS Group B
certification chain.

The Mathlib-side layer needs to convert "the algorithm returned a list of
non-unit divisors that multiply back to `f`" into "each divisor is
irreducible." The
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
normalized factor. Callers use this for algorithm branches that already expose
product preservation and `shouldRecord`/non-unit facts, but have not yet proved
irreducibility of the emitted factors.
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
partition case. It is kept as the exact equality form because the exported
lower-bound theorem below is the shape used by branch-level callers.
-/
theorem normalizedFactors_card_eq_length_of_irreducible_partition
    {α : Type*} [CommMonoidWithZero α]
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
    {α : Type*} [CommMonoidWithZero α]
    [NormalizationMonoid α] [UniqueFactorizationMonoid α]
    {f : α} (gs : List α)
    (hirr : ∀ g ∈ gs, Irreducible g)
    (hprod : Associated gs.prod f) :
    (normalizedFactors f).card ≤ gs.length := by
  rw [normalizedFactors_card_eq_length_of_irreducible_partition gs hirr hprod]

/--
Lower cardinality bound for a coverage-style square-free partition.

When `f` is square-free and every irreducible factor of `f` is associated to
some emitted entry in `gs`, the emitted list has at least as many entries as
`f` has normalized irreducible factors.  Combined with
`length_le_normalizedFactors_card`, this gives the cardinality equality
needed by `irreducible_of_partition_card_eq_normalizedFactors_card`.

Distinct normalized factors of a square-free `f` cannot share an emitted
witness (associated normalized elements are equal), so the witness map is
injective and the image cardinality bounds the list length. -/
theorem normalizedFactors_card_le_length_of_coverage
    {α : Type*} [CommMonoidWithZero α]
    [NormalizationMonoid α] [UniqueFactorizationMonoid α]
    {f : α} (hf : f ≠ 0) (hsf : Squarefree f)
    (gs : List α)
    (hcover : ∀ q ∈ normalizedFactors f, ∃ g ∈ gs, Associated g q) :
    (normalizedFactors f).card ≤ gs.length := by
  classical
  have hnodup : (normalizedFactors f).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf).mp hsf
  let φ : α → α := fun q =>
    if hq : ∃ g ∈ gs, Associated g q then hq.choose else q
  have hφ_mem : ∀ q ∈ normalizedFactors f, φ q ∈ gs := by
    intro q hq
    have hex : ∃ g ∈ gs, Associated g q := hcover q hq
    have hφq : φ q = hex.choose := dif_pos hex
    rw [hφq]
    exact hex.choose_spec.1
  have hφ_assoc : ∀ q ∈ normalizedFactors f, Associated (φ q) q := by
    intro q hq
    have hex : ∃ g ∈ gs, Associated g q := hcover q hq
    have hφq : φ q = hex.choose := dif_pos hex
    rw [hφq]
    exact hex.choose_spec.2
  have hφ_inj : ∀ q₁ ∈ normalizedFactors f, ∀ q₂ ∈ normalizedFactors f,
      φ q₁ = φ q₂ → q₁ = q₂ := by
    intro q₁ hq₁ q₂ hq₂ heq
    have h₁ := hφ_assoc q₁ hq₁
    have h₂ := hφ_assoc q₂ hq₂
    have hassoc : Associated q₁ q₂ := h₁.symm.trans (heq ▸ h₂)
    have hn₁ : normalize q₁ = q₁ :=
      normalize_normalized_factor q₁ hq₁
    have hn₂ : normalize q₂ = q₂ :=
      normalize_normalized_factor q₂ hq₂
    rw [← hn₁, ← hn₂]
    exact normalize_eq_normalize_iff_associated.mpr hassoc
  let image : Multiset α := (normalizedFactors f).map φ
  have himage_card : image.card = (normalizedFactors f).card := by
    simp [image, Multiset.card_map]
  have himage_nodup : image.Nodup :=
    Multiset.Nodup.map_on hφ_inj hnodup
  have himage_subset : ∀ x ∈ image, x ∈ gs.toFinset := by
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨q, hq, rfl⟩
    exact List.mem_toFinset.mpr (hφ_mem q hq)
  have himage_toFinset_card : image.toFinset.card = image.card :=
    Multiset.toFinset_card_of_nodup himage_nodup
  have himage_subset_finset : image.toFinset ⊆ gs.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset] at hx
    exact himage_subset x hx
  calc (normalizedFactors f).card
      = image.card := himage_card.symm
    _ = image.toFinset.card := himage_toFinset_card.symm
    _ ≤ gs.toFinset.card := Finset.card_le_card himage_subset_finset
    _ ≤ gs.length := List.toFinset_card_le gs

/--
The normalized factors of a list product of irreducibles are exactly the
normalizations of the list entries, viewed as a multiset.

Use this when a uniqueness or scalar-splitting proof needs to replace the
abstract UFD factor multiset of a certified product by the concrete flattened
list of factors.
-/
theorem normalizedFactors_list_prod_eq_of_irreducible
    {α : Type*} [CommMonoidWithZero α]
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

/-- A product of monic integer polynomials is monic. -/
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
factorization uniqueness theorem after executable factor entries have been
expanded by multiplicity. The theorem stays public as the clean monic
specialization; current BZ factorization uniqueness uses the normalize-fixed
variant below because executable factors are not necessarily monic.
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
is what the BZ uniqueness theorem actually has (the executable
`normalizeFactorSign` only enforces a nonnegative leading coefficient, not a
unit leading coefficient).

If two nonzero integer scalars multiply products of nonconstant `normalize`-fixed
irreducible integer polynomial factors to the same polynomial, the scalars
agree and the flattened factor lists agree as multisets. Constant factors are
ruled out by the `natDegree ≠ 0` hypothesis, so they cannot leak between the
scalar prefix and the factor list. This is the exported shape used by
`Factorization` uniqueness after translating executable factors to
`Polynomial ℤ`.
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
hypothesis to this lemma. Fast and exhaustive branch lemmas should use this
once they have product preservation, non-unit entries, and the final count
equality.
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
The polynomial degree lemma below is the usual public caller-facing package;
this theorem remains available for callers that need the raw sub-multiset
relation.
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
**UFD subset existence and uniqueness for squarefree-product divisors.**

In a unique factorization monoid, if `factors` is a `Nodup` multiset of
normalize-fixed irreducibles and `d` is a normalize-fixed divisor of
`factors.prod`, then there is a unique sub-multiset `S ≤ factors` whose
product equals `d`. The witness is `normalizedFactors d`; uniqueness uses
`normalizedFactors_prod_eq` to recover any candidate from its product.

This is the abstract Mathlib half of the
`existsUnique_modPFactorSubset_of_choosePrimeData` assembly: the final
caller instantiates `α := Polynomial (ZMod p)` and transports the
resulting sub-multiset through an executable factor-list indexing.
-/
theorem existsUnique_subset_product_eq_of_dvd_of_squarefree_prod
    {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α]
    [UniqueFactorizationMonoid α]
    {factors : Multiset α}
    (hirr : ∀ q ∈ factors, Irreducible q)
    (hnorm : ∀ q ∈ factors, normalize q = q)
    (_hnodup : factors.Nodup)
    {d : α} (hd_norm : normalize d = d) (hd_dvd : d ∣ factors.prod) :
    ∃! S : Multiset α, S ≤ factors ∧ S.prod = d := by
  classical
  rcases factors.empty_or_exists_mem with rfl | ⟨b, hb⟩
  · -- factors = ∅: `d ∣ 1` ⟹ `d` is a unit ⟹ `d = 1` (using `normalize d = d`).
    rw [Multiset.prod_zero] at hd_dvd
    have hd_unit : IsUnit d := isUnit_of_dvd_one hd_dvd
    have hd_one : d = 1 := by
      rw [← hd_norm]; exact normalize_eq_one.mpr hd_unit
    refine ⟨0, ⟨Multiset.zero_le _, ?_⟩, ?_⟩
    · rw [Multiset.prod_zero, hd_one]
    · rintro S ⟨hSle, _⟩
      exact Multiset.le_zero.mp hSle
  · -- factors ≠ ∅: pick `b ∈ factors` to derive `Nontrivial α`.
    haveI : Nontrivial α := nontrivial_of_ne b 0 (hirr b hb).ne_zero
    have hprod_ne : factors.prod ≠ 0 :=
      Multiset.prod_ne_zero fun hmem => (hirr 0 hmem).ne_zero rfl
    have hd_ne : d ≠ 0 := by
      intro hd0
      rw [hd0] at hd_dvd
      exact hprod_ne (zero_dvd_iff.mp hd_dvd)
    have hmap_id : factors.map normalize = factors := by
      refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id _)
      intro q hq
      simpa using hnorm q hq
    refine ⟨normalizedFactors d, ⟨?_, ?_⟩, ?_⟩
    · have hle : normalizedFactors d ≤ factors.map normalize :=
        normalizedFactors_le_map_normalize_of_dvd_prod_irreducibles hd_ne hirr hd_dvd
      rw [hmap_id] at hle
      exact hle
    · rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hd_ne, hd_norm]
    · rintro S ⟨hSle, hSprod⟩
      have hS_subset : ∀ q ∈ S, q ∈ factors :=
        fun q hq => Multiset.mem_of_le hSle hq
      have hSirr : ∀ q ∈ S, Irreducible q :=
        fun q hq => hirr q (hS_subset q hq)
      have hSnorm : ∀ q ∈ S, normalize q = q :=
        fun q hq => hnorm q (hS_subset q hq)
      have hSmap_id : S.map normalize = S := by
        refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id _)
        intro q hq
        simpa using hSnorm q hq
      have hSfactors : normalizedFactors S.prod = S.map normalize :=
        normalizedFactors_prod_eq S hSirr
      rw [hSmap_id, hSprod] at hSfactors
      exact hSfactors.symm

/--
**Polynomial subset-degree lemma.**

Over a field `K`, if `g : K[X]` is non-zero and divides the product of a
multiset of irreducible polynomials `qs`, then `g.natDegree` is the sum of
some sub-multiset of `qs.map natDegree`.

This is the degree-subset-sum packaging of
`normalizedFactors_le_map_normalize_of_dvd_prod_irreducibles` that the BZ
certificate degree-obstruction caller needs: the recorded modular factor
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
