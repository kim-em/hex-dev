/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Relrank

public section

/-!
# Multiquadratic towers and independent square classes

Integers `d₁, …, dₙ` are *independent square classes* when no nonempty
subproduct `∏_{i ∈ T} dᵢ` is a perfect square, equivalently when their images
generate a subgroup of order `2ⁿ` in `ℚ*/(ℚ*)²`. This file proves that
independence forces the multiquadratic field `ℚ(√d₁, …, √dₙ)` to have degree
exactly `2ⁿ` over `ℚ`.

The radicands may be negative, so the tower is built inside `ℂ` rather than `ℝ`:
`adjoinSqrt ds` adjoins every complex square root of every entry of `ds`.

The hypothesis is not implied by weaker-looking conditions. `12, 20, 45` are
pairwise distinct nonsquares with `20 * 45 = 900`, and the corresponding
multiquadratic field has degree `4`, not `8`.

## Main results

* `Hex.SquareClass.Independent`: no nonempty sublist of `ds` has square product.
* `Hex.SquareClass.independent_iff_sublists`: the reformulation an executable
  Bool-valued check decides, over `ℤ` and over the finite list `ds.sublists`.
* `Hex.SquareClass.Independent.of_perm`: independence is symmetric in the
  radicands, so it may be used at an arbitrary index and not only at the end of
  the tower as built.
* `Hex.SquareClass.isSquare_or_isSquare_mul`: the arithmetic core. If `a` is not
  a square in `F` and `b ∈ F` is a square in `F(√a)`, then `b` or `a * b` is a
  square in `F`.
* `Hex.SquareClass.not_isSquareIn_prod`: the strengthened induction hypothesis.
  A subproduct that uses at least one radicand not yet adjoined is not a square
  in the field built so far.
* `Hex.SquareClass.finrank_adjoinSqrt`: `[ℚ(√d₁, …, √dₙ) : ℚ] = 2ⁿ`.

The argument is elementary and self-contained; no Kummer theory is used beyond
Mathlib's irreducibility criterion for `X ^ p - C a`.
-/

namespace Hex.SquareClass

open IntermediateField Module Polynomial

noncomputable section

/-! ## Independence of square classes -/

/--
`ds` are *independent square classes*: no nonempty sublist of `ds` has a
product that is a square in `ℚ`.

Sublists rather than subsets of `Fin ds.length`: a sublist selects a subset of
*positions*, so repeated radicands are handled correctly (`[d, d]` is not
independent, its own product being `d ^ 2`), and the formulation inducts
directly on the list. `independent_iff_sublists` converts to the `ℤ`-valued
perfect-square test that an executable check performs.
-/
def Independent (ds : List ℤ) : Prop :=
  ∀ t : List ℤ, t.Sublist ds → t ≠ [] → ¬ IsSquare ((t.prod : ℤ) : ℚ)

/--
Independence tested over `ℤ`, quantified over the finite list `ds.sublists`.
This is the shape a Bool-valued executable check decides: `2 ^ ds.length`
integer perfect-square tests.
-/
theorem independent_iff_sublists {ds : List ℤ} :
    Independent ds ↔ ∀ t ∈ ds.sublists, t ≠ [] → ¬ IsSquare t.prod := by
  simp only [Independent, List.mem_sublists, Rat.isSquare_intCast_iff]

/-- A sublist of independent square classes is independent. -/
theorem Independent.sublist {ds t : List ℤ} (h : Independent ds) (ht : t.Sublist ds) :
    Independent t := fun s hs hne => h s (hs.trans ht) hne

/-- Independence is symmetric in the radicands. -/
theorem Independent.of_perm {ds ds' : List ℤ} (h : Independent ds) (hp : ds.Perm ds') :
    Independent ds' := by
  intro t ht hne
  obtain ⟨t', hperm, hsub⟩ := ht.subperm.trans hp.symm.subperm
  rw [← hperm.prod_eq]
  refine h t' hsub fun h0 => hne ?_
  rw [h0] at hperm
  exact hperm.symm.eq_nil

/-! ## Squares in an intermediate field of `ℂ / ℚ` -/

/--
`x` is a square in the intermediate field `K` of `ℂ / ℚ`: some element of `K`
squares to `x`. Phrasing this in the ambient field keeps the tower induction
free of subtype coercions.
-/
def IsSquareIn (K : IntermediateField ℚ ℂ) (x : ℂ) : Prop := ∃ z ∈ K, z ^ 2 = x

/-- Every integer lies in every intermediate field of `ℂ / ℚ`. -/
theorem intCast_mem (K : IntermediateField ℚ ℂ) (d : ℤ) : ((d : ℤ) : ℂ) ∈ K := by
  simp

/-- `IsSquareIn` is `IsSquare` read through the subtype. -/
theorem isSquareIn_iff_isSquare {K : IntermediateField ℚ ℂ} {x : ℂ} (hx : x ∈ K) :
    IsSquareIn K x ↔ IsSquare (⟨x, hx⟩ : K) := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact ⟨⟨z, hz⟩, by ext; simpa [sq] using hzx.symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨(y : ℂ), y.2, by
      have := congrArg (Subtype.val (p := fun x => x ∈ K)) hy
      simpa [sq] using this.symm⟩

/-- A nonzero square factor from `K` is invisible to `IsSquareIn K`. -/
theorem isSquareIn_sq_mul_iff {K : IntermediateField ℚ ℂ} {x y : ℂ} (hy : y ∈ K) (hy0 : y ≠ 0) :
    IsSquareIn K (y ^ 2 * x) ↔ IsSquareIn K x := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    refine ⟨z / y, K.div_mem hz hy, ?_⟩
    rw [div_pow, hzx, mul_div_cancel_left₀ x (pow_ne_zero 2 hy0)]
  · rintro ⟨z, hz, hzx⟩
    exact ⟨y * z, K.mul_mem hy hz, by rw [mul_pow, hzx]⟩

/-- Zero is a square, so a non-square is nonzero. -/
theorem ne_zero_of_not_isSquareIn {K : IntermediateField ℚ ℂ} {x : ℂ}
    (h : ¬ IsSquareIn K x) : x ≠ 0 := by
  rintro rfl
  exact h ⟨0, K.zero_mem, by ring⟩

/-- An integer that is a square in `ℚ ⊆ ℂ` is a square in `ℚ`. -/
theorem isSquare_ratCast_of_isSquareIn_bot {d : ℤ}
    (h : IsSquareIn ⊥ ((d : ℤ) : ℂ)) : IsSquare ((d : ℤ) : ℚ) := by
  obtain ⟨z, hz, hzd⟩ := h
  obtain ⟨q, rfl⟩ := (IntermediateField.mem_bot).1 hz
  rw [eq_ratCast (algebraMap ℚ ℂ) q] at hzd
  refine ⟨q, ?_⟩
  have hcast : ((q * q : ℚ) : ℂ) = (((d : ℤ) : ℚ) : ℂ) := by
    push_cast
    rw [← hzd]
    ring
  exact (Rat.cast_injective (α := ℂ) hcast).symm

/-! ## Lemma A: squares in a quadratic extension -/

section LemmaA

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/--
When `r ^ 2` lies in `F`, every element of `F(r)` is `x + y * r` with `x, y ∈ F`:
the `{1, r}` basis, obtained by reducing a polynomial expression modulo
`X ^ 2 - C a`.
-/
theorem exists_repr_of_mem_adjoin {a : F} {r : E} (hr : r ^ 2 = algebraMap F E a) {z : E}
    (hz : z ∈ IntermediateField.adjoin F ({r} : Set E)) :
    ∃ x y : F, z = algebraMap F E x + algebraMap F E y * r := by
  have hmonic : (X ^ 2 - C a : F[X]).Monic := monic_X_pow_sub_C a two_ne_zero
  have hroot : (Polynomial.aeval r) (X ^ 2 - C a : F[X]) = 0 := by simp [hr]
  have halg : IsAlgebraic F r := ⟨X ^ 2 - C a, hmonic.ne_zero, hroot⟩
  have hz' : z ∈ Algebra.adjoin F ({r} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hz
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'
  obtain ⟨p, hp⟩ := hz'
  set s := p %ₘ (X ^ 2 - C a : F[X]) with hs
  refine ⟨s.coeff 0, s.coeff 1, ?_⟩
  have hmod : (Polynomial.aeval r) s = z := by
    rw [← hp]
    conv_rhs => rw [← modByMonic_add_div p (X ^ 2 - C a : F[X])]
    simp [hs, hroot]
  have hdeg : s.natDegree < 2 := by
    have h1 : s.degree < (X ^ 2 - C a : F[X]).degree := degree_modByMonic_lt p hmonic
    rw [degree_X_pow_sub_C (by norm_num) a] at h1
    by_cases h0 : s = 0
    · simp [h0]
    · exact (natDegree_lt_iff_degree_lt h0).2 (by exact_mod_cast h1)
  rw [← hmod, aeval_eq_sum_range' hdeg]
  simp [Finset.sum_range_succ, Algebra.smul_def]

/--
**Lemma A.** Let `F` have characteristic `≠ 2`, let `a ∈ F` not be a square in
`F`, and let `r ^ 2 = a` in an extension `E`. If `b ∈ F` is a square in `F(r)`,
then `b` or `a * b` is a square in `F`.

Writing the witness as `x + y * r`, the `{1, r}` basis forces `2 * x * y = 0`,
hence `x = 0` or `y = 0`: the two cases give `b = y ^ 2 * a` and `b = x ^ 2`.
-/
theorem isSquare_or_isSquare_mul (h2 : (2 : F) ≠ 0) {a : F} (ha : ¬ IsSquare a) {r : E}
    (hr : r ^ 2 = algebraMap F E a) {b : F} {z : E}
    (hz : z ∈ IntermediateField.adjoin F ({r} : Set E)) (hzb : z ^ 2 = algebraMap F E b) :
    IsSquare b ∨ IsSquare (a * b) := by
  obtain ⟨x, y, rfl⟩ := exists_repr_of_mem_adjoin hr hz
  have hrange : r ∉ Set.range (algebraMap F E) := by
    rintro ⟨c, hc⟩
    refine ha ⟨c, (algebraMap F E).injective ?_⟩
    rw [map_mul, hc, ← sq, hr]
  have hexp : (algebraMap F E x + algebraMap F E y * r) ^ 2 =
      algebraMap F E (x ^ 2 + a * y ^ 2) + algebraMap F E (2 * x * y) * r := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    rw [← hr]
    ring
  have hkey : algebraMap F E (2 * x * y) * r = algebraMap F E (b - (x ^ 2 + a * y ^ 2)) := by
    rw [map_sub, ← hzb, hexp]
    ring
  have h2xy : 2 * x * y = 0 := by
    by_contra hne
    refine hrange ⟨(b - (x ^ 2 + a * y ^ 2)) / (2 * x * y), ?_⟩
    have hne' : algebraMap F E (2 * x * y) ≠ 0 := by
      simpa using (map_ne_zero_iff _ (algebraMap F E).injective).2 hne
    rw [map_div₀, ← hkey, mul_comm, mul_div_assoc, div_self hne', mul_one]
  rcases mul_eq_zero.1 h2xy with h | hy0
  · rcases mul_eq_zero.1 h with h2' | hx0
    · exact absurd h2' h2
    · right
      have hb : b = a * y ^ 2 := by
        refine (algebraMap F E).injective ?_
        rw [← hzb, hexp, hx0]
        simp
      exact ⟨a * y, by rw [hb]; ring⟩
  · left
    have hb : b = x ^ 2 := by
      refine (algebraMap F E).injective ?_
      rw [← hzb, hexp, hy0]
      simp
    exact ⟨x, by rw [hb]; ring⟩

/-- The minimal polynomial of a square root of a non-square. -/
theorem minpoly_eq_X_pow_two_sub_C {a : F} (ha : ¬ IsSquare a) {r : E}
    (hr : r ^ 2 = algebraMap F E a) : minpoly F r = X ^ 2 - C a := by
  have hirr : Irreducible (X ^ 2 - C a : F[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => ha ⟨b, by rw [← hb, sq]⟩
  have hroot : (Polynomial.aeval r) (X ^ 2 - C a : F[X]) = 0 := by simp [hr]
  exact (minpoly.eq_of_irreducible_of_monic hirr hroot (monic_X_pow_sub_C a two_ne_zero)).symm

end LemmaA

/-! ## The multiquadratic tower -/

/-- The complex square roots of the entries of `ds`. -/
def sqrtSet (ds : List ℤ) : Set ℂ := {x : ℂ | ∃ d ∈ ds, x ^ 2 = (d : ℂ)}

/--
`ℚ(√d₁, …, √dₙ)` realised inside `ℂ`: the intermediate field generated by every
complex square root of every entry of `ds`. Radicands may be negative, so `ℝ` is
not enough.
-/
def adjoinSqrt (ds : List ℤ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (sqrtSet ds)

/-- Every integer has a complex square root. -/
theorem exists_sqrt (d : ℤ) : ∃ r : ℂ, r ^ 2 = (d : ℂ) :=
  IsAlgClosed.exists_pow_nat_eq ((d : ℤ) : ℂ) (by norm_num)

@[simp]
theorem sqrtSet_nil : sqrtSet [] = ∅ := by simp [sqrtSet]

theorem sqrtSet_cons (d : ℤ) (ds : List ℤ) :
    sqrtSet (d :: ds) = {x : ℂ | x ^ 2 = (d : ℂ)} ∪ sqrtSet ds := by
  ext x
  simp only [sqrtSet, Set.mem_setOf_eq, Set.mem_union, List.mem_cons]
  constructor
  · rintro ⟨e, he | he, hx⟩
    · exact Or.inl (by rw [hx, he])
    · exact Or.inr ⟨e, he, hx⟩
  · rintro (hx | ⟨e, he, hx⟩)
    · exact ⟨d, Or.inl rfl, hx⟩
    · exact ⟨e, Or.inr he, hx⟩

/-- Adjoining all square roots of `c` is adjoining one of them. -/
theorem adjoin_sqrtSet_singleton {c r : ℂ} (hr : r ^ 2 = c) :
    IntermediateField.adjoin ℚ {x : ℂ | x ^ 2 = c} = IntermediateField.adjoin ℚ {r} := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 fun x hx => ?_) ?_
  · have hfac : (x - r) * (x + r) = 0 := by
      have : x ^ 2 = r ^ 2 := by rw [hr]; exact hx
      linear_combination this
    have hmem : r ∈ IntermediateField.adjoin ℚ ({r} : Set ℂ) :=
      IntermediateField.subset_adjoin ℚ _ rfl
    rcases mul_eq_zero.1 hfac with h | h
    · have : x = r := by linear_combination h
      exact this ▸ hmem
    · have : x = -r := by linear_combination h
      exact this ▸ (IntermediateField.adjoin ℚ ({r} : Set ℂ)).neg_mem hmem
  · exact IntermediateField.adjoin_le_iff.2 fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      exact IntermediateField.subset_adjoin ℚ _ (by rw [hx]; exact hr)

@[simp]
theorem adjoinSqrt_nil : adjoinSqrt [] = ⊥ := by
  simp [adjoinSqrt, IntermediateField.adjoin_empty]

/-- Consing a radicand adjoins one square root to the field built so far. -/
theorem adjoinSqrt_cons_sup {d : ℤ} {r : ℂ} (hr : r ^ 2 = (d : ℂ)) (ds : List ℤ) :
    adjoinSqrt (d :: ds) = adjoinSqrt ds ⊔ IntermediateField.adjoin ℚ ({r} : Set ℂ) := by
  rw [adjoinSqrt, adjoinSqrt, sqrtSet_cons, IntermediateField.adjoin_union,
    adjoin_sqrtSet_singleton hr, sup_comm]

/-- `adjoinSqrt` depends only on which radicands appear, not on their order. -/
theorem adjoinSqrt_of_perm {ds ds' : List ℤ} (hp : ds.Perm ds') :
    adjoinSqrt ds = adjoinSqrt ds' := by
  have : sqrtSet ds = sqrtSet ds' := by
    ext x
    simp only [sqrtSet, Set.mem_setOf_eq]
    exact ⟨fun ⟨d, hd, hx⟩ => ⟨d, hp.mem_iff.1 hd, hx⟩,
      fun ⟨d, hd, hx⟩ => ⟨d, hp.mem_iff.2 hd, hx⟩⟩
  rw [adjoinSqrt, adjoinSqrt, this]

/-- The tower grows monotonically as radicands are consed on. -/
theorem adjoinSqrt_le_cons (d : ℤ) (ds : List ℤ) : adjoinSqrt ds ≤ adjoinSqrt (d :: ds) := by
  refine IntermediateField.adjoin.mono ℚ _ _ ?_
  rw [sqrtSet_cons]
  exact Set.subset_union_right

/--
Lemma A transported to intermediate fields of `ℂ / ℚ`, stated in the ambient
field.
-/
theorem isSquareIn_or_isSquareIn_mul {F : IntermediateField ℚ ℂ} {a b : ℂ} (haF : a ∈ F)
    (hbF : b ∈ F) (ha : ¬ IsSquareIn F a) {r : ℂ} (hr : r ^ 2 = a)
    (hb : IsSquareIn (F ⊔ IntermediateField.adjoin ℚ ({r} : Set ℂ)) b) :
    IsSquareIn F b ∨ IsSquareIn F (a * b) := by
  obtain ⟨z, hz, hzb⟩ := hb
  have hsup := IntermediateField.restrictScalars_adjoin_eq_sup ℚ F ({r} : Set ℂ)
  have hzmem : z ∈ IntermediateField.adjoin F ({r} : Set ℂ) := (SetLike.ext_iff.1 hsup z).2 hz
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have : ((2 : F) : ℂ) = ((0 : F) : ℂ) := congrArg _ h
    norm_num at this
  have hres := isSquare_or_isSquare_mul (F := F) (E := ℂ) h2
    (a := ⟨a, haF⟩) ((isSquareIn_iff_isSquare haF).not.1 ha) (r := r) hr
    (b := ⟨b, hbF⟩) (z := z) hzmem hzb
  have hab : a * b ∈ F := F.mul_mem haF hbF
  rcases hres with h | h
  · exact Or.inl ((isSquareIn_iff_isSquare hbF).2 h)
  · exact Or.inr ((isSquareIn_iff_isSquare hab).2 h)

/--
**The strengthened claim.** Split the radicands as `built ++ rest`, where
`adjoinSqrt built` is the field constructed so far. Then no subproduct that uses
at least one radicand from `rest` is a square in `adjoinSqrt built`.

The strengthening is what makes the induction go through: Lemma A turns a
putative square at the top of the tower into a subproduct one level down that
still meets `rest`.
-/
theorem not_isSquareIn_prod : ∀ built rest : List ℤ, Independent (built ++ rest) →
    ∀ t u : List ℤ, t.Sublist built → u.Sublist rest → u ≠ [] →
      ¬ IsSquareIn (adjoinSqrt built) (((t ++ u).prod : ℤ) : ℂ) := by
  intro built
  induction built with
  | nil =>
    intro rest h t u ht hu hune hsq
    rw [List.sublist_nil.1 ht, List.nil_append] at hsq
    rw [adjoinSqrt_nil] at hsq
    exact h u (by simpa using hu) hune (isSquare_ratCast_of_isSquareIn_bot hsq)
  | cons d built ih =>
    intro rest h t u ht hu hune hsq
    obtain ⟨r, hr⟩ := exists_sqrt d
    have hperm : Independent (built ++ d :: rest) :=
      h.of_perm (List.perm_middle (a := d) (l₁ := built) (l₂ := rest)).symm
    have hdu : (d :: u).Sublist (d :: rest) := hu.cons_cons d
    have hune' : d :: u ≠ [] := by simp
    -- `d` itself is not a square one level down.
    have hd : ¬ IsSquareIn (adjoinSqrt built) ((d : ℤ) : ℂ) := by
      have := ih (d :: rest) hperm [] [d] (List.nil_sublist _)
        ((List.nil_sublist rest).cons_cons d) (by simp)
      simpa using this
    have hd0 : ((d : ℤ) : ℂ) ≠ 0 := ne_zero_of_not_isSquareIn hd
    -- Lemma A at the top of the tower.
    have hmem : (((t ++ u).prod : ℤ) : ℂ) ∈ adjoinSqrt built :=
      intCast_mem _ _
    rw [adjoinSqrt_cons_sup hr built] at hsq
    have hA := isSquareIn_or_isSquareIn_mul (intCast_mem (adjoinSqrt built) d) hmem hd hr hsq
    -- Split on whether `d` was selected.
    rcases List.sublist_cons_iff.1 ht with ht' | ⟨t', rfl, ht'⟩
    · rcases hA with hcase | hcase
      · exact ih (d :: rest) hperm t u ht' (hu.cons d) hune hcase
      · refine ih (d :: rest) hperm t (d :: u) ht' hdu hune' ?_
        have hshift : (((t ++ d :: u).prod : ℤ) : ℂ)
            = ((d : ℤ) : ℂ) * (((t ++ u).prod : ℤ) : ℂ) := by
          push_cast [List.prod_append, List.prod_cons]
          ring
        rw [hshift]
        exact hcase
    · have hb : (((d :: t' ++ u).prod : ℤ) : ℂ)
          = ((d : ℤ) : ℂ) * (((t' ++ u).prod : ℤ) : ℂ) := by
        push_cast [List.prod_append, List.prod_cons]
        ring
      rw [hb] at hA
      rcases hA with hcase | hcase
      · refine ih (d :: rest) hperm t' (d :: u) ht' hdu hune' ?_
        have hshift : (((t' ++ d :: u).prod : ℤ) : ℂ)
            = ((d : ℤ) : ℂ) * (((t' ++ u).prod : ℤ) : ℂ) := by
          push_cast [List.prod_append, List.prod_cons]
          ring
        rw [hshift]
        exact hcase
      · refine ih (d :: rest) hperm t' u ht' (hu.cons d) hune ?_
        rw [← isSquareIn_sq_mul_iff (intCast_mem (adjoinSqrt built) d) hd0]
        have hshift : ((d : ℤ) : ℂ) ^ 2 * (((t' ++ u).prod : ℤ) : ℂ)
            = ((d : ℤ) : ℂ) * (((d : ℤ) : ℂ) * (((t' ++ u).prod : ℤ) : ℂ)) := by ring
        rw [hshift]
        exact hcase

/--
A radicand is not a square in the field generated by the others.

Independence is symmetric in the radicands, so this holds at an arbitrary index
and not only at the top of the tower as built: pick any permutation putting the
radicand of interest first.
-/
theorem not_isSquareIn_of_perm_cons {ds rest : List ℤ} {d : ℤ} (h : Independent ds)
    (hp : ds.Perm (d :: rest)) : ¬ IsSquareIn (adjoinSqrt rest) ((d : ℤ) : ℂ) := by
  have hperm : Independent (rest ++ [d]) :=
    (h.of_perm hp).of_perm (List.perm_append_singleton d rest).symm
  have hkey := not_isSquareIn_prod rest [d] hperm [] [d] (List.nil_sublist _)
    (List.Sublist.refl _) (by simp)
  simpa using hkey

/--
The relative degree of one step of the tower is `2` once the new radicand is not
a square in the field built so far.
-/
theorem relfinrank_adjoinSqrt_cons {d : ℤ} {ds : List ℤ} {r : ℂ} (hr : r ^ 2 = (d : ℂ))
    (hd : ¬ IsSquareIn (adjoinSqrt ds) ((d : ℤ) : ℂ)) :
    IntermediateField.relfinrank (adjoinSqrt ds) (adjoinSqrt (d :: ds)) = 2 := by
  have hle := adjoinSqrt_le_cons d ds
  have hext : IntermediateField.extendScalars hle
      = IntermediateField.adjoin (adjoinSqrt ds) ({r} : Set ℂ) := by
    refine IntermediateField.restrictScalars_injective ℚ ?_
    refine Eq.trans (IntermediateField.extendScalars_restrictScalars hle) ?_
    refine Eq.trans (adjoinSqrt_cons_sup hr ds) ?_
    exact (IntermediateField.restrictScalars_adjoin_eq_sup ℚ (adjoinSqrt ds) ({r} : Set ℂ)).symm
  have haF : ((d : ℤ) : ℂ) ∈ adjoinSqrt ds := intCast_mem _ _
  have hrF : r ^ 2 = algebraMap (adjoinSqrt ds) ℂ ⟨((d : ℤ) : ℂ), haF⟩ := hr
  have hnsq : ¬ IsSquare (⟨((d : ℤ) : ℂ), haF⟩ : adjoinSqrt ds) :=
    (isSquareIn_iff_isSquare haF).not.1 hd
  have hint : IsIntegral (adjoinSqrt ds) r := by
    refine ⟨X ^ 2 - C ⟨((d : ℤ) : ℂ), haF⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [hrF]
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext,
    IntermediateField.adjoin.finrank hint, minpoly_eq_X_pow_two_sub_C hnsq hrF,
    natDegree_X_pow_sub_C]

/--
**The tower theorem, part (1).** Independent square classes generate a
multiquadratic field of degree exactly `2 ^ n`.
-/
theorem finrank_adjoinSqrt {ds : List ℤ} (h : Independent ds) :
    finrank ℚ (adjoinSqrt ds) = 2 ^ ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    obtain ⟨r, hr⟩ := exists_sqrt d
    have hsub : Independent ds := h.sublist ((List.sublist_cons_self d ds))
    have hd : ¬ IsSquareIn (adjoinSqrt ds) ((d : ℤ) : ℂ) :=
      not_isSquareIn_of_perm_cons h (List.Perm.refl _)
    have htower := IntermediateField.finrank_bot_mul_relfinrank (adjoinSqrt_le_cons d ds)
    rw [← htower, ih hsub, relfinrank_adjoinSqrt_cons hr hd, List.length_cons, pow_succ]

/--
Independence is a condition on the whole subgroup the radicands generate, not a
pairwise one: `12, 20, 45` are pairwise distinct nonsquares, yet
`20 * 45 = 900 = 30 ^ 2`.
-/
example : ¬ Independent [12, 20, 45] := fun h =>
  h [20, 45] (by decide) (by decide) ⟨30, by norm_num⟩

end

end Hex.SquareClass
