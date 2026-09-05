/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.SquareClass
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma

@[expose] public section

/-!
# The primitive element and minimal polynomial of a multiquadratic sum

`HexBerlekampZassenhausMathlib.SquareClass` proves that independent square
classes `d₁, …, dₙ` generate a multiquadratic field `K = ℚ(√d₁, …, √dₙ)` of
degree exactly `2ⁿ`. That says the field is big, not that any particular element
generates it. This file proves the rest of the tower theorem of
`reports/hexbz-quadratic-norm-certificate.md`: for any translation `c ∈ ℤ` and
any choice of complex square roots `rᵢ`, the sum

    α = c + ∑ᵢ rᵢ

generates `K`, and the product of `X - β` over the `2ⁿ` sign patterns
`β = c + ∑ᵢ ± rᵢ` is `α`'s minimal polynomial, hence irreducible.

## Main results

* `Hex.SquareClass.isGalois_adjoinSqrt`: `K / ℚ` is Galois. Normality is a
  compositum of the quadratic splitting fields of the `X² - dᵢ`, and
  separability is characteristic zero.
* `Hex.SquareClass.signOf_bijective` and `Hex.SquareClass.signOf_mul`:
  `Gal(K/ℚ) ≅ (ℤ/2)ⁿ`, concretely that reading `σ` off as the sign pattern by
  which it acts on the chosen roots is a bijection onto `Fin n → Bool`, and that
  it carries composition to pointwise `==`.
* `Hex.SquareClass.eq_one_of_gen_fixed`: the stabilizer of `α` is trivial.
* `Hex.SquareClass.adjoin_signSum_eq`: `ℚ(α) = K`.
* `Hex.SquareClass.minpoly_map_eq_signPoly`: the minimal polynomial of `α` is
  the sign-pattern product.
* `Hex.SquareClass.irreducible_of_map_eq_signPoly` and
  `Hex.SquareClass.irreducible_int_of_map_eq_signPoly`: a rational, or monic
  integer, polynomial that *is* the sign-pattern product is irreducible. This is
  the form a certificate checker consumes.

`HexBerlekampZassenhausMathlib.QuadraticNorm` carries the other half, that the
executable iterated norm *is* the sign-pattern product, but writes the product
as `signPatternPoly`, a `List.prod` over a fold-built list of signed sums,
rather than as this file's `signPoly`, a `Finset.prod` over `Fin n → Bool`. The
`Fin n → Bool` indexing is what lets an automorphism act on the product by a
reindexing equivalence, which is the whole argument here. Composing the two
halves therefore needs a lemma identifying the two encodings; that lemma is not
here, and belongs with the production integration.

The trivial-stabilizer argument runs through one arithmetic fact,
`Hex.SquareClass.eq_zero_of_sum_eq_zero`: no nontrivial integer linear relation
holds among the `rᵢ`. That is where independence is used *at an arbitrary
index*, through `Hex.SquareClass.sqrt_notMem_adjoinSqrt` applied to the
radicands with the index of interest moved to the front. Distinctness of the
`2ⁿ` sign sums is the same fact once more, not a separate argument.

The `2ⁿ` conjugates are never constructed: an automorphism is only ever *read*,
never built, so no surjectivity of the sign map is needed for the minimal
polynomial. The sign-pattern product is fixed by every automorphism because each
one permutes the sign patterns, so its coefficients are rational; it is monic of
degree `2ⁿ` and vanishes at `α`, which pins it to the minimal polynomial.
-/

namespace Hex.SquareClass

open IntermediateField Module Polynomial

noncomputable section

/-! ## The tower is Galois -/

/-- A complex square root of an integer is integral over `ℚ`. -/
theorem isIntegral_of_sq {d : ℤ} {r : ℂ} (hr : r ^ 2 = (d : ℂ)) : IsIntegral ℚ r := by
  refine ⟨X ^ 2 - C ((d : ℤ) : ℚ), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  rw [← Polynomial.aeval_def]
  simp [hr]

/-- The complex roots of `X ^ 2 - d` are the complex square roots of `d`. -/
theorem rootSet_X_pow_two_sub_C (d : ℤ) :
    (X ^ 2 - C ((d : ℤ) : ℚ)).rootSet ℂ = {x : ℂ | x ^ 2 = (d : ℂ)} := by
  have hne : (X ^ 2 - C ((d : ℤ) : ℚ) : ℚ[X]) ≠ 0 := (monic_X_pow_sub_C _ two_ne_zero).ne_zero
  ext x
  rw [Polynomial.mem_rootSet, Set.mem_ofPred_eq]
  simp only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]
  constructor
  · rintro ⟨-, h⟩
    simpa using h
  · intro h
    exact ⟨hne, by simpa using h⟩

/-- A quadratic subfield of the tower is normal: it splits `X ^ 2 - d`. -/
theorem normal_adjoin_sqrt {d : ℤ} {r : ℂ} (hr : r ^ 2 = (d : ℂ)) :
    Normal ℚ (IntermediateField.adjoin ℚ ({r} : Set ℂ)) := by
  have hsplits : (((X : ℚ[X]) ^ 2 - C ((d : ℤ) : ℚ)).map (algebraMap ℚ ℂ)).Splits :=
    IsAlgClosed.splits _
  have hsf := IntermediateField.adjoin_rootSet_isSplittingField (K := ℚ) (L := ℂ) hsplits
  rw [rootSet_X_pow_two_sub_C, adjoin_sqrtSet_singleton hr] at hsf
  exact Normal.of_isSplittingField (hFEp := hsf) _

instance finiteDimensional_adjoinSqrt (ds : List ℤ) :
    FiniteDimensional ℚ (adjoinSqrt ds) := by
  induction ds with
  | nil => rw [adjoinSqrt_nil]; infer_instance
  | cons d ds ih =>
    obtain ⟨r, hr⟩ := exists_sqrt d
    rw [adjoinSqrt_cons_sup hr ds]
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({r} : Set ℂ)) :=
      IntermediateField.adjoin.finiteDimensional (isIntegral_of_sq hr)
    infer_instance

instance normal_adjoinSqrt (ds : List ℤ) : Normal ℚ (adjoinSqrt ds) := by
  induction ds with
  | nil =>
    rw [adjoinSqrt_nil]
    exact Normal.of_algEquiv (IntermediateField.botEquiv ℚ ℂ).symm
  | cons d ds ih =>
    obtain ⟨r, hr⟩ := exists_sqrt d
    rw [adjoinSqrt_cons_sup hr ds]
    exact @IntermediateField.normal_sup ℚ ℂ _ _ _ (adjoinSqrt ds)
      (IntermediateField.adjoin ℚ ({r} : Set ℂ)) ih (normal_adjoin_sqrt hr)

instance isGalois_adjoinSqrt (ds : List ℤ) : IsGalois ℚ (adjoinSqrt ds) :=
  isGalois_iff.2 ⟨inferInstance, inferInstance⟩

/-! ## Sign patterns -/

/--
The sign-pattern sum `c + ∑ᵢ ± rᵢ`, where `ε i` selects the sign of the `i`-th
root. Stated over an arbitrary ring so that the tower and the ambient `ℂ` share
one definition.
-/
def signSum {R : Type*} [Ring R] {n : ℕ} (c : ℤ) (r : Fin n → R) (ε : Fin n → Bool) : R :=
  (c : R) + ∑ i, if ε i then r i else -r i

/-- The all-plus pattern gives the untwisted sum `c + ∑ᵢ rᵢ`. -/
theorem signSum_const_true {R : Type*} [Ring R] {n : ℕ} (c : ℤ) (r : Fin n → R) :
    signSum c r (fun _ => true) = (c : R) + ∑ i, r i := by
  simp [signSum]

/-- A ring map carries a sign-pattern sum to the sign-pattern sum of the images. -/
theorem map_signSum {R S : Type*} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) (c : ℤ)
    (r : Fin n → R) (ε : Fin n → Bool) :
    f (signSum c r ε) = signSum c (fun i => f (r i)) ε := by
  simp only [signSum, map_add, map_intCast, map_sum, apply_ite f, map_neg]

/-- The sign-pattern product `∏_ε (X - (c + ∑ᵢ ± rᵢ))`, the candidate minimal polynomial. -/
def signPoly {R : Type*} [CommRing R] {n : ℕ} (c : ℤ) (r : Fin n → R) : R[X] :=
  ∏ ε : Fin n → Bool, (X - C (signSum c r ε))

/-- The sign-pattern product is monic, being a product of monic linear factors. -/
theorem signPoly_monic {R : Type*} [CommRing R] {n : ℕ} (c : ℤ) (r : Fin n → R) :
    (signPoly c r).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- The sign-pattern product has degree `2 ^ n`, one factor per sign pattern. -/
theorem natDegree_signPoly {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} (c : ℤ)
    (r : Fin n → R) : (signPoly c r).natDegree = 2 ^ n := by
  rw [signPoly, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

/-- A ring map carries the sign-pattern product to the sign-pattern product of the images. -/
theorem map_signPoly {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (c : ℤ)
    (r : Fin n → R) : (signPoly c r).map f = signPoly c (fun i => f (r i)) := by
  rw [signPoly, signPoly, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun ε _ => by
    rw [Polynomial.map_sub, map_X, Polynomial.map_C, map_signSum]

/-- The all-plus pattern is a root of the sign-pattern product. -/
theorem signPoly_eval {R : Type*} [CommRing R] {n : ℕ} (c : ℤ) (r : Fin n → R) :
    (signPoly c r).eval (signSum c r (fun _ => true)) = 0 := by
  rw [signPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ (fun _ => true)) (by simp)

/-! ## Roots at an arbitrary index -/

/-- Every entry except the `j`-th survives erasing position `j`. -/
theorem getElem_mem_eraseIdx {α : Type*} {l : List α} {i j : Fin l.length} (hij : i ≠ j) :
    l[i] ∈ l.eraseIdx j :=
  List.mem_eraseIdx_iff_getElem.2 ⟨i, i.2, fun hc => hij (Fin.ext hc), rfl⟩

/-- Erasing position `j` and putting the `j`-th entry back in front recovers the list. -/
theorem perm_eraseIdx {α : Type*} [DecidableEq α] (l : List α) (j : Fin l.length) :
    l.Perm (l[j] :: l.eraseIdx j) :=
  (List.perm_cons_erase (List.getElem_mem j.2)).trans ((List.erase_getElem j.2).cons _)

/-- No integer linear relation holds among square roots of independent radicands. -/
theorem eq_zero_of_sum_eq_zero {ds : List ℤ} {r : Fin ds.length → ℂ} (h : Independent ds)
    (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) {a : Fin ds.length → ℤ}
    (ha : ∑ i, (a i : ℂ) * r i = 0) (j : Fin ds.length) : a j = 0 := by
  by_contra hj
  have haj : ((a j : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 hj
  set E := adjoinSqrt (ds.eraseIdx j) with hE
  have hmem : ∀ i ∈ Finset.univ.erase j, r i ∈ E := fun i hi =>
    sqrt_mem_adjoinSqrt (getElem_mem_eraseIdx (Finset.ne_of_mem_erase hi)) (hr i)
  have hsplit : ((a j : ℤ) : ℂ) * r j + ∑ i ∈ Finset.univ.erase j, ((a i : ℤ) : ℂ) * r i = 0 := by
    rw [Finset.add_sum_erase Finset.univ (fun i => ((a i : ℤ) : ℂ) * r i) (Finset.mem_univ j)]
    exact ha
  have key : r j = ((a j : ℤ) : ℂ)⁻¹ * (-(∑ i ∈ Finset.univ.erase j, ((a i : ℤ) : ℂ) * r i)) := by
    rw [eq_inv_mul_iff_mul_eq₀ haj]
    linear_combination hsplit
  refine sqrt_notMem_adjoinSqrt h (perm_eraseIdx ds j) (hr j) ?_
  rw [key]
  exact E.mul_mem (E.inv_mem (intCast_mem E (a j)))
    (E.neg_mem (sum_mem fun i hi => E.mul_mem (intCast_mem E (a i)) (hmem i hi)))

/-! ## The tower is generated by any one of its sign sums -/

/-- An intermediate field containing every square root of every radicand contains the tower. -/
theorem adjoinSqrt_le {M : IntermediateField ℚ ℂ} : ∀ ds : List ℤ,
    (∀ (x : ℂ) (d : ℤ), d ∈ ds → x ^ 2 = (d : ℂ) → x ∈ M) → adjoinSqrt ds ≤ M := by
  intro ds
  induction ds with
  | nil => intro _; rw [adjoinSqrt_nil]; exact bot_le
  | cons d ds ih =>
    intro hM
    obtain ⟨r, hr⟩ := exists_sqrt d
    rw [adjoinSqrt_cons_sup hr ds]
    refine sup_le (ih fun x e he hx => hM x e (List.mem_cons_of_mem d he) hx) ?_
    rw [IntermediateField.adjoin_simple_le_iff]
    exact hM r d (List.mem_cons_self ..) hr

/--
An intermediate field of the tower whose image in `ℂ` contains every square root
of every radicand is the whole tower.
-/
theorem eq_top_of_sqrt_mem {ds : List ℤ} (N : IntermediateField ℚ (adjoinSqrt ds))
    (hN : ∀ (x : ℂ) (d : ℤ), d ∈ ds → x ^ 2 = (d : ℂ) → x ∈ N.map (adjoinSqrt ds).val) :
    N = ⊤ := by
  have hle : adjoinSqrt ds ≤ N.map (adjoinSqrt ds).val := adjoinSqrt_le ds hN
  refine top_unique fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).1 (hle x.2)
  exact (Subtype.ext hyx : y = x) ▸ hy

/-- An automorphism sends a square root of an integer to plus or minus itself. -/
theorem eq_or_neg_of_sq {K : Type*} [Field K] [Algebra ℚ K] (σ : K ≃ₐ[ℚ] K) {x : K} {d : ℤ}
    (hx : x ^ 2 = (d : K)) : σ x = x ∨ σ x = -x := by
  have h : σ x ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
  rcases mul_eq_zero.1 (show (σ x - x) * (σ x + x) = 0 by linear_combination h) with h' | h'
  · exact Or.inl (by linear_combination h')
  · exact Or.inr (by linear_combination h')

section Roots

variable {ds : List ℤ} {r : Fin ds.length → ℂ}

/-- The chosen square roots, as elements of the tower. -/
def root (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (i : Fin ds.length) : adjoinSqrt ds :=
  ⟨r i, sqrt_mem_adjoinSqrt (List.getElem_mem i.2) (hr i)⟩

/-- The chosen root's underlying complex value. -/
@[simp]
theorem root_val (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (i : Fin ds.length) :
    ((root hr i : adjoinSqrt ds) : ℂ) = r i := rfl

/-- The chosen root squares to its radicand inside the tower. -/
theorem root_sq (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (i : Fin ds.length) :
    root hr i ^ 2 = ((ds[i] : ℤ) : adjoinSqrt ds) := by
  apply Subtype.ext
  push_cast
  exact hr i

open Classical in
/-- The sign pattern by which `σ` acts on the chosen roots. -/
noncomputable def signOf (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ))
    (σ : adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds) (i : Fin ds.length) : Bool :=
  decide (σ (root hr i) = root hr i)

/-- A radicand of independent square classes is nonzero: `0` is a square. -/
theorem getElem_ne_zero (h : Independent ds) (i : Fin ds.length) : ds[i] ≠ 0 := by
  intro h0
  refine independent_iff_sublists.1 h [ds[i]]
    (List.mem_sublists.2 (List.singleton_sublist.2 (List.getElem_mem i.2))) (by simp) ?_
  rw [List.prod_singleton, h0]
  exact ⟨0, by simp⟩

/-- A chosen root of an independent radicand is not its own negative. -/
theorem root_ne_neg_self (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ))
    (i : Fin ds.length) : root hr i ≠ -root hr i := by
  intro heq
  have hc : r i = -r i := by simpa using congrArg (fun x : adjoinSqrt ds => (x : ℂ)) heq
  have h0 : r i = 0 := by linear_combination hc / 2
  refine getElem_ne_zero h i ?_
  have hd : ((ds[i] : ℤ) : ℂ) = 0 := by rw [← hr i, h0]; ring
  exact_mod_cast hd

/-- Every automorphism of the tower acts on the chosen roots by its sign pattern. -/
theorem apply_root (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ))
    (σ : adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds) (i : Fin ds.length) :
    σ (root hr i) = if signOf hr σ i then root hr i else -root hr i := by
  by_cases hi : σ (root hr i) = root hr i
  · simp [signOf, hi]
  · rcases eq_or_neg_of_sq σ (root_sq hr i) with h | h
    · exact absurd h hi
    · simp [signOf, h]

/-- Reading a sign off an action recovers the sign pattern, the roots being nonzero. -/
theorem signOf_eq_of_apply (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ))
    {σ : adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds} {i : Fin ds.length} {b : Bool}
    (hb : σ (root hr i) = if b then root hr i else -root hr i) : signOf hr σ i = b := by
  have hne := root_ne_neg_self h hr i
  have heq := apply_root hr σ i
  rw [hb] at heq
  cases b <;> cases hs : signOf hr σ i <;> simp_all

/-- `α = c + ∑ᵢ √dᵢ`, as an element of the tower. -/
def gen (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) : adjoinSqrt ds :=
  signSum c (root hr) (fun _ => true)

/-- The generator's underlying complex value is the all-plus sign sum. -/
@[simp]
theorem gen_val (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) :
    ((gen hr c : adjoinSqrt ds) : ℂ) = signSum c r (fun _ => true) :=
  map_signSum ((adjoinSqrt ds).val : adjoinSqrt ds →ₐ[ℚ] ℂ).toRingHom c (root hr) _

/-- Only the identity fixes every chosen root. -/
theorem eq_one_of_root_fixed (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ))
    {σ : adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds} (hσ : ∀ i, σ (root hr i) = root hr i) : σ = 1 := by
  have hfix : ∀ y : adjoinSqrt ds, σ y = y →
      y ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hle : Subgroup.zpowers σ ≤
        MulAction.stabilizer (adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds) y :=
      Subgroup.zpowers_le.2 (by simpa [MulAction.mem_stabilizer_iff] using hy)
    simpa [MulAction.mem_stabilizer_iff] using hle hf
  have htop : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊤ := by
    refine eq_top_of_sqrt_mem _ ?_
    intro x d hd hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hd
    have hri : r ⟨i, hi⟩ ^ 2 = (ds[i] : ℂ) := hr ⟨i, hi⟩
    have hxr : x = r ⟨i, hi⟩ ∨ x = -r ⟨i, hi⟩ := by
      rcases mul_eq_zero.1
        (show (x - r ⟨i, hi⟩) * (x + r ⟨i, hi⟩) = 0 by linear_combination hx - hri) with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    rcases hxr with rfl | rfl
    · exact (IntermediateField.mem_map _).2 ⟨root hr ⟨i, hi⟩, hfix _ (hσ _), rfl⟩
    · exact (IntermediateField.mem_map _).2
        ⟨-root hr ⟨i, hi⟩, hfix _ (by rw [map_neg, hσ]), by simp⟩
  refine AlgEquiv.ext fun y => ?_
  have hy : y ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := htop ▸ trivial
  rw [IntermediateField.mem_fixedField_iff] at hy
  simpa using hy σ (Subgroup.mem_zpowers σ)

/-- **Trivial stabilizer.** Only the identity fixes the primitive element. -/
theorem eq_one_of_gen_fixed (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ)
    {σ : adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds} (hσ : σ (gen hr c) = gen hr c) : σ = 1 := by
  have he := apply_root hr σ
  refine eq_one_of_root_fixed hr fun i => ?_
  set a : Fin ds.length → ℤ := fun i => if signOf hr σ i then 0 else -2 with ha
  have hsum : ∑ i, root hr i
      = ∑ i, (if signOf hr σ i then root hr i else -root hr i) := by
    have h1 : σ (gen hr c) = signSum c (fun i => σ (root hr i)) (fun _ => true) :=
      map_signSum ((σ : adjoinSqrt ds →ₐ[ℚ] adjoinSqrt ds).toRingHom) c (root hr) _
    rw [hσ, gen, signSum_const_true, signSum_const_true] at h1
    simpa only [he] using add_left_cancel h1
  have hK : ∑ i, ((a i : ℤ) : adjoinSqrt ds) * root hr i = 0 := by
    have hterm : ∀ i : Fin ds.length, ((a i : ℤ) : adjoinSqrt ds) * root hr i
        = (if signOf hr σ i then root hr i else -root hr i) - root hr i := by
      intro i
      by_cases hei : signOf hr σ i = true
      · simp [ha, hei]
      · simp only [ha, hei, Bool.false_eq_true, ite_false]
        push_cast
        ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← hsum, sub_self]
  have hzero : ∑ i, ((a i : ℤ) : ℂ) * r i = 0 := by
    have hval := congrArg (fun x : adjoinSqrt ds => (x : ℂ)) hK
    push_cast at hval
    simpa using hval
  have hai := eq_zero_of_sum_eq_zero h hr hzero i
  have hei : signOf hr σ i = true := by by_contra hc; simp [ha, hc] at hai
  rw [he i, hei, ite_eq_left rfl]

end Roots

/-! ## The Galois group is the group of sign patterns -/

section Galois

variable {ds : List ℤ} {r : Fin ds.length → ℂ}

/-- Nothing but the identity fixes `ℚ(α)` pointwise. -/
theorem fixingSubgroup_adjoin_gen (h : Independent ds)
    (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) :
    IntermediateField.fixingSubgroup (IntermediateField.adjoin ℚ {gen hr c}) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  exact eq_one_of_gen_fixed h hr c (hσ _ (IntermediateField.mem_adjoin_simple_self ℚ _))

/-- **The tower theorem, part (2), read inside the tower.** -/
theorem adjoin_gen_eq_top (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) :
    IntermediateField.adjoin ℚ {gen hr c} = ⊤ := by
  rw [← IsGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {gen hr c}),
    fixingSubgroup_adjoin_gen h hr c, IntermediateField.fixedField_bot]

/-- An automorphism is determined by its sign pattern, the roots generating the tower. -/
theorem signOf_injective (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) :
    Function.Injective (signOf hr) := by
  intro σ τ hστ
  refine inv_mul_eq_one.1 (eq_one_of_root_fixed hr fun i => ?_)
  have hroot : τ (root hr i) = σ (root hr i) := by
    rw [apply_root hr σ i, apply_root hr τ i, hστ]
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, hroot, AlgEquiv.symm_apply_apply]

/-- The identity acts by the all-plus pattern. -/
@[simp]
theorem signOf_one (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) :
    signOf hr 1 = fun _ => true := by
  funext i
  simp [signOf]

/--
Composing automorphisms multiplies sign patterns pointwise. `Bool` under `==`
with `true` as identity is `ℤ/2`, so this is the homomorphism law that turns
`signOf_bijective` into the isomorphism `Gal(K/ℚ) ≅ (ℤ/2)ⁿ`.
-/
theorem signOf_mul (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ))
    (σ τ : adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds) :
    signOf hr (σ * τ) = fun i => signOf hr σ i == signOf hr τ i := by
  funext i
  refine signOf_eq_of_apply h hr ?_
  rw [AlgEquiv.mul_apply, apply_root hr τ i]
  cases ht : signOf hr τ i <;> cases hs : signOf hr σ i <;>
    simp [map_neg, apply_root hr σ i, hs]

/--
**The Galois group is `(ℤ/2)ⁿ`.** Reading `σ` off as the sign pattern by which it
acts on the chosen roots is a bijection onto the `2ⁿ` sign patterns: injective
because the roots generate the tower, surjective by the degree theorem. It is a
group homomorphism by `signOf_mul`.
-/
theorem signOf_bijective (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) :
    Function.Bijective (signOf hr) := by
  have hcard : Fintype.card (adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds)
      = Fintype.card (Fin ds.length → Bool) := by
    simp only [← Nat.card_eq_fintype_card]
    rw [IsGalois.card_aut_eq_finrank, finrank_adjoinSqrt h]
    simp
  exact (Fintype.bijective_iff_injective_and_card _).2 ⟨signOf_injective hr, hcard⟩

end Galois

/-! ## The minimal polynomial is the sign-pattern product -/

section Minpoly

variable {ds : List ℤ} {r : Fin ds.length → ℂ}

/-- Sign-pattern sums agree when their signed summands do. -/
theorem signSum_congr {R : Type*} [Ring R] {n : ℕ} (c : ℤ) {r r' : Fin n → R}
    {ε ε' : Fin n → Bool} (h : ∀ i, (if ε i then r i else -r i) = (if ε' i then r' i else -r' i)) :
    signSum c r ε = signSum c r' ε' :=
  congrArg _ (Finset.sum_congr rfl fun i _ => h i)

/-- An automorphism permutes the sign patterns by exclusive-or with its own. -/
theorem signPoly_comp_algEquiv (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ)
    (σ : adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds) :
    signPoly c (fun i => σ (root hr i)) = signPoly c (root hr) := by
  have hflip : ∀ ε : Fin ds.length → Bool, signSum c (fun i => σ (root hr i)) ε
      = signSum c (root hr) (fun i => ε i == signOf hr σ i) := by
    intro ε
    refine signSum_congr c fun i => ?_
    rw [apply_root hr σ i]
    cases ε i <;> cases signOf hr σ i <;> simp
  have hinv : Function.Involutive
      (fun (ε : Fin ds.length → Bool) i => ε i == signOf hr σ i) := by
    intro ε
    funext i
    cases signOf hr σ i <;> simp
  rw [signPoly, signPoly, Finset.prod_congr rfl fun ε _ => by rw [hflip ε]]
  exact Equiv.prod_comp (hinv.toPerm _) fun ε => X - C (signSum c (root hr) ε)

/-- The sign-pattern product has coefficients in `ℚ`. -/
theorem exists_monic_map_eq_signPoly (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) :
    ∃ Q : ℚ[X], Q.Monic ∧ Q.map (algebraMap ℚ (adjoinSqrt ds)) = signPoly c (root hr) := by
  have hfix : ∀ σ : adjoinSqrt ds ≃ₐ[ℚ] adjoinSqrt ds,
      (signPoly c (root hr)).map (σ : adjoinSqrt ds →ₐ[ℚ] adjoinSqrt ds).toRingHom
        = signPoly c (root hr) := fun σ => by
    rw [map_signPoly]
    exact signPoly_comp_algEquiv hr c σ
  have hlifts : signPoly c (root hr) ∈ Polynomial.lifts (algebraMap ℚ (adjoinSqrt ds)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [← IntermediateField.mem_bot, IsGalois.mem_bot_iff_fixed]
    intro σ
    conv_rhs => rw [← hfix σ]
    rw [Polynomial.coeff_map]
    rfl
  obtain ⟨Q, hQmap, -, hQmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts (signPoly_monic c (root hr))
  exact ⟨Q, hQmonic, hQmap⟩

/-- `α` has degree `2 ^ n` over `ℚ`, by the Galois correspondence and the degree theorem. -/
theorem natDegree_minpoly_gen (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ))
    (c : ℤ) : (minpoly ℚ (gen hr c)).natDegree = 2 ^ ds.length := by
  rw [← IntermediateField.adjoin.finrank (IsGalois.integral ℚ (gen hr c)),
    adjoin_gen_eq_top h hr c, IntermediateField.finrank_top', finrank_adjoinSqrt h]

/-- **The tower theorem, part (3), read inside the tower.** -/
theorem minpoly_gen_map (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) :
    (minpoly ℚ (gen hr c)).map (algebraMap ℚ (adjoinSqrt ds)) = signPoly c (root hr) := by
  obtain ⟨Q, hQmonic, hQmap⟩ := exists_monic_map_eq_signPoly hr c
  have hint : IsIntegral ℚ (gen hr c) := IsGalois.integral ℚ (gen hr c)
  have hmonic : (minpoly ℚ (gen hr c)).Monic := minpoly.monic hint
  have hQdeg : Q.natDegree = 2 ^ ds.length := by
    have hd := congrArg Polynomial.natDegree hQmap
    rwa [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ (adjoinSqrt ds)).injective,
      natDegree_signPoly] at hd
  have heval : (Polynomial.aeval (gen hr c)) Q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hQmap]
    exact signPoly_eval c (root hr)
  obtain ⟨v, hv⟩ := minpoly.dvd ℚ (gen hr c) heval
  have hvmonic : v.Monic := hmonic.of_mul_monic_left (hv ▸ hQmonic)
  have hdeg : (minpoly ℚ (gen hr c)).natDegree + v.natDegree = Q.natDegree := by
    rw [hv, hmonic.natDegree_mul hvmonic]
  have hv1 : v = 1 := by
    refine hvmonic.natDegree_eq_zero.1 ?_
    rw [natDegree_minpoly_gen h hr c, hQdeg] at hdeg
    omega
  rw [hv, hv1, mul_one] at hQmap
  exact hQmap

/-- The minimal polynomial of `α` is computed inside the tower. -/
theorem minpoly_signSum (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) :
    minpoly ℚ (signSum c r (fun _ => true)) = minpoly ℚ (gen hr c) := by
  rw [← gen_val hr c]
  exact minpoly.algHom_eq (adjoinSqrt ds).val (adjoinSqrt ds).val.injective (gen hr c)

/-- **The tower theorem, part (3).** The minimal polynomial is the sign-pattern product. -/
theorem minpoly_map_eq_signPoly (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ))
    (c : ℤ) : (minpoly ℚ (signSum c r (fun _ => true))).map (algebraMap ℚ ℂ) = signPoly c r := by
  have hmin := minpoly_signSum hr c
  have hcomp : ((adjoinSqrt ds).val : adjoinSqrt ds →ₐ[ℚ] ℂ).toRingHom.comp
      (algebraMap ℚ (adjoinSqrt ds)) = algebraMap ℚ ℂ := by
    ext q
    simp
  rw [hmin, ← hcomp, ← Polynomial.map_map, minpoly_gen_map h hr c, map_signPoly]
  rfl

end Minpoly

/-! ## Consequences in `ℂ` -/

section Consequences

variable {ds : List ℤ} {r : Fin ds.length → ℂ}

/-- `α` is integral over `ℚ`, lying in a finite extension. -/
theorem isIntegral_signSum (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) :
    IsIntegral ℚ (signSum c r (fun _ => true)) := by
  rw [← gen_val hr c]
  exact (IsGalois.integral ℚ (gen hr c)).map (adjoinSqrt ds).val

/-- `α` has degree `2 ^ n` over `ℚ`. -/
theorem natDegree_minpoly_signSum (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ))
    (c : ℤ) : (minpoly ℚ (signSum c r (fun _ => true))).natDegree = 2 ^ ds.length := by
  rw [minpoly_signSum hr c]
  exact natDegree_minpoly_gen h hr c

/-- **The tower theorem, part (2).** `α = c + ∑ᵢ √dᵢ` generates the whole tower. -/
theorem adjoin_signSum_eq (h : Independent ds) (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) :
    IntermediateField.adjoin ℚ {signSum c r (fun _ => true)} = adjoinSqrt ds := by
  have hle : IntermediateField.adjoin ℚ {signSum c r (fun _ => true)} ≤ adjoinSqrt ds := by
    rw [IntermediateField.adjoin_simple_le_iff, ← gen_val hr c]
    exact (gen hr c).2
  refine IntermediateField.eq_of_le_of_finrank_eq hle ?_
  rw [IntermediateField.adjoin.finrank (isIntegral_signSum hr c),
    natDegree_minpoly_signSum h hr c, finrank_adjoinSqrt h]

/--
**The consequence the certificate needs.** A rational polynomial that is the
sign-pattern product of independent square classes is irreducible: it is the
minimal polynomial of `α`.
-/
theorem irreducible_of_map_eq_signPoly (h : Independent ds)
    (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) {f : ℚ[X]}
    (hf : f.map (algebraMap ℚ ℂ) = signPoly c r) : Irreducible f := by
  have hfe : f = minpoly ℚ (signSum c r (fun _ => true)) :=
    Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
      (by rw [hf, minpoly_map_eq_signPoly h hr c])
  rw [hfe]
  exact minpoly.irreducible (isIntegral_signSum hr c)

/-- The same over `ℤ`, by Gauss's lemma: a monic integer sign-pattern product is irreducible. -/
theorem irreducible_int_of_map_eq_signPoly (h : Independent ds)
    (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) (c : ℤ) {f : ℤ[X]} (hfm : f.Monic)
    (hf : f.map (Int.castRingHom ℂ) = signPoly c r) : Irreducible f := by
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hfm.isPrimitive]
  refine irreducible_of_map_eq_signPoly h hr c ?_
  rw [Polynomial.map_map,
    RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ)]
  exact hf

end Consequences

/-! ## Sanity checks -/

example : Independent [2, 3, 5] := by decide +kernel

example : ¬ Independent [2, 3, 6] := by decide +kernel

/-- `√2 + √3 + √5` has degree `8` over `ℚ`. -/
example (r : Fin 3 → ℂ) (hr : ∀ i, r i ^ 2 = (((([2, 3, 5] : List ℤ))[i] : ℤ) : ℂ)) :
    (minpoly ℚ (signSum 0 r (fun _ => true))).natDegree = 8 := by
  have := natDegree_minpoly_signSum (ds := [2, 3, 5]) (by decide +kernel) hr 0
  simpa using this

end

end Hex.SquareClass
