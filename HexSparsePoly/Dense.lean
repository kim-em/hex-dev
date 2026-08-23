/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSparsePoly.Arith
public import HexPoly

@[expose] public section
set_option backward.proofsInPublic true

/-!
Conversion between the canonical sparse representation and `DensePoly`:
the array-level workers, `toDense` and `ofDense`, the homomorphism laws
in both directions, the degree-boundary transport, and both round trips.
`toDense` is the one operation whose cost is the degree, not the term
count; nothing in this library is implemented through it.
-/

namespace Hex

open scoped Hex

universe u

namespace SparsePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- One more than the largest exponent of a term array (`0` when empty):
the number of coefficients its dense form stores. -/
def termsBound (ts : Array (Nat × R)) : Nat :=
  ts.foldl (fun m t => max m (t.1 + 1)) 0

omit [Zero R] [DecidableEq R] in
/-- The bound fold dominates its initial value. -/
theorem le_foldl_max (l : List (Nat × R)) (init : Nat) :
    init ≤ l.foldl (fun m t => max m (t.1 + 1)) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
      exact Nat.le_trans (Nat.le_max_left _ _) (ih (max init (a.1 + 1)))

omit [Zero R] [DecidableEq R] in
/-- Every stored exponent is below the bound. -/
theorem exp_lt_foldl_max {l : List (Nat × R)} {t : Nat × R} (ht : t ∈ l)
    (init : Nat) : t.1 < l.foldl (fun m t => max m (t.1 + 1)) init := by
  induction l generalizing init with
  | nil => cases ht
  | cons a as ih =>
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
            (Nat.le_max_right init (t.1 + 1)))
          (le_foldl_max as _)
      · exact ih ht' _

omit [Zero R] [DecidableEq R] in
/-- The bound is least among exponent bounds at or above its initial
value. -/
theorem foldl_max_le {l : List (Nat × R)} {n : Nat}
    (init : Nat) (h0 : init ≤ n) (h : ∀ t ∈ l, t.1 < n) :
    l.foldl (fun m t => max m (t.1 + 1)) init ≤ n := by
  induction l generalizing init with
  | nil => exact h0
  | cons a as ih =>
      refine ih _ ?_ fun t ht => h t (List.mem_cons_of_mem _ ht)
      exact Nat.max_le.mpr ⟨h0, h a (List.mem_cons_self ..)⟩

omit [DecidableEq R] in
omit [Zero R] in
/-- Writing a term list into an array does not change its size. -/
theorem size_foldl_set (l : List (Nat × R)) (base : Array R) :
    (l.foldl (fun acc t => acc.setIfInBounds t.1 t.2) base).size =
      base.size := by
  induction l generalizing base with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, Array.size_setIfInBounds]

omit [DecidableEq R] in
/-- Writing a sorted, in-bounds term list into an array puts each
coefficient at its exponent and touches nothing else. -/
theorem getD_foldl_set {l : List (Nat × R)}
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (base : Array R)
    (hbound : ∀ t ∈ l, t.1 < base.size) (i : Nat) :
    (l.foldl (fun acc t => acc.setIfInBounds t.1 t.2) base).getD i 0 =
      if ∃ t ∈ l, t.1 = i then coeffList l i else base.getD i 0 := by
  induction l generalizing base with
  | nil => simp
  | cons a as ih =>
      rw [List.pairwise_cons] at hs
      rw [List.foldl_cons,
        ih hs.2 _ (by
          intro t ht
          rw [Array.size_setIfInBounds]
          exact hbound t (List.mem_cons_of_mem _ ht))]
      by_cases hmem : ∃ t ∈ as, t.1 = i
      · rw [if_pos hmem]
        obtain ⟨t, ht, hti⟩ := hmem
        rw [if_pos ⟨t, List.mem_cons_of_mem _ ht, hti⟩]
        have hai : ¬ a.1 = i := by
          have := hs.1 t ht
          omega
        simp only [coeffList, if_neg hai]
      · rw [if_neg hmem]
        by_cases hai : a.1 = i
        · rw [if_pos ⟨a, List.mem_cons_self .., hai⟩]
          subst hai
          rw [show coeffList (a :: as) a.1 = a.2 from by simp [coeffList]]
          have hlt : a.1 < (base.setIfInBounds a.1 a.2).size := by
            rw [Array.size_setIfInBounds]
            exact hbound a (List.mem_cons_self ..)
          rw [Array.getD, dif_pos hlt]
          exact Array.getElem_setIfInBounds_self hlt
        · rw [if_neg (by
            intro hcon
            obtain ⟨t, ht, hti⟩ := hcon
            rcases List.mem_cons.mp ht with rfl | ht'
            · exact hai hti
            · exact hmem ⟨t, ht', hti⟩)]
          by_cases hi : i < base.size
          · have hi' : i < (base.setIfInBounds a.1 a.2).size := by
              rw [Array.size_setIfInBounds]
              exact hi
            rw [Array.getD, dif_pos hi', Array.getD, dif_pos hi]
            exact Array.getElem_setIfInBounds_ne hi hai
          · rw [Array.getD, dif_neg (by rwa [Array.size_setIfInBounds]),
              Array.getD, dif_neg hi]

/-- Write each term of an arbitrary term array into a coefficient array
sized by the largest exponent. A conversion, not a canonicaliser: with
duplicate exponents the last write wins, which is what makes the
round-trip hypotheses below necessary. -/
def coeffsOfTerms (ts : Array (Nat × R)) : Array R :=
  ts.foldl (fun acc t => acc.setIfInBounds t.1 t.2)
    (Array.replicate (termsBound ts) 0)

/-- Keep the nonzero coefficients of a coefficient list with their
indices, starting at index `i`. Kernel-facing walk shared by
`termsOfCoeffs` and `ofDense`. -/
def termsOfCoeffsList : Nat → List R → List (Nat × R)
  | _, [] => []
  | i, c :: cs =>
      if c = 0 then termsOfCoeffsList (i + 1) cs
      else (i, c) :: termsOfCoeffsList (i + 1) cs

/-- Keep the nonzero coefficients of a coefficient array with their
indices. -/
def termsOfCoeffs (cs : Array R) : Array (Nat × R) :=
  (termsOfCoeffsList 0 cs.toList).toArray

/-- Every index stored by the walk is at least the starting index and
within the list. -/
theorem exp_mem_termsOfCoeffsList {l : List R} {i : Nat} {t : Nat × R}
    (ht : t ∈ termsOfCoeffsList i l) :
    i ≤ t.1 ∧ t.1 < i + l.length := by
  induction l generalizing i with
  | nil => cases ht
  | cons c cs ih =>
      simp only [termsOfCoeffsList] at ht
      split at ht
      · have := ih ht
        simp only [List.length_cons]
        omega
      · rcases List.mem_cons.mp ht with rfl | ht'
        · simp only [List.length_cons]
          omega
        · have := ih ht'
          simp only [List.length_cons]
          omega

/-- The walk emits a canonical term list. -/
theorem termsOfCoeffsList_canonical (l : List R) (i : Nat) :
    (termsOfCoeffsList i l).Pairwise (fun a b => a.1 < b.1) ∧
      ∀ t ∈ termsOfCoeffsList i l, t.2 ≠ 0 := by
  induction l generalizing i with
  | nil => simp [termsOfCoeffsList]
  | cons c cs ih =>
      obtain ⟨hpw, hnz⟩ := ih (i + 1)
      simp only [termsOfCoeffsList]
      split
      · exact ⟨hpw, hnz⟩
      · rename_i hc
        refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_⟩
        · intro t ht
          have := exp_mem_termsOfCoeffsList ht
          omega
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht'
          · exact hc
          · exact hnz t ht'

/-- The walk stores exactly the nonzero coefficients: its coefficient
at `i + e` is the list's value at `e`. -/
theorem coeffList_termsOfCoeffsList (l : List R) (i e : Nat) :
    coeffList (termsOfCoeffsList i l) (i + e) = l.getD e 0 := by
  induction l generalizing i e with
  | nil => simp [termsOfCoeffsList, coeffList]
  | cons c cs ih =>
      simp only [termsOfCoeffsList]
      cases e with
      | zero =>
          rw [List.getD_cons_zero]
          split
          · rename_i hc
            rw [hc]
            refine coeffList_eq_zero ?_
            intro t ht
            have := exp_mem_termsOfCoeffsList ht
            omega
          · simp only [coeffList]
            rw [if_pos (show i = i + 0 by omega)]
      | succ e =>
          rw [List.getD_cons_succ]
          split
          · rw [show i + (e + 1) = (i + 1) + e from by omega, ih]
          · simp only [coeffList,
              if_neg (show ¬ i = i + (e + 1) from by omega)]
            rw [show i + (e + 1) = (i + 1) + e from by omega, ih]

/-- The walk stores nothing below its starting index. -/
theorem coeffList_termsOfCoeffsList_of_lt (l : List R) {i f : Nat}
    (hf : f < i) : coeffList (termsOfCoeffsList i l) f = 0 := by
  refine coeffList_eq_zero ?_
  intro t ht
  have := exp_mem_termsOfCoeffsList ht
  omega

/-- Convert to the dense representation: allocate `degree + 1`
coefficients and write each stored term into its slot, `O(n)` in the
degree whatever the term count. The one operation here whose cost is not
governed by the term count; no operation in this library is implemented
through it. -/
def toDense (s : SparsePoly R) : DensePoly R :=
  DensePoly.ofCoeffs (coeffsOfTerms s.terms)

/-- The conversion preserves every coefficient. -/
@[simp, grind =] theorem coeff_toDense (s : SparsePoly R) (e : Nat) :
    s.toDense.coeff e = s.coeff e := by
  unfold toDense coeffsOfTerms
  rw [DensePoly.coeff_ofCoeffs, ← Array.foldl_toList]
  simp only [show (Zero.zero : R) = 0 from rfl]
  rw [getD_foldl_set s.pairwise_toList _
    (by
      intro t ht
      rw [Array.size_replicate]
      unfold termsBound
      rw [← Array.foldl_toList]
      exact exp_lt_foldl_max ht 0)
    e]
  by_cases hmem : ∃ t ∈ s.terms.toList, t.1 = e
  · rw [if_pos hmem]
    rfl
  · rw [if_neg hmem]
    have : s.coeff e = 0 := by
      refine coeffList_eq_zero ?_
      intro t ht hte
      exact hmem ⟨t, ht, hte⟩
    rw [this]
    by_cases he : e < (Array.replicate (termsBound s.terms) (0 : R)).size
    · rw [Array.getD, dif_pos he]
      exact Array.getElem_replicate he
    · rw [Array.getD, dif_neg he]

/-- Convert from the dense representation, keeping the nonzero
coefficients with their indices.

Kernel-facing specification (an ordered `List` walk); compiled code uses
`Hex.SparsePoly.ofDenseImpl`, the value-equal array pass selected by
`Hex.SparsePoly.ofDense_eq_impl`. -/
noncomputable def ofDense (p : DensePoly R) : SparsePoly R :=
  ofCanonicalList (termsOfCoeffsList 0 p.coeffs.toList)
    (termsOfCoeffsList_canonical p.coeffs.toList 0).1
    (termsOfCoeffsList_canonical p.coeffs.toList 0).2

/-- Array worker for `ofDenseImpl`: one indexed pass pushing the
nonzero coefficients. -/
def termsOfCoeffsArray (cs : Array R) : Array (Nat × R) :=
  (cs.foldl
    (fun st c => (if c = 0 then st.1 else st.1.push (st.2, c), st.2 + 1))
    ((#[] : Array (Nat × R)), 0)).1

private theorem foldl_push_eq_termsOfCoeffsList (l : List R) :
    ∀ (i : Nat) (acc : Array (Nat × R)),
    (l.foldl
      (fun st c => (if c = 0 then st.1 else st.1.push (st.2, c), st.2 + 1))
      (acc, i)).1 = acc ++ (termsOfCoeffsList i l).toArray := by
  induction l with
  | nil =>
      intro i acc
      simp [termsOfCoeffsList]
  | cons c cs ih =>
      intro i acc
      simp only [List.foldl_cons]
      by_cases hc : c = 0
      · rw [if_pos hc]
        show (cs.foldl _ (acc, i + 1)).1 = _
        rw [ih (i + 1) acc]
        simp only [termsOfCoeffsList, if_pos hc]
      · rw [if_neg hc]
        show (cs.foldl _ (acc.push (i, c), i + 1)).1 = _
        rw [ih (i + 1) (acc.push (i, c))]
        simp only [termsOfCoeffsList, if_neg hc]
        apply Array.toList_inj.mp
        simp

/-- The array pass agrees with the kernel-facing list walk. -/
theorem termsOfCoeffsArray_eq (cs : Array R) :
    termsOfCoeffsArray cs = (termsOfCoeffsList 0 cs.toList).toArray := by
  unfold termsOfCoeffsArray
  rw [← Array.foldl_toList, foldl_push_eq_termsOfCoeffsList cs.toList 0 #[]]
  apply Array.toList_inj.mp
  simp

/-- Runtime implementation of {name}`ofDense`: one array pass (value-equal
to {name}`ofDense` by `ofDense_eq_impl`, registered `@[csimp]`). -/
def ofDenseImpl (p : DensePoly R) : SparsePoly R where
  terms := termsOfCoeffsArray p.coeffs
  canonical := by
    rw [termsOfCoeffsArray_eq]
    exact (ofDense p).canonical

/-- The list walk and the array pass build the same polynomial. -/
theorem ofDense_eq_ofDenseImpl (p : DensePoly R) :
    ofDense p = ofDenseImpl p :=
  eq_of_terms_eq (termsOfCoeffsArray_eq p.coeffs).symm

/-- Register the array pass as the compiled implementation of
{name}`ofDense`. -/
@[csimp]
theorem ofDense_eq_impl : @ofDense = @ofDenseImpl := by
  funext R _ _ p
  exact ofDense_eq_ofDenseImpl p

/-- The conversion preserves every coefficient. -/
@[simp, grind =] theorem coeff_ofDense (p : DensePoly R) (e : Nat) :
    (ofDense p).coeff e = p.coeff e := by
  unfold ofDense
  rw [coeff_ofCanonicalList]
  have h := coeffList_termsOfCoeffsList p.coeffs.toList 0 e
  rw [Nat.zero_add] at h
  rw [h]
  exact DensePoly.toList_getD_eq_coeff p e

omit [DecidableEq R] in
omit [Zero R] in
/-- `getD` on an array agrees with `getD` on its list. -/
theorem toList_getD (a : Array R) (i : Nat) (d : R) :
    a.toList.getD i d = a.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

omit [DecidableEq R] in
/-- The dense image of a sorted term array stores exactly its
coefficients. -/
theorem getD_coeffsOfTerms {ts : Array (Nat × R)}
    (hs : ts.toList.Pairwise (fun a b => a.1 < b.1)) (e : Nat) :
    (coeffsOfTerms ts).getD e 0 = coeffList ts.toList e := by
  unfold coeffsOfTerms
  rw [← Array.foldl_toList]
  rw [getD_foldl_set hs _
    (by
      intro t ht
      rw [Array.size_replicate]
      unfold termsBound
      rw [← Array.foldl_toList]
      exact exp_lt_foldl_max ht 0)
    e]
  by_cases hmem : ∃ t ∈ ts.toList, t.1 = e
  · rw [if_pos hmem]
  · rw [if_neg hmem,
      coeffList_eq_zero fun t ht hte => hmem ⟨t, ht, hte⟩]
    by_cases he : e < (Array.replicate (termsBound ts) (0 : R)).size
    · rw [Array.getD, dif_pos he]
      exact Array.getElem_replicate he
    · rw [Array.getD, dif_neg he]

/-- The sparse image of a coefficient array stores exactly its
coefficients. -/
theorem coeffList_termsOfCoeffs (cs : Array R) (e : Nat) :
    coeffList (termsOfCoeffs cs).toList e = cs.getD e 0 := by
  unfold termsOfCoeffs
  rw [List.toList_toArray]
  have h := coeffList_termsOfCoeffsList cs.toList 0 e
  rw [Nat.zero_add] at h
  rw [h, toList_getD]

/-- Round trip through the dense coefficients: exact on canonical term
arrays, and false without either half of the invariant (a stored zero
vanishes, a duplicate is overwritten, unsorted input comes back
sorted). -/
theorem terms_coeffs {ts : Array (Nat × R)} (h : SparsePolyCanonical ts) :
    termsOfCoeffs (coeffsOfTerms ts) = ts := by
  have hcanon := termsOfCoeffsList_canonical (coeffsOfTerms ts).toList 0
  have hlist : (termsOfCoeffs (coeffsOfTerms ts)).toList = ts.toList := by
    unfold termsOfCoeffs
    rw [List.toList_toArray]
    refine coeffList_ext hcanon.1 h.1 hcanon.2
      (fun t ht => h.2 t (Array.mem_def.mpr ht)) ?_
    intro e
    have h1 := coeffList_termsOfCoeffs (coeffsOfTerms ts) e
    unfold termsOfCoeffs at h1
    rw [List.toList_toArray] at h1
    rw [h1, getD_coeffsOfTerms h.1]
  exact Array.toList_inj.mp hlist

/-- Round trip through the term list: exact on trailing-zero-free
coefficient arrays, and false without `DensePolyNormalized` (a trailing
zero is not reconstructed). It is `DensePoly`'s own invariant that makes
the sparse round trip exact. -/
theorem coeffs_terms {cs : Array R} (h : DensePolyNormalized cs) :
    coeffsOfTerms (termsOfCoeffs cs) = cs := by
  have hsorted : (termsOfCoeffs cs).toList.Pairwise
      (fun a b => a.1 < b.1) := by
    unfold termsOfCoeffs
    rw [List.toList_toArray]
    exact (termsOfCoeffsList_canonical cs.toList 0).1
  have hexp_lt : ∀ t ∈ (termsOfCoeffs cs).toList, t.1 < cs.size := by
    intro t ht
    unfold termsOfCoeffs at ht
    rw [List.toList_toArray] at ht
    have := exp_mem_termsOfCoeffsList ht
    simpa using this.2
  have hsize : (coeffsOfTerms (termsOfCoeffs cs)).size = cs.size := by
    unfold coeffsOfTerms
    rw [← Array.foldl_toList, size_foldl_set, Array.size_replicate]
    refine Nat.le_antisymm ?_ ?_
    · unfold termsBound
      rw [← Array.foldl_toList]
      exact foldl_max_le 0 (Nat.zero_le _) hexp_lt
    · rcases Nat.eq_zero_or_pos cs.size with hzero | hpos
      · omega
      · have hlast : cs.getD (cs.size - 1) 0 ≠ 0 := by
          rcases h with hempty | hback
          · omega
          · rw [Array.back?_eq_getElem?,
              Array.getElem?_eq_getElem (by omega)] at hback
            rw [Array.getD, dif_pos (by omega)]
            intro hval
            exact hback (congrArg some hval)
        have hcoeff : coeffList (termsOfCoeffs cs).toList
            (cs.size - 1) ≠ 0 := by
          rw [coeffList_termsOfCoeffs]
          exact hlast
        have hmem : ∃ t ∈ (termsOfCoeffs cs).toList,
            t.1 = cs.size - 1 := by
          by_cases hc : ∃ t ∈ (termsOfCoeffs cs).toList, t.1 = cs.size - 1
          · exact hc
          · exact absurd (coeffList_eq_zero
              fun t ht hte => hc ⟨t, ht, hte⟩) hcoeff
        obtain ⟨t, ht, hte⟩ := hmem
        unfold termsBound
        rw [← Array.foldl_toList]
        have := exp_lt_foldl_max ht 0
        omega
  refine Array.ext hsize ?_
  intro i hi₁ hi₂
  have hgetD := getD_coeffsOfTerms hsorted i
  rw [coeffList_termsOfCoeffs] at hgetD
  rw [Array.getD, dif_pos hi₁, Array.getD, dif_pos hi₂] at hgetD
  exact hgetD

/-- Round trip on the bundled types, dense side out: unconditional,
because the type carries its canonical form. -/
@[simp, grind =] theorem ofDense_toDense (s : SparsePoly R) :
    ofDense s.toDense = s := by
  apply ext_coeff
  intro e
  rw [coeff_ofDense, coeff_toDense]

/-- Round trip on the bundled types, sparse side out: unconditional,
because `DensePoly` carries its trailing-zero-free form. -/
@[simp, grind =] theorem toDense_ofDense (p : DensePoly R) :
    (ofDense p).toDense = p := by
  apply DensePoly.ext_coeff
  intro e
  rw [coeff_toDense, coeff_ofDense]

/-- The dense conversion is injective, which is how sparse identities
are transported back from dense ones. -/
theorem toDense_inj {s t : SparsePoly R} (h : s.toDense = t.toDense) :
    s = t := by
  rw [← ofDense_toDense s, ← ofDense_toDense t, h]

/-- The conversion sends zero to zero. -/
@[simp, grind =] theorem toDense_zero :
    (0 : SparsePoly R).toDense = 0 := by
  apply DensePoly.ext_coeff
  intro e
  rw [coeff_toDense, coeff_zero]
  exact (DensePoly.coeff_eq_zero_of_size_le 0 (by simp)).symm

/-- The conversion sends one to one. -/
@[simp, grind =] theorem toDense_one [One R] :
    (1 : SparsePoly R).toDense = 1 := by
  apply DensePoly.ext_coeff
  intro e
  rw [coeff_toDense]
  show coeff 1 e = (DensePoly.C 1).coeff e
  rw [coeff_one, DensePoly.coeff_C]
  rfl

/-- The conversion sends monomials to dense monomials. -/
@[simp, grind =] theorem toDense_monomial (e : Nat) (c : R) :
    (monomial e c).toDense = DensePoly.monomial e c := by
  apply DensePoly.ext_coeff
  intro f
  rw [coeff_toDense, coeff_monomial, DensePoly.coeff_monomial]
  rfl

/-- The conversion is additive. -/
theorem toDense_add {S : Type u} [Lean.Grind.Semiring S] [DecidableEq S]
    (s t : SparsePoly S) : (s + t).toDense = s.toDense + t.toDense := by
  apply DensePoly.ext_coeff
  intro e
  rw [coeff_toDense, coeff_add,
    DensePoly.coeff_add _ _ _ (by grind), coeff_toDense, coeff_toDense]

/-- The conversion commutes with negation. -/
theorem toDense_neg {S : Type u} [Lean.Grind.Ring S] [DecidableEq S]
    (s : SparsePoly S) : (-s).toDense = -s.toDense := by
  apply DensePoly.ext_coeff
  intro e
  rw [coeff_toDense, coeff_neg]
  show _ = (DensePoly.neg s.toDense).coeff e
  unfold DensePoly.neg
  rw [DensePoly.coeff_sub _ _ _ (by grind), coeff_toDense]
  show 0 - coeff s e = (0 : DensePoly S).coeff e - coeff s e
  rw [show (0 : DensePoly S).coeff e = 0 from
    DensePoly.coeff_eq_zero_of_size_le 0 (by simp)]

/-- The reverse conversion sends zero to zero. -/
theorem ofDense_zero : ofDense (0 : DensePoly R) = 0 := by
  apply ext_coeff
  intro e
  rw [coeff_ofDense, coeff_zero]
  exact DensePoly.coeff_eq_zero_of_size_le 0 (by simp)

/-- The reverse conversion sends one to one. -/
theorem ofDense_one [One R] : ofDense (1 : DensePoly R) = 1 := by
  apply ext_coeff
  intro e
  rw [coeff_ofDense, coeff_one]
  show (DensePoly.C 1).coeff e = _
  rw [DensePoly.coeff_C]
  rfl

/-- The reverse conversion is additive. -/
theorem ofDense_add {S : Type u} [Lean.Grind.Semiring S] [DecidableEq S]
    (p q : DensePoly S) : ofDense (p + q) = ofDense p + ofDense q := by
  apply ext_coeff
  intro e
  rw [coeff_ofDense, coeff_add, DensePoly.coeff_add _ _ _ (by grind),
    coeff_ofDense, coeff_ofDense]

/-- The reverse conversion commutes with negation. -/
theorem ofDense_neg {S : Type u} [Lean.Grind.Ring S] [DecidableEq S]
    (p : DensePoly S) : ofDense (-p) = -(ofDense p) := by
  apply ext_coeff
  intro e
  rw [coeff_ofDense, coeff_neg, coeff_ofDense]
  show (DensePoly.neg p).coeff e = _
  unfold DensePoly.neg
  rw [DensePoly.coeff_sub _ _ _ (by grind)]
  rw [show (0 : DensePoly S).coeff e = 0 from
    DensePoly.coeff_eq_zero_of_size_le 0 (by simp)]

section MulSemiring

variable {S : Type u} [Lean.Grind.Semiring S] [DecidableEq S]

omit [DecidableEq S] in
private theorem zero_add_zero : (Zero.zero : S) + Zero.zero = Zero.zero := by
  show (0 : S) + 0 = 0
  grind

/-- Fold congruence pointwise on the folded function and initial value. -/
theorem foldl_congr' {α β : Type _} {l : List α} {f g : β → α → β}
    {i j : β} (hij : i = j) (hfg : ∀ b : β, ∀ a ∈ l, f b a = g b a) :
    l.foldl f i = l.foldl g j := by
  subst hij
  induction l generalizing i with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [hfg i a (List.mem_cons_self ..)]
      exact ih fun b x hx => hfg b x (List.mem_cons_of_mem _ hx)

/-- A fresh insertion is the inserted coefficient, with no algebra
assumed. -/
theorem addCoeff_zero_left (c : S) : addCoeff 0 c = c := by
  unfold addCoeff
  rw [if_pos rfl]
  by_cases hc : c = 0
  · rw [if_pos hc, hc]
  · rw [if_neg hc]

/-- Coefficients of a fold of sums, sparse side. -/
theorem coeff_foldl_add {α : Type _} (l : List α)
    (g : α → SparsePoly S) (init : SparsePoly S) (f : Nat) :
    (l.foldl (fun acc a => acc + g a) init).coeff f =
      l.foldl (fun acc a => acc + (g a).coeff f) (init.coeff f) := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih, coeff_add]

/-- Coefficients of a fold of sums, dense side. -/
private theorem dense_coeff_foldl_add {α : Type _} (l : List α)
    (g : α → DensePoly S) (init : DensePoly S) (f : Nat) :
    (l.foldl (fun acc a => acc + g a) init).coeff f =
      l.foldl (fun acc a => acc + (g a).coeff f) (init.coeff f) := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih, DensePoly.coeff_add _ _ _ zero_add_zero]

omit [DecidableEq S] in
/-- One block of the pairwise product, folded at a target exponent: at
most one product of a term of `s` with the sorted terms of `t` lands on
any exponent, and its value is the {name}`mulMonomial` coefficient. -/
private theorem foldl_add_block (a : Nat × S) {l : List (Nat × S)}
    (hs : l.Pairwise (fun x y => x.1 < y.1)) (x : S) (f : Nat) :
    ((l.map fun b => (a.1 + b.1, a.2 * b.2)).filter
        (fun u => u.1 = f)).foldl (fun acc u => acc + u.2) x =
      x + (if a.1 ≤ f then a.2 * coeffList l (f - a.1) else 0) := by
  induction l generalizing x with
  | nil =>
      simp only [List.map_nil, List.filter_nil, List.foldl_nil, coeffList]
      split <;> grind
  | cons b bs ih =>
      rw [List.pairwise_cons] at hs
      simp only [List.map_cons]
      by_cases hbf : a.1 + b.1 = f
      · rw [List.filter_cons_of_pos (by simpa using hbf), List.foldl_cons]
        have hempty : ((bs.map fun u => (a.1 + u.1, a.2 * u.2)).filter
            (fun u => u.1 = f)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro u hu
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
          have := hs.1 v hv
          simp only [decide_eq_true_eq]
          omega
        rw [hempty, List.foldl_nil,
          if_pos (show a.1 ≤ f from by omega)]
        have : coeffList (b :: bs) (f - a.1) = b.2 := by
          simp only [coeffList]
          rw [if_pos (show b.1 = f - a.1 from by omega)]
        rw [this]
      · rw [List.filter_cons_of_neg (by simpa using hbf), ih hs.2]
        by_cases haf : a.1 ≤ f
        · rw [if_pos haf, if_pos haf]
          have : coeffList (b :: bs) (f - a.1) = coeffList bs (f - a.1) := by
            simp only [coeffList]
            rw [if_neg (show ¬ b.1 = f - a.1 from by omega)]
          rw [this]
        · rw [if_neg haf, if_neg haf]

/-- The pairwise-product coefficient, reorganised as a fold of
{name}`mulMonomial` coefficients over the left operand's terms. -/
theorem coeff_mul_foldl (s t : SparsePoly S) (f : Nat) :
    (s * t).coeff f =
      s.terms.toList.foldl
        (fun acc a => acc + (mulMonomial a.1 a.2 t).coeff f) 0 := by
  show (s.mul t).coeff f = _
  unfold mul
  rw [coeff_ofTerms_addCoeff]
  have hz : ∀ c : S, (0 : S) + c = c := by grind
  simp only [addCoeff_eq_add hz]
  rw [List.toList_toArray, List.filter_flatMap, List.foldl_flatMap]
  have hstep : ∀ (x : S) (a : Nat × S),
      ((t.terms.toList.map fun b => (a.1 + b.1, a.2 * b.2)).filter
          (fun u => u.1 = f)).foldl (fun acc u => acc + u.2) x =
        x + (mulMonomial a.1 a.2 t).coeff f := by
    intro x a
    rw [foldl_add_block a t.pairwise_toList x f, coeff_mulMonomial]
    rfl
  exact foldl_congr' rfl fun b a _ => hstep b a

/-- The pairwise product is the fold of monomial multiples: the shape
the dense transport consumes. -/
theorem mul_eq_foldl (s t : SparsePoly S) :
    s * t =
      s.terms.toList.foldl (fun acc a => acc + mulMonomial a.1 a.2 t) 0 := by
  apply ext_coeff
  intro f
  rw [coeff_mul_foldl, coeff_foldl_add, coeff_zero]

/-- The dense image of a fold of sums. -/
theorem toDense_foldl_add {α : Type _} (l : List α)
    (g : α → SparsePoly S) (init : SparsePoly S) :
    (l.foldl (fun acc a => acc + g a) init).toDense =
      l.foldl (fun acc a => acc + (g a).toDense) init.toDense := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih, toDense_add]

/-- A fold of dense monomials at the stored terms rebuilds the dense
image. -/
theorem toDense_foldl_monomial (s : SparsePoly S) :
    s.toDense =
      s.terms.toList.foldl
        (fun acc a => acc + DensePoly.monomial a.1 a.2) 0 := by
  apply DensePoly.ext_coeff
  intro f
  rw [dense_coeff_foldl_add]
  have hfold : ∀ (l : List (Nat × S)),
      l.Pairwise (fun x y => x.1 < y.1) → ∀ x : S,
      l.foldl (fun acc a => acc + (DensePoly.monomial a.1 a.2).coeff f) x =
        x + coeffList l f := by
    intro l hl
    induction l with
    | nil =>
        intro x
        simp only [List.foldl_nil, coeffList]
        grind
    | cons a as ih =>
        rw [List.pairwise_cons] at hl
        intro x
        simp only [List.foldl_cons]
        rw [ih hl.2, DensePoly.coeff_monomial]
        simp only [coeffList, show (Zero.zero : S) = 0 from rfl]
        by_cases hf : f = a.1
        · rw [if_pos hf, if_pos hf.symm,
            coeffList_eq_zero (fun t ht hte => by
              have := hl.1 t ht
              omega)]
          grind
        · rw [if_neg hf, if_neg (fun h : a.1 = f => hf h.symm)]
          grind
  rw [hfold s.terms.toList s.pairwise_toList,
    show (0 : DensePoly S).coeff f = 0 from
      DensePoly.coeff_eq_zero_of_size_le 0 (by simp),
    coeff_toDense]
  show coeff s f = 0 + coeff s f
  grind

end MulSemiring

section MulRing

variable {S : Type u} [Lean.Grind.CommRing S] [DecidableEq S]

/-- The dense image of a monomial multiple is the dense monomial
product. -/
theorem toDense_mulMonomial (e : Nat) (c : S) (t : SparsePoly S) :
    (mulMonomial e c t).toDense = DensePoly.monomial e c * t.toDense := by
  have hmono : DensePoly.monomial e c =
      DensePoly.scale c (DensePoly.monomial e 1) := by
    apply DensePoly.ext_coeff
    intro f
    rw [DensePoly.coeff_scale_semiring, DensePoly.coeff_monomial,
      DensePoly.coeff_monomial]
    simp only [show (Zero.zero : S) = 0 from rfl]
    grind
  rw [hmono, ← DensePoly.scale_mul,
    DensePoly.monomial_one_mul_poly_eq_shift]
  apply DensePoly.ext_coeff
  intro f
  rw [coeff_toDense, coeff_mulMonomial, DensePoly.coeff_scale_semiring,
    DensePoly.coeff_shift, coeff_toDense]
  simp only [show (Zero.zero : S) = 0 from rfl]
  grind

/-- Multiplying a fold of sums on the right distributes. -/
private theorem foldl_add_mul_right {α : Type _} (l : List α)
    (g : α → DensePoly S) (T : DensePoly S) (init : DensePoly S) :
    (l.foldl (fun acc a => acc + g a) init) * T =
      l.foldl (fun acc a => acc + g a * T) (init * T) := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih, DensePoly.mul_add_left_poly]

/-- The conversion is multiplicative: the transported convolution. This
is where `coeff_mul` and the multiplicative ring laws come from. -/
theorem toDense_mul (s t : SparsePoly S) :
    (s * t).toDense = s.toDense * t.toDense := by
  rw [mul_eq_foldl, toDense_foldl_add]
  rw [show s.toDense = s.terms.toList.foldl
      (fun acc a => acc + DensePoly.monomial a.1 a.2) 0 from
    toDense_foldl_monomial s]
  rw [foldl_add_mul_right, DensePoly.zero_mul]
  refine foldl_congr' toDense_zero fun b a _ => ?_
  rw [toDense_mulMonomial]

/-- The multiplicative homomorphism, dense side in. -/
theorem ofDense_mul (p q : DensePoly S) :
    ofDense (p * q) = ofDense p * ofDense q := by
  apply toDense_inj
  rw [toDense_mul, toDense_ofDense, toDense_ofDense, toDense_ofDense]

/-- The convolution, by transport: multiplication agrees with the dense
coefficient sum. -/
theorem coeff_mul (s t : SparsePoly S) (n : Nat) :
    (s * t).coeff n = DensePoly.mulCoeffSum s.toDense t.toDense n := by
  rw [← coeff_toDense (s * t) n, toDense_mul, DensePoly.coeff_mul]

/-! The multiplicative ring laws, by transport through the injective
{name}`toDense`. The dense side proves them at `Lean.Grind.CommRing`,
so that is where they live here too. -/

/-- Multiplication is associative. -/
theorem mul_assoc (s t u : SparsePoly S) : s * t * u = s * (t * u) := by
  apply toDense_inj
  rw [toDense_mul, toDense_mul, toDense_mul, toDense_mul]
  exact DensePoly.mul_assoc_poly _ _ _

/-- Multiplication is commutative. -/
theorem mul_comm (s t : SparsePoly S) : s * t = t * s := by
  apply toDense_inj
  rw [toDense_mul, toDense_mul]
  exact DensePoly.mul_comm_poly _ _

/-- One is a right identity for multiplication. -/
@[simp, grind =] theorem mul_one (s : SparsePoly S) :
    s * 1 = s := by
  apply toDense_inj
  rw [toDense_mul, toDense_one]
  exact DensePoly.mul_one_right_poly _

/-- One is a left identity for multiplication. -/
@[simp, grind =] theorem one_mul (s : SparsePoly S) :
    1 * s = s := by
  rw [mul_comm]
  exact mul_one s

/-- Zero absorbs on the right of multiplication. -/
@[simp, grind =] theorem mul_zero (s : SparsePoly S) : s * 0 = 0 := by
  apply toDense_inj
  rw [toDense_mul, toDense_zero]
  rw [DensePoly.mul_comm_poly]
  exact DensePoly.zero_mul _

/-- Zero absorbs on the left of multiplication. -/
@[simp, grind =] theorem zero_mul (s : SparsePoly S) : 0 * s = 0 := by
  apply toDense_inj
  rw [toDense_mul, toDense_zero]
  exact DensePoly.zero_mul _

/-- Multiplication distributes over addition on the left. -/
theorem left_distrib (s t u : SparsePoly S) :
    s * (t + u) = s * t + s * u := by
  apply toDense_inj
  rw [toDense_mul, toDense_add, toDense_add, toDense_mul, toDense_mul]
  exact DensePoly.mul_add_right_poly _ _ _

/-- Multiplication distributes over addition on the right. -/
theorem right_distrib (s t u : SparsePoly S) :
    (s + t) * u = s * u + t * u := by
  apply toDense_inj
  rw [toDense_mul, toDense_add, toDense_add, toDense_mul, toDense_mul]
  exact DensePoly.mul_add_left_poly _ _ _

/-- The zeroth power is one. -/
@[simp, grind =] theorem pow_zero (s : SparsePoly S) : s ^ 0 = 1 := by
  show pow s 0 = 1
  rw [pow, dif_pos rfl]

private theorem pow_unfold (s : SparsePoly S) (n : Nat) (hn : ¬ n = 0) :
    s ^ n = if n % 2 = 1 then s * (s * s) ^ (n / 2) else (s * s) ^ (n / 2) := by
  show pow s n = _
  rw [pow, dif_neg hn]
  rfl

/-- The conversion respects scalar multiplication. -/
theorem toDense_scale (c : S) (s : SparsePoly S) :
    (scale c s).toDense = DensePoly.scale c s.toDense := by
  apply DensePoly.ext_coeff
  intro f
  rw [coeff_toDense, coeff_scale, DensePoly.coeff_scale_semiring,
    coeff_toDense]

/-- The conversion sends constants to constants. -/
@[simp, grind =] theorem toDense_C (c : S) :
    (C c).toDense = DensePoly.C c := by
  apply DensePoly.ext_coeff
  intro f
  rw [coeff_toDense, coeff_C, DensePoly.coeff_C]
  rfl

/-- Scalar multiplication is multiplication by the constant. -/
theorem scale_eq_C_mul (c : S) (s : SparsePoly S) :
    scale c s = C c * s := by
  apply toDense_inj
  rw [toDense_scale, toDense_mul, toDense_C]
  have hshift0 : DensePoly.shift 0 s.toDense = s.toDense := by
    apply DensePoly.ext_coeff
    intro f
    rw [DensePoly.coeff_shift]
    simp
  have hmono : DensePoly.C c = DensePoly.scale c (DensePoly.C (1 : S)) := by
    apply DensePoly.ext_coeff
    intro f
    rw [DensePoly.coeff_scale_semiring, DensePoly.coeff_C, DensePoly.coeff_C]
    simp only [show (Zero.zero : S) = 0 from rfl]
    grind
  have hC1 : DensePoly.C (1 : S) = DensePoly.monomial 0 1 := by
    apply DensePoly.ext_coeff
    intro f
    rw [DensePoly.coeff_C, DensePoly.coeff_monomial]
  rw [hmono, hC1, ← DensePoly.scale_mul,
    DensePoly.monomial_one_mul_poly_eq_shift, hshift0]

/-- Sparse monomials multiply exponentwise, by transport. -/
theorem monomial_mul_monomial (a b : Nat) (c d : S) :
    monomial a c * monomial b d = monomial (a + b) (c * d) := by
  apply toDense_inj
  rw [toDense_mul, toDense_monomial, toDense_monomial, toDense_monomial]
  exact DensePoly.monomial_mul_monomial a b c d

/-- The power recurrence: with {name}`pow_zero` this characterises the
binary powering completely, and together with {name}`coeff_mul` it is
what the SPEC's `coeff_pow` obligation reduces to. -/
theorem pow_succ (s : SparsePoly S) (n : Nat) : s ^ (n + 1) = s * s ^ n := by
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
      match n with
      | 0 =>
          rw [pow_unfold s 1 (by omega), if_pos rfl, pow_zero, pow_zero]
      | m + 1 =>
          by_cases hodd : (m + 2) % 2 = 1
          · rw [pow_unfold s (m + 2) (by omega), if_pos hodd,
              pow_unfold s (m + 1) (by omega),
              if_neg (show ¬ (m + 1) % 2 = 1 from by omega),
              show (m + 2) / 2 = (m + 1) / 2 from by omega]
          · rw [pow_unfold s (m + 2) (by omega), if_neg hodd,
              pow_unfold s (m + 1) (by omega),
              if_pos (show (m + 1) % 2 = 1 from by omega),
              show (m + 2) / 2 = (m + 1) / 2 + 1 from by omega,
              ih ((m + 1) / 2) (by omega) (s * s), mul_assoc]

end MulRing

/-- On a sorted term list the last stored exponent dominates. -/
theorem exp_le_back {s : SparsePoly R} {t : Nat × R}
    (hback : s.terms.back? = some t) :
    ∀ u ∈ s.terms.toList, u.1 ≤ t.1 := by
  intro u hu
  rw [Array.back?_eq_getElem?] at hback
  obtain ⟨hlt, hval⟩ := Array.getElem?_eq_some_iff.mp hback
  obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.mp hu
  have hi' : i < s.terms.size := by simpa using hi
  rcases Nat.lt_trichotomy i (s.terms.size - 1) with h | h | h
  · have := List.pairwise_iff_getElem.mp s.pairwise_toList i
      (s.terms.size - 1) (by simpa using hi') (by simpa using by omega) h
    rw [hiu] at this
    rw [← hval]
    have harr : s.terms.toList[s.terms.size - 1]'(by simpa using by omega) =
        s.terms[s.terms.size - 1]'(by omega) :=
      Array.getElem_toList _
    rw [harr] at this
    exact Nat.le_of_lt this
  · rw [← hiu]
    have harr : s.terms.toList[i]'hi = s.terms[s.terms.size - 1]'(by omega) := by
      subst h
      exact Array.getElem_toList _
    rw [harr, hval]
    exact Nat.le_refl _
  · omega

/-- The leading coefficient is the coefficient at the last stored
exponent. -/
theorem leadingCoeff_eq_coeff {s : SparsePoly R} {t : Nat × R}
    (hback : s.terms.back? = some t) : s.leadingCoeff = s.coeff t.1 := by
  unfold leadingCoeff
  rw [hback]
  rw [Array.back?_eq_getElem?] at hback
  obtain ⟨hlt, hval⟩ := Array.getElem?_eq_some_iff.mp hback
  refine (coeffList_eq_of_mem s.pairwise_toList ?_ rfl).symm
  rw [← hval]
  exact List.mem_iff_getElem.mpr
    ⟨s.terms.size - 1, by simpa using hlt, Array.getElem_toList _⟩

/-- The dense image stores exactly `degree + 1` coefficients. -/
theorem size_toDense_eq {s : SparsePoly R} {t : Nat × R}
    (hback : s.terms.back? = some t) : s.toDense.size = t.1 + 1 := by
  have hbound : termsBound s.terms = t.1 + 1 := by
    refine Nat.le_antisymm ?_ ?_
    · unfold termsBound
      rw [← Array.foldl_toList]
      refine foldl_max_le 0 (Nat.zero_le _) ?_
      intro u hu
      have := exp_le_back hback u hu
      omega
    · rw [Array.back?_eq_getElem?] at hback
      obtain ⟨hlt, hval⟩ := Array.getElem?_eq_some_iff.mp hback
      unfold termsBound
      rw [← Array.foldl_toList]
      have hmem : t ∈ s.terms.toList := by
        rw [← hval]
        exact List.mem_iff_getElem.mpr
          ⟨s.terms.size - 1, by simpa using hlt, Array.getElem_toList _⟩
      have := exp_lt_foldl_max hmem 0
      omega
  refine Nat.le_antisymm ?_ ?_
  · show (DensePoly.ofCoeffs (coeffsOfTerms s.terms)).size ≤ t.1 + 1
    refine Nat.le_trans (DensePoly.size_ofCoeffs_le _) ?_
    unfold coeffsOfTerms
    rw [← Array.foldl_toList, size_foldl_set, Array.size_replicate, hbound]
    exact Nat.le_refl _
  · have hnz : s.toDense.coeff t.1 ≠ 0 := by
      rw [coeff_toDense, ← leadingCoeff_eq_coeff hback]
      unfold leadingCoeff
      rw [hback]
      rw [Array.back?_eq_getElem?] at hback
      obtain ⟨hlt, hval⟩ := Array.getElem?_eq_some_iff.mp hback
      refine s.canonical.2 t ?_
      rw [← hval]
      exact Array.mem_def.mpr (List.mem_iff_getElem.mpr
        ⟨s.terms.size - 1, by simpa using hlt, Array.getElem_toList _⟩)
    by_cases hle : s.toDense.size ≤ t.1
    · exact absurd (DensePoly.coeff_eq_zero_of_size_le _ hle) hnz
    · omega

/-- The degree boundary transports: a leading coefficient is a
coefficient at the degree, and `coeff_toDense` alone says nothing about
where the degree is. -/
@[simp, grind =] theorem degree?_toDense (s : SparsePoly R) :
    s.toDense.degree? = s.degree? := by
  unfold DensePoly.degree? degree?
  cases hback : s.terms.back? with
  | none =>
      rw [Array.back?_eq_none_iff] at hback
      have hzero : s = 0 := by
        apply ext_coeff
        intro e
        rw [coeff_zero]
        refine coeffList_eq_zero ?_
        intro u hu
        have : u ∈ s.terms := Array.mem_def.mpr hu
        rw [hback] at this
        simp at this
      rw [hzero]
      rw [show (0 : SparsePoly R).toDense = 0 from toDense_zero]
      simp
  | some t =>
      have hsize := size_toDense_eq hback
      rw [dif_neg (by omega)]
      simp only [Option.map_some]
      congr 1
      omega

/-- The leading coefficient transports through the dense conversion. -/
@[simp, grind =] theorem leadingCoeff_toDense (s : SparsePoly R) :
    s.toDense.leadingCoeff = s.leadingCoeff := by
  cases hback : s.terms.back? with
  | none =>
      rw [Array.back?_eq_none_iff] at hback
      unfold leadingCoeff DensePoly.leadingCoeff
      rw [hback]
      have hcoeff : s.toDense.coeff (s.toDense.size - 1) = 0 := by
        rw [coeff_toDense]
        refine coeffList_eq_zero ?_
        intro u hu
        have : u ∈ s.terms := Array.mem_def.mpr hu
        rw [hback] at this
        simp at this
      exact hcoeff
  | some t =>
      have hsize := size_toDense_eq hback
      have : s.toDense.leadingCoeff = s.toDense.coeff (s.toDense.size - 1) :=
        rfl
      rw [this, hsize, coeff_toDense,
        show t.1 + 1 - 1 = t.1 from by omega,
        ← leadingCoeff_eq_coeff hback]

/-- A sparse polynomial is monic when its leading coefficient is `1`,
matching the `DensePoly` convention. -/
def Monic [One R] (s : SparsePoly R) : Prop :=
  s.leadingCoeff = 1

instance [One R] (s : SparsePoly R) : Decidable s.Monic :=
  inferInstanceAs (Decidable (s.leadingCoeff = 1))

/-- Monicity transports through the dense conversion. -/
@[simp] theorem monic_toDense [One R] (s : SparsePoly R) :
    s.toDense.Monic ↔ s.Monic := by
  unfold DensePoly.Monic Monic
  rw [leadingCoeff_toDense]

end SparsePoly

end Hex
