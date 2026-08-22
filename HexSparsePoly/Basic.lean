/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ArrayDecEq

@[expose] public section
set_option backward.proofsInPublic true

/-!
The canonical sparse representation of univariate polynomials: a sorted
array of `(exponent, coefficient)` terms with strictly increasing
exponents and no stored zero coefficients, its constructors, accessors,
and ordered term-iteration API.
-/

namespace Hex

open scoped Hex

universe u v

/-- A term array is canonical when its exponents are strictly increasing
and no stored coefficient is zero. -/
def SparsePolyCanonical {R : Type u} [Zero R] [DecidableEq R]
    (terms : Array (Nat × R)) : Prop :=
  terms.toList.Pairwise (fun a b => a.1 < b.1) ∧ ∀ t ∈ terms, t.2 ≠ 0

/-- A univariate polynomial over `R` as a canonical sorted array of
`(exponent, coefficient)` terms, ascending in exponent. Exponents are
`Nat`, so degrees like `10^6` cost nothing to store; only `toDense`
materialises a coefficient vector.

Per design principle 10, consumers read `terms` through the API
(`coeff`, `support`, `numTerms`, `degree?`, `leadingCoeff`, and the
ordered `toTerms` and `foldTerms`), not directly, so the representation
can change. -/
structure SparsePoly (R : Type u) [Zero R] [DecidableEq R] where
  /-- The stored `(exponent, coefficient)` terms in strictly increasing
  exponent order, with no zero coefficients. -/
  terms : Array (Nat × R)
  /-- Proof that `terms` is canonical. -/
  canonical : SparsePolyCanonical terms

namespace SparsePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/- The comparison routes through `Hex.instDecidableEqArray` from
`HexBasic/ArrayDecEq.lean`, which compares the term `List`s so the kernel
can reduce it across a module boundary, and whose `@[csimp]` redirect
restores the in-place `Array` comparison in compiled code. `Prod`'s
`DecidableEq` is written out in `Init.Core` rather than derived, so it is
not a second stall; the conformance module-boundary probe checks that. -/
instance : DecidableEq (SparsePoly R) := fun a b =>
  match decEq a.terms b.terms with
  | isTrue h =>
      isTrue (by
        cases a with | mk ta ca =>
        cases b with | mk tb cb =>
        cases h
        rfl)
  | isFalse h =>
      isFalse (by
        intro hab
        apply h
        rw [hab])

/-- The zero polynomial: the empty term array. -/
def zero : SparsePoly R where
  terms := #[]
  canonical := by
    constructor
    · simp
    · intro t ht
      simp at ht

instance : Zero (SparsePoly R) where
  zero := zero

/-- The number of stored terms, which is the size of the support. -/
def numTerms (s : SparsePoly R) : Nat :=
  s.terms.size

/-- `true` exactly when the polynomial is zero. -/
def isZero (s : SparsePoly R) : Bool :=
  s.terms.isEmpty

/-- The stored exponents in increasing order; exactly the exponents whose
coefficient is nonzero. -/
def support (s : SparsePoly R) : Array Nat :=
  s.terms.map (·.1)

/-- The degree, or `none` for the zero polynomial. The terms ascend in
exponent, so the degree is the last stored exponent. -/
def degree? (s : SparsePoly R) : Option Nat :=
  s.terms.back?.map (·.1)

/-- The leading coefficient, which is `0` for the zero polynomial. -/
def leadingCoeff (s : SparsePoly R) : R :=
  match s.terms.back? with
  | some t => t.2
  | none => 0

/-- The stored terms in increasing exponent order. -/
def toTerms (s : SparsePoly R) : List (Nat × R) :=
  s.terms.toList

/-- Fold over the stored terms in increasing exponent order, `O(t)`. -/
def foldTerms {β : Type v} (s : SparsePoly R) (f : β → Nat → R → β)
    (init : β) : β :=
  s.terms.foldl (fun acc t => f acc t.1 t.2) init

/-- The coefficient at exponent `e` in a term list: the first stored match,
`0` when absent. On a canonical list the match is unique. -/
def coeffList : List (Nat × R) → Nat → R
  | [], _ => 0
  | t :: ts, e => if t.1 = e then t.2 else coeffList ts e

/-- The coefficient at `e`. Kernel-facing specification (an ordered
`List` lookup); compiled code uses `Hex.SparsePoly.coeffImpl`, the
value-equal binary search selected by `Hex.SparsePoly.coeff_eq_impl`. -/
noncomputable def coeff (s : SparsePoly R) (e : Nat) : R :=
  coeffList s.terms.toList e

/-- Binary-search worker for `coeffImpl`: find the coefficient at
exponent `e` among indices in `[lo, hi)` of a term array sorted by
strictly increasing exponent. -/
def coeffSearch (ts : Array (Nat × R)) (e : Nat) (lo hi : Nat) : R :=
  if _h : lo < hi then
    match ts[(lo + hi) / 2]? with
    | some t =>
        if t.1 = e then t.2
        else if t.1 < e then coeffSearch ts e ((lo + hi) / 2 + 1) hi
        else coeffSearch ts e lo ((lo + hi) / 2)
    | none => 0
  else 0
termination_by hi - lo
decreasing_by all_goals omega

/-- Runtime implementation of {name}`coeff`: binary search on the sorted
term array, `O(log t)` (value-equal to {name}`coeff` by `coeff_eq_impl`,
registered `@[csimp]`). -/
def coeffImpl (s : SparsePoly R) (e : Nat) : R :=
  coeffSearch s.terms e 0 s.terms.size

omit [DecidableEq R] in
/-- A term list with no term at exponent `e` has coefficient `0` there. -/
theorem coeffList_eq_zero {l : List (Nat × R)} {e : Nat}
    (h : ∀ t ∈ l, t.1 ≠ e) : coeffList l e = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      have ha : a.1 ≠ e := h a (List.mem_cons_self ..)
      simp only [coeffList, if_neg ha]
      exact ih fun t ht => h t (List.mem_cons_of_mem _ ht)

omit [DecidableEq R] in
/-- On a list with strictly increasing exponents, a stored term at
exponent `e` is the coefficient there. -/
theorem coeffList_eq_of_mem {l : List (Nat × R)} {t : Nat × R} {e : Nat}
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (ht : t ∈ l) (he : t.1 = e) :
    coeffList l e = t.2 := by
  induction l with
  | nil => cases ht
  | cons a as ih =>
      rw [List.pairwise_cons] at hs
      cases ht with
      | head => simp only [coeffList, if_pos he]
      | tail _ hmem =>
          have hlt : a.1 < t.1 := hs.1 t hmem
          have hne : a.1 ≠ e := by omega
          simp only [coeffList, if_neg hne]
          exact ih hs.2 hmem

omit [DecidableEq R] in
/-- On the range that the sortedness invariant confines the matching
exponent to, the binary search agrees with the ordered `List` lookup. -/
theorem coeffSearch_eq_coeffList (ts : Array (Nat × R)) (e : Nat)
    (hs : ts.toList.Pairwise (fun a b => a.1 < b.1)) (lo hi : Nat)
    (hhi : hi ≤ ts.size)
    (hrange : ∀ i, (h : i < ts.size) → ts[i].1 = e → lo ≤ i ∧ i < hi) :
    coeffSearch ts e lo hi = coeffList ts.toList e := by
  unfold coeffSearch
  split
  · rename_i hlt
    have hmid : (lo + hi) / 2 < ts.size := by omega
    split
    · rename_i t heq
      obtain ⟨_, hval⟩ := Array.getElem?_eq_some_iff.mp heq
      subst hval
      by_cases h1 : (ts[(lo + hi) / 2]).1 = e
      · rw [if_pos h1]
        refine (coeffList_eq_of_mem hs ?_ h1).symm
        exact List.mem_iff_getElem.mpr
          ⟨(lo + hi) / 2, by simpa using hmid, by simp⟩
      · rw [if_neg h1]
        have hidx : ∀ i j, (hij : i < j) → (hj : j < ts.size) →
            (ts[i]'(by omega)).1 < ts[j].1 := by
          intro i j hij hj
          have := List.pairwise_iff_getElem.mp hs i j
            (by simpa using by omega) (by simpa using hj) hij
          simpa using this
        by_cases h2 : (ts[(lo + hi) / 2]).1 < e
        · rw [if_pos h2]
          refine coeffSearch_eq_coeffList ts e hs _ _ hhi ?_
          intro i hisz hie
          obtain ⟨-, hupper⟩ := hrange i hisz hie
          refine ⟨?_, hupper⟩
          rcases Nat.lt_trichotomy i ((lo + hi) / 2) with hlt' | heq' | hgt'
          · have := hidx i ((lo + hi) / 2) hlt' hmid
            omega
          · subst heq'
            exact absurd hie h1
          · omega
        · rw [if_neg h2]
          refine coeffSearch_eq_coeffList ts e hs _ _ (by omega) ?_
          intro i hisz hie
          obtain ⟨hlower, -⟩ := hrange i hisz hie
          refine ⟨hlower, ?_⟩
          rcases Nat.lt_trichotomy ((lo + hi) / 2) i with hlt' | heq' | hgt'
          · have := hidx ((lo + hi) / 2) i hlt' hisz
            omega
          · subst heq'
            exact absurd hie h1
          · omega
    · rename_i heq
      have := Array.getElem?_eq_none_iff.mp heq
      omega
  · rename_i hnlt
    refine (coeffList_eq_zero ?_).symm
    intro t htmem hte
    obtain ⟨i, hilen, hit⟩ := List.mem_iff_getElem.mp htmem
    have hisz : i < ts.size := by simpa using hilen
    have : ts[i].1 = e := by
      rw [← Array.getElem_toList (by simpa using hisz)]
      rw [hit]
      exact hte
    have := hrange i hisz this
    omega
termination_by hi - lo
decreasing_by all_goals omega

/-- The kernel-facing `List` lookup and the binary search compute the same
coefficient on every canonical polynomial. -/
theorem coeff_eq_coeffImpl (s : SparsePoly R) (e : Nat) :
    coeff s e = coeffImpl s e := by
  unfold coeff coeffImpl
  exact (coeffSearch_eq_coeffList s.terms e s.canonical.1 0 s.terms.size
    (Nat.le_refl _) (fun i h _ => ⟨Nat.zero_le _, h⟩)).symm

/-- Register the binary search as the compiled implementation of
{name}`coeff`. -/
@[csimp]
theorem coeff_eq_impl : @coeff = @coeffImpl := by
  funext R _ _ s e
  exact coeff_eq_coeffImpl s e

/-- Linear canonicality check on a term list: adjacent exponents strictly
increase and no stored coefficient is zero. The pairwise form of the
invariant is the one induction wants; this adjacent form is the one an
`O(t)` check wants, and `isCanonicalList_iff` is the equivalence. -/
def isCanonicalList : List (Nat × R) → Bool
  | [] => true
  | [t] => decide (t.2 ≠ 0)
  | a :: b :: ts =>
      decide (a.2 ≠ 0) && decide (a.1 < b.1) && isCanonicalList (b :: ts)

/-- The adjacent-pair check decides the pairwise invariant: `<` on `Nat`
is transitive, so strict increase between neighbours is strict increase
between every pair. -/
theorem isCanonicalList_iff {l : List (Nat × R)} :
    isCanonicalList l = true ↔
      (l.Pairwise (fun a b => a.1 < b.1) ∧ ∀ t ∈ l, t.2 ≠ 0) := by
  induction l with
  | nil => simp [isCanonicalList]
  | cons a as ih =>
      cases as with
      | nil => simp [isCanonicalList]
      | cons b bs =>
          simp only [isCanonicalList, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨ha0, hab⟩, hrest⟩
            obtain ⟨hpw, hnz⟩ := ih.mp hrest
            refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_⟩
            · intro t ht
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact hab
              · have hb : b.1 < t.1 := (List.pairwise_cons.mp hpw).1 t ht'
                omega
            · intro t ht
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact ha0
              · exact hnz t ht'
          · rintro ⟨hpw, hnz⟩
            rw [List.pairwise_cons] at hpw
            refine ⟨⟨hnz a (List.mem_cons_self ..),
              hpw.1 b (List.mem_cons_self ..)⟩, ?_⟩
            exact ih.mpr ⟨hpw.2, fun t ht => hnz t (List.mem_cons_of_mem _ ht)⟩

/-- Linear canonicality check on a term array, `O(t)`. -/
def isCanonical (ts : Array (Nat × R)) : Bool :=
  isCanonicalList ts.toList

/-- The `O(t)` adjacent-pair check decides {name}`SparsePolyCanonical`. -/
theorem isCanonical_iff {ts : Array (Nat × R)} :
    isCanonical ts = true ↔ SparsePolyCanonical ts := by
  unfold isCanonical SparsePolyCanonical
  rw [isCanonicalList_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t ht => h2 t (Array.mem_def.mp ht)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t ht => h2 t (Array.mem_def.mpr ht)⟩

instance (ts : Array (Nat × R)) : Decidable (SparsePolyCanonical ts) :=
  decidable_of_iff _ isCanonical_iff

omit [DecidableEq R] in
/-- A sorted term list has coefficient `0` below its head exponent. -/
theorem coeffList_eq_zero_of_lt_head {b : Nat × R} {bs : List (Nat × R)}
    {e : Nat} (hs : (b :: bs).Pairwise (fun x y => x.1 < y.1))
    (he : e < b.1) : coeffList (b :: bs) e = 0 := by
  refine coeffList_eq_zero ?_
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht'
  · omega
  · have := (List.pairwise_cons.mp hs).1 t ht'
    omega

omit [DecidableEq R] in
/-- The tail of a sorted term list has coefficient `0` at the head's
exponent: strict increase means the head's exponent never recurs. -/
theorem coeffList_tail_eq_zero {a : Nat × R} {as : List (Nat × R)}
    (hs : (a :: as).Pairwise (fun x y => x.1 < y.1)) :
    coeffList as a.1 = 0 := by
  refine coeffList_eq_zero ?_
  intro t ht
  have := (List.pairwise_cons.mp hs).1 t ht
  omega

omit [DecidableEq R] in
/-- Two canonical term lists with the same coefficient function are equal.
This is the list-level content of `SparsePoly.ext_coeff`: strict exponent
increase forbids duplicates and fixes the order, and the zero-free
condition makes every stored term observable. -/
theorem coeffList_ext {l₁ l₂ : List (Nat × R)}
    (hs₁ : l₁.Pairwise (fun a b => a.1 < b.1))
    (hs₂ : l₂.Pairwise (fun a b => a.1 < b.1))
    (hnz₁ : ∀ t ∈ l₁, t.2 ≠ 0) (hnz₂ : ∀ t ∈ l₂, t.2 ≠ 0)
    (h : ∀ e, coeffList l₁ e = coeffList l₂ e) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons b bs =>
          have hb := h b.1
          simp only [coeffList] at hb
          exact absurd hb.symm (hnz₂ b (List.mem_cons_self ..))
  | cons a as ih =>
      cases l₂ with
      | nil =>
          have ha := h a.1
          simp only [coeffList] at ha
          exact absurd ha (hnz₁ a (List.mem_cons_self ..))
      | cons b bs =>
          have hexp : a.1 = b.1 := by
            rcases Nat.lt_trichotomy a.1 b.1 with hlt | heq | hgt
            · exfalso
              have ha := h a.1
              rw [coeffList_eq_zero_of_lt_head hs₂ hlt] at ha
              simp only [coeffList] at ha
              exact hnz₁ a (List.mem_cons_self ..) ha
            · exact heq
            · exfalso
              have hb := h b.1
              rw [coeffList_eq_zero_of_lt_head hs₁ hgt] at hb
              simp only [coeffList] at hb
              exact hnz₂ b (List.mem_cons_self ..) hb.symm
          have hcoeff : a.2 = b.2 := by
            have ha := h a.1
            simp only [coeffList, if_pos hexp.symm] at ha
            exact ha
          have htail : as = bs := by
            refine ih (List.pairwise_cons.mp hs₁).2
              (List.pairwise_cons.mp hs₂).2
              (fun t ht => hnz₁ t (List.mem_cons_of_mem _ ht))
              (fun t ht => hnz₂ t (List.mem_cons_of_mem _ ht)) ?_
            intro e
            by_cases heq : e = a.1
            · subst heq
              rw [coeffList_tail_eq_zero hs₁, hexp, coeffList_tail_eq_zero hs₂]
            · have hna : ¬(a.1 = e) := fun hc => heq hc.symm
              have hnb : ¬(b.1 = e) := by
                intro hc
                exact heq (by omega)
              have he := h e
              simp only [coeffList, if_neg hna, if_neg hnb] at he
              exact he
          rw [Prod.ext hexp hcoeff, htail]

/-- Extensionality: canonical representations of the same coefficient
function are equal. Everything below is proved from this. -/
@[ext] theorem ext_coeff {s t : SparsePoly R}
    (h : ∀ e, s.coeff e = t.coeff e) : s = t := by
  cases s with | mk ts hts =>
  cases t with | mk tt htt =>
  have hlist : ts.toList = tt.toList := by
    refine coeffList_ext hts.1 htt.1 ?_ ?_ h
    · intro t ht
      exact hts.2 t (Array.mem_def.mpr ht)
    · intro t ht
      exact htt.2 t (Array.mem_def.mpr ht)
  cases Array.toList_inj.mp hlist
  rfl

end SparsePoly

end Hex
