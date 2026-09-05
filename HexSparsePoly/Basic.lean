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
def SparsePolyCanonical {R : Type u} [Zero R]
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
      simp only [coeffList, ite_eq_right ha]
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
      | head => simp only [coeffList, ite_eq_left he]
      | tail _ hmem =>
          have hlt : a.1 < t.1 := hs.1 t hmem
          have hne : a.1 ≠ e := by omega
          simp only [coeffList, ite_eq_right hne]
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
      · rw [ite_eq_left h1]
        refine (coeffList_eq_of_mem hs ?_ h1).symm
        exact List.mem_iff_getElem.mpr
          ⟨(lo + hi) / 2, by simpa using hmid, by simp⟩
      · rw [ite_eq_right h1]
        have hidx : ∀ i j, (hij : i < j) → (hj : j < ts.size) →
            (ts[i]'(by omega)).1 < ts[j].1 := by
          intro i j hij hj
          have := List.pairwise_iff_getElem.mp hs i j
            (by simpa using by omega) (by simpa using hj) hij
          simpa using this
        by_cases h2 : (ts[(lo + hi) / 2]).1 < e
        · rw [ite_eq_left h2]
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
        · rw [ite_eq_right h2]
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
            simp only [coeffList, ite_eq_left hexp.symm] at ha
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
              simp only [coeffList, ite_eq_right hna, ite_eq_right hnb] at he
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

/-- The coefficient stored at an exponent after adding `c` to a stored
coefficient `d` there, where `d = 0` encodes "absent": a zero sum (and a
zero insertion) leaves the exponent absent, encoded as `0` again. On a
canonical representation the stored coefficient is `0` exactly when the
term is absent, so this is the whole observable effect of `addTerm` at
its target exponent. -/
def addCoeff [Add R] (d c : R) : R :=
  if d = 0 then (if c = 0 then 0 else c)
  else (if d + c = 0 then 0 else d + c)

/-- Ordered insert of `c · x^e` into a sorted term list: insert a new
term when `c ≠ 0` and `e` is absent, replace the stored coefficient by
the sum when the sum is nonzero, and delete the term when the sum is
zero. -/
def addTermList [Add R] : List (Nat × R) → Nat → R → List (Nat × R)
  | [], e, c => if c = 0 then [] else [(e, c)]
  | t :: ts, e, c =>
      if e < t.1 then (if c = 0 then t :: ts else (e, c) :: t :: ts)
      else if t.1 = e then
        (if t.2 + c = 0 then ts else (t.1, t.2 + c) :: ts)
      else t :: addTermList ts e c

/-- Every exponent stored after an insert was stored before or is the
inserted one. -/
theorem exp_mem_addTermList [Add R] {l : List (Nat × R)} {e : Nat} {c : R}
    {t : Nat × R} (ht : t ∈ addTermList l e c) :
    t.1 = e ∨ ∃ u ∈ l, t.1 = u.1 := by
  induction l generalizing t with
  | nil =>
      simp only [addTermList] at ht
      split at ht
      · cases ht
      · rcases List.mem_cons.mp ht with rfl | h'
        · exact Or.inl rfl
        · cases h'
  | cons a as ih =>
      simp only [addTermList] at ht
      split at ht
      · split at ht
        · exact Or.inr ⟨t, ht, rfl⟩
        · rcases List.mem_cons.mp ht with rfl | h'
          · exact Or.inl rfl
          · exact Or.inr ⟨t, h', rfl⟩
      · split at ht
        · split at ht
          · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, rfl⟩
          · rcases List.mem_cons.mp ht with rfl | h'
            · exact Or.inr ⟨a, List.mem_cons_self .., rfl⟩
            · exact Or.inr ⟨t, List.mem_cons_of_mem _ h', rfl⟩
        · rcases List.mem_cons.mp ht with rfl | h'
          · exact Or.inr ⟨t, List.mem_cons_self .., rfl⟩
          · rcases ih h' with h | ⟨u, hu, he⟩
            · exact Or.inl h
            · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, he⟩

/-- The ordered insert preserves both halves of the canonical
invariant. This is the proof the whole library rests on: every
specialised operation re-establishes what {name}`addTermList` establishes
here for arbitrary input. -/
theorem addTermList_canonical [Add R] {l : List (Nat × R)}
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (hnz : ∀ t ∈ l, t.2 ≠ 0)
    (e : Nat) (c : R) :
    (addTermList l e c).Pairwise (fun a b => a.1 < b.1) ∧
      ∀ t ∈ addTermList l e c, t.2 ≠ 0 := by
  induction l with
  | nil =>
      simp only [addTermList]
      split
      · simp
      · rename_i hc
        constructor
        · simp
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | h'
          · exact hc
          · cases h'
  | cons a as ih =>
      rw [List.pairwise_cons] at hs
      obtain ⟨hpw, hnztail⟩ :=
        ih hs.2 (fun t ht => hnz t (List.mem_cons_of_mem _ ht))
      have hnza : a.2 ≠ 0 := hnz a (List.mem_cons_self ..)
      simp only [addTermList]
      split
      · rename_i hlt
        split
        · exact ⟨List.pairwise_cons.mpr ⟨hs.1, hs.2⟩, hnz⟩
        · rename_i hc
          refine ⟨List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr hs⟩, ?_⟩
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | h'
            · exact hlt
            · have := hs.1 t h'
              omega
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | h'
            · exact hc
            · exact hnz t h'
      · split
        · rename_i hnlt heq
          split
          · exact ⟨hs.2, fun t ht => hnz t (List.mem_cons_of_mem _ ht)⟩
          · rename_i hsum
            refine ⟨List.pairwise_cons.mpr ⟨hs.1, hs.2⟩, ?_⟩
            intro t ht
            rcases List.mem_cons.mp ht with rfl | h'
            · exact hsum
            · exact hnz t (List.mem_cons_of_mem _ h')
        · rename_i hnlt hne
          refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_⟩
          · intro t ht
            rcases exp_mem_addTermList ht with h | ⟨u, hu, hue⟩
            · omega
            · have := hs.1 u hu
              omega
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | h'
            · exact hnza
            · exact hnztail t h'

/-- Add `c · x^e` to `s`, combining with an existing term at `e` and
deleting the term when the sum is zero.

Kernel-facing specification (a single ordered `List` insert); compiled
code uses `Hex.SparsePoly.addTermImpl`, the value-equal binary search and
in-place array update selected by `Hex.SparsePoly.addTerm_eq_impl`. -/
noncomputable def addTerm [Add R] (s : SparsePoly R) (e : Nat) (c : R) :
    SparsePoly R where
  terms := (addTermList s.terms.toList e c).toArray
  canonical := by
    obtain ⟨h1, h2⟩ := addTermList_canonical s.canonical.1
      (fun t ht => s.canonical.2 t (Array.mem_def.mpr ht)) e c
    exact ⟨by simpa using h1, fun t ht => h2 t (by simpa using Array.mem_def.mp ht)⟩

/-- Equal term arrays give equal polynomials: the proof field is
irrelevant. -/
theorem eq_of_terms_eq {s t : SparsePoly R} (h : s.terms = t.terms) :
    s = t := by
  cases s with | mk ts hts =>
  cases t with | mk tt htt =>
  cases h
  rfl

/-- The whole observable effect of the ordered insert: the coefficient
at `e` becomes {name}`addCoeff` of the stored coefficient and `c`, and
every other coefficient is unchanged. -/
theorem coeffList_addTermList [Add R] {l : List (Nat × R)}
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (hnz : ∀ t ∈ l, t.2 ≠ 0)
    (e : Nat) (c : R) (f : Nat) :
    coeffList (addTermList l e c) f =
      if f = e then addCoeff (coeffList l e) c else coeffList l f := by
  induction l with
  | nil =>
      by_cases hc : c = 0
      · by_cases hf : f = e
        · subst hf
          simp [addTermList, coeffList, addCoeff, hc]
        · simp [addTermList, coeffList, hc, hf]
      · by_cases hf : f = e
        · subst hf
          simp [addTermList, coeffList, addCoeff, hc]
        · have hef : ¬e = f := fun h => hf h.symm
          simp [addTermList, coeffList, hc, hef, hf]
  | cons a as ih =>
      rw [List.pairwise_cons] at hs
      have hnza : a.2 ≠ 0 := hnz a (List.mem_cons_self ..)
      have hnztail : ∀ t ∈ as, t.2 ≠ 0 :=
        fun t ht => hnz t (List.mem_cons_of_mem _ ht)
      rcases Nat.lt_trichotomy e a.1 with hlt | heq | hgt
      · -- `e` sits below the head: insert in front (or do nothing).
        have hcoeff_e : coeffList (a :: as) e = 0 :=
          coeffList_eq_zero_of_lt_head (List.pairwise_cons.mpr hs) hlt
        by_cases hc : c = 0
        · simp only [addTermList, ite_eq_left hlt, ite_eq_left hc]
          by_cases hf : f = e
          · subst hf
            rw [ite_eq_left rfl, hcoeff_e, addCoeff]
            simp [hc]
          · rw [ite_eq_right hf]
        · simp only [addTermList, ite_eq_left hlt, ite_eq_right hc]
          by_cases hf : f = e
          · subst hf
            rw [ite_eq_left rfl, hcoeff_e, addCoeff]
            simp only [coeffList]
            simp [hc]
          · rw [ite_eq_right hf]
            simp only [coeffList]
            rw [ite_eq_right (fun h : e = f => hf h.symm)]
      · -- the head is the target: combine or delete.
        have hcoeff_e : coeffList (a :: as) e = a.2 := by
          simp only [coeffList, ite_eq_left heq.symm]
        have htail_e : coeffList as e = 0 := by
          have := coeffList_tail_eq_zero
            (a := a) (as := as) (List.pairwise_cons.mpr hs)
          rw [← heq] at this
          exact this
        have hnotlt : ¬ e < a.1 := by omega
        by_cases hsum : a.2 + c = 0
        · simp only [addTermList, ite_eq_right hnotlt, ite_eq_left heq.symm, ite_eq_left hsum]
          by_cases hf : f = e
          · subst hf
            rw [ite_eq_left rfl, hcoeff_e, addCoeff, ite_eq_right hnza, ite_eq_left hsum,
              htail_e]
          · rw [ite_eq_right hf]
            simp only [coeffList]
            rw [ite_eq_right (fun h : a.1 = f => hf (by omega))]
        · simp only [addTermList, ite_eq_right hnotlt, ite_eq_left heq.symm, ite_eq_right hsum]
          by_cases hf : f = e
          · subst hf
            rw [ite_eq_left rfl, hcoeff_e, addCoeff, ite_eq_right hnza, ite_eq_right hsum]
            simp only [coeffList, ite_eq_left heq.symm]
          · rw [ite_eq_right hf]
            simp only [coeffList]
            rw [ite_eq_right (fun h : a.1 = f => hf (by omega)),
              ite_eq_right (fun h : a.1 = f => hf (by omega))]
      · -- the head sits below the target: recurse into the tail.
        have hnotlt : ¬ e < a.1 := by omega
        have hne : ¬ a.1 = e := by omega
        simp only [addTermList, ite_eq_right hnotlt, ite_eq_right hne]
        by_cases hf : f = e
        · subst hf
          rw [ite_eq_left rfl]
          simp only [coeffList, ite_eq_right hne]
          rw [ih hs.2 hnztail, ite_eq_left rfl]
        · rw [ite_eq_right hf]
          simp only [coeffList]
          by_cases haf : a.1 = f
          · rw [ite_eq_left haf, ite_eq_left haf]
          · rw [ite_eq_right haf, ite_eq_right haf, ih hs.2 hnztail, ite_eq_right hf]

/-- Coefficient description of {name}`addTerm`: {name}`addCoeff` at the
target exponent, unchanged elsewhere. -/
theorem coeff_addTerm [Add R] (s : SparsePoly R) (e : Nat) (c : R)
    (f : Nat) :
    (s.addTerm e c).coeff f =
      if f = e then addCoeff (s.coeff e) c else s.coeff f := by
  unfold coeff addTerm
  exact coeffList_addTermList s.canonical.1
    (fun t ht => s.canonical.2 t (Array.mem_def.mpr ht)) e c f

/-- Binary-search worker for `addTermImpl`: the least index in
`[lo, hi)` whose exponent is at least `e` (or `hi` when there is none),
on an array sorted by strictly increasing exponent. -/
def lowerBound (ts : Array (Nat × R)) (e : Nat) (lo hi : Nat) : Nat :=
  if _h : lo < hi then
    match ts[(lo + hi) / 2]? with
    | some t =>
        if t.1 < e then lowerBound ts e ((lo + hi) / 2 + 1) hi
        else lowerBound ts e lo ((lo + hi) / 2)
    | none => lo
  else lo
termination_by hi - lo
decreasing_by all_goals omega

omit [DecidableEq R] in
omit [Zero R] in
/-- On a sorted range, {name}`lowerBound` splits the indices: every
exponent below the returned position is below `e`, every exponent at or
beyond it is at least `e`. -/
theorem lowerBound_spec (ts : Array (Nat × R)) (e : Nat)
    (hs : ts.toList.Pairwise (fun a b => a.1 < b.1)) (lo hi : Nat)
    (hlohi : lo ≤ hi) (hhi : hi ≤ ts.size)
    (hbelow : ∀ i, (h : i < ts.size) → i < lo → ts[i].1 < e)
    (habove : ∀ i, (h : i < ts.size) → hi ≤ i → e ≤ ts[i].1) :
    lo ≤ lowerBound ts e lo hi ∧ lowerBound ts e lo hi ≤ hi ∧
      (∀ i, (h : i < ts.size) → i < lowerBound ts e lo hi → ts[i].1 < e) ∧
      (∀ i, (h : i < ts.size) → lowerBound ts e lo hi ≤ i → e ≤ ts[i].1) := by
  have hidx : ∀ i j, (hij : i < j) → (hj : j < ts.size) →
      (ts[i]'(by omega)).1 < ts[j].1 := by
    intro i j hij hj
    have := List.pairwise_iff_getElem.mp hs i j
      (by simpa using by omega) (by simpa using hj) hij
    simpa using this
  unfold lowerBound
  split
  · rename_i hlt
    have hmid : (lo + hi) / 2 < ts.size := by omega
    split
    · rename_i t heq
      obtain ⟨_, hval⟩ := Array.getElem?_eq_some_iff.mp heq
      subst hval
      by_cases h1 : (ts[(lo + hi) / 2]).1 < e
      · rw [ite_eq_left h1]
        have := lowerBound_spec ts e hs ((lo + hi) / 2 + 1) hi
          (by omega) hhi ?_ habove
        · exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩
        · intro i hi' hilt
          rcases Nat.lt_trichotomy i ((lo + hi) / 2) with h' | h' | h'
          · have := hidx i ((lo + hi) / 2) h' hmid
            omega
          · subst h'
            exact h1
          · omega
      · rw [ite_eq_right h1]
        have := lowerBound_spec ts e hs lo ((lo + hi) / 2)
          (by omega) (by omega) hbelow ?_
        · exact ⟨this.1, by omega, this.2.2.1, this.2.2.2⟩
        · intro i hi' hile
          rcases Nat.lt_trichotomy ((lo + hi) / 2) i with h' | h' | h'
          · have := hidx ((lo + hi) / 2) i h' hi'
            omega
          · subst h'
            omega
          · omega
    · rename_i heq
      have := Array.getElem?_eq_none_iff.mp heq
      omega
  · rename_i hnlt
    have hlohi' : lo = hi := by omega
    subst hlohi'
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun i h hi => hbelow i h hi,
      fun i h hi => habove i h hi⟩
termination_by hi - lo
decreasing_by all_goals omega

omit [DecidableEq R] in
omit [Zero R] in
/-- {name}`lowerBound` never exceeds `hi`, with no sortedness needed:
this is what makes the insertion index valid. -/
theorem lowerBound_le (ts : Array (Nat × R)) (e : Nat) (lo hi : Nat)
    (h : lo ≤ hi) : lowerBound ts e lo hi ≤ hi := by
  unfold lowerBound
  split
  · rename_i hlt
    split
    · rename_i t heq
      split
      · exact lowerBound_le ts e ((lo + hi) / 2 + 1) hi (by omega)
      · exact Nat.le_trans
          (lowerBound_le ts e lo ((lo + hi) / 2) (by omega)) (by omega)
    · omega
  · omega
termination_by hi - lo
decreasing_by all_goals omega

/-- The ordered insert, described at the splice position: with `p`
splitting the sorted list into exponents below `e` and at least `e`, the
insert is an index-`p` erase, set, insert, or append. This is the
list-level shape that the in-place array implementation mirrors. -/
theorem addTermList_splice [Add R] {l : List (Nat × R)} {e : Nat}
    {p : Nat}
    (hbelow : ∀ i, (h : i < l.length) → i < p → l[i].1 < e)
    (habove : ∀ i, (h : i < l.length) → p ≤ i → e ≤ l[i].1) (c : R) :
    addTermList l e c =
      match l[p]? with
      | some t =>
          if t.1 = e then
            (if t.2 + c = 0 then l.eraseIdx p else l.set p (e, t.2 + c))
          else (if c = 0 then l else l.insertIdx p (e, c))
      | none => if c = 0 then l else l ++ [(e, c)] := by
  induction l generalizing p with
  | nil =>
      simp only [addTermList, List.getElem?_nil]
      rfl
  | cons a as ih =>
      cases p with
      | zero =>
          have hae : e ≤ a.1 := habove 0 (by simp) (Nat.zero_le _)
          simp only [List.getElem?_cons_zero]
          by_cases heq : a.1 = e
          · have hnotlt : ¬ e < a.1 := by omega
            simp only [addTermList, ite_eq_right hnotlt, ite_eq_left heq]
            rw [heq]
            simp
          · have hlt : e < a.1 := by omega
            simp only [addTermList, ite_eq_left hlt, ite_eq_right heq]
            by_cases hc : c = 0
            · rw [ite_eq_left hc, ite_eq_left hc]
            · rw [ite_eq_right hc, ite_eq_right hc]
              rfl
      | succ q =>
          have ha : a.1 < e := hbelow 0 (by simp) (Nat.succ_pos _)
          have hnotlt : ¬ e < a.1 := by omega
          have hne : ¬ a.1 = e := by omega
          simp only [addTermList, ite_eq_right hnotlt, ite_eq_right hne,
            List.getElem?_cons_succ]
          rw [ih (p := q) ?_ ?_]
          · cases has : as[q]? with
            | some t =>
                simp only
                by_cases hte : t.1 = e
                · rw [ite_eq_left hte, ite_eq_left hte]
                  by_cases hsum : t.2 + c = 0
                  · rw [ite_eq_left hsum, ite_eq_left hsum, List.eraseIdx_cons_succ]
                  · rw [ite_eq_right hsum, ite_eq_right hsum, List.set_cons_succ]
                · rw [ite_eq_right hte, ite_eq_right hte]
                  by_cases hc : c = 0
                  · rw [ite_eq_left hc, ite_eq_left hc]
                  · rw [ite_eq_right hc, ite_eq_right hc, List.insertIdx_succ_cons]
            | none =>
                simp only
                by_cases hc : c = 0
                · rw [ite_eq_left hc, ite_eq_left hc]
                · rw [ite_eq_right hc, ite_eq_right hc, List.cons_append]
          · intro i h hip
            have := hbelow (i + 1) (by simpa using by omega) (by omega)
            simpa using this
          · intro i h hpi
            have := habove (i + 1) (by simpa using by omega) (by omega)
            simpa using this

/-- In-place array worker for `addTermImpl`: binary search for the
splice position, then a single erase, set, insert, or push. `O(log t)`
search plus an `O(t)` shift. -/
def addTermArray [Add R] (ts : Array (Nat × R)) (e : Nat) (c : R) :
    Array (Nat × R) :=
  match hp : ts[lowerBound ts e 0 ts.size]? with
  | some t =>
      if t.1 = e then
        if t.2 + c = 0 then
          ts.eraseIdx (lowerBound ts e 0 ts.size)
            (by obtain ⟨h, -⟩ := Array.getElem?_eq_some_iff.mp hp; exact h)
        else
          ts.set (lowerBound ts e 0 ts.size) (e, t.2 + c)
            (by obtain ⟨h, -⟩ := Array.getElem?_eq_some_iff.mp hp; exact h)
      else if c = 0 then ts
      else
        ts.insertIdx (lowerBound ts e 0 ts.size) (e, c)
          (lowerBound_le ts e 0 ts.size (Nat.zero_le _))
  | none =>
      if c = 0 then ts else ts.push (e, c)

/-- On a sorted array the in-place worker computes exactly the ordered
`List` insert. -/
theorem addTermArray_eq [Add R] {ts : Array (Nat × R)}
    (hs : ts.toList.Pairwise (fun a b => a.1 < b.1)) (e : Nat) (c : R) :
    addTermArray ts e c = (addTermList ts.toList e c).toArray := by
  obtain ⟨-, -, hbelow, habove⟩ := lowerBound_spec ts e hs 0 ts.size
    (Nat.zero_le _) (Nat.le_refl _) (by omega) (by intro i h hi; omega)
  have hsplice := addTermList_splice (l := ts.toList) (e := e)
    (p := lowerBound ts e 0 ts.size)
    (fun i h hip => hbelow i (by simpa using h) hip)
    (fun i h hpi => habove i (by simpa using h) hpi) c
  rw [← Array.toList_inj]
  simp only [hsplice]
  unfold addTermArray
  split
  · rename_i t hp
    have hp' : ts.toList[lowerBound ts e 0 ts.size]? = some t := by
      rw [Array.getElem?_toList, hp]
    simp only [hp']
    by_cases hte : t.1 = e
    · rw [ite_eq_left hte, ite_eq_left hte]
      by_cases hsum : t.2 + c = 0
      · rw [ite_eq_left hsum, ite_eq_left hsum, Array.toList_eraseIdx]
      · rw [ite_eq_right hsum, ite_eq_right hsum, Array.toList_set]
    · rw [ite_eq_right hte, ite_eq_right hte]
      by_cases hc : c = 0
      · rw [ite_eq_left hc, ite_eq_left hc]
      · rw [ite_eq_right hc, ite_eq_right hc, Array.toList_insertIdx]
  · rename_i hp
    have hp' : ts.toList[lowerBound ts e 0 ts.size]? = none := by
      rw [Array.getElem?_toList, hp]
    simp only [hp']
    by_cases hc : c = 0
    · rw [ite_eq_left hc, ite_eq_left hc]
    · rw [ite_eq_right hc, ite_eq_right hc, Array.toList_push]

/-- Runtime implementation of {name}`addTerm`: binary search and one
in-place array splice (value-equal to {name}`addTerm` by
`addTerm_eq_impl`, registered `@[csimp]`). -/
def addTermImpl [Add R] (s : SparsePoly R) (e : Nat) (c : R) :
    SparsePoly R where
  terms := addTermArray s.terms e c
  canonical := by
    rw [addTermArray_eq s.canonical.1]
    exact (s.addTerm e c).canonical

/-- The ordered-`List` specification and the in-place splice compute the
same polynomial. -/
theorem addTerm_eq_addTermImpl [Add R] (s : SparsePoly R) (e : Nat)
    (c : R) : addTerm s e c = addTermImpl s e c :=
  eq_of_terms_eq (addTermArray_eq s.canonical.1 e c).symm

/-- Register the in-place splice as the compiled implementation of
{name}`addTerm`. -/
@[csimp]
theorem addTerm_eq_impl : @addTerm = @addTermImpl := by
  funext R _ _ _ s e c
  exact addTerm_eq_addTermImpl s e c

/-- The canonical polynomial with the given terms. Exponents may repeat
and may appear in any order, and coefficients at equal exponents are
summed and zero results are dropped.

Kernel-facing specification (a fold of {name}`addTerm`); compiled code
uses `Hex.SparsePoly.ofTermsImpl`, the value-equal stable sort and
combining pass selected by `Hex.SparsePoly.ofTerms_eq_impl`. -/
noncomputable def ofTerms [Add R] (ts : Array (Nat × R)) : SparsePoly R :=
  ts.foldl (fun s t => s.addTerm t.1 t.2) 0

/-- The zero polynomial has zero coefficients. -/
@[simp, grind =] theorem coeff_zero (e : Nat) :
    (0 : SparsePoly R).coeff e = 0 :=
  rfl

/-- Coefficient description of the {name}`addTerm` fold, with no algebra
assumed: at each exponent it is the {name}`addCoeff` fold, in input
order, over the terms at that exponent. -/
theorem coeff_foldl_addTerm [Add R] (l : List (Nat × R))
    (s : SparsePoly R) (e : Nat) :
    (l.foldl (fun s t => s.addTerm t.1 t.2) s).coeff e =
      (l.filter (fun t => t.1 = e)).foldl (fun acc t => addCoeff acc t.2)
        (s.coeff e) := by
  induction l generalizing s with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hte : t.1 = e
      · rw [List.filter_cons_of_pos (by simpa using hte),
          List.foldl_cons, coeff_addTerm, ite_eq_left hte.symm, hte]
      · rw [List.filter_cons_of_neg (by simpa using hte),
          coeff_addTerm, ite_eq_right (fun h : e = t.1 => hte h.symm)]

/-- Coefficient description of {name}`ofTerms`, with no algebra assumed. -/
theorem coeff_ofTerms_addCoeff [Add R] (ts : Array (Nat × R)) (e : Nat) :
    (ofTerms ts).coeff e =
      (ts.toList.filter (fun t => t.1 = e)).foldl
        (fun acc t => addCoeff acc t.2) 0 := by
  unfold ofTerms
  rw [← Array.foldl_toList]
  exact coeff_foldl_addTerm ts.toList 0 e

/-- Once `0` is a left identity for `+`, the delete-and-reinsert step is
plain addition. -/
theorem addCoeff_eq_add [Add R] (hzero : ∀ c : R, 0 + c = c) (d c : R) :
    addCoeff d c = d + c := by
  unfold addCoeff
  by_cases hd : d = 0
  · subst hd
    by_cases hc : c = 0
    · subst hc
      rw [ite_eq_left rfl, ite_eq_left rfl, hzero]
    · rw [ite_eq_left rfl, ite_eq_right hc, hzero]
  · by_cases hs : d + c = 0
    · rw [ite_eq_right hd, ite_eq_left hs, hs]
    · rw [ite_eq_right hd, ite_eq_right hs]

/-- The coefficient of `ofTerms ts` at `e` is the sum, in input order, of
the coefficients of the terms of `ts` at `e`. The `hzero` hypothesis is
what identifies a fresh insertion `c` with the fold's `0 + c`; a
coefficient type with `Lean.Grind.Semiring` discharges it from
`add_zero` and `add_comm`. -/
theorem coeff_ofTerms [Add R] (hzero : ∀ c : R, 0 + c = c)
    (ts : Array (Nat × R)) (e : Nat) :
    (ofTerms ts).coeff e =
      (ts.filter (fun t => t.1 = e)).foldl (fun a t => a + t.2) 0 := by
  rw [coeff_ofTerms_addCoeff, ← Array.foldl_toList, Array.toList_filter]
  simp only [addCoeff_eq_add hzero]

/-- Combining worker for `ofTermsImpl`: walk a `≤`-sorted term list with
the run exponent `e` and its accumulated coefficient `acc`, replaying the
{name}`addCoeff` semantics of the {name}`addTerm` fold within each
equal-exponent block and emitting the nonzero results. -/
def combineRun [Add R] (e : Nat) (acc : R) : List (Nat × R) → List (Nat × R)
  | [] => if acc = 0 then [] else [(e, acc)]
  | t :: ts =>
      if t.1 = e then combineRun e (addCoeff acc t.2) ts
      else if acc = 0 then combineRun t.1 (addCoeff 0 t.2) ts
      else (e, acc) :: combineRun t.1 (addCoeff 0 t.2) ts

/-- Combine the equal-exponent blocks of a `≤`-sorted term list in one
pass, dropping zero results. -/
def combineSorted [Add R] : List (Nat × R) → List (Nat × R)
  | [] => []
  | t :: ts => combineRun t.1 (addCoeff 0 t.2) ts

/-- The combining pass emits a canonical list whose exponents all lie at
or above the run exponent. -/
theorem combineRun_canonical [Add R] {l : List (Nat × R)} {e : Nat}
    {acc : R} (hs : l.Pairwise (fun a b => a.1 ≤ b.1))
    (hge : ∀ t ∈ l, e ≤ t.1) :
    (combineRun e acc l).Pairwise (fun a b => a.1 < b.1) ∧
      (∀ t ∈ combineRun e acc l, t.2 ≠ 0) ∧
      ∀ t ∈ combineRun e acc l, e ≤ t.1 := by
  induction l generalizing e acc with
  | nil =>
      by_cases hacc : acc = 0
      · simp [combineRun, hacc]
      · refine ⟨?_, ?_, ?_⟩ <;> simp [combineRun, hacc]
  | cons t ts ih =>
      rw [List.pairwise_cons] at hs
      have hts : ∀ u ∈ ts, t.1 ≤ u.1 := hs.1
      by_cases hte : t.1 = e
      · simp only [combineRun, ite_eq_left hte]
        exact ih hs.2 fun u hu => Nat.le_trans (hte ▸ hts u hu) (Nat.le_refl _)
      · have hlt : e < t.1 := by
          have := hge t (List.mem_cons_self ..)
          omega
        obtain ⟨hpw, hnz, hge'⟩ := ih (e := t.1) (acc := addCoeff 0 t.2)
          hs.2 hts
        by_cases hacc : acc = 0
        · simp only [combineRun, ite_eq_right hte, ite_eq_left hacc]
          exact ⟨hpw, hnz, fun u hu => by have := hge' u hu; omega⟩
        · simp only [combineRun, ite_eq_right hte, ite_eq_right hacc]
          refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_, ?_⟩
          · intro u hu
            have := hge' u hu
            omega
          · intro u hu
            rcases List.mem_cons.mp hu with rfl | hu'
            · exact hacc
            · exact hnz u hu'
          · intro u hu
            rcases List.mem_cons.mp hu with rfl | hu'
            · exact Nat.le_refl _
            · have := hge' u hu'
              omega

/-- Coefficient description of the combining pass: the run's own
exponent reads its accumulator folded over the rest of its block, and
every other exponent reads its whole block folded from `0`. -/
theorem coeffList_combineRun [Add R] {l : List (Nat × R)} {e : Nat}
    {acc : R} (hs : l.Pairwise (fun a b => a.1 ≤ b.1))
    (hge : ∀ t ∈ l, e ≤ t.1) (f : Nat) :
    coeffList (combineRun e acc l) f =
      if f = e then
        (l.filter (fun t => t.1 = e)).foldl (fun a t => addCoeff a t.2) acc
      else
        (l.filter (fun t => t.1 = f)).foldl (fun a t => addCoeff a t.2) 0 := by
  induction l generalizing e acc with
  | nil =>
      by_cases hf : f = e
      · subst hf
        by_cases hacc : acc = 0
        · simp [combineRun, hacc, coeffList]
        · simp [combineRun, hacc, coeffList]
      · by_cases hacc : acc = 0
        · simp [combineRun, hacc, coeffList, hf]
        · have hef : ¬e = f := fun h => hf h.symm
          simp [combineRun, hacc, coeffList, hf, hef]
  | cons t ts ih =>
      rw [List.pairwise_cons] at hs
      have hts : ∀ u ∈ ts, t.1 ≤ u.1 := hs.1
      by_cases hte : t.1 = e
      · rw [show combineRun e acc (t :: ts) = combineRun e (addCoeff acc t.2) ts
          from by rw [combineRun, ite_eq_left hte]]
        rw [ih hs.2 (fun u hu => hte ▸ hts u hu)]
        by_cases hf : f = e
        · subst hf
          rw [ite_eq_left rfl, ite_eq_left rfl,
            List.filter_cons_of_pos (by simpa using hte), List.foldl_cons]
        · rw [ite_eq_right hf, ite_eq_right hf,
            List.filter_cons_of_neg (by simpa using fun h : t.1 = f => hf (by omega))]
      · have hlt : e < t.1 := by
          have := hge t (List.mem_cons_self ..)
          omega
        have hfilter_e : ts.filter (fun u => u.1 = e) = [] := by
          rw [List.filter_eq_nil_iff]
          intro u hu
          have := hts u hu
          simp only [decide_eq_true_eq]
          omega
        have ihspec := ih (e := t.1) (acc := addCoeff 0 t.2) hs.2 hts
        by_cases hacc : acc = 0
        · rw [show combineRun e acc (t :: ts) =
              combineRun t.1 (addCoeff 0 t.2) ts
            from by rw [combineRun, ite_eq_right hte, ite_eq_left hacc]]
          rw [ihspec]
          by_cases hf1 : f = t.1
          · subst hf1
            rw [ite_eq_left rfl, ite_eq_right (by omega),
              List.filter_cons_of_pos (by simp), List.foldl_cons]
          · rw [ite_eq_right hf1]
            by_cases hfe : f = e
            · subst hfe
              rw [ite_eq_left rfl,
                List.filter_cons_of_neg (by simpa using fun h : t.1 = f => hf1 h.symm),
                hfilter_e, hacc]
            · rw [ite_eq_right hfe,
                List.filter_cons_of_neg (by simpa using fun h : t.1 = f => hf1 h.symm)]
        · rw [show combineRun e acc (t :: ts) =
              (e, acc) :: combineRun t.1 (addCoeff 0 t.2) ts
            from by rw [combineRun, ite_eq_right hte, ite_eq_right hacc]]
          simp only [coeffList]
          by_cases hfe : f = e
          · subst hfe
            rw [ite_eq_left rfl, ite_eq_left rfl,
              List.filter_cons_of_neg (by simpa using fun h : t.1 = f => by omega),
              hfilter_e]
            rfl
          · rw [ite_eq_right (fun h : e = f => hfe h.symm), ite_eq_right hfe, ihspec]
            by_cases hf1 : f = t.1
            · subst hf1
              rw [ite_eq_left rfl, List.filter_cons_of_pos (by simp),
                List.foldl_cons]
            · rw [ite_eq_right hf1,
                List.filter_cons_of_neg (by simpa using fun h : t.1 = f => hf1 h.symm)]

/-- Coefficient description of {name}`combineSorted` on a `≤`-sorted
list: each exponent reads its block folded from `0`. -/
theorem coeffList_combineSorted [Add R] {l : List (Nat × R)}
    (hs : l.Pairwise (fun a b => a.1 ≤ b.1)) (f : Nat) :
    coeffList (combineSorted l) f =
      (l.filter (fun t => t.1 = f)).foldl (fun a t => addCoeff a t.2) 0 := by
  cases l with
  | nil => rfl
  | cons t ts =>
      rw [List.pairwise_cons] at hs
      rw [show combineSorted (t :: ts) = combineRun t.1 (addCoeff 0 t.2) ts
          from rfl,
        coeffList_combineRun hs.2 hs.1]
      by_cases hf : f = t.1
      · subst hf
        rw [ite_eq_left rfl, List.filter_cons_of_pos (by simp), List.foldl_cons]
      · rw [ite_eq_right hf,
          List.filter_cons_of_neg (by simpa using fun h : t.1 = f => hf h.symm)]

omit [Zero R] [DecidableEq R] in
/-- Stability of the exponent sort, in the form the combining pass needs:
sorting by exponent does not reorder the terms within any one exponent's
block. -/
theorem filter_exp_mergeSort {l : List (Nat × R)} (e : Nat) :
    (l.mergeSort (fun a b => a.1 ≤ b.1)).filter (fun t => t.1 = e) =
      l.filter (fun t => t.1 = e) := by
  have htrans : ∀ a b c : Nat × R,
      (fun a b : Nat × R => (a.1 ≤ b.1 : Bool)) a b →
      (fun a b : Nat × R => (a.1 ≤ b.1 : Bool)) b c →
      (fun a b : Nat × R => (a.1 ≤ b.1 : Bool)) a c := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    omega
  have htotal : ∀ a b : Nat × R,
      ((fun a b : Nat × R => (a.1 ≤ b.1 : Bool)) a b ||
       (fun a b : Nat × R => (a.1 ≤ b.1 : Bool)) b a) := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  have hpw : (l.filter (fun t => t.1 = e)).Pairwise
      (fun a b : Nat × R => (a.1 ≤ b.1 : Bool) = true) := by
    have hmem : ∀ t ∈ l.filter (fun t => t.1 = e), t.1 = e := by
      intro t ht
      simpa using (List.mem_filter.mp ht).2
    refine List.pairwise_of_forall_mem_list ?_
    intro a ha b hb
    simp only [decide_eq_true_eq]
    rw [hmem a ha, hmem b hb]
    exact Nat.le_refl _
  have hsub : (l.filter (fun t => t.1 = e)).Sublist
      (l.mergeSort (fun a b => a.1 ≤ b.1)) :=
    List.sublist_mergeSort htrans htotal hpw List.filter_sublist
  have hsub2 : (l.filter (fun t => t.1 = e)).Sublist
      ((l.mergeSort (fun a b => a.1 ≤ b.1)).filter (fun t => t.1 = e)) := by
    have := hsub.filter (fun t => t.1 = e)
    rwa [List.filter_eq_self.mpr (fun a ha => (List.mem_filter.mp ha).2)] at this
  have hperm : ((l.mergeSort (fun a b => a.1 ≤ b.1)).filter
      (fun t => t.1 = e)).Perm (l.filter (fun t => t.1 = e)) :=
    (List.mergeSort_perm l _).filter _
  exact (hsub2.eq_of_length hperm.length_eq.symm).symm

/-- Runtime implementation of {name}`ofTerms`: stable sort by exponent,
then one combining pass, `O(m log m)` on `m` input terms against the
specification's `O(m²)` worst case (value-equal to {name}`ofTerms` by
`ofTerms_eq_impl`, registered `@[csimp]`). Stability is load-bearing:
it is what makes the per-block fold agree with the input-order fold of
the specification with no algebra assumed. -/
def ofTermsImpl [Add R] (ts : Array (Nat × R)) : SparsePoly R where
  terms :=
    (combineSorted (ts.toList.mergeSort (fun a b => a.1 ≤ b.1))).toArray
  canonical := by
    have hs : (ts.toList.mergeSort (fun a b => a.1 ≤ b.1)).Pairwise
        (fun a b => a.1 ≤ b.1) := by
      have := List.pairwise_mergeSort (le := fun a b : Nat × R => (a.1 ≤ b.1 : Bool))
        (fun a b c hab hbc => by
          simp only [decide_eq_true_eq] at *
          omega)
        (fun a b => by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          omega)
        ts.toList
      exact this.imp fun h => by simpa using h
    constructor
    · rw [List.toList_toArray]
      cases hsort : ts.toList.mergeSort (fun a b => a.1 ≤ b.1) with
      | nil => simp [combineSorted]
      | cons t rest =>
          rw [hsort] at hs
          rw [List.pairwise_cons] at hs
          exact (combineRun_canonical hs.2 hs.1).1
    · intro t ht
      have ht' := Array.mem_def.mp ht
      rw [List.toList_toArray] at ht'
      cases hsort : ts.toList.mergeSort (fun a b => a.1 ≤ b.1) with
      | nil =>
          rw [hsort] at ht'
          cases ht'
      | cons u rest =>
          rw [hsort] at hs ht'
          rw [List.pairwise_cons] at hs
          exact (combineRun_canonical hs.2 hs.1).2.1 t ht'

/-- The {name}`addTerm` fold and the stable sort-and-combine pass build
the same polynomial, with no algebra assumed. -/
theorem ofTerms_eq_ofTermsImpl [Add R] (ts : Array (Nat × R)) :
    ofTerms ts = ofTermsImpl ts := by
  apply ext_coeff
  intro e
  rw [coeff_ofTerms_addCoeff]
  have hs : (ts.toList.mergeSort (fun a b => a.1 ≤ b.1)).Pairwise
      (fun a b => a.1 ≤ b.1) := by
    have := List.pairwise_mergeSort (le := fun a b : Nat × R => (a.1 ≤ b.1 : Bool))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at *
        omega)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega)
      ts.toList
    exact this.imp fun h => by simpa using h
  show _ = coeffList (ofTermsImpl ts).terms.toList e
  rw [show (ofTermsImpl ts).terms =
      (combineSorted (ts.toList.mergeSort (fun a b => a.1 ≤ b.1))).toArray
    from rfl, List.toList_toArray, coeffList_combineSorted hs,
    filter_exp_mergeSort]

/-- Register the stable sort-and-combine pass as the compiled
implementation of {name}`ofTerms`. -/
@[csimp]
theorem ofTerms_eq_impl : @ofTerms = @ofTermsImpl := by
  funext R _ _ _ ts
  exact ofTerms_eq_ofTermsImpl ts

/-- The monomial `c · x^e`. The zero coefficient collapses to the zero
polynomial. -/
def monomial (e : Nat) (c : R) : SparsePoly R :=
  if hc : c = 0 then 0
  else
    { terms := #[(e, c)]
      canonical := by
        constructor
        · simp
        · intro t ht
          have := Array.mem_def.mp ht
          simp only [List.mem_cons] at this
          rcases this with rfl | h'
          · exact hc
          · cases h' }

/-- The constant polynomial with value `c`. The zero constant collapses
to the zero polynomial. -/
def C (c : R) : SparsePoly R :=
  monomial 0 c

/-- The variable `x`. -/
def X [One R] : SparsePoly R :=
  monomial 1 1

instance [One R] : One (SparsePoly R) where
  one := C 1

/-- Characterising lemma for monomials: coefficient `c` at `e`, zero
elsewhere, even when `c = 0`. -/
@[simp, grind =] theorem coeff_monomial (e : Nat) (c : R) (f : Nat) :
    (monomial e c).coeff f = if f = e then c else 0 := by
  unfold monomial
  by_cases hc : c = 0
  · rw [dite_eq_left hc]
    by_cases hf : f = e
    · rw [ite_eq_left hf, coeff_zero, hc]
    · rw [ite_eq_right hf, coeff_zero]
  · rw [dite_eq_right hc]
    show coeffList [(e, c)] f = _
    simp only [coeffList]
    by_cases hf : f = e
    · rw [ite_eq_left (hf ▸ rfl), ite_eq_left hf]
    · rw [ite_eq_right (fun h : e = f => hf h.symm), ite_eq_right hf]

/-- A constant stores its value at exponent `0`. -/
@[simp, grind =] theorem coeff_C (c : R) (f : Nat) :
    (C c).coeff f = if f = 0 then c else 0 :=
  coeff_monomial 0 c f

/-- The one polynomial is the constant `1`. -/
@[simp, grind =] theorem coeff_one [One R] (f : Nat) :
    (1 : SparsePoly R).coeff f = if f = 0 then 1 else 0 :=
  coeff_C 1 f

/-- The variable has coefficient `1` at exponent `1`. -/
@[simp, grind =] theorem coeff_X [One R] (f : Nat) :
    (X : SparsePoly R).coeff f = if f = 1 then 1 else 0 :=
  coeff_monomial 1 1 f

end SparsePoly

/-- `#sp[(e₀, c₀), (e₁, c₁), …]` constructs the canonical sparse
polynomial with the given `(exponent, coefficient)` terms: any order,
repeated exponents summed, zero coefficients dropped, mirroring `#p[…]`
for `DensePoly`. -/
syntax (name := sparsePolyLiteral) "#sp[" term,* "]" : term

macro_rules
  | `(#sp[$terms,*]) => `(Hex.SparsePoly.ofTerms #[$terms,*])



end Hex
