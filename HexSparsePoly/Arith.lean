/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSparsePoly.Basic

@[expose] public section
set_option backward.proofsInPublic true

/-!
Arithmetic on canonical sparse polynomials: addition and subtraction as
linear merges, negation, scalar and monomial multiplication as filtered
coefficient maps, multiplication as the canonicalised pairwise product,
binary powering, the operator instances, and the ring laws.
-/

namespace Hex

open scoped Hex

universe u

namespace SparsePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- Linear merge of two sorted term lists: `fl` maps a coefficient
present only on the left, `fr` one present only on the right, `fb`
combines a collision, and zero results are dropped. `add` and `sub` are
instances. -/
def mergeWith (fl fr : R → R) (fb : R → R → R) :
    List (Nat × R) → List (Nat × R) → List (Nat × R)
  | [], l₂ =>
      l₂.filterMap fun t => if fr t.2 = 0 then none else some (t.1, fr t.2)
  | a :: as, [] =>
      (a :: as).filterMap fun t =>
        if fl t.2 = 0 then none else some (t.1, fl t.2)
  | a :: as, b :: bs =>
      if a.1 < b.1 then
        if fl a.2 = 0 then mergeWith fl fr fb as (b :: bs)
        else (a.1, fl a.2) :: mergeWith fl fr fb as (b :: bs)
      else if b.1 < a.1 then
        if fr b.2 = 0 then mergeWith fl fr fb (a :: as) bs
        else (b.1, fr b.2) :: mergeWith fl fr fb (a :: as) bs
      else
        if fb a.2 b.2 = 0 then mergeWith fl fr fb as bs
        else (a.1, fb a.2 b.2) :: mergeWith fl fr fb as bs
termination_by l₁ l₂ => l₁.length + l₂.length
decreasing_by all_goals simp +arith

/-- Every exponent stored by the merge comes from one of the inputs. -/
theorem exp_mem_mergeWith {fl fr : R → R} {fb : R → R → R}
    {l₁ l₂ : List (Nat × R)} {t : Nat × R}
    (ht : t ∈ mergeWith fl fr fb l₁ l₂) :
    (∃ u ∈ l₁, t.1 = u.1) ∨ ∃ u ∈ l₂, t.1 = u.1 := by
  induction l₁, l₂ using mergeWith.induct fl fr fb with
  | case1 l₂ =>
      rw [mergeWith] at ht
      obtain ⟨u, hu, hut⟩ := List.mem_filterMap.mp ht
      right
      refine ⟨u, hu, ?_⟩
      split at hut
      · cases hut
      · cases hut
        rfl
  | case2 a as =>
      rw [mergeWith] at ht
      obtain ⟨u, hu, hut⟩ := List.mem_filterMap.mp ht
      left
      refine ⟨u, hu, ?_⟩
      split at hut
      · cases hut
      · cases hut
        rfl
  | case3 a as b bs hab hz ih =>
      rw [mergeWith, if_pos hab, if_pos hz] at ht
      rcases ih ht with ⟨u, hu, hut⟩ | ⟨u, hu, hut⟩
      · exact Or.inl ⟨u, List.mem_cons_of_mem _ hu, hut⟩
      · exact Or.inr ⟨u, hu, hut⟩
  | case4 a as b bs hab hz ih =>
      rw [mergeWith, if_pos hab, if_neg hz] at ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Or.inl ⟨a, List.mem_cons_self .., rfl⟩
      · rcases ih ht' with ⟨u, hu, hut⟩ | ⟨u, hu, hut⟩
        · exact Or.inl ⟨u, List.mem_cons_of_mem _ hu, hut⟩
        · exact Or.inr ⟨u, hu, hut⟩
  | case5 a as b bs hab hba hz ih =>
      rw [mergeWith, if_neg hab, if_pos hba, if_pos hz] at ht
      rcases ih ht with ⟨u, hu, hut⟩ | ⟨u, hu, hut⟩
      · exact Or.inl ⟨u, hu, hut⟩
      · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hut⟩
  | case6 a as b bs hab hba hz ih =>
      rw [mergeWith, if_neg hab, if_pos hba, if_neg hz] at ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Or.inr ⟨b, List.mem_cons_self .., rfl⟩
      · rcases ih ht' with ⟨u, hu, hut⟩ | ⟨u, hu, hut⟩
        · exact Or.inl ⟨u, hu, hut⟩
        · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hut⟩
  | case7 a as b bs hab hba hz ih =>
      rw [mergeWith, if_neg hab, if_neg hba, if_pos hz] at ht
      rcases ih ht with ⟨u, hu, hut⟩ | ⟨u, hu, hut⟩
      · exact Or.inl ⟨u, List.mem_cons_of_mem _ hu, hut⟩
      · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hut⟩
  | case8 a as b bs hab hba hz ih =>
      rw [mergeWith, if_neg hab, if_neg hba, if_neg hz] at ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Or.inl ⟨a, List.mem_cons_self .., rfl⟩
      · rcases ih ht' with ⟨u, hu, hut⟩ | ⟨u, hu, hut⟩
        · exact Or.inl ⟨u, List.mem_cons_of_mem _ hu, hut⟩
        · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hut⟩

/-- The merge of two canonical term lists is canonical. -/
theorem mergeWith_canonical {fl fr : R → R} {fb : R → R → R}
    {l₁ l₂ : List (Nat × R)}
    (hs₁ : l₁.Pairwise (fun a b => a.1 < b.1))
    (hs₂ : l₂.Pairwise (fun a b => a.1 < b.1)) :
    (mergeWith fl fr fb l₁ l₂).Pairwise (fun a b => a.1 < b.1) ∧
      ∀ t ∈ mergeWith fl fr fb l₁ l₂, t.2 ≠ 0 := by
  induction l₁, l₂ using mergeWith.induct fl fr fb with
  | case1 l₂ =>
      rw [mergeWith]
      constructor
      · refine List.Pairwise.filterMap _ ?_ hs₂
        intro a b hab x hx y hy
        split at hx
        · cases hx
        · split at hy
          · cases hy
          · cases hx
            cases hy
            exact hab
      · intro t ht
        obtain ⟨u, hu, hut⟩ := List.mem_filterMap.mp ht
        split at hut
        · cases hut
        · cases hut
          rename_i hz
          exact hz
  | case2 a as =>
      rw [mergeWith]
      constructor
      · refine List.Pairwise.filterMap _ ?_ hs₁
        intro x y hxy u hu v hv
        split at hu
        · cases hu
        · split at hv
          · cases hv
          · cases hu
            cases hv
            exact hxy
      · intro t ht
        obtain ⟨u, hu, hut⟩ := List.mem_filterMap.mp ht
        split at hut
        · cases hut
        · cases hut
          rename_i hz
          exact hz
  | case3 a as b bs hab hz ih =>
      rw [mergeWith, if_pos hab, if_pos hz]
      exact ih (List.pairwise_cons.mp hs₁).2 hs₂
  | case4 a as b bs hab hz ih =>
      rw [mergeWith, if_pos hab, if_neg hz]
      rw [List.pairwise_cons] at hs₁
      obtain ⟨hpw, hnz⟩ := ih hs₁.2 hs₂
      refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_⟩
      · intro t ht
        rcases exp_mem_mergeWith ht with ⟨u, hu, hut⟩ | ⟨u, hu, hut⟩
        · have := hs₁.1 u hu
          omega
        · rcases List.mem_cons.mp hu with rfl | hu'
          · omega
          · have := (List.pairwise_cons.mp hs₂).1 u hu'
            omega
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact hz
        · exact hnz t ht'
  | case5 a as b bs hab hba hz ih =>
      rw [mergeWith, if_neg hab, if_pos hba, if_pos hz]
      exact ih hs₁ (List.pairwise_cons.mp hs₂).2
  | case6 a as b bs hab hba hz ih =>
      rw [mergeWith, if_neg hab, if_pos hba, if_neg hz]
      rw [List.pairwise_cons] at hs₂
      obtain ⟨hpw, hnz⟩ := ih hs₁ hs₂.2
      refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_⟩
      · intro t ht
        rcases exp_mem_mergeWith ht with ⟨u, hu, hut⟩ | ⟨u, hu, hut⟩
        · rcases List.mem_cons.mp hu with rfl | hu'
          · omega
          · have := (List.pairwise_cons.mp hs₁).1 u hu'
            omega
        · have := hs₂.1 u hu
          omega
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact hz
        · exact hnz t ht'
  | case7 a as b bs hab hba hz ih =>
      rw [mergeWith, if_neg hab, if_neg hba, if_pos hz]
      exact ih (List.pairwise_cons.mp hs₁).2 (List.pairwise_cons.mp hs₂).2
  | case8 a as b bs hab hba hz ih =>
      rw [mergeWith, if_neg hab, if_neg hba, if_neg hz]
      rw [List.pairwise_cons] at hs₁ hs₂
      obtain ⟨hpw, hnz⟩ := ih hs₁.2 hs₂.2
      refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_⟩
      · intro t ht
        rcases exp_mem_mergeWith ht with ⟨u, hu, hut⟩ | ⟨u, hu, hut⟩
        · have := hs₁.1 u hu
          omega
        · have := hs₂.1 u hu
          omega
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact hz
        · exact hnz t ht'

/-- Coefficient description of the zero-filtered coefficient map used by
the merge's one-sided cases. -/
theorem coeffList_filterMap_map {f : R → R} {l : List (Nat × R)}
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (hf0 : f 0 = 0) (e : Nat) :
    coeffList
        (l.filterMap fun t => if f t.2 = 0 then none else some (t.1, f t.2))
        e = f (coeffList l e) := by
  induction l with
  | nil => simpa [coeffList] using hf0.symm
  | cons a as ih =>
      rw [List.pairwise_cons] at hs
      by_cases hz : f a.2 = 0
      · simp only [List.filterMap_cons, if_pos hz]
        by_cases hae : a.1 = e
        · have hrest0 : coeffList
              (as.filterMap fun t =>
                if f t.2 = 0 then none else some (t.1, f t.2)) e = 0 := by
            refine coeffList_eq_zero ?_
            intro t ht
            obtain ⟨u, hu, hut⟩ := List.mem_filterMap.mp ht
            split at hut
            · cases hut
            · cases hut
              have := hs.1 u hu
              omega
          rw [hrest0]
          simp only [coeffList, if_pos hae]
          exact hz.symm
        · rw [ih hs.2]
          simp only [coeffList, if_neg hae]
      · simp only [List.filterMap_cons, if_neg hz]
        by_cases hae : a.1 = e
        · simp only [coeffList, if_pos hae]
        · simp only [coeffList, if_neg hae]
          exact ih hs.2

/-- Coefficient description of the merge. The three compatibility
hypotheses identify the structural choices with the pointwise `fb`
against an absent side's `0`. -/
theorem coeffList_mergeWith {fl fr : R → R} {fb : R → R → R}
    {l₁ l₂ : List (Nat × R)}
    (hs₁ : l₁.Pairwise (fun a b => a.1 < b.1))
    (hs₂ : l₂.Pairwise (fun a b => a.1 < b.1))
    (hb00 : fb 0 0 = 0) (hbl : ∀ x, fb x 0 = fl x) (hbr : ∀ y, fb 0 y = fr y)
    (e : Nat) :
    coeffList (mergeWith fl fr fb l₁ l₂) e =
      fb (coeffList l₁ e) (coeffList l₂ e) := by
  have hfl0 : fl 0 = 0 := by rw [← hbl, hb00]
  have hfr0 : fr 0 = 0 := by rw [← hbr, hb00]
  induction l₁, l₂ using mergeWith.induct fl fr fb with
  | case1 l₂ =>
      rw [mergeWith, coeffList_filterMap_map hs₂ hfr0]
      show _ = fb (coeffList [] e) _
      rw [show coeffList ([] : List (Nat × R)) e = 0 from rfl, hbr]
  | case2 a as =>
      rw [mergeWith, coeffList_filterMap_map hs₁ hfl0]
      rw [show coeffList ([] : List (Nat × R)) e = 0 from rfl, hbl]
  | case3 a as b bs hab hz ih =>
      rw [List.pairwise_cons] at hs₁
      rw [mergeWith, if_pos hab, if_pos hz, ih hs₁.2 hs₂]
      by_cases hae : a.1 = e
      · have htail : coeffList as e = 0 := by
          refine coeffList_eq_zero ?_
          intro t ht
          have := hs₁.1 t ht
          omega
        have hright : coeffList (b :: bs) e = 0 :=
          coeffList_eq_zero_of_lt_head hs₂ (by omega)
        rw [htail, hright, hb00]
        simp only [coeffList, if_pos hae]
        rw [hbl, hz]
      · simp only [coeffList, if_neg hae]
  | case4 a as b bs hab hz ih =>
      rw [List.pairwise_cons] at hs₁
      rw [mergeWith, if_pos hab, if_neg hz]
      by_cases hae : a.1 = e
      · have hright : coeffList (b :: bs) e = 0 :=
          coeffList_eq_zero_of_lt_head hs₂ (by omega)
        rw [hright]
        simp only [coeffList, if_pos hae]
        rw [hbl]
      · simp only [coeffList, if_neg hae]
        exact ih hs₁.2 hs₂
  | case5 a as b bs hab hba hz ih =>
      rw [List.pairwise_cons] at hs₂
      rw [mergeWith, if_neg hab, if_pos hba, if_pos hz, ih hs₁ hs₂.2]
      by_cases hbe : b.1 = e
      · have htail : coeffList bs e = 0 := by
          refine coeffList_eq_zero ?_
          intro t ht
          have := hs₂.1 t ht
          omega
        have hleft : coeffList (a :: as) e = 0 :=
          coeffList_eq_zero_of_lt_head hs₁ (by omega)
        rw [htail, hleft, hb00]
        simp only [coeffList, if_pos hbe]
        rw [hbr, hz]
      · simp only [coeffList, if_neg hbe]
  | case6 a as b bs hab hba hz ih =>
      rw [List.pairwise_cons] at hs₂
      rw [mergeWith, if_neg hab, if_pos hba, if_neg hz]
      by_cases hbe : b.1 = e
      · have hleft : coeffList (a :: as) e = 0 :=
          coeffList_eq_zero_of_lt_head hs₁ (by omega)
        rw [hleft]
        simp only [coeffList, if_pos hbe]
        rw [hbr]
      · simp only [coeffList, if_neg hbe]
        exact ih hs₁ hs₂.2
  | case7 a as b bs hab hba hz ih =>
      have habeq : a.1 = b.1 := by omega
      rw [List.pairwise_cons] at hs₁ hs₂
      rw [mergeWith, if_neg hab, if_neg hba, if_pos hz, ih hs₁.2 hs₂.2]
      by_cases hae : a.1 = e
      · have htail₁ : coeffList as e = 0 := by
          refine coeffList_eq_zero ?_
          intro t ht
          have := hs₁.1 t ht
          omega
        have htail₂ : coeffList bs e = 0 := by
          refine coeffList_eq_zero ?_
          intro t ht
          have := hs₂.1 t ht
          omega
        rw [htail₁, htail₂, hb00]
        simp only [coeffList, if_pos hae, if_pos (habeq ▸ hae)]
        exact hz.symm
      · simp only [coeffList, if_neg hae, if_neg (habeq ▸ hae)]
  | case8 a as b bs hab hba hz ih =>
      have habeq : a.1 = b.1 := by omega
      rw [List.pairwise_cons] at hs₁ hs₂
      rw [mergeWith, if_neg hab, if_neg hba, if_neg hz]
      by_cases hae : a.1 = e
      · simp only [coeffList, if_pos hae, if_pos (habeq ▸ hae)]
      · simp only [coeffList, if_neg hae, if_neg (habeq ▸ hae)]
        exact ih hs₁.2 hs₂.2

/-- The canonical-form invariant, list-level: exponents strictly
increase. -/
theorem pairwise_toList (s : SparsePoly R) :
    s.terms.toList.Pairwise (fun a b => a.1 < b.1) :=
  s.canonical.1

/-- The canonical-form invariant, list-level: no stored coefficient is
zero. -/
theorem nonzero_toList (s : SparsePoly R) :
    ∀ t ∈ s.terms.toList, t.2 ≠ 0 :=
  fun t ht => s.canonical.2 t (Array.mem_def.mpr ht)

/-- The stored exponents are exactly the exponents with a nonzero
coefficient. Uses both canonical-form invariants: strict increase makes
the stored coefficient the coefficient, and zero-freedom makes it
nonzero. -/
theorem mem_support_iff (s : SparsePoly R) (e : Nat) :
    e ∈ s.support.toList ↔ s.coeff e ≠ 0 := by
  show e ∈ (s.terms.map (·.1)).toList ↔ coeffList s.terms.toList e ≠ 0
  rw [Array.toList_map, List.mem_map]
  constructor
  · intro h hzero
    obtain ⟨t, ht, hte⟩ := h
    rw [coeffList_eq_of_mem s.pairwise_toList ht hte] at hzero
    exact s.nonzero_toList t ht hzero
  · intro h
    cases Decidable.em (∃ t, t ∈ s.terms.toList ∧ t.1 = e) with
    | inl hex => exact hex
    | inr hnot =>
        exact absurd (coeffList_eq_zero fun t ht hte => hnot ⟨t, ht, hte⟩) h

/-- Package a canonical term list as a polynomial. -/
def ofCanonicalList (l : List (Nat × R))
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (hnz : ∀ t ∈ l, t.2 ≠ 0) :
    SparsePoly R where
  terms := l.toArray
  canonical :=
    ⟨by simpa using hs,
     fun t ht => hnz t (by simpa using Array.mem_def.mp ht)⟩

/-- Packaging a canonical term list keeps its list coefficients. -/
@[simp] theorem coeff_ofCanonicalList (l : List (Nat × R))
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (hnz : ∀ t ∈ l, t.2 ≠ 0)
    (e : Nat) : (ofCanonicalList l hs hnz).coeff e = coeffList l e := by
  unfold ofCanonicalList coeff
  rw [List.toList_toArray]

/-- Map exponents and coefficients over a term list, dropping the terms
whose new coefficient is zero. `neg`, `scale`, and `mulMonomial` are
instances (with the identity exponent map or a shift). -/
def mapTerms (g : Nat → Nat) (f : Nat → R → R) (l : List (Nat × R)) :
    List (Nat × R) :=
  l.filterMap fun t =>
    if f t.1 t.2 = 0 then none else some (g t.1, f t.1 t.2)

/-- Every exponent stored by the map is the image of a stored one. -/
theorem exp_mem_mapTerms {g : Nat → Nat} {f : Nat → R → R}
    {l : List (Nat × R)} {t : Nat × R} (ht : t ∈ mapTerms g f l) :
    ∃ u ∈ l, t.1 = g u.1 := by
  obtain ⟨u, hu, hut⟩ := List.mem_filterMap.mp ht
  refine ⟨u, hu, ?_⟩
  split at hut
  · cases hut
  · cases hut
    rfl

/-- The map of a canonical term list along a strictly monotone exponent
map is canonical. -/
theorem mapTerms_canonical {g : Nat → Nat} {f : Nat → R → R}
    {l : List (Nat × R)} (hs : l.Pairwise (fun a b => a.1 < b.1))
    (hmono : ∀ a ∈ l, ∀ b ∈ l, a.1 < b.1 → g a.1 < g b.1) :
    (mapTerms g f l).Pairwise (fun a b => a.1 < b.1) ∧
      ∀ t ∈ mapTerms g f l, t.2 ≠ 0 := by
  induction l with
  | nil => simp [mapTerms]
  | cons a as ih =>
      rw [List.pairwise_cons] at hs
      obtain ⟨hpw, hnz⟩ := ih hs.2 fun x hx y hy =>
        hmono x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      by_cases hz : f a.1 a.2 = 0
      · rw [show mapTerms g f (a :: as) = mapTerms g f as from by
          simp only [mapTerms, List.filterMap_cons, if_pos hz]]
        exact ⟨hpw, hnz⟩
      · rw [show mapTerms g f (a :: as) =
            (g a.1, f a.1 a.2) :: mapTerms g f as from by
          simp only [mapTerms, List.filterMap_cons, if_neg hz]]
        refine ⟨List.pairwise_cons.mpr ⟨?_, hpw⟩, ?_⟩
        · intro t ht
          obtain ⟨u, hu, hut⟩ := exp_mem_mapTerms ht
          rw [hut]
          exact hmono a (List.mem_cons_self ..) u (List.mem_cons_of_mem _ hu)
            (hs.1 u hu)
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht'
          · exact hz
          · exact hnz t ht'

/-- Coefficient of the mapped list at a mapped exponent, for an exponent
map injective into the stored exponents. -/
theorem coeffList_mapTerms_apply {g : Nat → Nat} {f : Nat → R → R}
    {l : List (Nat × R)} {e : Nat}
    (hs : l.Pairwise (fun a b => a.1 < b.1))
    (hinj : ∀ u ∈ l, g u.1 = g e → u.1 = e) (hf0 : f e 0 = 0) :
    coeffList (mapTerms g f l) (g e) = f e (coeffList l e) := by
  induction l with
  | nil => simpa [mapTerms, coeffList] using hf0.symm
  | cons a as ih =>
      rw [List.pairwise_cons] at hs
      have ih' := ih hs.2 fun u hu => hinj u (List.mem_cons_of_mem _ hu)
      by_cases hz : f a.1 a.2 = 0
      · rw [show mapTerms g f (a :: as) = mapTerms g f as from by
          simp only [mapTerms, List.filterMap_cons, if_pos hz]]
        by_cases hae : a.1 = e
        · have htail : coeffList (mapTerms g f as) (g e) = 0 := by
            refine coeffList_eq_zero ?_
            intro t ht
            obtain ⟨u, hu, hut⟩ := exp_mem_mapTerms ht
            rw [hut]
            intro hgu
            have := hinj u (List.mem_cons_of_mem _ hu) hgu
            have := hs.1 u hu
            omega
          rw [htail]
          simp only [coeffList, if_pos hae]
          rw [← hae, hz]
        · rw [ih']
          simp only [coeffList, if_neg hae]
      · rw [show mapTerms g f (a :: as) =
            (g a.1, f a.1 a.2) :: mapTerms g f as from by
          simp only [mapTerms, List.filterMap_cons, if_neg hz]]
        by_cases hae : a.1 = e
        · simp only [coeffList, if_pos (show g a.1 = g e from by rw [hae]),
            if_pos hae]
          rw [hae]
        · simp only [coeffList,
            if_neg (fun h : g a.1 = g e =>
              hae (hinj a (List.mem_cons_self ..) h)),
            if_neg hae]
          exact ih'

/-- The mapped list stores nothing outside the image of the exponent
map. -/
theorem coeffList_mapTerms_of_ne {g : Nat → Nat} {f : Nat → R → R}
    {l : List (Nat × R)} {x : Nat} (hx : ∀ u ∈ l, g u.1 ≠ x) :
    coeffList (mapTerms g f l) x = 0 := by
  refine coeffList_eq_zero ?_
  intro t ht
  obtain ⟨u, hu, hut⟩ := exp_mem_mapTerms ht
  rw [hut]
  exact hx u hu

/-- Add two sparse polynomials by a linear merge of the sorted term
arrays, `O(s + t)`: sums at a matching exponent, and a zero sum stores
nothing. -/
def add [Add R] (s t : SparsePoly R) : SparsePoly R :=
  ofCanonicalList (mergeWith id id (· + ·) s.terms.toList t.terms.toList)
    (mergeWith_canonical s.pairwise_toList t.pairwise_toList).1
    (mergeWith_canonical s.pairwise_toList t.pairwise_toList).2

instance [Add R] : Add (SparsePoly R) where
  add := add

/-- Coefficient law for {name}`add`, under the pointwise hypotheses it
needs; the `Lean.Grind.Semiring` form is `coeff_add`. -/
theorem coeff_add' [Add R] (h00 : (0 : R) + 0 = 0)
    (hl : ∀ x : R, x + 0 = x) (hr : ∀ y : R, 0 + y = y)
    (s t : SparsePoly R) (e : Nat) :
    (s + t).coeff e = s.coeff e + t.coeff e := by
  show (s.add t).coeff e = _
  unfold add
  rw [coeff_ofCanonicalList]
  have h := coeffList_mergeWith (fl := id) (fr := id) (fb := (· + ·))
    s.pairwise_toList t.pairwise_toList h00 hl hr e
  rw [h]
  rfl

/-- Grind-classes form of `coeff_add'`: addition is coefficientwise. -/
@[simp, grind =] theorem coeff_add {S : Type u} [Lean.Grind.Semiring S]
    [DecidableEq S] (s t : SparsePoly S) (e : Nat) :
    (s + t).coeff e = s.coeff e + t.coeff e :=
  coeff_add' (by grind) (by grind) (by grind) s t e

/-- Subtract two sparse polynomials by a linear merge, `O(s + t)`. -/
def sub [Sub R] (s t : SparsePoly R) : SparsePoly R :=
  ofCanonicalList
    (mergeWith id (fun y => 0 - y) (· - ·) s.terms.toList t.terms.toList)
    (mergeWith_canonical s.pairwise_toList t.pairwise_toList).1
    (mergeWith_canonical s.pairwise_toList t.pairwise_toList).2

instance [Sub R] : Sub (SparsePoly R) where
  sub := sub

/-- Coefficient law for {name}`sub`, under the pointwise hypotheses it
needs; the `Lean.Grind.Ring` form is `coeff_sub`. -/
theorem coeff_sub' [Sub R] (h00 : (0 : R) - 0 = 0)
    (hl : ∀ x : R, x - 0 = x) (s t : SparsePoly R) (e : Nat) :
    (s - t).coeff e = s.coeff e - t.coeff e := by
  show (s.sub t).coeff e = _
  unfold sub
  rw [coeff_ofCanonicalList]
  have h := coeffList_mergeWith (fl := id) (fr := fun y => (0 : R) - y)
    (fb := (· - ·)) s.pairwise_toList t.pairwise_toList h00 hl
    (fun y => rfl) e
  rw [h]
  rfl

/-- Grind-classes form of `coeff_sub'`: subtraction is coefficientwise. -/
@[simp, grind =] theorem coeff_sub {S : Type u} [Lean.Grind.Ring S]
    [DecidableEq S] (s t : SparsePoly S) (e : Nat) :
    (s - t).coeff e = s.coeff e - t.coeff e :=
  coeff_sub' (by grind) (by grind) s t e

/-- Negate a sparse polynomial: subtraction from zero, compiled as one
filtered coefficient map. Over a ring the exponents and the term count
are unchanged; `[Sub R]` alone does not supply that, so the zero filter
stays. -/
def neg [Sub R] (s : SparsePoly R) : SparsePoly R :=
  ofCanonicalList (mapTerms id (fun _ c => 0 - c) s.terms.toList)
    (mapTerms_canonical s.pairwise_toList fun _ _ _ _ h => h).1
    (mapTerms_canonical s.pairwise_toList fun _ _ _ _ h => h).2

instance [Sub R] : Neg (SparsePoly R) where
  neg := neg

/-- Coefficient law for {name}`neg`, under the pointwise hypothesis it
needs; the `Lean.Grind.Ring` form is `coeff_neg`. -/
theorem coeff_neg' [Sub R] (h00 : (0 : R) - 0 = 0) (s : SparsePoly R)
    (e : Nat) : (-s).coeff e = 0 - s.coeff e := by
  show (s.neg).coeff e = _
  unfold neg
  rw [coeff_ofCanonicalList]
  exact coeffList_mapTerms_apply (g := id) s.pairwise_toList
    (fun u _ h => h) h00

/-- Grind-classes form of `coeff_neg'`: negation is coefficientwise. -/
@[simp, grind =] theorem coeff_neg {S : Type u} [Lean.Grind.Ring S]
    [DecidableEq S] (s : SparsePoly S) (e : Nat) :
    (-s).coeff e = 0 - s.coeff e :=
  coeff_neg' (by grind) s e

/-- Multiply every coefficient by `c`, dropping the products that
vanish: `c = 0` gives the zero polynomial, and a zero divisor `c` can
delete an interior term while leaving its neighbours. -/
def scale [Mul R] (c : R) (s : SparsePoly R) : SparsePoly R :=
  ofCanonicalList (mapTerms id (fun _ x => c * x) s.terms.toList)
    (mapTerms_canonical s.pairwise_toList fun _ _ _ _ h => h).1
    (mapTerms_canonical s.pairwise_toList fun _ _ _ _ h => h).2

/-- Coefficient law for {name}`scale`, under the pointwise hypothesis it
needs; the `Lean.Grind.Semiring` form is `coeff_scale`. -/
theorem coeff_scale' [Mul R] (hc0 : ∀ c : R, c * 0 = 0) (c : R)
    (s : SparsePoly R) (e : Nat) : (scale c s).coeff e = c * s.coeff e := by
  unfold scale
  rw [coeff_ofCanonicalList]
  exact coeffList_mapTerms_apply (g := id) s.pairwise_toList
    (fun u _ h => h) (hc0 c)

/-- Grind-classes form of `coeff_scale'`: scaling multiplies each coefficient. -/
@[simp, grind =] theorem coeff_scale {S : Type u} [Lean.Grind.Semiring S]
    [DecidableEq S] (c : S) (s : SparsePoly S) (e : Nat) :
    (scale c s).coeff e = c * s.coeff e :=
  coeff_scale' (by grind) c s e

/-- Multiply by the monomial `c · x^e`: add `e` to every exponent and
multiply every coefficient by `c`. The exponent shift is strictly
monotone, so the only canonicalisation is the zero filter. This is the
cheap shift `mul` is built from, `O(s)`. -/
def mulMonomial [Mul R] (e : Nat) (c : R) (s : SparsePoly R) :
    SparsePoly R :=
  ofCanonicalList (mapTerms (fun e' => e + e') (fun _ x => c * x)
      s.terms.toList)
    (mapTerms_canonical s.pairwise_toList fun _ _ _ _ h => by omega).1
    (mapTerms_canonical s.pairwise_toList fun _ _ _ _ h => by omega).2

/-- Coefficient law for {name}`mulMonomial`, under the pointwise
hypothesis it needs; the `Lean.Grind.Semiring` form is
`coeff_mulMonomial`. -/
theorem coeff_mulMonomial' [Mul R] (hc0 : ∀ c : R, c * 0 = 0)
    (s : SparsePoly R) (e : Nat) (c : R) (f : Nat) :
    (mulMonomial e c s).coeff f =
      if e ≤ f then c * s.coeff (f - e) else 0 := by
  unfold mulMonomial
  rw [coeff_ofCanonicalList]
  by_cases hef : e ≤ f
  · rw [if_pos hef]
    have happly := coeffList_mapTerms_apply (g := fun e' => e + e')
      (f := fun _ x => c * x) (l := s.terms.toList) (e := f - e)
      s.pairwise_toList (fun u _ h => by omega) (hc0 c)
    rw [show e + (f - e) = f from by omega] at happly
    rw [happly]
    rfl
  · rw [if_neg hef]
    exact coeffList_mapTerms_of_ne fun u _ h => by omega

/-- Grind-classes form of `coeff_mulMonomial'`: a monomial multiple shifts and scales the coefficients. -/
@[simp, grind =] theorem coeff_mulMonomial {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S] (s : SparsePoly S) (e : Nat)
    (c : S) (f : Nat) :
    (mulMonomial e c s).coeff f =
      if e ≤ f then c * s.coeff (f - e) else 0 :=
  coeff_mulMonomial' (by grind) s e c f

/-- Multiply two sparse polynomials: the canonicalised pairwise product.
Every pair of exponents contributes, exponent sums collide freely, and
{name}`ofTerms` combines the collisions and drops what cancels. The
pairwise products are built through the term `List`s so the kernel can
reduce this specification (`Array.flatMap` stalls kernel reduction; the
value is unchanged). The `@[csimp]` implementation is selected by the
Phase-4 sparse-multiplication bench family; until then compiled code
runs this specification through {name}`ofTerms`'s sort-and-combine
twin. -/
def mul [Add R] [Mul R] (s t : SparsePoly R) : SparsePoly R :=
  ofTerms ((s.terms.toList.flatMap fun a =>
    t.terms.toList.map fun b => (a.1 + b.1, a.2 * b.2)).toArray)

instance [Add R] [Mul R] : Mul (SparsePoly R) where
  mul := mul

/-- Tree accumulator for `mulImpl`: fold every pairwise product into an
`Std.ExtTreeMap` keyed on the exponent sum, replaying {name}`addCoeff`
per key so the accumulated value is exactly the specification's
input-order fold. A stored `0` encodes an exponent whose partial sum
cancelled and is dropped at read-out. -/
def mulTree [Add R] [Mul R] (s t : SparsePoly R) :
    Std.ExtTreeMap Nat R compare :=
  s.terms.foldl (init := ∅) fun acc a =>
    t.terms.foldl (init := acc) fun acc b =>
      acc.insert (a.1 + b.1)
        (addCoeff (acc.getD (a.1 + b.1) 0) (a.2 * b.2))

/-- One product list folded into the tree reads back as the per-key
{name}`addCoeff` fold. -/
private theorem getD_foldl_insert [Add R] (ps : List (Nat × R))
    (acc : Std.ExtTreeMap Nat R compare) (f : Nat) :
    (ps.foldl
        (fun acc t => acc.insert t.1 (addCoeff (acc.getD t.1 0) t.2))
        acc).getD f 0 =
      (ps.filter (fun t => t.1 = f)).foldl
        (fun a t => addCoeff a t.2) (acc.getD f 0) := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih =>
      rw [List.foldl_cons, ih]
      by_cases hpf : p.1 = f
      · rw [List.filter_cons_of_pos (by simpa using hpf), List.foldl_cons,
          Std.ExtTreeMap.getD_insert,
          if_pos (Std.LawfulEqCmp.compare_eq_iff_eq.mpr hpf), hpf]
      · rw [List.filter_cons_of_neg (by simpa using hpf),
          Std.ExtTreeMap.getD_insert,
          if_neg (fun h => hpf (Std.LawfulEqCmp.compare_eq_iff_eq.mp h))]

/-- The tree reads back the whole pairwise-product fold. -/
private theorem getD_mulTree [Add R] [Mul R] (s t : SparsePoly R)
    (f : Nat) :
    (mulTree s t).getD f 0 =
      ((s.terms.toList.flatMap fun a =>
          t.terms.toList.map fun b => (a.1 + b.1, a.2 * b.2)).filter
        (fun u => u.1 = f)).foldl (fun a u => addCoeff a u.2) 0 := by
  unfold mulTree
  rw [← Array.foldl_toList]
  have hnested : ∀ (l : List (Nat × R)) (acc : Std.ExtTreeMap Nat R compare),
      l.foldl (fun acc a => t.terms.foldl
        (fun acc b => acc.insert (a.1 + b.1)
          (addCoeff (acc.getD (a.1 + b.1) 0) (a.2 * b.2))) acc) acc =
      (l.flatMap fun a => t.terms.toList.map fun b =>
        (a.1 + b.1, a.2 * b.2)).foldl
        (fun acc u => acc.insert u.1 (addCoeff (acc.getD u.1 0) u.2)) acc := by
    intro l acc
    rw [List.foldl_flatMap]
    induction l generalizing acc with
    | nil => rfl
    | cons a as ihl =>
        rw [List.foldl_cons, List.foldl_cons, List.foldl_map,
          ← Array.foldl_toList, ihl]
  rw [hnested, getD_foldl_insert, Std.ExtTreeMap.getD_empty]

/-- Runtime implementation of {name}`mul`, selected by the Phase-4
sparse-multiplication bench family (see the SPEC's measured note): the
`ExtTreeMap` accumulation, which beat sort-and-combine on both
collision shapes and the Johnson heap merge everywhere (value-equal to
{name}`mul` by `mul_eq_impl`, registered `@[csimp]`). -/
def mulImpl [Add R] [Mul R] (s t : SparsePoly R) : SparsePoly R where
  terms := ((mulTree s t).toList.filter (fun u => u.2 ≠ 0)).toArray
  canonical := by
    constructor
    · rw [List.toList_toArray]
      refine List.Pairwise.imp ?_
        (List.Pairwise.filter _ Std.ExtTreeMap.ordered_keys_toList)
      intro a b hab
      exact Nat.compare_eq_lt.mp hab
    · intro u hu
      have := Array.mem_def.mp hu
      rw [List.toList_toArray] at this
      have := (List.mem_filter.mp this).2
      simpa using this

/-- The filtered ordered read-out has the tree's coefficients. -/
private theorem coeffList_mulImpl [Add R] [Mul R] (s t : SparsePoly R)
    (f : Nat) :
    coeffList ((mulTree s t).toList.filter (fun u => u.2 ≠ 0)) f =
      (mulTree s t).getD f 0 := by
  cases hf : (mulTree s t)[f]? with
  | none =>
      rw [Std.ExtTreeMap.getD_eq_getD_getElem?, hf, Option.getD_none]
      refine coeffList_eq_zero ?_
      intro u hu huf
      have hmem := (List.mem_filter.mp hu).1
      have hsome : (mulTree s t)[u.1]? = some u.2 :=
        Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
      rw [huf, hf] at hsome
      cases hsome
  | some v =>
      rw [Std.ExtTreeMap.getD_eq_getD_getElem?, hf, Option.getD_some]
      by_cases hv : v = 0
      · subst hv
        refine coeffList_eq_zero ?_
        intro u hu huf
        obtain ⟨hmem, hnz⟩ := List.mem_filter.mp hu
        have hsome : (mulTree s t)[u.1]? = some u.2 :=
          Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
        rw [huf, hf] at hsome
        have h20 := Option.some.inj hsome
        simp [← h20] at hnz
      · have hval : coeffList ((mulTree s t).toList.filter
            (fun u => u.2 ≠ 0)) (f, v).1 = (f, v).2 := by
          refine coeffList_eq_of_mem ?_ ?_ rfl
          · refine List.Pairwise.imp ?_
              (List.Pairwise.filter _ Std.ExtTreeMap.ordered_keys_toList)
            intro a b hab
            exact Nat.compare_eq_lt.mp hab
          · refine List.mem_filter.mpr ⟨?_, by simpa using hv⟩
            exact Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hf
        exact hval

/-- The specification and the tree accumulation compute the same
polynomial, with no algebra assumed: the tree replays the
{name}`addCoeff` steps per key in the specification's input order. -/
theorem mul_eq_mulImpl [Add R] [Mul R] (s t : SparsePoly R) :
    mul s t = mulImpl s t := by
  apply ext_coeff
  intro f
  show (mul s t).coeff f = coeffList _ f
  unfold mul mulImpl
  rw [coeff_ofTerms_addCoeff, List.toList_toArray, List.toList_toArray,
    coeffList_mulImpl, getD_mulTree]

/-- Register the tree accumulation as the compiled implementation of
{name}`mul`. -/
@[csimp]
theorem mul_eq_impl : @mul = @mulImpl := by
  funext R _ _ _ _ s t
  exact mul_eq_mulImpl s t

/-- Raise to a power by binary powering over {name}`mul`. A caller
wanting `f(x^k)` should use `substPow`, never `pow`: the cost
difference is the whole reason this library exists. -/
def pow [One R] [Add R] [Mul R] (s : SparsePoly R) (n : Nat) :
    SparsePoly R :=
  if _h : n = 0 then 1
  else if n % 2 = 1 then s.mul (pow (s.mul s) (n / 2))
  else pow (s.mul s) (n / 2)
termination_by n
decreasing_by all_goals omega

instance [One R] [Add R] [Mul R] : Pow (SparsePoly R) Nat where
  pow := pow

/-- Divisibility by existence of a cofactor, matching the `DensePoly`
convention. -/
instance [Add R] [Mul R] : Dvd (SparsePoly R) where
  dvd p q := ∃ r, q = p * r

/-- Divisibility unfolds to a cofactor witness. -/
theorem dvd_def [Add R] [Mul R] (p q : SparsePoly R) :
    p ∣ q ↔ ∃ r, q = p * r :=
  Iff.rfl

section Laws

variable {S : Type u} [Lean.Grind.Semiring S] [DecidableEq S]

/-- Addition is commutative. -/
theorem add_comm (s t : SparsePoly S) : s + t = t + s := by
  apply ext_coeff
  intro e
  simp only [coeff_add]
  grind

/-- Addition is associative. -/
theorem add_assoc (s t u : SparsePoly S) : s + t + u = s + (t + u) := by
  apply ext_coeff
  intro e
  simp only [coeff_add]
  grind

/-- Zero is a right identity for addition. -/
@[simp, grind =] theorem add_zero (s : SparsePoly S) : s + 0 = s := by
  apply ext_coeff
  intro e
  simp only [coeff_add, coeff_zero]
  grind

/-- Zero is a left identity for addition. -/
@[simp, grind =] theorem zero_add (s : SparsePoly S) : 0 + s = s := by
  apply ext_coeff
  intro e
  simp only [coeff_add, coeff_zero]
  grind

/- The multiplicative ring laws (`mul_assoc`, `mul_comm`, `mul_one`,
`one_mul`, `mul_zero`, `zero_mul`, and the two distributive laws) live
in `HexSparsePoly/Dense.lean`: the SPEC proves them by transport through
`toDense`, so their proofs need the conversion layer this file precedes.
`coeff_mul` likewise. -/

end Laws

end SparsePoly

end Hex
