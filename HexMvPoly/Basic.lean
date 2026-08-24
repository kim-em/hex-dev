/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.Conditional
public import HexBasic.ListShim
public import HexMvPoly.Mono

@[expose] public section
set_option backward.proofsInPublic true

/-!
The canonical distributed representation of multivariate polynomials,
its constructors, and ordered term-iteration API.
-/

namespace Hex

open scoped Hex

universe u

/-- A canonical distributed multivariate polynomial. The backing tree map
stores only nonzero coefficients and uses the explicit comparator `cmp`. -/
structure MvPoly (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  /-- Internal backing map. Consumers should use `termsList`, `foldTerms`,
  `monomials`, and `termCount` so the representation can change. -/
  termsInternal : Std.ExtTreeMap (Mono n) R cmp
  /-- Canonical-form invariant: zero coefficients are absent. -/
  nonzeroInternal : ∀ m : Mono n, termsInternal[m]? ≠ some 0

namespace MvPoly

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

section Representation

variable [Zero R]

/-- The absent coefficient of a monomial. -/
@[inline] def coeff? (m : Mono n) (p : MvPoly n R cmp) : Option R :=
  p.termsInternal[m]?

/-- Coefficient of a monomial, returning zero outside the support. -/
@[inline] def coeff (m : Mono n) (p : MvPoly n R cmp) : R :=
  (coeff? m p).getD 0

/-- Ordered term list, in increasing `cmp` order. -/
def termsList (p : MvPoly n R cmp) : List (Mono n × R) :=
  p.termsInternal.toList

/-- Compatibility spelling for consumers that iterate over all terms. -/
def toList (p : MvPoly n R cmp) : List (Mono n × R) :=
  termsList p

/-- Fold over terms in increasing `cmp` order. -/
@[inline] def foldTerms (f : α → Mono n → R → α) (init : α)
    (p : MvPoly n R cmp) : α :=
  p.termsInternal.foldl f init

/-- Monomials in the support, in increasing `cmp` order. -/
def monomials (p : MvPoly n R cmp) : List (Mono n) :=
  (termsList p).map Prod.fst

/-- Monomials in the support, in increasing `cmp` order. -/
def support (p : MvPoly n R cmp) : List (Mono n) :=
  monomials p

/-- The canonical support enumeration contains no duplicate monomials. -/
theorem monomials_nodup (p : MvPoly n R cmp) : p.monomials.Nodup := by
  unfold monomials termsList
  rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
  exact p.termsInternal.nodup_keys

/-- A monomial occurs in the ordered monomial list exactly when coefficient
lookup succeeds. -/
theorem mem_monomials_iff_isSome (m : Mono n) (p : MvPoly n R cmp) :
    m ∈ p.monomials ↔ (p.coeff? m).isSome := by
  unfold monomials termsList coeff?
  rw [Std.ExtTreeMap.map_fst_toList_eq_keys, Std.ExtTreeMap.mem_keys,
    Std.ExtTreeMap.mem_iff_isSome_getElem?]

/-- A monomial occurs in the ordered monomial list exactly when its
coefficient is nonzero. -/
@[simp] theorem mem_monomials_iff (m : Mono n) (p : MvPoly n R cmp) :
    m ∈ p.monomials ↔ coeff m p ≠ 0 := by
  rw [mem_monomials_iff_isSome]
  unfold coeff
  cases hcoeff : coeff? m p with
  | none => simp
  | some c =>
      have hc : c ≠ 0 := by
        intro hzero
        apply p.nonzeroInternal m
        unfold coeff? at hcoeff
        simpa [hzero] using hcoeff
      simp [hc]

/-- Membership in the support is equivalent to having a nonzero
coefficient. -/
@[simp] theorem mem_support_iff (m : Mono n) (p : MvPoly n R cmp) :
    m ∈ p.support ↔ coeff m p ≠ 0 := by
  unfold support
  exact mem_monomials_iff m p

/-- A monomial outside the canonical support has coefficient zero. -/
theorem coeff_eq_zero_of_not_mem (m : Mono n) (p : MvPoly n R cmp)
    (h : m ∉ p.monomials) :
    coeff m p = 0 := by
  unfold coeff
  cases hcoeff : coeff? m p with
  | none => rfl
  | some c =>
      exfalso
      exact h ((mem_monomials_iff_isSome m p).mpr (by simp [hcoeff]))

/-- A stored term carries exactly the coefficient returned by lookup. -/
theorem coeff_eq_of_mem_terms (p : MvPoly n R cmp) {m : Mono n} {c : R}
    (h : (m, c) ∈ p.termsList) :
    coeff m p = c := by
  unfold termsList at h
  have hcoeff := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp h
  unfold coeff coeff?
  rw [hcoeff]
  rfl

/-- Number of nonzero terms. -/
@[inline] def termCount (p : MvPoly n R cmp) : Nat :=
  p.termsInternal.size

/-- Greatest term in `cmp` order.

This uses the tree's logarithmic maximum-key query followed by one logarithmic
lookup. Keeping the definition in terms of the public key and lookup API gives
downstream proofs access to the complete maximum-entry specification even
though `Std.ExtTreeMap.maxEntry?` currently lacks corresponding lemmas. -/
@[inline] def maxTerm? (p : MvPoly n R cmp) : Option (Mono n × R) :=
  p.termsInternal.maxKey?.bind fun m =>
    p.termsInternal[m]?.map fun c => (m, c)

/-- A maximum term is exactly a stored coefficient whose monomial bounds
every supported monomial in `cmp` order. -/
theorem maxTerm?_eq_some_iff (p : MvPoly n R cmp)
    (m : Mono n) (c : R) :
    p.maxTerm? = some (m, c) ↔
      p.coeff? m = some c ∧
        ∀ k ∈ p.monomials, (cmp k m).isLE := by
  constructor
  · intro hterm
    unfold maxTerm? at hterm
    cases hmax : p.termsInternal.maxKey? with
    | none =>
        simp [hmax] at hterm
    | some k =>
        cases hcoeff : p.termsInternal[k]? with
        | none =>
            simp [hmax, hcoeff] at hterm
        | some value =>
            simp only [hmax, Option.bind_some, hcoeff, Option.map_some,
              Option.some.injEq, Prod.mk.injEq] at hterm
            rcases hterm with ⟨rfl, rfl⟩
            constructor
            · exact hcoeff
            · intro k hk
              have hbound :=
                (Std.ExtTreeMap.maxKey?_eq_some_iff_mem_and_forall.mp hmax).2
                  k
              apply hbound
              rw [Std.ExtTreeMap.mem_iff_isSome_getElem?]
              exact (mem_monomials_iff_isSome k p).mp hk
  · rintro ⟨hcoeff, hbound⟩
    change p.termsInternal[m]? = some c at hcoeff
    have hmem : m ∈ p.termsInternal := by
      rw [Std.ExtTreeMap.mem_iff_isSome_getElem?]
      simp [hcoeff]
    have hmax : p.termsInternal.maxKey? = some m := by
      apply Std.ExtTreeMap.maxKey?_eq_some_iff_mem_and_forall.mpr
      refine ⟨hmem, ?_⟩
      intro k hk
      apply hbound k
      rw [mem_monomials_iff_isSome]
      unfold coeff?
      rw [← Std.ExtTreeMap.mem_iff_isSome_getElem?]
      exact hk
    unfold maxTerm?
    rw [hmax]
    simp [hcoeff]

/-- The zero polynomial. -/
def zero : MvPoly n R cmp where
  termsInternal := ∅
  nonzeroInternal := by simp

instance : Zero (MvPoly n R cmp) where
  zero := zero

instance : Inhabited (MvPoly n R cmp) :=
  ⟨0⟩

/-- The stored representation contains no explicit zero coefficient. -/
theorem coeff?_ne_zero (p : MvPoly n R cmp) (m : Mono n) :
    coeff? m p ≠ some 0 :=
  p.nonzeroInternal m

/-- Coefficients determine a canonical multivariate polynomial. -/
@[ext] theorem ext {p q : MvPoly n R cmp}
    (h : ∀ m, coeff m p = coeff m q) : p = q := by
  cases p with
  | mk pt hp =>
    cases q with
    | mk qt hq =>
      have ht : pt = qt := Std.ExtTreeMap.ext_getElem? fun m => by
        have hm := h m
        change pt[m]?.getD 0 = qt[m]?.getD 0 at hm
        cases hpt : pt[m]? with
        | none =>
          cases hqt : qt[m]? with
          | none => rfl
          | some c =>
            simp [hpt, hqt] at hm
            exfalso
            apply hq m
            simp [hqt, ← hm]
        | some c =>
          cases hqt : qt[m]? with
          | none =>
            simp [hpt, hqt] at hm
            exfalso
            apply hp m
            simp [hpt, hm]
          | some d =>
            simp [hpt, hqt] at hm
            simp [hm]
      cases ht
      rfl

/-- Boolean equality compares ordered term lists, avoiding the tree map's
derived equality implementation in the kernel replay path. -/
instance [DecidableEq R] : BEq (MvPoly n R cmp) where
  beq p q := decide (p.termsList = q.termsList)

instance [DecidableEq R] : LawfulBEq (MvPoly n R cmp) where
  eq_of_beq := by
    intro p q h
    change decide (p.termsList = q.termsList) = true at h
    have hl : p.termsList = q.termsList := of_decide_eq_true h
    have ht : p.termsInternal = q.termsInternal :=
      Std.ExtTreeMap.toList_inj.mp hl
    cases p with
    | mk pt hp =>
      cases q with
      | mk qt hq =>
        simp only at ht
        subst ht
        rfl
  rfl := by
    intro p
    change decide (p.termsList = p.termsList) = true
    simp

instance [DecidableEq R] : DecidableEq (MvPoly n R cmp) := fun p q =>
  match decEq p.termsList q.termsList with
  | isTrue hl =>
      isTrue <| by
        have ht : p.termsInternal = q.termsInternal :=
          Std.ExtTreeMap.toList_inj.mp hl
        cases p with
        | mk pt hp =>
          cases q with
          | mk qt hq =>
            simp only at ht
            subst ht
            rfl
  | isFalse hl =>
      isFalse fun hpq => hl (congrArg termsList hpq)

/-- A single term, dropping it when its coefficient is zero. -/
def monomial [BEq R] [LawfulBEq R] (m : Mono n) (c : R) : MvPoly n R cmp :=
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  if hc : c = 0 then
    0
  else
    { termsInternal := (∅ : Std.ExtTreeMap (Mono n) R cmp).insert m c
      nonzeroInternal := by
        intro k
        rw [Std.ExtTreeMap.getElem?_insert]
        split
        · simpa using hc
        · simp }

/-- A constant polynomial. -/
def C [BEq R] [LawfulBEq R] (c : R) : MvPoly n R cmp :=
  monomial Mono.zero c

/-- The variable `xᵢ`. -/
def X [One R] [BEq R] [LawfulBEq R] (i : Fin n) : MvPoly n R cmp :=
  monomial (Mono.unit i) 1

/-- Add `c` to the coefficient at `m`, deleting the term if the new
coefficient is zero. -/
def addMonomial [Add R] [BEq R] [LawfulBEq R]
    (p : MvPoly n R cmp) (m : Mono n) (c : R) : MvPoly n R cmp :=
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  { termsInternal := p.termsInternal.alter m fun old =>
      let c' := old.getD 0 + c
      if c' = 0 then none else some c'
    nonzeroInternal := by
      intro k
      rw [Std.ExtTreeMap.getElem?_alter]
      split
      · simp only
        split <;> simp_all
      · exact p.nonzeroInternal k }

end Representation

/-- Build a polynomial by summing duplicate monomials and dropping all
zero coefficients. Only additive structure is needed by the constructor. -/
def ofTerms [Zero R] [Add R] [BEq R] [LawfulBEq R]
    (ts : List (Mono n × R)) : MvPoly n R cmp :=
  ts.foldl (fun p t => addMonomial p t.1 t.2) 0

/-- Every coefficient of the zero polynomial is zero. -/
@[simp] theorem coeff_zero [Zero R] (m : Mono n) :
    coeff m (0 : MvPoly n R cmp) = 0 := by
  change ((∅ : Std.ExtTreeMap (Mono n) R cmp)[m]?).getD 0 = 0
  simp

/-- A monomial polynomial has its supplied coefficient at the selected
monomial and zero elsewhere. -/
theorem coeff_monomial [Zero R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (m m' : Mono n) (c : R) :
    coeff m (monomial m' c : MvPoly n R cmp) =
      if m = m' then c else 0 := by
  by_cases hc : c = 0
  · rw [monomial, Hex.dite_eq_left hc]
    change ((∅ : Std.ExtTreeMap (Mono n) R cmp)[m]?).getD 0 = _
    simp [hc]
  · rw [monomial, Hex.dite_eq_right hc]
    unfold coeff coeff?
    rw [Std.ExtTreeMap.getElem?_insert]
    by_cases hm : m = m'
    · subst m
      simp
    · have hm' : m' ≠ m := fun h => hm h.symm
      simp [hm, hm']

/-- A constant polynomial is supported at the zero monomial. -/
theorem coeff_C [Zero R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (m : Mono n) (c : R) :
    coeff m (C c : MvPoly n R cmp) =
      if m = Mono.zero then c else 0 := by
  simp [C, coeff_monomial]

/-- The constant polynomial with zero coefficient is the zero polynomial. -/
@[simp] theorem C_zero [Zero R] [BEq R] [LawfulBEq R] [DecidableEq R] :
    C (0 : R) = (0 : MvPoly n R cmp) := by
  apply ext
  intro m
  rw [coeff_C, coeff_zero]
  split <;> rfl

/-- A variable polynomial is supported at its unit monomial. -/
theorem coeff_X [Zero R] [One R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (m : Mono n) (i : Fin n) :
    coeff m (X i : MvPoly n R cmp) =
      if m = Mono.unit i then 1 else 0 := by
  simp [X, coeff_monomial]

/-- Adding a monomial changes only the selected coefficient. -/
theorem coeff_addMonomial [Zero R] [Add R] [BEq R] [LawfulBEq R]
    [DecidableEq R]
    (p : MvPoly n R cmp) (m k : Mono n) (c : R) :
    coeff k (addMonomial p m c) =
      if k = m then coeff k p + c else coeff k p := by
  unfold addMonomial coeff coeff?
  rw [Std.ExtTreeMap.getElem?_alter]
  by_cases hkm : k = m
  · subst k
    simp
    split <;> simp_all
  · have hmk : m ≠ k := fun h => hkm h.symm
    simp [hkm, hmk]

/-- `ofTerms` sums the coefficients of duplicate monomials. -/
theorem coeff_ofTerms [Lean.Grind.Semiring R] [BEq R] [LawfulBEq R]
    [DecidableEq R]
    (m : Mono n) (ts : List (Mono n × R)) :
    coeff m (ofTerms ts : MvPoly n R cmp) =
      (ts.filter (fun t => t.1 = m)).foldl (fun acc t => acc + t.2) 0 := by
  have aux : ∀ (us : List (Mono n × R)) (init : MvPoly n R cmp),
      coeff m (us.foldl (fun p t => addMonomial p t.1 t.2) init) =
        (us.filter (fun t => t.1 = m)).foldl
          (fun acc t => acc + t.2) (coeff m init) := by
    intro us
    induction us with
    | nil =>
      intro init
      rfl
    | cons t us ih =>
      intro init
      rw [List.foldl_cons, ih]
      by_cases ht : t.1 = m
      · simp [ht, coeff_addMonomial]
      · have hmt : m ≠ t.1 := fun h => ht h.symm
        simp [ht, hmt, coeff_addMonomial]
  simpa [ofTerms] using aux ts (0 : MvPoly n R cmp)

/-- Filtering the canonical term list at one monomial recovers its
coefficient. -/
theorem coeff_terms [Lean.Grind.Semiring R] [BEq R] [LawfulBEq R]
    [DecidableEq R]
    (m : Mono n) (p : MvPoly n R cmp) :
    (p.termsList.filter (fun t => t.1 = m)).foldl
        (fun acc t => acc + t.2) 0 =
      coeff m p := by
  have hnodup : p.termsList.Nodup := by
    have hkeys :=
      Std.ExtTreeMap.distinct_keys_toList (t := p.termsInternal)
    exact hkeys.imp fun hcmp hab => by
      cases hab
      simp at hcmp
  cases hcoeff : p.termsInternal[m]? with
  | none =>
    have hfilter : p.termsList.filter (fun t => t.1 = m) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro t ht
      rcases List.mem_filter.mp ht with ⟨ht, htm⟩
      have htcoeff :=
        (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).mp ht
      have htm' := of_decide_eq_true htm
      subst m
      simp_all
    simp [hfilter, coeff, coeff?, hcoeff]
  | some c =>
    have hfilter : p.termsList.filter (fun t => t.1 = m) = [(m, c)] := by
      apply List.Perm.eq_singleton
      rw [List.perm_ext_iff_of_nodup (hnodup.filter _) (by simp)]
      intro t
      constructor
      · intro ht
        rcases List.mem_filter.mp ht with ⟨ht, htm⟩
        have htcoeff :=
          (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).mp ht
        have htm' := of_decide_eq_true htm
        subst m
        simp_all
      · intro ht
        simp only [List.mem_singleton] at ht
        subst t
        exact List.mem_filter.mpr
          ⟨(Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).mpr hcoeff, by simp⟩
    rw [hfilter]
    simp only [List.foldl_cons, List.foldl_nil]
    unfold coeff coeff?
    rw [hcoeff]
    change 0 + c = c
    exact Lean.Grind.AddCommMonoid.zero_add c

end MvPoly

end Hex
