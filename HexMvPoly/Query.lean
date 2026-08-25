/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Operations

public section

/-!
Degree, variable, leading-term, and support-restriction queries for
`Hex.MvPoly`.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Maximum total degree of a supported monomial, or zero for the zero
polynomial. -/
def totalDegree [Zero R] (p : MvPoly n R cmp) : Nat :=
  p.foldTerms (fun d m _ => max d m.degree) 0

/-- Maximum exponent of variable `i`, or zero for the zero polynomial. -/
def degreeOf [Zero R] (i : Fin n) (p : MvPoly n R cmp) : Nat :=
  p.foldTerms (fun d m _ => max d (Mono.degreeOf i m)) 0

/-- Total degree is the maximum monomial degree in ordered term iteration. -/
theorem totalDegree_eq [Zero R] (p : MvPoly n R cmp) :
    totalDegree p =
      p.foldTerms (fun d m _ => max d (Mono.degree m)) 0 := by
  rfl

/-- Per-variable degree is the maximum exponent in ordered term iteration. -/
theorem degreeOf_eq [Zero R] (i : Fin n) (p : MvPoly n R cmp) :
    degreeOf i p =
      p.foldTerms (fun d m _ => max d (Mono.degreeOf i m)) 0 := by
  rfl

/-- A one-term polynomial carries its monomial exponent when its coefficient
is nonzero. -/
theorem degreeOf_monomial [Zero R] [BEq R] [LawfulBEq R]
    [DecidableEq R] (i : Fin n) (m : Mono n) (c : R) :
    degreeOf i (monomial m c : MvPoly n R cmp) =
      if c = 0 then 0 else m[i] := by
  unfold degreeOf foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  change (monomial m c : MvPoly n R cmp).termsList.foldl
      (fun d term => max d (Mono.degreeOf i term.1)) 0 = _
  rw [termsList_monomial]
  by_cases hc : c = 0 <;> simp [hc, Mono.degreeOf]

/-- The exponent of a supported monomial is bounded by the polynomial's
degree in that variable. -/
theorem degreeOf_monomial_le [Zero R] (i : Fin n) (p : MvPoly n R cmp)
    {m : Mono n} (hm : m ∈ p.monomials) :
    Mono.degreeOf i m ≤ degreeOf i p := by
  unfold monomials at hm
  rcases List.mem_map.mp hm with ⟨term, hterm, hfirst⟩
  rcases term with ⟨k, c⟩
  simp only at hfirst
  subst k
  unfold degreeOf foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  change Mono.degreeOf i m ≤ p.termsList.foldl
    (fun d term => max d (Mono.degreeOf i term.1)) 0
  have le_start (terms : List (Mono n × R)) (init : Nat) :
      init ≤ terms.foldl
        (fun d term => max d (Mono.degreeOf i term.1)) init := by
    induction terms generalizing init with
    | nil => exact Nat.le_refl _
    | cons term terms ih =>
        exact Nat.le_trans (Nat.le_max_left ..) (ih _)
  have member_bound :
      ∀ (terms : List (Mono n × R)) (init : Nat) {term},
        term ∈ terms →
          Mono.degreeOf i term.1 ≤ terms.foldl
            (fun d term => max d (Mono.degreeOf i term.1)) init := by
    intro terms init term hterm
    induction terms generalizing init with
    | nil => simp at hterm
    | cons head terms ih =>
        simp only [List.foldl_cons]
        cases List.mem_cons.mp hterm with
        | inl h =>
            subst head
            exact Nat.le_trans (Nat.le_max_right ..) (le_start terms _)
        | inr h => exact ih _ h
  exact member_bound p.termsList 0 hterm

/-- Coordinatewise maximum of all supported exponent vectors. -/
def degrees [Zero R] (p : MvPoly n R cmp) : Mono n :=
  p.foldTerms (fun d m _ => Mono.lcm d m) Mono.zero

/-- The coordinatewise degree vector is a fold over the canonical terms. -/
theorem degrees_eq [Zero R] (p : MvPoly n R cmp) :
    degrees p =
      p.foldTerms (fun d m _ => Mono.lcm d m) Mono.zero := by
  rfl

/-- Each coordinate of `degrees` is the corresponding per-variable degree. -/
@[simp] theorem getElem_degrees [Zero R]
    (p : MvPoly n R cmp) (i : Fin n) :
    p.degrees[i] = degreeOf i p := by
  have fold_get :
      ∀ (ts : List (Mono n × R)) (d : Mono n) (e : Nat),
        d[i] = e →
          (ts.foldl (fun d term => Mono.lcm d term.1) d)[i] =
            ts.foldl (fun e term => max e (Mono.degreeOf i term.1)) e := by
    intro ts
    induction ts with
    | nil =>
        intro d e h
        exact h
    | cons term ts ih =>
        intro d e h
        simp only [List.foldl_cons]
        apply ih
        rw [Mono.getElem_lcm, h]
        rfl
  unfold degrees degreeOf foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList,
    Std.ExtTreeMap.foldl_eq_foldl_toList]
  exact fold_get p.termsInternal.toList Mono.zero 0 (Mono.getElem_zero i)

/-- Variables occurring in at least one supported monomial, in increasing
index order. -/
def vars [Zero R] (p : MvPoly n R cmp) : List (Fin n) :=
  Mono.support p.degrees

/-- Variables are the support of the coordinatewise degree vector. -/
theorem vars_eq [Zero R] (p : MvPoly n R cmp) :
    vars p = Mono.support p.degrees := by
  rfl

/-- A variable occurs exactly when its maximum exponent is nonzero. -/
@[simp] theorem mem_vars_iff [Zero R] (i : Fin n) (p : MvPoly n R cmp) :
    i ∈ p.vars ↔ degreeOf i p ≠ 0 := by
  rw [vars_eq]
  unfold Mono.support
  rw [List.mem_filter]
  simp only [List.mem_finRange, true_and]
  change (p.degrees[i] != 0) = true ↔ degreeOf i p ≠ 0
  rw [getElem_degrees]
  simp

/-- A polynomial with no occurring variables is its constant coefficient. -/
theorem eq_C_of_vars_eq_nil [Zero R] [BEq R] [LawfulBEq R]
    [DecidableEq R] (p : MvPoly n R cmp) (hvars : p.vars = []) :
    p = C (coeff Mono.zero p) := by
  apply ext
  intro m
  rw [coeff_C]
  by_cases hmzero : m = Mono.zero
  · rw [ite_eq_left hmzero]
    subst m
    rfl
  · rw [ite_eq_right hmzero]
    apply coeff_eq_zero_of_not_mem
    intro hmem
    have hsupport : m.support ≠ [] := by
      intro hnil
      apply hmzero
      apply Vector.ext
      intro j hj
      let i : Fin n := ⟨j, hj⟩
      change m[i] = (Mono.zero : Mono n)[i]
      rw [Mono.getElem_zero]
      by_cases hi : m[i] = 0
      · exact hi
      · have himem : i ∈ m.support := by
          unfold Mono.support
          rw [List.mem_filter]
          refine ⟨List.mem_finRange _, ?_⟩
          exact bne_iff_ne.mpr hi
        rw [hnil] at himem
        contradiction
    cases hs : m.support with
    | nil => exact False.elim (hsupport hs)
    | cons i is =>
        have himem : i ∈ m.support := by
          rw [hs]
          exact List.mem_cons_self
        have hi : m[i] ≠ 0 := by
          unfold Mono.support at himem
          rw [List.mem_filter] at himem
          simpa using himem.2
        have hdegree : degreeOf i p = 0 := by
          by_cases hzero : degreeOf i p = 0
          · exact hzero
          · have hivar : i ∈ p.vars := (mem_vars_iff i p).mpr hzero
            rw [hvars] at hivar
            contradiction
        have hle := degreeOf_monomial_le i p hmem
        rw [hdegree] at hle
        change m[i] ≤ 0 at hle
        omega

/-- Greatest supported term in the polynomial's monomial order. -/
@[expose] def leadingTerm [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Option (Mono n × R) :=
  p.maxTerm?

/-- The leading term is the maximum entry of the canonical term map. -/
theorem leadingTerm_eq [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    leadingTerm p = p.maxTerm? := by
  rfl

/-- A leading term is exactly a stored coefficient whose monomial bounds
every monomial in the canonical support. -/
theorem leadingTerm_eq_some_iff [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) (m : Mono n) (c : R) :
    p.leadingTerm = some (m, c) ↔
      p.coeff? m = some c ∧
        ∀ k ∈ p.monomials, (cmp k m).isLE :=
  maxTerm?_eq_some_iff p m c

/-- The coefficient recorded by a leading term is the public coefficient at
its monomial. -/
theorem coeff_eq_of_leadingTerm [Zero R] [IsMonomialOrder cmp]
    {p : MvPoly n R cmp} {m : Mono n} {c : R}
    (h : p.leadingTerm = some (m, c)) :
    p.coeff m = c := by
  have hcoeff := (leadingTerm_eq_some_iff p m c).mp h |>.1
  unfold coeff
  rw [hcoeff]
  rfl

/-- Every supported monomial is at most the leading monomial. -/
theorem le_leadingTerm [Zero R] [IsMonomialOrder cmp]
    {p : MvPoly n R cmp} {m : Mono n} {c : R}
    (h : p.leadingTerm = some (m, c)) :
    ∀ k ∈ p.monomials, (cmp k m).isLE :=
  (leadingTerm_eq_some_iff p m c).mp h |>.2

/-- Greatest supported monomial in the polynomial's monomial order. -/
def leadingMono [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Option (Mono n) :=
  p.leadingTerm.map Prod.fst

/-- The leading monomial is the monomial projection of the leading term. -/
theorem leadingMono_eq [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    leadingMono p = p.leadingTerm.map Prod.fst := by
  rfl

/-- Compatibility spelling for `leadingMono`. -/
def leadingMonomial [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Option (Mono n) :=
  p.leadingMono

/-- The compatibility spelling agrees with `leadingMono`. -/
theorem leadingMonomial_eq [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    leadingMonomial p = p.leadingMono := by
  rfl

/-- Coefficient of the greatest supported monomial, or zero for the zero
polynomial. -/
def leadingCoeff [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : R :=
  match p.leadingTerm with
  | none => 0
  | some term => term.2

/-- The leading coefficient is the coefficient projection of the leading
term, defaulting to zero. -/
theorem leadingCoeff_eq [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    leadingCoeff p = (p.leadingTerm.map Prod.snd).getD 0 := by
  unfold leadingCoeff
  cases p.leadingTerm <;> rfl

/-- A nonzero constant has its defining coefficient as leading term. -/
theorem leadingTerm_C [Zero R] [BEq R] [LawfulBEq R] [DecidableEq R]
    [IsMonomialOrder cmp] {c : R} (hc : c ≠ 0) :
    leadingTerm (C c : MvPoly n R cmp) = some (Mono.zero, c) := by
  apply (leadingTerm_eq_some_iff (C c : MvPoly n R cmp) Mono.zero c).mpr
  constructor
  · unfold coeff? C monomial
    rw [Hex.dite_eq_right hc, Std.ExtTreeMap.getElem?_insert_self]
  · intro m hm
    have hcoeff := (mem_monomials_iff m (C c : MvPoly n R cmp)).mp hm
    rw [coeff_C] at hcoeff
    by_cases hmzero : m = Mono.zero
    · subst m
      rw [show cmp Mono.zero Mono.zero = .eq from Std.ReflCmp.compare_self]
      trivial
    · rw [Hex.ite_eq_right hmzero] at hcoeff
      contradiction

/-- A nonzero one-term polynomial has its defining term as leading term. -/
theorem leadingTerm_monomial [Zero R] [BEq R] [LawfulBEq R]
    [DecidableEq R] [IsMonomialOrder cmp] {m : Mono n} {c : R}
    (hc : c ≠ 0) :
    leadingTerm (monomial m c : MvPoly n R cmp) = some (m, c) := by
  apply (leadingTerm_eq_some_iff
    (monomial m c : MvPoly n R cmp) m c).mpr
  constructor
  · unfold coeff? monomial
    rw [Hex.dite_eq_right hc, Std.ExtTreeMap.getElem?_insert_self]
  · intro k hk
    have hcoeff :=
      (mem_monomials_iff k (monomial m c : MvPoly n R cmp)).mp hk
    rw [coeff_monomial] at hcoeff
    by_cases hkm : k = m
    · subst k
      rw [show cmp m m = .eq from Std.ReflCmp.compare_self]
      trivial
    · rw [Hex.ite_eq_right hkm] at hcoeff
      contradiction

/-- A polynomial has no leading term exactly when it is zero. -/
@[simp] theorem leadingTerm_eq_none_iff [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : p.leadingTerm = none ↔ p = 0 := by
  constructor
  · intro hnone
    unfold leadingTerm maxTerm? at hnone
    cases hmax : p.termsInternal.maxKey? with
    | none =>
        have hempty : p.termsInternal = ∅ :=
          Std.ExtTreeMap.maxKey?_eq_none_iff.mp hmax
        apply ext
        intro m
        rw [coeff_zero]
        unfold coeff coeff?
        rw [hempty]
        simp
    | some m =>
        have hmem : m ∈ p.termsInternal :=
          (Std.ExtTreeMap.maxKey?_eq_some_iff_mem_and_forall.mp hmax).1
        have hisSome : p.termsInternal[m]?.isSome := by
          rw [← Std.ExtTreeMap.mem_iff_isSome_getElem?]
          exact hmem
        cases hcoeff : p.termsInternal[m]? with
        | none => simp [hcoeff] at hisSome
        | some c => simp [hmax, hcoeff] at hnone
  · rintro rfl
    unfold leadingTerm maxTerm?
    change
      ((∅ : Std.ExtTreeMap (Mono n) R cmp).maxKey?.bind fun m =>
        (∅ : Std.ExtTreeMap (Mono n) R cmp)[m]?.map fun c => (m, c)) = none
    rw [Std.ExtTreeMap.maxKey?_empty]
    rfl

/-- Retain exactly the terms whose monomials satisfy `keep`. -/
@[expose] def restrictBy [Zero R]
    (keep : Mono n → Bool) (p : MvPoly n R cmp) : MvPoly n R cmp where
  termsInternal := p.termsInternal.filter fun m _ => keep m
  nonzeroInternal := by
    intro m
    rw [Std.ExtTreeMap.getElem?_filter']
    cases hcoeff : p.termsInternal[m]? with
    | none => simp [Option.filter]
    | some c =>
      cases hkeep : keep m
      · simp [Option.filter]
      · have hc : c ≠ 0 := by
          intro hzero
          apply p.nonzeroInternal m
          rw [hcoeff, hzero]
        simpa [Option.filter] using hc

/-- Retain the terms whose exponent of `i` is at most `bound`. -/
@[expose] def restrictDegree [Zero R]
    (i : Fin n) (bound : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.restrictBy fun m => decide (Mono.degreeOf i m ≤ bound)

/-- Per-variable restriction is restriction by the corresponding exponent
bound. -/
theorem restrictDegree_eq [Zero R]
    (i : Fin n) (bound : Nat) (p : MvPoly n R cmp) :
    restrictDegree i bound p =
      p.restrictBy fun m => decide (Mono.degreeOf i m ≤ bound) := by
  rfl

/-- Retain the terms whose total degree is at most `bound`. -/
@[expose] def restrictTotalDegree [Zero R]
    (bound : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.restrictBy fun m => decide (Mono.degree m ≤ bound)

/-- Total-degree restriction is restriction by the monomial degree bound. -/
theorem restrictTotalDegree_eq [Zero R]
    (bound : Nat) (p : MvPoly n R cmp) :
    restrictTotalDegree bound p =
      p.restrictBy fun m => decide (Mono.degree m ≤ bound) := by
  rfl

/-- Restriction keeps exactly the coefficients whose monomials satisfy the
predicate. -/
theorem coeff_restrictBy [Zero R]
    (keep : Mono n → Bool) (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (restrictBy keep p) = if keep m then coeff m p else 0 := by
  unfold restrictBy coeff coeff?
  rw [Std.ExtTreeMap.getElem?_filter']
  cases hcoeff : p.termsInternal[m]? <;>
    cases hkeep : keep m <;>
    simp [Option.filter]

/-- The zero polynomial has total degree zero. -/
@[simp] theorem totalDegree_zero [Zero R] :
    totalDegree (0 : MvPoly n R cmp) = 0 := by
  rfl

/-- Every variable has degree zero in the zero polynomial. -/
@[simp] theorem degreeOf_zero [Zero R] (i : Fin n) :
    degreeOf i (0 : MvPoly n R cmp) = 0 := by
  rfl

/-- The coordinatewise degree vector of zero is the zero monomial. -/
@[simp] theorem degrees_zero [Zero R] :
    degrees (0 : MvPoly n R cmp) = Mono.zero := by
  rfl

/-- No variable occurs in the zero polynomial. -/
@[simp] theorem vars_zero [Zero R] :
    vars (0 : MvPoly n R cmp) = [] := by
  simp [vars, degrees_zero, Mono.support, Mono.zero]

/-- The zero polynomial has no leading term. -/
@[simp] theorem leadingTerm_zero [Zero R] [IsMonomialOrder cmp] :
    leadingTerm (0 : MvPoly n R cmp) = none := by
  unfold leadingTerm maxTerm?
  change
    ((∅ : Std.ExtTreeMap (Mono n) R cmp).maxKey?.bind fun m =>
      (∅ : Std.ExtTreeMap (Mono n) R cmp)[m]?.map fun c => (m, c)) = none
  rw [Std.ExtTreeMap.maxKey?_empty]
  rfl

/-- The zero polynomial has no leading monomial. -/
@[simp] theorem leadingMono_zero [Zero R] [IsMonomialOrder cmp] :
    leadingMono (0 : MvPoly n R cmp) = none := by
  rw [leadingMono_eq, leadingTerm_zero]
  rfl

/-- The compatibility leading-monomial spelling returns none on zero. -/
@[simp] theorem leadingMonomial_zero [Zero R] [IsMonomialOrder cmp] :
    leadingMonomial (0 : MvPoly n R cmp) = none := by
  rw [leadingMonomial_eq, leadingMono_zero]

/-- The zero polynomial has leading coefficient zero. -/
@[simp] theorem leadingCoeff_zero [Zero R] [IsMonomialOrder cmp] :
    leadingCoeff (0 : MvPoly n R cmp) = 0 := by
  rw [leadingCoeff_eq, leadingTerm_zero]
  rfl

end Hex.MvPoly
