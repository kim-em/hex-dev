/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
public import HexMvPoly.Structural
public import HexPoly

@[expose] public section

/-!
The recursive univariate view of a multivariate polynomial.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Remove coordinate `i` from an exponent vector. This is the explicit
Mathlib-free form of precomposition by `Fin.succAbove i`. -/
def removeVar (i : Fin (n + 1)) (m : Mono (n + 1)) : Mono n :=
  Hex.Vector.ofFn' fun j =>
    if j.val < i.val then
      m[(⟨j.val, by omega⟩ : Fin (n + 1))]
    else
      m[(⟨j.val + 1, by omega⟩ : Fin (n + 1))]

/-- Insert exponent `e` at coordinate `i`. -/
def insertVar (i : Fin (n + 1)) (e : Nat) (m : Mono n) : Mono (n + 1) :=
  Hex.Vector.ofFn' fun j =>
    if hsame : j.val = i.val then e
    else if hlt : j.val < i.val then
      m[(⟨j.val, by omega⟩ : Fin n)]
    else
      m[(⟨j.val - 1, by omega⟩ : Fin n)]

/-- The inserted variable has the supplied exponent. -/
@[simp] theorem degreeOf_insertVar
    (i : Fin (n + 1)) (e : Nat) (m : Mono n) :
    Mono.degreeOf i (insertVar i e m) = e := by
  simp [Mono.degreeOf, insertVar]

/-- Removing a freshly inserted variable recovers the original monomial. -/
@[simp] theorem removeVar_insertVar
    (i : Fin (n + 1)) (e : Nat) (m : Mono n) :
    removeVar i (insertVar i e m) = m := by
  apply Vector.ext
  intro j
  intro hj
  by_cases hlt : j < i.val
  · have hne : j ≠ i.val := Nat.ne_of_lt hlt
    simp [removeVar, insertVar, hlt, hne]
  · have hne : j + 1 ≠ i.val := by omega
    have hnlt : ¬ j + 1 < i.val := by omega
    simp [removeVar, insertVar, hlt, hne, hnlt]

/-- Re-inserting a removed variable with its old exponent recovers the
original monomial. -/
@[simp] theorem insertVar_removeVar
    (i : Fin (n + 1)) (m : Mono (n + 1)) :
    insertVar i (Mono.degreeOf i m) (removeVar i m) = m := by
  apply Vector.ext
  intro j
  intro hj
  by_cases heq : j = i.val
  · simp [insertVar, Mono.degreeOf, heq]
  · by_cases hlt : j < i.val
    · simp [insertVar, removeVar, heq, hlt]
    · have hnlt : ¬ j - 1 < i.val := by omega
      have hsucc : j - 1 + 1 = j := by omega
      simp [insertVar, removeVar, heq, hlt, hnlt, hsucc]

/-- Inserting a variable is jointly injective in the new exponent and the
remaining monomial. -/
theorem insertVar_inj (i : Fin (n + 1)) (e d : Nat) (m k : Mono n) :
    insertVar i e m = insertVar i d k ↔ e = d ∧ m = k := by
  constructor
  · intro h
    constructor
    · simpa only [degreeOf_insertVar] using congrArg (Mono.degreeOf i) h
    · simpa only [removeVar_insertVar] using congrArg (removeVar i) h
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Array length needed to accumulate every exponent bucket. -/
def toUnivariateSize (i : Fin (n + 1))
    (terms : List (Mono (n + 1) × R)) : Nat :=
  terms.foldl
    (fun bound term => max bound (Mono.degreeOf i term.1 + 1)) 0

/-- Accumulate one source term into its dense univariate coefficient bucket.
The caller must ensure that the term's selected degree is below `coeffs.size`;
otherwise `Array.set!` leaves the array unchanged. -/
def toUnivariateStep [Lean.Grind.Semiring R] [DecidableEq R]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (i : Fin (n + 1)) (coeffs : Array (MvPoly n R cmp'))
    (term : Mono (n + 1) × R) : Array (MvPoly n R cmp') :=
  let e := Mono.degreeOf i term.1
  let c := (coeffs.getD e 0).addMonomial (removeVar i term.1) term.2
  coeffs.set! e c

/-- Dense coefficient array obtained by two linear passes over sparse terms:
one to determine the array size and one to populate its buckets. -/
def toUnivariateCoeffs [Lean.Grind.Semiring R] [DecidableEq R]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (i : Fin (n + 1)) (terms : List (Mono (n + 1) × R)) :
    Array (MvPoly n R cmp') :=
  terms.foldl
    (fun coeffs term => toUnivariateStep (cmp' := cmp') i coeffs term)
    (Array.replicate (toUnivariateSize i terms) 0)

/-- Every encountered main-variable exponent fits in the allocated recursive
coefficient array. -/
private theorem degreeOf_lt_size (i : Fin (n + 1))
    (terms : List (Mono (n + 1) × R)) {term : Mono (n + 1) × R}
    (hterm : term ∈ terms) :
    Mono.degreeOf i term.1 < toUnivariateSize i terms := by
  have hbound :=
    List.le_foldl_max_of_mem terms
      (fun term => Mono.degreeOf i term.1 + 1) (init := 0) hterm
  unfold toUnivariateSize
  omega

/-- Updating one recursive coefficient bucket preserves the array size. -/
@[simp] private theorem size_toUnivariateStep
    [Lean.Grind.Semiring R] [DecidableEq R]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (i : Fin (n + 1)) (coeffs : Array (MvPoly n R cmp'))
    (term : Mono (n + 1) × R) :
    (toUnivariateStep (cmp' := cmp') i coeffs term).size = coeffs.size := by
  simp [toUnivariateStep]

/-- Reading an updated bucket yields the inserted term at its exponent and
the previous bucket elsewhere. -/
private theorem getD_toUnivariateStep
    [Lean.Grind.Semiring R] [DecidableEq R]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (i : Fin (n + 1)) (coeffs : Array (MvPoly n R cmp'))
    (term : Mono (n + 1) × R) (e : Nat)
    (hbound : Mono.degreeOf i term.1 < coeffs.size) :
    (toUnivariateStep (cmp' := cmp') i coeffs term).getD e 0 =
      if Mono.degreeOf i term.1 = e then
        (coeffs.getD e 0).addMonomial (removeVar i term.1) term.2
      else
        coeffs.getD e 0 := by
  by_cases heq : Mono.degreeOf i term.1 = e
  · subst e
    simp [toUnivariateStep, Array.getD, hbound]
  · by_cases he : e < coeffs.size
    · unfold Array.getD
      simp [toUnivariateStep, Array.set!_eq_setIfInBounds, hbound, he, heq]
    · unfold Array.getD
      simp [toUnivariateStep, Array.set!_eq_setIfInBounds, hbound, he, heq]

/-- Folding source terms into recursive buckets accumulates exactly the
matching coefficients. -/
private theorem coeff_foldSteps
    [Lean.Grind.Semiring R] [DecidableEq R]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (i : Fin (n + 1)) (allTerms terms : List (Mono (n + 1) × R))
    (hterms : terms ⊆ allTerms) (coeffs : Array (MvPoly n R cmp'))
    (hsize : coeffs.size = toUnivariateSize i allTerms)
    (e : Nat) (m : Mono n) :
    coeff m
        ((terms.foldl
          (fun coeffs term =>
            toUnivariateStep (cmp' := cmp') i coeffs term)
          coeffs).getD e 0) =
      terms.foldl
        (fun acc term =>
          if Mono.degreeOf i term.1 = e then
            if m = removeVar i term.1 then acc + term.2 else acc
          else acc)
        (coeff m (coeffs.getD e 0)) := by
  induction terms generalizing coeffs with
  | nil => rfl
  | cons term terms ih =>
      simp only [List.foldl_cons]
      have hmem : term ∈ allTerms :=
        hterms (List.mem_cons_self ..)
      have htail : terms ⊆ allTerms :=
        fun _ h => hterms (List.mem_cons_of_mem term h)
      have hbound : Mono.degreeOf i term.1 < coeffs.size := by
        rw [hsize]
        exact degreeOf_lt_size i allTerms hmem
      rw [ih htail _ (size_toUnivariateStep i coeffs term |>.trans hsize)]
      rw [getD_toUnivariateStep i coeffs term e hbound]
      by_cases heq : Mono.degreeOf i term.1 = e
      · rw [if_pos heq, if_pos heq, coeff_addMonomial]
      · rw [if_neg heq, if_neg heq]

/-- Coefficients of `p` as a dense univariate polynomial in variable `i`.
Each coefficient is a polynomial in the remaining `n` variables. -/
def toUnivariate [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly (n + 1) R cmp) : DensePoly (MvPoly n R cmp') :=
  let terms := p.termsList
  DensePoly.ofCoeffs (toUnivariateCoeffs i terms)

/-- Inverse of `toUnivariate`, reinserting variable `i`. -/
def ofUnivariate [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (q : DensePoly (MvPoly n R cmp')) : MvPoly (n + 1) R cmp :=
  (List.range q.size).foldl
    (fun acc e =>
      (q.coeff e).foldTerms
        (fun acc m c => acc.addMonomial (insertVar i e m) c)
        acc)
    0

/-- A recursive-view coefficient is the source coefficient indexed by the
inserted main-variable exponent. -/
theorem toUnivariate_coeff [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly (n + 1) R cmp) (e : Nat) (m : Mono n) :
    coeff m ((toUnivariate i cmp' p).coeff e) =
      coeff (insertVar i e m) p := by
  unfold toUnivariate
  rw [DensePoly.coeff_ofCoeffs]
  unfold toUnivariateCoeffs
  change
    coeff m
        ((p.termsList.foldl
          (fun coeffs term =>
            toUnivariateStep (cmp' := cmp') i coeffs term)
          (Array.replicate (toUnivariateSize i p.termsList) 0)).getD
            e (0 : MvPoly n R cmp')) =
      coeff (insertVar i e m) p
  rw [coeff_foldSteps i p.termsList p.termsList (fun _ h => h)
    (Array.replicate (toUnivariateSize i p.termsList) 0) (by simp) e m]
  have hinit :
      coeff m
          ((Array.replicate (toUnivariateSize i p.termsList)
            (0 : MvPoly n R cmp')).getD e 0) = 0 := by
    simp [Array.getD]
  rw [hinit]
  rw [← coeff_terms (insertVar i e m) p, List.foldl_filter]
  apply List.foldl_congr
  intro acc term _
  simp only [decide_eq_true_eq]
  by_cases hkey : term.1 = insertVar i e m
  · have hdegree : Mono.degreeOf i term.1 = e := by
      rw [hkey, degreeOf_insertVar]
    have hremove : m = removeVar i term.1 := by
      rw [hkey, removeVar_insertVar]
    rw [if_pos hdegree, if_pos hremove, if_pos hkey]
  · by_cases hdegree : Mono.degreeOf i term.1 = e
    · by_cases hremove : m = removeVar i term.1
      · have hkey' : term.1 = insertVar i e m := by
          calc
            term.1 =
                insertVar i (Mono.degreeOf i term.1)
                  (removeVar i term.1) :=
              (insertVar_removeVar i term.1).symm
            _ = insertVar i e m := by rw [hdegree, ← hremove]
        exact (hkey hkey').elim
      · rw [if_pos hdegree, if_neg hremove, if_neg hkey]
    · rw [if_neg hdegree, if_neg hkey]

/-- Folding one recursive coefficient into the multivariate result changes
exactly its inserted monomials. -/
private theorem coeff_foldInsert [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly n R cmp') (d e : Nat) (m : Mono n)
    (init : MvPoly (n + 1) R cmp) :
    coeff (insertVar i e m)
        (p.foldTerms
          (fun acc k c => acc.addMonomial (insertVar i d k) c)
          init) =
      coeff (insertVar i e m) init +
        if d = e then coeff m p else 0 := by
  have aux : ∀ (terms : List (Mono n × R))
      (init : MvPoly (n + 1) R cmp),
      coeff (insertVar i e m)
          (terms.foldl
            (fun acc term =>
              acc.addMonomial (insertVar i d term.1) term.2)
            init) =
        terms.foldl
          (fun acc term =>
            if insertVar i e m = insertVar i d term.1 then
              acc + term.2
            else acc)
          (coeff (insertVar i e m) init) := by
    intro terms
    induction terms with
    | nil =>
        intro init
        rfl
    | cons term terms ih =>
        intro init
        simp only [List.foldl_cons]
        rw [ih, coeff_addMonomial]
  unfold foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList, aux]
  change
    p.termsList.foldl
        (fun acc term =>
          if insertVar i e m = insertVar i d term.1 then acc + term.2
          else acc)
        (coeff (insertVar i e m) init) =
      coeff (insertVar i e m) init + if d = e then coeff m p else 0
  by_cases hde : d = e
  · subst d
    rw [if_pos rfl]
    calc
      p.termsList.foldl
          (fun acc term =>
            if insertVar i e m = insertVar i e term.1 then acc + term.2
            else acc)
          (coeff (insertVar i e m) init) =
          p.termsList.foldl
            (fun acc term => acc + if term.1 = m then term.2 else 0)
            (coeff (insertVar i e m) init) := by
              apply List.foldl_congr
              intro acc term _
              by_cases hkey : term.1 = m
              · have hinsert : insertVar i e m = insertVar i e term.1 := by
                  rw [hkey]
                rw [if_pos hinsert, if_pos hkey]
              · have hinsert : insertVar i e m ≠ insertVar i e term.1 := by
                  intro h
                  exact hkey ((insertVar_inj i e e m term.1).mp h).2.symm
                rw [if_neg hinsert, if_neg hkey,
                  Lean.Grind.Semiring.add_zero]
      _ = coeff (insertVar i e m) init +
          p.termsList.foldl
            (fun acc term => acc + if term.1 = m then term.2 else 0)
            0 :=
        List.foldl_add_eq_add_foldl _ _ _
      _ = coeff (insertVar i e m) init + coeff m p := by
        congr 1
        rw [← coeff_terms m p, List.foldl_filter]
        apply List.foldl_congr
        intro acc term _
        simp only [decide_eq_true_eq]
        by_cases hkey : term.1 = m
        · rw [if_pos hkey, if_pos hkey]
        · rw [if_neg hkey, if_neg hkey,
            Lean.Grind.Semiring.add_zero]
  · rw [if_neg hde, Lean.Grind.Semiring.add_zero]
    calc
      p.termsList.foldl
          (fun acc term =>
            if insertVar i e m = insertVar i d term.1 then acc + term.2
            else acc)
          (coeff (insertVar i e m) init) =
          p.termsList.foldl (fun acc _ => acc)
            (coeff (insertVar i e m) init) := by
              apply List.foldl_congr
              intro acc term _
              have hinsert : insertVar i e m ≠ insertVar i d term.1 := by
                intro h
                exact hde ((insertVar_inj i e d m term.1).mp h).1.symm
              rw [if_neg hinsert]
      _ = coeff (insertVar i e m) init :=
        List.foldl_const_step _ _

/-- Reassembly sends a recursive coefficient back to its inserted
multivariate monomial. -/
theorem ofUnivariate_coeff [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (q : DensePoly (MvPoly n R cmp')) (e : Nat) (m : Mono n) :
    coeff (insertVar i e m) (ofUnivariate (cmp := cmp) i cmp' q) =
      coeff m (q.coeff e) := by
  have coeff_foldIndices : ∀ (indices : List Nat)
      (init : MvPoly (n + 1) R cmp),
      coeff (insertVar i e m)
          (indices.foldl
            (fun acc d =>
              (q.coeff d).foldTerms
                (fun acc k c => acc.addMonomial (insertVar i d k) c)
                acc)
            init) =
        indices.foldl
          (fun acc d =>
            acc + if d = e then coeff m (q.coeff d) else 0)
          (coeff (insertVar i e m) init) := by
    intro indices
    induction indices with
    | nil =>
        intro init
        rfl
    | cons d indices ih =>
        intro init
        simp only [List.foldl_cons]
        rw [ih, coeff_foldInsert]
  unfold ofUnivariate
  rw [coeff_foldIndices, coeff_zero]
  by_cases he : e < q.size
  · have hsingle := List.foldl_add_single
        (List.range q.size) (0 : R) e (fun d => coeff m (q.coeff d))
        (List.mem_range.mpr he) List.nodup_range
    exact hsingle.trans (by grind)
  · have hzero : q.coeff e = 0 :=
      DensePoly.coeff_eq_zero_of_size_le q (Nat.le_of_not_gt he)
    rw [List.foldl_add_eq_self, hzero, coeff_zero]
    intro d hd
    have hdlt : d < q.size := List.mem_range.mp hd
    have hde : d ≠ e := by omega
    rw [if_neg hde]

/-- Converting to the recursive view and back is the identity. -/
theorem ofUnivariate_toUnivariate [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly (n + 1) R cmp) :
    ofUnivariate (cmp := cmp) i cmp' (toUnivariate i cmp' p) = p := by
  apply MvPoly.ext
  intro m
  rw [← insertVar_removeVar i m, ofUnivariate_coeff,
    toUnivariate_coeff, insertVar_removeVar]

/-- Converting a recursive polynomial to multivariate form and back is the
identity. -/
theorem toUnivariate_ofUnivariate [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (q : DensePoly (MvPoly n R cmp')) :
    toUnivariate i cmp' (ofUnivariate (cmp := cmp) i cmp' q) = q := by
  apply DensePoly.ext_coeff
  intro e
  apply MvPoly.ext
  intro m
  rw [toUnivariate_coeff, ofUnivariate_coeff]

end Hex.MvPoly
