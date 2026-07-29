/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
public import HexMvPoly.Query

@[expose] public section

/-!
Direct, fixed-variable-order Horner, and partial evaluation for
`Hex.MvPoly`.
-/

namespace Hex.MvPoly

universe u v

variable {n : Nat} {R : Type u} {S : Type v}
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Evaluate coefficients through `f` and variables through `x`. Powers are
computed by repeated squaring in `Mono.prod`. -/
def eval₂ [Zero R] [Lean.Grind.Semiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) : S :=
  p.foldTerms (fun acc m c => acc + f c * Mono.prod x m) 0

/-- Evaluate a polynomial at `x`. -/
def eval [Lean.Grind.Semiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) : R :=
  eval₂ id x p

/-- A term whose coefficient has already been mapped into the target
semiring. -/
abbrev HornerTerm (n : Nat) (S : Type v) := Mono n × S

/-- Terms sharing one exponent in the variable currently being evaluated. -/
abbrev HornerGroup (n : Nat) (S : Type v) := Nat × List (HornerTerm n S)

/-- Read an exponent using a natural variable index, returning zero when the
index is out of range. -/
def hornerExponent (k : Nat) (m : Mono n) : Nat :=
  if h : k < n then m[(⟨k, h⟩ : Fin n)] else 0

/-- Add a term to an association list keyed by one variable exponent. -/
def insertHornerTerm (exponent : Nat) (term : HornerTerm n S) :
    List (HornerGroup n S) → List (HornerGroup n S)
  | [] => [(exponent, [term])]
  | group :: groups =>
      if group.1 = exponent then
        (group.1, term :: group.2) :: groups
      else
        group :: insertHornerTerm exponent term groups

/-- Insert an exponent group into descending exponent order. -/
def insertHornerGroupDesc (group : HornerGroup n S) :
    List (HornerGroup n S) → List (HornerGroup n S)
  | [] => [group]
  | group' :: groups =>
      if group'.1 < group.1 then
        group :: group' :: groups
      else
        group' :: insertHornerGroupDesc group groups

/-- Collect terms into groups keyed by their exponent at variable `k`. -/
def collectHornerGroups (k : Nat) (terms : List (HornerTerm n S)) :
    List (HornerGroup n S) :=
  terms.foldl
    (fun groups term => insertHornerTerm (hornerExponent k term.1) term groups) []

/-- Sort exponent groups from high exponent to low exponent. -/
def sortHornerGroups (groups : List (HornerGroup n S)) :
    List (HornerGroup n S) :=
  groups.foldl (fun sorted group => insertHornerGroupDesc group sorted) []

/-- Group terms by one variable exponent, ordered from high to low. -/
def hornerGroups (k : Nat) (terms : List (HornerTerm n S)) :
    List (HornerGroup n S) :=
  sortHornerGroups (collectHornerGroups k terms)

/-! # Horner grouping invariants -/

private def groupTerms (groups : List (HornerGroup n S)) :
    List (HornerTerm n S) :=
  groups.flatMap fun group => group.2

private theorem insertHornerTerm_perm (exponent : Nat)
    (term : HornerTerm n S) (groups : List (HornerGroup n S)) :
    (groupTerms (insertHornerTerm exponent term groups)).Perm
      (term :: groupTerms groups) := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      unfold insertHornerTerm
      by_cases heq : group.1 = exponent
      · simp [heq, groupTerms]
      · rw [if_neg heq]
        change
          (group.2 ++ groupTerms (insertHornerTerm exponent term groups)).Perm
            (term :: (group.2 ++ groupTerms groups))
        exact (ih.append_left group.2).trans List.perm_middle

private theorem collectHornerGroups_perm_aux (k : Nat)
    (terms : List (HornerTerm n S)) (groups : List (HornerGroup n S)) :
    (groupTerms
        (terms.foldl
          (fun groups term =>
            insertHornerTerm (hornerExponent k term.1) term groups)
          groups)).Perm
      (terms ++ groupTerms groups) := by
  induction terms generalizing groups with
  | nil => rfl
  | cons term terms ih =>
      simp only [List.foldl_cons]
      have hins :
          (terms ++
              groupTerms
                (insertHornerTerm (hornerExponent k term.1) term groups)).Perm
            (terms ++ term :: groupTerms groups) :=
        (insertHornerTerm_perm (hornerExponent k term.1) term groups).append_left
          terms
      have hfront :
          (terms ++ term :: groupTerms groups).Perm
            (term :: terms ++ groupTerms groups) :=
        List.perm_middle
      exact
        (ih
          (insertHornerTerm (hornerExponent k term.1) term groups)).trans
          (hins.trans hfront)

private theorem collectHornerGroups_perm (k : Nat)
    (terms : List (HornerTerm n S)) :
    (groupTerms (collectHornerGroups k terms)).Perm terms := by
  simpa [collectHornerGroups, groupTerms] using
    collectHornerGroups_perm_aux k terms []

private theorem insertHornerGroupDesc_perm (group : HornerGroup n S)
    (groups : List (HornerGroup n S)) :
    (groupTerms (insertHornerGroupDesc group groups)).Perm
      (group.2 ++ groupTerms groups) := by
  induction groups with
  | nil => rfl
  | cons group' groups ih =>
      unfold insertHornerGroupDesc
      by_cases hlt : group'.1 < group.1
      · simp [hlt, groupTerms]
      · rw [if_neg hlt]
        change
          (group'.2 ++ groupTerms (insertHornerGroupDesc group groups)).Perm
            (group.2 ++ (group'.2 ++ groupTerms groups))
        exact
          (ih.append_left group'.2).trans
            (by
              simpa [List.append_assoc] using
                List.perm_append_comm_assoc group'.2 group.2 (groupTerms groups))

private theorem sortHornerGroups_perm_aux (groups sorted : List (HornerGroup n S)) :
    (groupTerms
        (groups.foldl
          (fun sorted group => insertHornerGroupDesc group sorted)
          sorted)).Perm
      (groupTerms groups ++ groupTerms sorted) := by
  induction groups generalizing sorted with
  | nil => rfl
  | cons group groups ih =>
      simp only [List.foldl_cons]
      have hins :
          (groupTerms groups ++
              groupTerms (insertHornerGroupDesc group sorted)).Perm
            (groupTerms groups ++ (group.2 ++ groupTerms sorted)) :=
        (insertHornerGroupDesc_perm group sorted).append_left
          (groupTerms groups)
      have hfront :
          (groupTerms groups ++ (group.2 ++ groupTerms sorted)).Perm
            (group.2 ++ (groupTerms groups ++ groupTerms sorted)) := by
        simpa [List.append_assoc] using
          List.perm_append_comm_assoc
            (groupTerms groups) group.2 (groupTerms sorted)
      exact
        (ih (insertHornerGroupDesc group sorted)).trans
          (by simpa [groupTerms] using hins.trans hfront)

private theorem sortHornerGroups_perm (groups : List (HornerGroup n S)) :
    (groupTerms (sortHornerGroups groups)).Perm (groupTerms groups) := by
  simpa [sortHornerGroups, groupTerms] using
    sortHornerGroups_perm_aux groups []

private theorem hornerGroups_perm (k : Nat) (terms : List (HornerTerm n S)) :
    (groupTerms (hornerGroups k terms)).Perm terms := by
  exact
    (sortHornerGroups_perm (collectHornerGroups k terms)).trans
      (collectHornerGroups_perm k terms)

private theorem mem_insertHornerGroupDesc
    (target group : HornerGroup n S) (groups : List (HornerGroup n S)) :
    target ∈ insertHornerGroupDesc group groups ↔
      target = group ∨ target ∈ groups := by
  induction groups with
  | nil => simp [insertHornerGroupDesc]
  | cons group' groups ih =>
      unfold insertHornerGroupDesc
      by_cases hlt : group'.1 < group.1
      · simp [hlt]
      · rw [if_neg hlt]
        simp only [List.mem_cons, ih]
        constructor
        · rintro (heq | heq | hmem)
          · exact Or.inr (Or.inl heq)
          · exact Or.inl heq
          · exact Or.inr (Or.inr hmem)
        · rintro (heq | heq | hmem)
          · exact Or.inr (Or.inl heq)
          · exact Or.inl heq
          · exact Or.inr (Or.inr hmem)

private theorem insertHornerGroupDesc_desc (group : HornerGroup n S)
    (groups : List (HornerGroup n S))
    (hdesc : groups.Pairwise fun left right => right.1 ≤ left.1) :
    (insertHornerGroupDesc group groups).Pairwise
      fun left right => right.1 ≤ left.1 := by
  induction groups with
  | nil => simp [insertHornerGroupDesc]
  | cons group' groups ih =>
      rw [List.pairwise_cons] at hdesc
      unfold insertHornerGroupDesc
      by_cases hlt : group'.1 < group.1
      · rw [if_pos hlt, List.pairwise_cons]
        constructor
        · intro target htarget
          simp only [List.mem_cons] at htarget
          rcases htarget with rfl | htarget
          · omega
          · exact Nat.le_trans (hdesc.1 target htarget) (Nat.le_of_lt hlt)
        · exact List.pairwise_cons.mpr hdesc
      · rw [if_neg hlt, List.pairwise_cons]
        constructor
        · intro target htarget
          rw [mem_insertHornerGroupDesc] at htarget
          rcases htarget with rfl | htarget
          · omega
          · exact hdesc.1 target htarget
        · exact ih hdesc.2

private theorem sortHornerGroups_desc_aux
    (groups sorted : List (HornerGroup n S))
    (hdesc : sorted.Pairwise fun left right => right.1 ≤ left.1) :
    (groups.foldl
      (fun sorted group => insertHornerGroupDesc group sorted)
      sorted).Pairwise fun left right => right.1 ≤ left.1 := by
  induction groups generalizing sorted with
  | nil => exact hdesc
  | cons group groups ih =>
      simp only [List.foldl_cons]
      exact ih _ (insertHornerGroupDesc_desc group sorted hdesc)

private theorem sortHornerGroups_desc (groups : List (HornerGroup n S)) :
    (sortHornerGroups groups).Pairwise
      fun left right => right.1 ≤ left.1 := by
  exact sortHornerGroups_desc_aux groups [] List.Pairwise.nil

private theorem hornerGroups_desc (k : Nat) (terms : List (HornerTerm n S)) :
    (hornerGroups k terms).Pairwise
      fun left right => right.1 ≤ left.1 :=
  sortHornerGroups_desc (collectHornerGroups k terms)

private def groupsKeyed (k : Nat) (groups : List (HornerGroup n S)) : Prop :=
  ∀ group ∈ groups, ∀ term ∈ group.2,
    hornerExponent k term.1 = group.1

private theorem insertHornerTerm_at (k exponent : Nat)
    (term : HornerTerm n S) (groups : List (HornerGroup n S))
    (hterm : hornerExponent k term.1 = exponent)
    (hgroups : groupsKeyed k groups) :
    groupsKeyed k (insertHornerTerm exponent term groups) := by
  revert hgroups
  induction groups with
  | nil =>
      intro _
      intro target htarget candidate hcand
      simp only [insertHornerTerm, List.mem_singleton] at htarget
      subst target
      simp only [List.mem_singleton] at hcand
      subst candidate
      exact hterm
  | cons group groups ih =>
      intro hgroups
      have htail : groupsKeyed k groups := by
        intro target htarget candidate hcand
        exact hgroups target (List.mem_cons_of_mem group htarget) candidate hcand
      unfold insertHornerTerm
      by_cases heq : group.1 = exponent
      · rw [if_pos heq]
        intro target htarget candidate hcand
        simp only [List.mem_cons] at htarget
        rcases htarget with htarget | htarget
        · subst target
          simp only [List.mem_cons] at hcand
          rcases hcand with hcand | hcand
          · subst candidate
            exact hterm.trans heq.symm
          · exact hgroups group (List.mem_cons_self ..) candidate hcand
        · exact hgroups target (List.mem_cons_of_mem group htarget) candidate hcand
      · rw [if_neg heq]
        intro target htarget candidate hcand
        simp only [List.mem_cons] at htarget
        rcases htarget with htarget | htarget
        · subst target
          exact hgroups group (List.mem_cons_self ..) candidate hcand
        · exact ih htail target htarget candidate hcand

private theorem collectHornerGroups_at_aux (k : Nat)
    (terms : List (HornerTerm n S)) (groups : List (HornerGroup n S))
    (hgroups : groupsKeyed k groups) :
    groupsKeyed k
      (terms.foldl
        (fun groups term =>
          insertHornerTerm (hornerExponent k term.1) term groups)
        groups) := by
  induction terms generalizing groups with
  | nil => exact hgroups
  | cons term terms ih =>
      simp only [List.foldl_cons]
      exact ih _ (insertHornerTerm_at k _ term groups rfl hgroups)

private theorem collectHornerGroups_at (k : Nat)
    (terms : List (HornerTerm n S)) :
    groupsKeyed k (collectHornerGroups k terms) := by
  apply collectHornerGroups_at_aux
  intro group hgroup
  simp at hgroup

private theorem insertHornerGroupDesc_at (k : Nat)
    (group : HornerGroup n S) (groups : List (HornerGroup n S))
    (hgroup : ∀ term ∈ group.2, hornerExponent k term.1 = group.1)
    (hgroups : groupsKeyed k groups) :
    groupsKeyed k (insertHornerGroupDesc group groups) := by
  intro target htarget term hterm
  rw [mem_insertHornerGroupDesc] at htarget
  rcases htarget with rfl | htarget
  · exact hgroup term hterm
  · exact hgroups target htarget term hterm

private theorem sortHornerGroups_at_aux (k : Nat)
    (groups sorted : List (HornerGroup n S))
    (hgroups : groupsKeyed k groups) (hsorted : groupsKeyed k sorted) :
    groupsKeyed k
      (groups.foldl
        (fun sorted group => insertHornerGroupDesc group sorted)
        sorted) := by
  induction groups generalizing sorted with
  | nil => exact hsorted
  | cons group groups ih =>
      simp only [List.foldl_cons]
      have hgroup :
          ∀ term ∈ group.2, hornerExponent k term.1 = group.1 :=
        hgroups group (List.mem_cons_self ..)
      have htail : groupsKeyed k groups := by
        intro target htarget term hterm
        exact hgroups target (List.mem_cons_of_mem group htarget) term hterm
      exact ih _ htail (insertHornerGroupDesc_at k group sorted hgroup hsorted)

private theorem sortHornerGroups_at (k : Nat)
    (groups : List (HornerGroup n S)) (hgroups : groupsKeyed k groups) :
    groupsKeyed k (sortHornerGroups groups) := by
  apply sortHornerGroups_at_aux k groups [] hgroups
  intro group hgroup
  simp at hgroup

private theorem hornerGroups_at (k : Nat)
    (terms : List (HornerTerm n S)) :
    groupsKeyed k (hornerGroups k terms) :=
  sortHornerGroups_at k _ (collectHornerGroups_at k terms)

/-- Advance one descending sparse-Horner exponent group. -/
def hornerStep [Lean.Grind.Semiring S]
    (x : S) (state group : Nat × S) : Nat × S :=
  (group.1,
    state.2 * Mono.powBySq x (state.1 - group.1) + group.2)

/-- Sparse Horner fold over already-evaluated coefficient groups. Callers must
supply groups in descending exponent order. Missing exponents are skipped with
repeated-squaring powers. -/
def evalSparseHornerGroups [Lean.Grind.Semiring S]
    (x : S) : List (Nat × S) → S
  | [] => 0
  | group :: groups =>
      let state := groups.foldl (hornerStep x) group
      state.2 * Mono.powBySq x state.1

/-! # Sparse Horner algebra -/

private def weightedSum [Lean.Grind.Semiring S]
    (x : S) (groups : List (Nat × S)) : S :=
  groups.foldl
    (fun acc group => acc + group.2 * Mono.powBySq x group.1) 0

private theorem weightedSum_cons [Lean.Grind.Semiring S]
    (x : S) (group : Nat × S) (groups : List (Nat × S)) :
    weightedSum x (group :: groups) =
      group.2 * Mono.powBySq x group.1 + weightedSum x groups := by
  unfold weightedSum
  simp only [List.foldl_cons]
  rw [Lean.Grind.AddCommMonoid.zero_add, List.foldl_add_eq_add_foldl]

private theorem sparseFold_eq [Lean.Grind.Semiring S]
    (x : S) (groups : List (Nat × S)) (previous : Nat) (acc : S)
    (hbound : ∀ group ∈ groups, group.1 ≤ previous)
    (hdesc : groups.Pairwise fun left right => right.1 ≤ left.1) :
    let state := groups.foldl (hornerStep x) (previous, acc)
    state.2 * Mono.powBySq x state.1 =
      acc * Mono.powBySq x previous + weightedSum x groups := by
  induction groups generalizing previous acc with
  | nil =>
      simp [weightedSum, Lean.Grind.Semiring.add_zero]
  | cons group groups ih =>
      rw [List.pairwise_cons] at hdesc
      have hle : group.1 ≤ previous :=
        hbound group (List.mem_cons_self ..)
      have htail : ∀ target ∈ groups, target.1 ≤ group.1 :=
        hdesc.1
      have hrec :=
        ih group.1
          (acc * Mono.powBySq x (previous - group.1) + group.2)
          htail hdesc.2
      have hpow :
          Mono.powBySq x (previous - group.1) *
              Mono.powBySq x group.1 =
            Mono.powBySq x previous := by
        rw [Mono.powBySq_eq_pow, Mono.powBySq_eq_pow,
          Mono.powBySq_eq_pow, ← Lean.Grind.Semiring.pow_add,
          Nat.sub_add_cancel hle]
      have hstep :
          (acc * Mono.powBySq x (previous - group.1) + group.2) *
              Mono.powBySq x group.1 =
            acc * Mono.powBySq x previous +
              group.2 * Mono.powBySq x group.1 := by
        calc
          (acc * Mono.powBySq x (previous - group.1) + group.2) *
                Mono.powBySq x group.1 =
              acc * Mono.powBySq x (previous - group.1) *
                  Mono.powBySq x group.1 +
                group.2 * Mono.powBySq x group.1 :=
            Lean.Grind.Semiring.right_distrib ..
          _ = acc *
                (Mono.powBySq x (previous - group.1) *
                  Mono.powBySq x group.1) +
                group.2 * Mono.powBySq x group.1 := by
            rw [Lean.Grind.Semiring.mul_assoc]
          _ = acc * Mono.powBySq x previous +
                group.2 * Mono.powBySq x group.1 := by rw [hpow]
      simp only [List.foldl_cons]
      rw [show hornerStep x (previous, acc) group =
        (group.1,
          acc * Mono.powBySq x (previous - group.1) + group.2) from rfl]
      rw [hrec, hstep]
      rw [weightedSum_cons, Lean.Grind.Semiring.add_assoc]

private theorem evalSparseHornerGroups_eq [Lean.Grind.Semiring S]
    (x : S) (groups : List (Nat × S))
    (hdesc : groups.Pairwise fun left right => right.1 ≤ left.1) :
    evalSparseHornerGroups x groups = weightedSum x groups := by
  cases groups with
  | nil => rfl
  | cons group groups =>
      rw [List.pairwise_cons] at hdesc
      have hfold := sparseFold_eq x groups group.1 group.2 hdesc.1 hdesc.2
      have hfold' :
          let state := groups.foldl (hornerStep x) group
          state.2 * Mono.powBySq x state.1 =
            group.2 * Mono.powBySq x group.1 + weightedSum x groups := by
        simpa only [Prod.eta] using hfold
      rw [evalSparseHornerGroups]
      change
        let state := groups.foldl (hornerStep x) group
        state.2 * Mono.powBySq x state.1 =
          weightedSum x (group :: groups)
      exact hfold'.trans (weightedSum_cons x group groups).symm

/-- Evaluate sparse terms by fixed-order Horner in variables
`0, 1, ..., n - 1`. `fuel` is the number of variables left. -/
def eval₂HornerTerms [Lean.Grind.Semiring S]
    (xs : Nat → S) : Nat → Nat → List (HornerTerm n S) → S
  | 0, _, terms => terms.foldl (fun acc term => acc + term.2) 0
  | fuel + 1, k, terms =>
      let groups := hornerGroups k terms
      let evaluatedGroups := groups.map fun group =>
        (group.1, eval₂HornerTerms xs fuel (k + 1) group.2)
      evalSparseHornerGroups (xs k) evaluatedGroups

/-! # Recursive term semantics -/

private def termValue [Lean.Grind.Semiring S]
    (xs : Nat → S) : Nat → Nat → HornerTerm n S → S
  | 0, _, term => term.2
  | fuel + 1, k, term =>
      termValue xs fuel (k + 1) term *
        Mono.powBySq (xs k) (hornerExponent k term.1)

private theorem weightedGroups_eq [Lean.Grind.Semiring S]
    (xs : Nat → S) (fuel k : Nat) (groups : List (HornerGroup n S))
    (hat : groupsKeyed k groups)
    (hrec : ∀ group ∈ groups,
      eval₂HornerTerms xs fuel (k + 1) group.2 =
        group.2.foldl
          (fun acc term => acc + termValue xs fuel (k + 1) term) 0) :
    weightedSum (xs k)
        (groups.map fun group =>
          (group.1, eval₂HornerTerms xs fuel (k + 1) group.2)) =
      (groupTerms groups).foldl
        (fun acc term => acc + termValue xs (fuel + 1) k term) 0 := by
  unfold weightedSum
  rw [List.foldl_map]
  unfold groupTerms
  rw [List.foldl_add_flatMap]
  apply List.foldl_congr
  intro acc group hgroup
  rw [hrec group hgroup]
  calc
    acc +
          group.2.foldl
              (fun acc term =>
                acc + termValue xs fuel (k + 1) term) 0 *
            Mono.powBySq (xs k) group.1 =
        acc +
          group.2.foldl
            (fun acc term =>
              acc + termValue xs fuel (k + 1) term *
                Mono.powBySq (xs k) group.1) 0 := by
      rw [List.foldl_add_mul_right_zero]
    _ = acc +
          group.2.foldl
            (fun acc term => acc + termValue xs (fuel + 1) k term) 0 := by
      congr 1
      apply List.foldl_add_congr
      intro term hterm
      simp only [termValue]
      rw [hat group hgroup term hterm]
    _ = group.2.foldl
          (fun acc term => acc + termValue xs (fuel + 1) k term) acc :=
      (List.foldl_add_eq_add_foldl group.2
        (termValue xs (fuel + 1) k) acc).symm

private theorem eval₂HornerTerms_eq [Lean.Grind.Semiring S]
    (xs : Nat → S) (fuel k : Nat) (terms : List (HornerTerm n S)) :
    eval₂HornerTerms xs fuel k terms =
      terms.foldl
        (fun acc term => acc + termValue xs fuel k term) 0 := by
  induction fuel generalizing k terms with
  | zero => rfl
  | succ fuel ih =>
      let groups := hornerGroups k terms
      have hdesc :
          (groups.map fun group =>
            (group.1, eval₂HornerTerms xs fuel (k + 1) group.2)).Pairwise
              fun left right => right.1 ≤ left.1 := by
        rw [List.pairwise_map]
        exact hornerGroups_desc k terms
      unfold eval₂HornerTerms
      rw [evalSparseHornerGroups_eq (xs k) _ hdesc]
      rw [weightedGroups_eq xs fuel k groups
        (hornerGroups_at k terms)
        (fun group _ => ih (k + 1) group.2)]
      exact List.foldl_add_perm
        (termValue xs (fuel + 1) k)
        (hornerGroups_perm k terms) 0

private def termProd [Lean.Grind.Semiring S]
    (xs : Nat → S) : Nat → Nat → Mono n → S
  | 0, _, _ => 1
  | fuel + 1, k, m =>
      Mono.powBySq (xs k) (hornerExponent k m) *
        termProd xs fuel (k + 1) m

private theorem termValue_eq_mul_prod [Lean.Grind.CommSemiring S]
    (xs : Nat → S) (fuel k : Nat) (term : HornerTerm n S) :
    termValue xs fuel k term =
      term.2 * termProd xs fuel k term.1 := by
  induction fuel generalizing k with
  | zero =>
      simp [termValue, termProd, Lean.Grind.Semiring.mul_one]
  | succ fuel ih =>
      rw [termValue, termProd, ih]
      calc
        term.2 * termProd xs fuel (k + 1) term.1 *
              Mono.powBySq (xs k) (hornerExponent k term.1) =
            term.2 *
              (termProd xs fuel (k + 1) term.1 *
                Mono.powBySq (xs k) (hornerExponent k term.1)) :=
          Lean.Grind.Semiring.mul_assoc ..
        _ = term.2 *
              (Mono.powBySq (xs k) (hornerExponent k term.1) *
                termProd xs fuel (k + 1) term.1) := by
          rw [Lean.Grind.CommSemiring.mul_comm
            (termProd xs fuel (k + 1) term.1)]

private theorem hornerExponent_dropHead (k : Nat) (m : Mono (n + 1)) :
    hornerExponent (k + 1) m =
      hornerExponent k (Mono.dropHead m) := by
  unfold hornerExponent
  by_cases hk : k < n
  · have hk' : k + 1 < n + 1 := by omega
    simp only [hk, hk', ↓reduceDIte]
    rw [Mono.getElem_dropHead]
    congr 1
  · have hk' : ¬ k + 1 < n + 1 := by omega
    simp [hk, hk']

private theorem termProd_dropHead [Lean.Grind.Semiring S]
    (xs : Nat → S) (fuel k : Nat) (m : Mono (n + 1)) :
    termProd xs fuel (k + 1) m =
      termProd (fun j => xs (j + 1)) fuel k (Mono.dropHead m) := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
      rw [termProd, termProd, hornerExponent_dropHead, ih]

private theorem termProd_full [Lean.Grind.Semiring S]
    (xs : Nat → S) (m : Mono n) :
    termProd xs n 0 m =
      Mono.prod (fun i => xs i.val) m := by
  letI : Std.Associative (· * · : S → S → S) :=
    ⟨Lean.Grind.Semiring.mul_assoc⟩
  letI : Std.LawfulIdentity (· * · : S → S → S) 1 :=
    { left_id := Lean.Grind.Semiring.one_mul
      right_id := Lean.Grind.Semiring.mul_one }
  induction n generalizing xs with
  | zero =>
      simp [termProd, Mono.prod]
  | succ n ih =>
      rw [termProd, termProd_dropHead,
        ih (fun j => xs (j + 1)) (Mono.dropHead m)]
      unfold Mono.prod
      rw [List.finRange_succ]
      simp only [List.foldl_cons, List.foldl_map]
      rw [Lean.Grind.Semiring.one_mul]
      simp only [hornerExponent, Nat.zero_lt_succ, ↓reduceDIte]
      have htail :
          (List.finRange n).foldl
              (fun acc i =>
                acc *
                  Mono.powBySq (xs (i.val + 1)) (Mono.dropHead m)[i]) 1 =
            (List.finRange n).foldl
              (fun acc i =>
                acc * Mono.powBySq (xs i.succ.val) m[i.succ]) 1 := by
        apply List.foldl_congr
        intro acc i _
        simp only [Mono.getElem_dropHead]
        rfl
      calc
        Mono.powBySq (xs 0) m[0] *
              (List.finRange n).foldl
                (fun acc i =>
                  acc *
                    Mono.powBySq (xs (i.val + 1)) (Mono.dropHead m)[i]) 1 =
            Mono.powBySq (xs 0) m[0] *
              (List.finRange n).foldl
                (fun acc i =>
                  acc * Mono.powBySq (xs i.succ.val) m[i.succ]) 1 := by
          rw [htail]
        _ = (List.finRange n).foldl
              (fun acc i =>
                acc * Mono.powBySq (xs i.succ.val) m[i.succ])
              (Mono.powBySq (xs 0) m[0]) :=
          (List.foldl_mul_eq_mul_foldl
            (List.finRange n)
            (fun i => Mono.powBySq (xs i.succ.val) m[i.succ])
            (Mono.powBySq (xs 0) m[0])).symm

private theorem termValue_full [Lean.Grind.CommSemiring S]
    (xs : Nat → S) (term : HornerTerm n S) :
    termValue xs n 0 term =
      term.2 * Mono.prod (fun i => xs i.val) term.1 := by
  rw [termValue_eq_mul_prod, termProd_full]

/-- Evaluate using fixed-variable-order sparse Horner evaluation. The target
semiring is commutative because variable nesting may reorder factors. -/
def eval₂Horner [Zero R] [Lean.Grind.CommSemiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) : S :=
  let xs : Nat → S := fun k => if h : k < n then x ⟨k, h⟩ else 0
  let terms := p.termsList.map fun term => (term.1, f term.2)
  eval₂HornerTerms xs n 0 terms

/-- Evaluate at `x` using fixed-variable-order sparse Horner evaluation. -/
def evalHorner [Lean.Grind.CommSemiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) : R :=
  eval₂Horner id x p

/-- Erase the exponents of variables assigned by `s`. -/
def eraseAssigned (s : Fin n → Option R) (m : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun i => if (s i).isSome then 0 else m[i]

/-- Evaluate the variables assigned by `s`, leaving all other variables in
the same ambient polynomial ring. Terms that collide are combined. -/
def partialEval [Lean.Grind.Semiring R] [DecidableEq R]
    (s : Fin n → Option R) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.foldTerms
    (fun acc m c =>
      let assigned := Mono.prod (fun i => (s i).getD 1) m
      acc.addMonomial (eraseAssigned s m) (c * assigned))
    0

theorem eval₂_eq [Zero R] [Lean.Grind.Semiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) :
    eval₂ f x p =
      p.termsList.foldl (fun acc term => acc + f term.2 * Mono.prod x term.1) 0 := by
  unfold eval₂ foldTerms termsList
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]

theorem eval_eq [Lean.Grind.Semiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) :
    eval x p =
      p.termsList.foldl (fun acc term => acc + term.2 * Mono.prod x term.1) 0 := by
  unfold eval
  simpa using eval₂_eq id x p

theorem eval₂Horner_eq [Zero R] [Lean.Grind.CommSemiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) :
    eval₂Horner f x p = eval₂ f x p := by
  let xs : Nat → S := fun k => if h : k < n then x ⟨k, h⟩ else 0
  change
    eval₂HornerTerms xs n 0
        (p.termsList.map fun term => (term.1, f term.2)) =
      eval₂ f x p
  rw [eval₂HornerTerms_eq, eval₂_eq, List.foldl_map]
  have hxs : (fun i : Fin n => xs i.val) = x := by
    funext i
    simp [xs]
  apply List.foldl_congr
  intro acc term _
  rw [termValue_full, hxs]

theorem evalHorner_eq [Lean.Grind.CommSemiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) :
    evalHorner x p = eval x p := by
  unfold evalHorner eval
  exact eval₂Horner_eq id x p

end Hex.MvPoly
