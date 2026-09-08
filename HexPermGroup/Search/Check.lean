/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Predicate

public section

namespace Hex.PermGroup.Search

/-- Every branch is either expanded completely, rejected by a replayable
constraint reason, checked at a leaf, or contained in the final subgroup. -/
inductive Certificate (Reason : Type) where
  | branch (children : Array (Certificate Reason))
  | rejected (reason : Reason)
  | covered
  | leaf

variable {G : Group n} {P : Predicate n}

/-- Reconstruct child choices from the checked chain, rejecting missing or
extra branches and validating all pruning against the final result group. -/
@[expose] def checkTree (C : Constraint G P) (K : Group n) (t : Node G)
    (certificate : Certificate C.Reason) : Bool :=
  match certificate with
  | .rejected reason => C.reject t reason
  | .covered => t.covered K
  | .leaf =>
    match t.suffix with
    | .leaf _ _ => !P.test t.rep.val || K.contains t.rep.val
    | .cons _ _ => false
  | .branch children =>
    match hs : t.suffix with
    | .leaf _ _ => false
    | .cons level tail =>
      if hc : children.size = level.orbit.points.size then
        decide (∀ i : Fin level.orbit.points.size,
          checkTree C K (t.child hs i) children[i.val] = true)
      else false
termination_by t.suffix.length
decreasing_by
  all_goals
    change tail.length < t.suffix.length
    rw [hs]
    exact Nat.lt_succ_self _

theorem checkTree_branch (C : Constraint G P) (K : Group n) (t : Node G)
    {level : Level n} {tail : Chain n} (hs : t.suffix = .cons level tail)
    (children : Array (Certificate C.Reason)) :
    checkTree C K t (.branch children) =
      if hc : children.size = level.orbit.points.size then
        decide (∀ i : Fin level.orbit.points.size, checkTree C K (t.child hs i) children[i.val] = true)
      else false := by
  cases t with
  | mk base suffix checked inside rep =>
    simp only at hs
    subst suffix
    rw [checkTree]

theorem checkTree_branch_leaf (C : Constraint G P) (K : Group n) (t : Node G)
    {S : Array (Perm n)} {words : Vector Program S.size} (hs : t.suffix = .leaf S words)
    (children : Array (Certificate C.Reason)) : checkTree C K t (.branch children) = false := by
  cases t with
  | mk base suffix checked inside rep =>
    simp only at hs
    subst suffix
    rw [checkTree]

/-- Replay accounts for every satisfying completion of a node. -/
theorem checkTree_sound (C : Constraint G P) (K : Group n) (t : Node G)
    (certificate : Certificate C.Reason) (hc : checkTree C K t certificate = true)
    (p : Perm n) (hp : t.Contains p) (hP : P.test p = true) : Generated K.generators p := by
  cases certificate with
  | rejected reason =>
    have he := C.sound t reason (by simpa only [checkTree] using hc) p hp
    rw [hP] at he
    cases he
  | covered => exact t.covered_sound K (by simpa only [checkTree] using hc) hp
  | leaf =>
    cases hs : t.suffix with
    | leaf S words =>
      have he := (t.leaf_contains hs p).mp hp
      subst p
      simp only [checkTree, hs, hP, Bool.not_true, Bool.false_or] at hc
      exact (K.contains_iff _).mp hc
    | cons level tail => simp only [checkTree, hs, Bool.false_eq_true] at hc
  | branch children =>
    simp only [checkTree] at hc
    split at hc
    · cases hc
    · rename_i level tail hs
      split at hc
      · rename_i hsize
        obtain ⟨i, hi⟩ := (t.contains_children hs p).mp hp
        exact checkTree_sound C K (t.child hs i) children[i.val]
          ((of_decide_eq_true hc) i) p hi hP
      · cases hc
termination_by t.suffix.length
decreasing_by
  all_goals simp_all [Node.child, Chain.length]

/-- A certificate checked against an intermediate subgroup remains valid when
that subgroup grows; earlier coverage claims can be replayed against the final one. -/
theorem checkTree_mono (C : Constraint G P) (t : Node G) (certificate : Certificate C.Reason)
    {K L : Group n} (hkl : K.IsSubgroup L) (hc : checkTree C K t certificate = true) :
    checkTree C L t certificate = true := by
  cases certificate with
  | rejected reason => simpa only [checkTree] using hc
  | covered =>
    simpa only [checkTree] using t.covered_mono hkl (by simpa only [checkTree] using hc)
  | leaf =>
    cases hs : t.suffix with
    | leaf S words =>
      simp only [checkTree, hs] at hc ⊢
      by_cases hp : P.test t.rep.val = true
      · simp only [hp, Bool.not_true, Bool.false_or] at hc ⊢
        exact (L.contains_iff _).mpr (hkl _ ((K.contains_iff _).mp hc))
      · simp [Bool.eq_false_iff.mpr hp]
    | cons level tail => simp only [checkTree, hs, Bool.false_eq_true] at hc
  | branch children =>
    cases hs : t.suffix with
    | leaf S words => rw [checkTree_branch_leaf C K t hs] at hc; cases hc
    | cons level tail =>
      rw [checkTree_branch C K t hs] at hc
      rw [checkTree_branch C L t hs]
      split at hc
      · rename_i hsize
        rw [dite_eq_left hsize]
        apply decide_eq_true
        intro i
        exact checkTree_mono C (t.child hs i) children[i.val] hkl ((of_decide_eq_true hc) i)
      · cases hc
termination_by t.suffix.length
decreasing_by
  all_goals simp_all [Node.child, Chain.length]

/-- A checked result subgroup and a complete account of the original search
tree are both required; checking the result's chain alone is insufficient. -/
@[expose] def checkSearch (C : Constraint G P) (K : Group n) (certificate : Certificate C.Reason) : Bool :=
  K.isSubgroup G && decide (∀ i : Fin K.generators.size, P.test K.generators[i.val] = true) &&
    checkTree C K (Node.root G) certificate

theorem checkSearch_spec (C : Constraint G P) (K : Group n) (certificate : Certificate C.Reason)
    (h : checkSearch C K certificate = true) (p : Perm n) :
    Generated K.generators p ↔ Generated G.generators p ∧ P.test p = true := by
  simp only [checkSearch, Bool.and_eq_true] at h
  constructor
  · intro hp
    exact ⟨(Group.isSubgroup_iff K G).mp h.1.1 p hp, P.generated (of_decide_eq_true h.1.2) hp⟩
  · rintro ⟨hp, hP⟩
    exact checkTree_sound C K (Node.root G) certificate h.2 p ((Node.root_contains G p).mpr hp) hP

end Hex.PermGroup.Search
