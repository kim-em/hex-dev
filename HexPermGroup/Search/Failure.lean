/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Check

public section

namespace Hex.PermGroup.Search

variable {G : Group n} {test : Perm n → Bool}

/-- A negative answer accounts for every completion. Subgroup coverage is not
a valid reason here: even one satisfying element would refute nonexistence. -/
@[expose] def checkFailure (C : Pruner G test) (t : Node G) (certificate : Certificate C.Reason) : Bool :=
  match certificate with
  | .covered => false
  | .rejected r => C.reject t r
  | .leaf =>
    match t.suffix with
    | .leaf _ _ => !test t.rep.val
    | .cons _ _ => false
  | .branch children =>
    match hs : t.suffix with
    | .leaf _ _ => false
    | .cons level tail =>
      if hc : children.size = level.orbit.points.size then
        decide (∀ i : Fin level.orbit.points.size, checkFailure C (t.child hs i) children[i.val] = true)
      else false
termination_by t.suffix.length
decreasing_by
  all_goals
    change tail.length < t.suffix.length
    rw [hs]
    exact Nat.lt_succ_self _

theorem checkFailure_branch (C : Pruner G test) (t : Node G)
    {level : Level n} {tail : Chain n} (hs : t.suffix = .cons level tail)
    (children : Array (Certificate C.Reason)) :
    checkFailure C t (.branch children) =
      if hc : children.size = level.orbit.points.size then
        decide (∀ i : Fin level.orbit.points.size, checkFailure C (t.child hs i) children[i.val] = true)
      else false := by
  cases t with
  | mk base suffix checked inside rep =>
    simp only at hs
    subst suffix
    rw [checkFailure]

theorem checkFailure_sound (C : Pruner G test) (t : Node G) (certificate : Certificate C.Reason)
    (hc : checkFailure C t certificate = true) (p : Perm n) (hp : t.Contains p) : test p = false := by
  cases certificate with
  | covered => simp only [checkFailure, Bool.false_eq_true] at hc
  | rejected r => exact C.sound t r (by simpa only [checkFailure] using hc) p hp
  | leaf =>
    cases hs : t.suffix with
    | leaf S words =>
      have he := (t.leaf_contains hs p).mp hp
      subst p
      simpa only [checkFailure, hs, Bool.not_eq_true'] using hc
    | cons level tail => simp only [checkFailure, hs, Bool.false_eq_true] at hc
  | branch children =>
    simp only [checkFailure] at hc
    split at hc
    · cases hc
    · rename_i level tail hs
      split at hc
      · obtain ⟨i, hi⟩ := (t.contains_children hs p).mp hp
        exact checkFailure_sound C (t.child hs i) children[i.val] ((of_decide_eq_true hc) i) p hi
      · cases hc
termination_by t.suffix.length
decreasing_by
  all_goals simp_all [Node.child, Chain.length]

theorem checkFailure_spec (C : Pruner G test) (certificate : Certificate C.Reason)
    (hc : checkFailure C (Node.root G) certificate = true) :
    ¬ ∃ p : Element G, test p.val = true := by
  rintro ⟨p, hp⟩
  have he := checkFailure_sound C (Node.root G) certificate hc p.val ((Node.root_contains G p.val).mpr p.property)
  rw [hp] at he
  cases he

/-- Positive answers need only replay a word in the original generators and
the defining test; they make no completeness claim about other branches. -/
@[expose] def checkWitness (G : Group n) (test : Perm n → Bool) (p : Perm n) (word : Program) : Bool :=
  checkWord G.generators p word && test p

theorem checkWitness_spec (G : Group n) (test : Perm n → Bool) (p : Perm n) (word : Program)
    (h : checkWitness G test p word = true) : Generated G.generators p ∧ test p = true := by
  simp only [checkWitness, Bool.and_eq_true] at h
  exact ⟨checkWord_sound h.1, h.2⟩

end Hex.PermGroup.Search
