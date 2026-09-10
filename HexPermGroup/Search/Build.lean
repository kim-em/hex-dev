/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Children

public section

namespace Hex.PermGroup.Search

variable {G : Group n} {P : Predicate n}

/-- Exact deterministic backtracking. A successful leaf contributes a new
generator only if needed; subsequent subtrees can be covered by the growing
subgroup. Rejected subtrees retain the constraint's replayable reason. -/
@[expose] def visit (C : Constraint G P) (t : Node G) (a : Accumulator G P) : Result C t a :=
  if hc : t.covered a.group = true then
    { acc := a
      grows := fun _ hp => hp
      certificate := .covered
      checked := by simpa only [checkTree] using hc }
  else
    match hr : C.find t with
    | some reason =>
      { acc := a
        grows := fun _ hp => hp
        certificate := .rejected reason
        checked := by simpa only [checkTree] using C.checked t reason hr }
    | none =>
      match hs : t.suffix with
      | .leaf S words =>
        if hp : P.test t.rep.val = true then
          if hm : a.group.contains t.rep.val = true then
            { acc := a
              grows := fun _ hq => hq
              certificate := .leaf
              checked := by simp [checkTree, hs, hm] }
          else
            { acc := a.adjoin t.rep hp
              grows := a.adjoin_grows t.rep hp
              certificate := .leaf
              checked := by
                simp only [checkTree, hs, hp, Bool.not_true, Bool.false_or]
                exact ((a.adjoin t.rep hp).group.contains_iff _).mpr (a.mem_adjoin t.rep hp) }
        else
          { acc := a
            grows := fun _ hq => hq
            certificate := .leaf
            checked := by simp [checkTree, hs, Bool.eq_false_iff.mpr hp] }
      | .cons level tail =>
        let children := Children.collect C (t.child hs)
          (fun a i => visit C (t.child hs i) a) a level.orbit.points.size (Nat.le_refl _)
        { acc := children.acc
          grows := children.grows
          certificate := .branch children.certificates.toArray
          checked := by
            rw [checkTree_branch C children.acc.group t hs]
            simp only [Vector.size_toArray]
            exact decide_eq_true children.checked }
termination_by t.suffix.length
decreasing_by
  all_goals
    change tail.length < t.suffix.length
    rw [hs]
    exact Nat.lt_succ_self _

/-- An accepted completeness certificate accompanies every exact result. -/
structure Solution {G : Group n} {P : Predicate n} (C : Constraint G P) where
  group : Group n
  certificate : Certificate C.Reason
  checked : checkSearch C group certificate = true

theorem Solution.spec (C : Constraint G P) (s : Solution C) (p : Perm n) :
    Generated s.group.generators p ↔ Generated G.generators p ∧ P.test p = true :=
  checkSearch_spec C s.group s.certificate s.checked p

/-- Search starts with the trivial subgroup and follows the input group's
checked chain. No list of all input elements is constructed. -/
@[expose] def solve (C : Constraint G P) : Solution C :=
  let r := visit C (Node.root G) (Accumulator.empty G P)
  { group := r.acc.group
    certificate := r.certificate
    checked := by
      rw [checkSearch, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨(Group.isSubgroup_iff _ _).mpr r.acc.inside, ?_⟩, r.checked⟩
      apply decide_eq_true
      intro i
      exact r.acc.satisfies _ (.generator (Array.getElem_mem i.isLt)) }

end Hex.PermGroup.Search
