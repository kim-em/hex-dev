/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.DagExpand

public section

namespace Hex.SignDet.Dag
variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

private theorem Expansion.step_bounds (memo : Array (Replay E Ctx)) (entry : Entry E Ctx)
    (tree : Replay E Ctx) (h : Expansion.step memo entry = some tree) :
    ∀ pair ∈ entry.children, pair.1 < memo.size ∧ pair.2 < memo.size := by
  cases hc : entry.children with
  | none => simp
  | some pair =>
    rcases pair with ⟨left, right⟩
    unfold Expansion.step at h
    simp only [hc] at h
    cases hl : memo[left]? with
    | none => simp [hl, bind, Option.bind] at h
    | some l =>
      cases hr : memo[right]? with
      | none => simp [hl, hr, bind, Option.bind] at h
      | some r =>
        obtain ⟨bl, _⟩ := Array.getElem?_eq_some_iff.mp hl
        obtain ⟨br, _⟩ := Array.getElem?_eq_some_iff.mp hr
        intro pair hp
        have same : pair = (left, right) := Option.some.inj hp.symm
        subst pair
        exact ⟨bl, br⟩

private theorem Expansion.fold_bounds (entries : List (Entry E Ctx))
    (memo result : Array (Replay E Ctx))
    (h : entries.foldlM (fun memo entry => do
      let tree ← Expansion.step memo entry
      pure (memo.push tree)) memo = some result) :
    ∀ (i : Nat) (hi : i < entries.length), ∀ pair ∈ entries[i].children,
      pair.1 < memo.size + i ∧ pair.2 < memo.size + i := by
  induction entries generalizing memo with
  | nil => simp
  | cons entry entries ih =>
    simp only [List.foldlM_cons] at h
    cases hs : Expansion.step memo entry with
    | none => simp [hs, bind, Option.bind] at h
    | some tree =>
      simp only [hs, bind, Option.bind, pure] at h
      intro i hi pair hp
      cases i with
      | zero =>
        simpa using Expansion.step_bounds memo entry tree hs pair hp
      | succ i =>
        have ht := ih (memo.push tree) h i (by simpa using hi) pair
          (by simpa using hp)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

variable [DecidableEq Ctx] [Hashable E] [Hashable Ctx]

/-- The actual encoder always selects an existing entry, even for a tree
whose arithmetic or support evidence is invalid. -/
theorem encode_root (tree : Replay E Ctx) : (encode tree).root < (encode tree).entries.size := by
  obtain ⟨memo, valid, _, index⟩ := Expansion.encodeFrom_expands Expansion.valid_empty tree
  obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp index
  change (encodeFrom {} tree).2 < (encodeFrom {} tree).1.entries.size
  rw [valid.size]
  exact bound

/-- Every encoded child points strictly backward in the actual entry array.
This holds for every entry, independent of replay validity. -/
theorem encode_bounds (tree : Replay E Ctx) (i : Nat)
    (hi : i < (encode tree).entries.size) :
    ∀ pair ∈ (encode tree).entries[i].children, pair.1 < i ∧ pair.2 < i := by
  obtain ⟨memo, valid, _, _⟩ := Expansion.encodeFrom_expands Expansion.valid_empty tree
  have fold := valid.fold
  rw [← Array.foldlM_toList] at fold
  have bounds := Expansion.fold_bounds _ #[] memo fold i (by simpa [encode] using hi)
  simpa [encode] using bounds

end Hex.SignDet.Dag

/-- info: 'Hex.SignDet.Dag.encode_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dag.encode_bounds
