/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Dag
public import HexSignDet.SignOperands

public section

namespace Hex.SignDet.Dag

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
  [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Sign dependencies of every stored node, including unreachable entries. -/
@[expose] def signOperands (p : DensePoly E) (a b : Endpoint E) (dag : Dag E Ctx) : List E :=
  dag.entries.toList.flatMap fun entry => entry.node.signOperands p a b

/-- A checked step depends on the same finite signs as its local node; memoized
children contribute their literal values rather than another sign computation. -/
theorem step_sign_congr (sign sign' : E → Int) (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (memo : Array (Checked sign context p a b))
    (memo' : Array (Checked sign' context p a b)) (entry : Entry E Ctx)
    (hm : memo.map Checked.value = memo'.map Checked.value)
    (h : ∀ x ∈ entry.node.signOperands p a b, sign x = sign' x) :
    (step sign context p a b memo entry).map Checked.value =
      (step sign' context p a b memo' entry).map Checked.value := by
  have hn := entry.node.check_sign_congr sign sign' context p a b entry.node.queries h
  have hv (i : Nat) : (memo[i]?).map Checked.value = (memo'[i]?).map Checked.value := by
    simpa only [Array.getElem?_map] using congrArg (fun xs => xs[i]?) hm
  rw [step_eq, step_eq]
  cases hc : entry.children with
  | none =>
    have hb := Replay.check_sign_congr sign sign' context p a b entry.node.queries
      (.leaf entry.node) h
    simp only [hb, pure, Option.map_dite]
  | some pair =>
    rcases pair with ⟨left, right⟩
    cases hl : memo[left]? with
    | none =>
      have hl' : memo'[left]? = none := by
        have he := hv left
        simp only [hl, Option.map_none] at he
        cases ht : memo'[left]? <;> simp_all
      simp only [hl, hl', bind, Option.bind, Option.map_none]
    | some l =>
      cases hl' : memo'[left]? with
      | none => have he := hv left; simp [hl, hl'] at he
      | some l' =>
        rcases l with ⟨lv, la⟩
        rcases l' with ⟨lv', la'⟩
        have hleft : lv = lv' := by simpa [hl, hl'] using hv left
        subst lv'
        cases hr : memo[right]? with
        | none =>
          have hr' : memo'[right]? = none := by
            have he := hv right
            simp only [hr, Option.map_none] at he
            cases ht : memo'[right]? <;> simp_all
          simp only [hl, hl', hr, hr', bind, Option.bind, Option.map_none]
        | some r =>
          cases hr' : memo'[right]? with
          | none => have he := hv right; simp [hr, hr'] at he
          | some r' =>
            rcases r with ⟨rv, ra⟩
            rcases r' with ⟨rv', ra'⟩
            have hright : rv = rv' := by simpa [hr, hr'] using hv right
            subst rv'
            simp only [hl, hl', hr, hr', bind, Option.bind, hn, pure]
            split <;> (try rfl)
            split <;> (try rfl)
            split <;> rfl

/-- Finite sign agreement preserves every prefix of the actual checked fold,
including rejections and the literal values kept in its memo array. -/
theorem fold_sign_congr (sign sign' : E → Int) (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (entries : List (Entry E Ctx))
    (memo : Array (Checked sign context p a b))
    (memo' : Array (Checked sign' context p a b))
    (hm : memo.map Checked.value = memo'.map Checked.value)
    (h : ∀ entry ∈ entries, ∀ x ∈ entry.node.signOperands p a b, sign x = sign' x) :
    (entries.foldlM (fun memo entry => do
      let next ← step sign context p a b memo entry
      pure (memo.push next)) memo).map (Array.map Checked.value) =
    (entries.foldlM (fun memo entry => do
      let next ← step sign' context p a b memo entry
      pure (memo.push next)) memo').map (Array.map Checked.value) := by
  induction entries generalizing memo memo' with
  | nil => simpa only [List.foldlM_nil, pure, Option.map_some] using congrArg some hm
  | cons entry entries ih =>
    have hs := step_sign_congr sign sign' context p a b memo memo' entry hm
      (h entry (by simp))
    have ht : ∀ entry ∈ entries, ∀ x ∈ entry.node.signOperands p a b,
        sign x = sign' x := fun entry he => h entry (by simp [he])
    cases hn : step sign context p a b memo entry with
    | none =>
      have hn' : step sign' context p a b memo' entry = none := by
        simp only [hn, Option.map_none] at hs
        cases hh : step sign' context p a b memo' entry <;> simp_all
      simp only [List.foldlM_cons, hn, hn', bind, Option.bind, Option.map_none]
    | some next =>
      cases hn' : step sign' context p a b memo' entry with
      | none => simp [hn, hn'] at hs
      | some next' =>
        have hv : next.value = next'.value := by simpa [hn, hn'] using hs
        have hp : (memo.push next).map Checked.value =
            (memo'.push next').map Checked.value := by
          simp only [Array.map_push, hm, hv]
        simp only [List.foldlM_cons, hn, hn', bind, Option.bind, pure]
        exact ih (memo.push next) (memo'.push next') hp ht

private theorem select_congr (sign sign' : E → Int) (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (qs : List (DensePoly E)) (root : Nat)
    (memo : Option (Array (Checked sign context p a b)))
    (memo' : Option (Array (Checked sign' context p a b)))
    (hm : memo.map (Array.map Checked.value) = memo'.map (Array.map Checked.value)) :
    ((do
      let values ← memo
      let selected ← values[root]?
      if h : selected.value.node.queries = qs then
        return ⟨selected.value, by simpa only [h] using selected.accepted⟩
      else none) : Option {t : Replay E Ctx // t.check sign context p a b qs = true}).map
      Subtype.val =
    ((do
      let values ← memo'
      let selected ← values[root]?
      if h : selected.value.node.queries = qs then
        return ⟨selected.value, by simpa only [h] using selected.accepted⟩
      else none) : Option {t : Replay E Ctx // t.check sign' context p a b qs = true}).map
      Subtype.val := by
  cases memo with
  | none =>
    have hn : memo' = none := by simpa only [Option.map_none, Option.map_eq_none_iff] using hm.symm
    subst memo'
    rfl
  | some values =>
    cases memo' with
    | none => simp at hm
    | some values' =>
      have hv : values.map Checked.value = values'.map Checked.value := by simpa using hm
      have hr : (values[root]?).map Checked.value = (values'[root]?).map Checked.value := by
        simpa only [Array.getElem?_map] using congrArg (fun xs => xs[root]?) hv
      cases hl : values[root]? with
      | none =>
        have hl' : values'[root]? = none := by
          simpa only [hl, Option.map_none, Option.map_eq_none_iff] using hr.symm
        simp only [hl, hl', bind, Option.bind, Option.map_none]
      | some selected =>
        cases hl' : values'[root]? with
        | none => simp [hl, hl'] at hr
        | some selected' =>
          rcases selected with ⟨value, accepted⟩
          rcases selected' with ⟨value', accepted'⟩
          have he : value = value' := by simpa [hl, hl'] using hr
          subst value'
          simp only [hl, hl', bind, Option.bind, pure, Option.map_dite]

/-- Finite agreement on all stored nodes preserves the returned tree as well
as failure, without rerunning a recursively expanded tree. -/
theorem replay_sign_congr (sign sign' : E → Int) (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (qs : List (DensePoly E)) (dag : Dag E Ctx)
    (h : ∀ x ∈ dag.signOperands p a b, sign x = sign' x) :
    (replay? sign context p a b qs dag).map Subtype.val =
      (replay? sign' context p a b qs dag).map Subtype.val := by
  have hf := fold_sign_congr sign sign' context p a b dag.entries.toList #[] #[] (by simp)
    (fun entry he x hx => h x (List.mem_flatMap.mpr ⟨entry, he, hx⟩))
  rw [Array.foldlM_toList, Array.foldlM_toList] at hf
  rw [replay_eq, replay_eq]
  exact select_congr sign sign' context p a b qs dag.root _ _ hf

/-- The graph's exact Boolean result depends only on its finite inventory,
including malformed, unreachable and rejected entries. -/
theorem check_sign_congr (sign sign' : E → Int) (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (qs : List (DensePoly E)) (dag : Dag E Ctx)
    (h : ∀ x ∈ dag.signOperands p a b, sign x = sign' x) :
    check sign context p a b qs dag = check sign' context p a b qs dag := by
  have he := replay_sign_congr sign sign' context p a b qs dag h
  simpa only [Option.isSome_map, check] using congrArg Option.isSome he

end Hex.SignDet.Dag
