/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.LimitSweep
import all HexGraphIso.Nauty.Search.Generic

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Limited

/-- The literal common tail of `Generic.nodeStep`, for either state type. -/
def tail {σ γ : Type} [Generic.Policy σ n (γ := γ)] (next : Generic.SweepFn σ n)
    (first : Bool) (level nc tc size : Nat) (cell : VSet n) (s : σ) : Generic.Exit × σ := Id.run do
  let s := Generic.Policy.cheapCheck (n := n) first level s
  let tv := cell.nextElem none
  let (exit, index, out) := next first level nc tc (tv.getD 0) tv cell 0 s
  match exit with
  | .done => return (.unwind (level - 1) false,
      Generic.Policy.afterSweep (n := n) first level size index out)
  | _ => return (exit, out)

/-- This decomposition is definitionally the executed node step. -/
theorem nodeStep_eq {σ γ : Type} [Generic.Policy σ n (γ := γ)]
    (g : γ) (tcLevel : Nat) (next : Generic.SweepFn σ n)
    (first : Bool) (level nc : Nat) (s : σ) :
    Generic.nodeStep g tcLevel next first level nc s =
      let r := Generic.Policy.visit (n := n) g level nc s
      let recorded := if first then Generic.Policy.recordFirst (n := n) level r.2.1 r.2.2
        else Generic.Policy.compareCodes (n := n) level r.2.1 r.2.2
      let t := Generic.Policy.chooseTarget (n := n) first g tcLevel level r.1 recorded
      if first then
        if r.1 == n then (.unwind (level - 1) false, Generic.Policy.firstterminal (n := n) level t.2.2.2)
        else tail next first level r.1 t.1.toNat t.2.2.1 t.2.1 t.2.2.2
      else
        let c := Generic.Policy.classify (n := n) g level r.1 t.2.2.2
        let e := Generic.Policy.leafExit (n := n) c.1 level c.2
        match e.1 with
        | .done => tail next first level r.1 t.1.toNat t.2.2.1 t.2.1 e.2
        | _ => e := by rfl

theorem cheap_ready (first : Bool) (level : Nat) (s : State n) :
    Ready ((policy (n := n)).cheapCheck first level s) ↔ Ready s := map_ready _ s

theorem cheap_value (first : Bool) (level : Nat) {s : State n} (hs : Ready s) :
    ((policy (n := n)).cheapCheck first level s).value =
      (Sparse.policy (n := n)).cheapCheck first level s.value := map_value _ hs

theorem afterSweep_ready (first : Bool) (level size index : Nat) (s : State n) :
    Ready ((policy (n := n)).afterSweep first level size index s) ↔ Ready s := map_ready _ s

theorem afterSweep_value (first : Bool) (level size index : Nat) {s : State n} (hs : Ready s) :
    ((policy (n := n)).afterSweep first level size index s).value =
      (Sparse.policy (n := n)).afterSweep first level size index s.value := map_value _ hs

theorem tail_eq {next : Generic.SweepFn (State n) n}
    {plain : Generic.SweepFn (Sparse.State n) n} (hn : SweepEq next plain)
    (first : Bool) (level nc tc size : Nat) (cell : VSet n) (s : State n)
    (h : Ready (tail next first level nc tc size cell s).2) :
    Ready s ∧ nodeValue (tail next first level nc tc size cell s) =
      tail plain first level nc tc size cell s.value := by
  unfold tail at h
  dsimp only at h
  generalize he : next first level nc tc ((cell.nextElem none).getD 0)
    (cell.nextElem none) cell 0 ((policy (n := n)).cheapCheck first level s) = r at h
  obtain ⟨exit, index, out⟩ := r
  cases exit
  all_goals
    have hout : Ready out := by
      first | exact h | exact (afterSweep_ready first level size index out).mp h
    have hr := hn first level nc tc ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0
      ((policy (n := n)).cheapCheck first level s) (by rw [he]; exact hout)
    have hs := (cheap_ready first level s).mp hr.1
    have hp := hr.2.symm
    rw [he] at hp
    simp only [sweepValue, cheap_value first level hs] at hp
    refine ⟨hs, ?_⟩
    simp only [tail, he, hp, Id.run_pure, nodeValue, afterSweep_value first level size index hout]

/-- Rejecting a visit produces an exhausted node immediately; it cannot
call the supplied sibling continuation or execute native callbacks. -/
theorem nodeStep_exhausted (g : Graph n) (tcLevel : Nat) (next : Generic.SweepFn (State n) n)
    (first : Bool) (level nc : Nat) (s : State n)
    (hg : (s.exhausted || s.remaining == 0) = true) :
    (Generic.nodeStep g tcLevel next first level nc s).2.exhausted = true := by
  have hv : (policy (n := n)).visit g level nc s = (n, 0, { s with exhausted := true }) := by
    change visit g level nc s = _
    simp only [visit, hg, ite_true]
  rw [nodeStep_eq, hv]
  cases first
  · rfl
  · simp only [ite_true, beq_self_eq_true]
    rfl

/-- An accepted bounded node takes exactly the native visit, classification
and child-sweep path. Rejected visits cannot produce an accepted return. -/
theorem nodeStep_value {next : Generic.SweepFn (State n) n}
    {plain : Generic.SweepFn (Sparse.State n) n} (hn : SweepEq next plain)
    (g : Graph n) (tcLevel : Nat) (first : Bool) (level nc : Nat) (s : State n)
    (h : Ready (Generic.nodeStep g tcLevel next first level nc s).2) :
    Ready s ∧ nodeValue (Generic.nodeStep g tcLevel next first level nc s) =
      Generic.nodeStep g tcLevel plain first level nc s.value := by
  by_cases hg : (s.exhausted || s.remaining == 0) = true
  · have he := nodeStep_exhausted g tcLevel next first level nc s hg
    dsimp only [Ready] at h
    rw [he] at h
    cases h
  · have hs : s.exhausted = false := by
      cases he : s.exhausted <;> simp_all
    refine ⟨hs, ?_⟩
    simp only [nodeStep_eq, Generic.Policy.visit, visit, hg] at h ⊢
    generalize hv : Sparse.visit g level nc s.value = r at h ⊢
    obtain ⟨count, code, value⟩ := r
    cases first
    all_goals
      simp only [Generic.Policy.recordFirst, Generic.Policy.compareCodes, Generic.Policy.chooseTarget,
        Generic.Policy.firstterminal, Generic.Policy.classify, Generic.Policy.leafExit,
        map, Bool.false_eq_true, ite_false, ite_true] at h ⊢
    case false =>
      let t := Sparse.chooseTarget false g tcLevel level count (compareCodes level code value)
      let c := Sparse.classify g level count t.2.2.2
      generalize he : leafExit c.1 level c.2 = e at h ⊢
      obtain ⟨exit, out⟩ := e
      cases exit
      all_goals first | rfl | exact (tail_eq hn _ _ _ _ _ _ _ h).2
    case true =>
      by_cases hc : (count == n) = true
      · simp only [hc, ite_true] at h ⊢
        rfl
      · simp only [hc, Bool.false_eq_true, ite_false] at h ⊢
        exact (tail_eq hn _ _ _ _ _ _ _ h).2

end Hex.GraphIso.Nauty.Sparse.Limited
