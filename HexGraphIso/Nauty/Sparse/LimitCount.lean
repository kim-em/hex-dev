/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.LimitBudget
import all HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Limited

/-- The quota counter counts the native search's actual node visits. -/
def Counted (s : State n) : Prop := s.value.numnodes = s.visited

theorem map_counted {s : State n} (h : Counted s)
    (f : Sparse.State n → Sparse.State n) (hf : (f s.value).numnodes = s.value.numnodes) :
    Counted (map f s) := by
  unfold map
  split
  · exact h
  · exact hf.trans h

theorem visit_counted {s : State n} (h : Counted s) (g : Graph n) (level nc : Nat) :
    Counted (visit g level nc s).2.2 := by
  unfold visit
  split
  · exact h
  · exact congrArg (· + 1) h

private theorem compare_count (s : Sparse.State n) (level code : Nat) :
    (compareCodes level code s).numnodes = s.numnodes := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.numnodes, ite_self]

private theorem target_count (s : Sparse.State n) (g : Graph n) (first : Bool)
    (tcLevel level nc : Nat) :
    (Sparse.chooseTarget first g tcLevel level nc s).2.2.2.numnodes = s.numnodes := by
  unfold Sparse.chooseTarget
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite SearchState.numnodes, ite_self]

private theorem classify_count (s : Sparse.State n) (g : Graph n) (level nc : Nat) :
    (Sparse.classify g level nc s).2.numnodes = s.numnodes := by
  have scatter_count (lab : Array Nat) (s : Sparse.State n) :
      (scatter lab s).numnodes = s.numnodes := rfl
  unfold Sparse.classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  simp only [apply_ite SearchState.numnodes, scatter_count, ite_self]

private theorem leaf_count (s : Sparse.State n) (leaf : Generic.Leaf) (level : Nat) :
    (leafExit leaf level s).2.numnodes = s.numnodes := by
  have admit_count (s : Sparse.State n) : (admit s).numnodes = s.numnodes := by
    unfold admit pushAuto
    simp only [Id.run_pure]
    split <;> rfl
  have prune_count (s : Sparse.State n) : (pruneReturn level s).2.numnodes = s.numnodes := by
    unfold pruneReturn pushAuto
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    repeat' split
    all_goals rfl
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first | rfl | exact admit_count _ | exact prune_count _

/-- Every native callback preserves the equality of the two counters;
only `visit` increments them, together, after admission. -/
theorem countPolicy (g : Graph n) (inf tcLevel : Nat) :
    Generic.Preserve g inf tcLevel (Counted (n := n)) where
  visit := fun level nc s h => visit_counted h g level nc
  record := fun _ _ _ h => map_counted h _ rfl
  compare := fun _ _ _ h => map_counted h _ (compare_count ..)
  target := by
    intro first level nc s h
    change Counted (if s.exhausted then ((-1 : Int), VSet.empty (n := n), 0, s) else _).2.2.2
    split
    · exact h
    · exact (target_count ..).trans h
  terminal := fun _ _ h => map_counted h _ rfl
  classify := by
    intro level nc s h
    change Counted (if s.exhausted then (Generic.Leaf.bad, s) else _).2
    split
    · exact h
    · exact (classify_count ..).trans h
  leaf := by
    intro leaf level s h
    change Counted (if s.exhausted then (Generic.Exit.fuel, s) else _).2
    split
    · exact h
    · exact (leaf_count ..).trans h
  cheap := by
    intro first level s h
    apply map_counted h
    change (cheapCheck first level s.value).numnodes = s.value.numnodes
    unfold cheapCheck
    split <;> rfl
  child := by
    intro first level tc tv s h
    apply map_counted h
    cases first <;> rfl
  afterChild := fun _ _ _ h => map_counted h _ rfl
  leave := fun _ _ h => map_counted h _ rfl
  recover := by
    intro level s h
    apply map_counted h
    change (recoverLevels level (recoverPtn inf level s.value)).numnodes = s.value.numnodes
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.numnodes, ite_self]
  afterSweep := by
    intro first level size index s h
    apply map_counted h
    cases first <;> unfold Sparse.policy afterSweep
    all_goals simp only [Bool.false_eq_true, ite_false, ite_true,
      apply_ite SearchState.numnodes, ite_self]

theorem node_counted {s : State n} (h : Counted s)
    (g : Graph n) (inf tcLevel fuel level nc : Nat) (first : Bool) :
    Counted (Generic.node first g inf tcLevel fuel level nc s).2 :=
  Generic.node_sound (countPolicy g inf tcLevel).sound first fuel level nc s h

/-- The actual node count is bounded even for an exhausted return. -/
theorem node_nodes {limit : Nat} {s : State n} (hb : Budget limit s) (hc : Counted s)
    (g : Graph n) (inf tcLevel fuel level nc : Nat) (first : Bool) :
    (Generic.node first g inf tcLevel fuel level nc s).2.value.numnodes ≤ limit := by
  have hb' := node_budget hb g inf tcLevel fuel level nc first
  have hc' := node_counted hc g inf tcLevel fuel level nc first
  dsimp only [Budget] at hb'
  dsimp only [Counted] at hc'
  omega

/-- A completed bounded root reports exactly its admitted native visits. -/
theorem run?_counted {limit : Nat} {g : Graph n} {lab : Array Nat} {ends : List Nat}
    {s : State n} (h : run? limit g lab ends = some s) : Counted s := by
  unfold run? at h
  split at h
  · cases h
  · split at h
    · cases Option.some.inj h
      rfl
    · dsimp only at h
      split at h
      · cases h
      · cases Option.some.inj h
        exact node_counted (by rfl) g (n + 2) 100 (n + 2) 1 ends.length true

theorem run?_nodes {limit : Nat} {g : Graph n} {lab : Array Nat} {ends : List Nat}
    {s : State n} (h : run? limit g lab ends = some s) : s.value.numnodes ≤ limit := by
  rw [show s.value.numnodes = s.visited from run?_counted h]
  exact run?_visited h

theorem runColored?_nodes {limit : Nat} {G : GraphIso.Sparse.Colored n k}
    {s : State n} (h : runColored? limit G = some s) : s.value.numnodes ≤ limit :=
  run?_nodes h

/-- The two native traversals together fit the single supplied quota. -/
theorem runPair?_nodes {limit : Nat} {G H : GraphIso.Sparse.Colored n k}
    {a b : State n} (h : runPair? limit G H = some (a, b)) :
    a.value.numnodes + b.value.numnodes ≤ limit := by
  unfold runPair? at h
  change (runColored? limit G).bind (fun sa =>
    (runColored? sa.remaining H).bind (fun sb => some (sa, sb))) = some (a, b) at h
  cases ha : runColored? limit G with
  | none => simp only [ha, Option.bind_none, reduceCtorEq] at h
  | some sa =>
    cases hb : runColored? sa.remaining H with
    | none => simp only [ha, hb, Option.bind_some, Option.bind_none, reduceCtorEq] at h
    | some sb =>
      simp only [ha, hb, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hab := run?_budget ha
      have hac := run?_counted ha
      have hbc := runColored?_nodes hb
      dsimp only [Budget] at hab
      dsimp only [Counted] at hac
      omega

end Hex.GraphIso.Nauty.Sparse.Limited
