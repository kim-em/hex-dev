/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Limited
public import HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Policy.Preserve

public section

namespace Hex.GraphIso.Nauty.Sparse.Limited

/-- Every executed policy callback conserves admitted visits plus quota. -/
theorem budgetPolicy (g : Graph n) (inf tcLevel limit : Nat) :
    Generic.Preserve g inf tcLevel (Budget (n := n) limit) where
  visit := fun level nc s h => visit_budget h g level nc
  record := fun _ _ _ h => map_budget h _
  compare := fun _ _ _ h => map_budget h _
  target := by
    intro first level nc s h
    change Budget limit (if s.exhausted then ((-1 : Int), VSet.empty (n := n), 0, s) else _).2.2.2
    split <;> exact h
  terminal := fun _ _ h => map_budget h _
  classify := by
    intro level nc s h
    change Budget limit (if s.exhausted then (Generic.Leaf.bad, s) else _).2
    split <;> exact h
  leaf := by
    intro leaf level s h
    change Budget limit (if s.exhausted then (Generic.Exit.fuel, s) else _).2
    split <;> exact h
  cheap := fun _ _ _ h => map_budget h _
  child := fun _ _ _ _ _ h => map_budget h _
  afterChild := fun _ _ _ h => map_budget h _
  leave := fun _ _ h => map_budget h _
  recover := fun _ _ h => map_budget h _
  afterSweep := fun _ _ _ _ _ h => map_budget h _

/-- The actual mutual recursion conserves the quota through all returns. -/
theorem node_budget {limit : Nat} {s : State n} (h : Budget limit s)
    (g : Graph n) (inf tcLevel fuel level numcells : Nat) (first : Bool) :
    Budget limit (Generic.node first g inf tcLevel fuel level numcells s).2 :=
  Generic.node_sound (budgetPolicy g inf tcLevel limit).sound first fuel level numcells s h

/-- Every accepted root retains its exact original node budget. -/
theorem run?_budget {limit : Nat} {g : Graph n} {lab : Array Nat} {ends : List Nat}
    {s : State n} (h : run? limit g lab ends = some s) : Budget limit s := by
  unfold run? at h
  split at h
  · cases h
  · rename_i hl
    split at h
    · cases Option.some.inj h
      dsimp only [Budget]
      omega
    · dsimp only at h
      split at h
      · cases h
      · cases Option.some.inj h
        exact node_budget (by simp only [Budget, Nat.zero_add])
          g (n + 2) 100 (n + 2) 1 ends.length true

/-- A successful bounded search never admits more than its node limit. -/
theorem run?_visited {limit : Nat} {g : Graph n} {lab : Array Nat} {ends : List Nat}
    {s : State n} (h : run? limit g lab ends = some s) : s.visited ≤ limit := by
  have hb := run?_budget h
  dsimp only [Budget] at hb
  omega

theorem runColored?_visited {limit : Nat} {G : GraphIso.Sparse.Colored n k}
    {s : State n} (h : runColored? limit G = some s) : s.visited ≤ limit :=
  run?_visited h

/-- After exhaustion every callback retains the entire wrapped state.
The native payload cannot be changed by unwinding or sibling processing. -/
theorem frozenPolicy (g : Graph n) (inf tcLevel : Nat) (s : State n)
    (hs : s.exhausted = true) : Generic.Preserve g inf tcLevel (fun t : State n => t = s) := by
  cases s with
  | mk value remaining visited exhausted =>
    cases hs
    constructor
    all_goals intros
    all_goals subst_vars
    all_goals rfl

/-- Exhaustion is absorbing throughout the actual mutual recursion. -/
theorem node_exhausted (g : Graph n) (inf tcLevel fuel level nc : Nat) (first : Bool)
    (s : State n) (hs : s.exhausted = true) :
    (Generic.node first g inf tcLevel fuel level nc s).2 = s :=
  Generic.node_sound (frozenPolicy g inf tcLevel s hs).sound first fuel level nc s rfl

end Hex.GraphIso.Nauty.Sparse.Limited
