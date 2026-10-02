/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Run

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Limited

/-- Search-limit bookkeeping surrounds the unchanged native search state.
`visited` counts admitted node visits; exhaustion prevents all later native
policy operations from executing. -/
structure State (n : Nat) where
  value : Sparse.State n
  remaining : Nat
  visited : Nat := 0
  exhausted : Bool := false

/-- Apply a native state operation while retaining the limit counters. -/
def map (f : Sparse.State n → Sparse.State n) (s : State n) : State n :=
  if s.exhausted then s else { s with value := f s.value }

/-- Admit a node before calling sparse refinement. No native visit occurs
after the remaining quota reaches zero. -/
def visit (g : Graph n) (level numcells : Nat) (s : State n) : Nat × Nat × State n :=
  if s.exhausted || s.remaining == 0 then (n, 0, { s with exhausted := true })
  else
    let r := Sparse.visit g level numcells s.value
    (r.1, r.2.1, {
      value := r.2.2
      remaining := s.remaining - 1
      visited := s.visited + 1
      exhausted := false })

/-- Every non-visit callback delegates to the production sparse policy.
An exhausted first-path node becomes terminal without executing native
callbacks; off-path exhaustion propagates the ordinary fuel exit. -/
instance policy : Generic.Policy (State n) n (γ := Graph n) where
  visit := visit
  recordFirst level code := map ((Sparse.policy (n := n)).recordFirst level code)
  compareCodes level code := map ((Sparse.policy (n := n)).compareCodes level code)
  chooseTarget first g tcLevel level numcells s :=
    if s.exhausted then (-1, .empty, 0, s) else
      let r := (Sparse.policy (n := n)).chooseTarget first g tcLevel level numcells s.value
      (r.1, r.2.1, r.2.2.1, { s with value := r.2.2.2 })
  firstterminal level := map ((Sparse.policy (n := n)).firstterminal level)
  classify g level numcells s :=
    if s.exhausted then (.bad, s) else
      let r := (Sparse.policy (n := n)).classify g level numcells s.value
      (r.1, { s with value := r.2 })
  leafExit leaf level s :=
    if s.exhausted then (.fuel, s) else
      let r := (Sparse.policy (n := n)).leafExit leaf level s.value
      (r.1, { s with value := r.2 })
  cheapCheck first level := map ((Sparse.policy (n := n)).cheapCheck first level)
  child first level tc tv := map ((Sparse.policy (n := n)).child first level tc tv)
  afterChildFirst level tv := map ((Sparse.policy (n := n)).afterChildFirst level tv)
  leaveChild tv := map ((Sparse.policy (n := n)).leaveChild tv)
  orbit s tv := if s.exhausted then 0 else (Sparse.policy (n := n)).orbit s.value tv
  shortprune cell s := if s.exhausted then .empty else (Sparse.policy (n := n)).shortprune cell s.value
  longprune cell s := if s.exhausted then .empty else (Sparse.policy (n := n)).longprune cell s.value
  recover inf level := map ((Sparse.policy (n := n)).recover inf level)
  afterSweep first level size index := map ((Sparse.policy (n := n)).afterSweep first level size index)

/-- Run a node-limited native search. Exhaustion returns no search result.
The empty root costs one node, matching the direct search's convention. -/
def run? (maxNodes : Nat) (g : Graph n) (lab : Array Nat) (ends : List Nat) : Option (State n) :=
  if maxNodes = 0 then none else
    let initial := Sparse.initial g lab ends
    if n = 0 then
      some {
        value := Sparse.finish g { initial with numnodes := 1, canupdates := 1 }
        remaining := maxNodes - 1
        visited := 1 }
    else
      let r := Generic.node true g (n + 2) 100 (n + 2) 1 ends.length
        ({ value := initial, remaining := maxNodes } : State n)
      if r.2.exhausted || r.1 == .fuel then none
      else some { r.2 with value := Sparse.finish g r.2.value }

def runColored? (maxNodes : Nat) (G : GraphIso.Sparse.Colored n k) : Option (State n) :=
  let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
  run? maxNodes (.ofGraph G.graph) p.1 p.2

/-- Both searches share one quota; the second receives only what the first
left unused. Exhaustion of either search leaves the pair inconclusive. -/
def runPair? (maxNodes : Nat) (G H : GraphIso.Sparse.Colored n k) :
    Option (State n × State n) := do
  let a ← runColored? maxNodes G
  let b ← runColored? a.remaining H
  return (a, b)

/-- The sum of admitted visits and the remaining quota. -/
def Budget (limit : Nat) (s : State n) : Prop := s.visited + s.remaining = limit

theorem map_budget {limit : Nat} {s : State n} (h : Budget limit s)
    (f : Sparse.State n → Sparse.State n) : Budget limit (map f s) := by
  unfold map
  split <;> exact h

theorem visit_budget {limit : Nat} {s : State n} (h : Budget limit s)
    (g : Graph n) (level numcells : Nat) : Budget limit (visit g level numcells s).2.2 := by
  unfold visit
  split
  · exact h
  · rename_i ha
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at ha
    dsimp only [Budget] at h ⊢
    omega

theorem visit_exhausted (g : Graph n) (level numcells : Nat) (s : State n)
    (h : s.remaining = 0) :
    visit g level numcells s = (n, 0, { s with exhausted := true }) := by
  simp only [visit, h, beq_self_eq_true, Bool.or_true, ite_true]

theorem run?_zero (g : Graph n) (lab : Array Nat) (ends : List Nat) :
    run? 0 g lab ends = none := by simp only [run?, ite_true]

theorem runColored?_zero (G : GraphIso.Sparse.Colored n k) : runColored? 0 G = none :=
  run?_zero ..

end Hex.GraphIso.Nauty.Sparse.Limited
