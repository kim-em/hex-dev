/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineIndex
public import HexGraphIso.Nauty.Sparse.RefineBoundary
public import HexGraphIso.Nauty.Cert.Cert

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Exact incoming accounting remains exact after the complete refinement. -/
theorem refineWith_count (G : Hex.SparseGraph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n scratch) (hc : numcells = bcount ptn level n) :
    let t := refineWith (.ofGraph G) level lab ptn active numcells scratch
    t.numcells = bcount t.ptn level n := by
  have h := (refineWith_state G level lab ptn active numcells scratch hp hs hend ha hb).2.2.1.count
  omega

/-- The production visit returns a cache valid for its actual refined node. -/
theorem visit_valid (G : Hex.SparseGraph n) (level numcells : Nat) (s : State n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level)
    (ha : ∀ v, s.active.mem v = true → v = 0 ∨ s.ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n s.canong.scratch) :
    let t := (visit (.ofGraph G) level numcells s).2.2
    Scratch.Valid n t.lab t.ptn level t.canong.scratch :=
  (refineWith_state G level s.lab s.ptn s.active numcells s.canong.scratch hp hs hend ha hb).2.2.2.2.2

/-- All partition-state facts required by search survive the sparse visit,
including the sentinel values used by individualization and recovery. -/
theorem visit_nodeOk (G : Hex.SparseGraph n) (level numcells : Nat) (s : State n)
    (hp : s.lab.toList.Perm (List.range n)) (h : NodeOk n level s.lab s.ptn s.active)
    (hb : Scratch.Bounded n s.canong.scratch) :
    let t := (visit (.ofGraph G) level numcells s).2.2
    NodeOk n level t.lab t.ptn t.active := by
  have hend : s.ptn[n - 1]! ≤ level := by simpa only [h.ptnSize] using h.ptnEnd
  have ht := refineWith_state G level s.lab s.ptn s.active numcells s.canong.scratch
    hp h.ptnSize hend h.starts hb
  have hvals := refineWith_boundary (.ofGraph G) level s.lab s.ptn s.active numcells s.canong.scratch
  dsimp only [visit]
  let t := refineWith (.ofGraph G) level s.lab s.ptn s.active numcells s.canong.scratch
  change NodeOk n level t.lab t.ptn t.active
  have hl : t.lab.size = n := by simpa only [Array.length_toList, List.length_range] using ht.1.length_eq
  refine ⟨hl, ?_, ht.2.1, ?_, ht.2.2.2.2.1.starts, ?_⟩
  · intro i hi
    apply perm_bound ht.1
    simpa only [hl] using hi
  · rw [ht.2.1, ht.2.2.1.closed _ hend]
    exact hend
  · intro q
    rcases hvals.values q with he | he
    · rw [he]
      exact h.vals q
    · exact Or.inl (by rw [he]; exact Nat.le_refl _)

end Hex.GraphIso.Nauty.Sparse
