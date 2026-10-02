/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceFrame
public import HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.TraceFrame

variable {G : GraphIso.Sparse.Colored n k} {base level cells numcells : Nat}
    {root st : State n}

/-- The first-reference verdict's actual scatter stabilizes every frozen
partition containing the current and first labels. Its cheap guard does
not change which permutation is scattered. -/
theorem first_scatter (h : TraceFrame G base root st) (hp : Ready G base cells root)
    (hn : 0 < n) (hb : 1 ≤ base)
    (he : (classify (.ofGraph G.graph) level numcells st).1 = .autoFirst) :
    CellStab root.ptn base root.lab (classify (.ofGraph G.graph) level numcells st).2.workperm := by
  have hout := (classify_first (Prod.ext he rfl)).2.2.1
  apply (congrArg (fun s : State n => CellStab root.ptn base root.lab s.workperm) hout).mpr
  exact h.frame.scatter_stab hp hn hb h.first.1 h.first.2
    (scatter_map h.work h.first.1 (label_perm hp hn hb h.first.1 h.first.2))

/-- Canonical-reference admission scatters the saved canonical label
to the current label, both inside the frozen ancestor partition. -/
theorem canon_scatter (h : TraceFrame G base root st) (hp : Ready G base cells root)
    (hn : 0 < n) (hb : 1 ≤ base)
    (he : (classify (.ofGraph G.graph) level numcells st).1 = .autoCanon) :
    CellStab root.ptn base root.lab (classify (.ofGraph G.graph) level numcells st).2.workperm :=
  h.frame.scatter_stab hp hn hb h.canon.1 h.canon.2
    (classify_canon_map he h.work h.canon.1 (label_perm hp hn hb h.canon.1 h.canon.2))

/-- The classifier and leaf action preserve the entire frozen-ancestor
invariant. Every new trace entry is the literal scattered permutation;
the other verdicts retain the trace and only update their documented fields. -/
theorem classified (h : TraceFrame G base root st) (hp : Ready G base cells root)
    (hr : Ready G level numcells st) (hn : 0 < n) (hb : 1 ≤ base) (hlevel : base ≤ level) :
    let c := classify (.ofGraph G.graph) level numcells st
    TraceFrame G base root (leafExit c.1 level c.2).2 := by
  intro c
  have hclass := hr.classify
  have hleaf := hclass.ready.leaf c.1
  apply h.extend hp hn hb (hclass.frame.trans hleaf.frame) hlevel hlevel
  · intro gamma hg
    change gamma ∈ (leafExit c.1 level c.2).2.genTrace at hg
    rw [leafExit_trace, classify_trace] at hg
    cases he : c.1 with
    | autoFirst =>
      simp only [he, Array.mem_push] at hg
      exact hg.elim (h.trace gamma) (fun heq => heq ▸ h.first_scatter hp hn hb he)
    | autoCanon =>
      simp only [he, Array.mem_push] at hg
      exact hg.elim (h.trace gamma) (fun heq => heq ▸ h.canon_scatter hp hn hb he)
    | internal => exact h.trace gamma (by simpa only [he] using hg)
    | bad => exact h.trace gamma (by simpa only [he] using hg)
    | better _ => exact h.trace gamma (by simpa only [he] using hg)
  · exact (leafExit_workSize c.1 level c.2).trans
      ((classify_workSize (.ofGraph G.graph) level numcells st).trans h.work)

end Hex.GraphIso.Nauty.Sparse.TraceFrame
