/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstCompare
public import HexGraphIso.Nauty.Sparse.TraceResult
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Sparse.Run
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every nonempty initialized native search returns settled comparisons.
Its first reference and incumbent lower bound come from the actual first
descent, with every structural and allocation premise derived at the root. -/
theorem runState_codes (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    ∃ fs bs, ReturnCodes G.graph [] bs fs (runState (.ofGraph G.graph) p.1 p.2).2 := by
  obtain ⟨last, leaf, fs, path, hlen, hc⟩ := initial_comparison G hn
  obtain ⟨bs, hr⟩ := firstPath_returned hn path (by omega) (NodeInv.initial G hn)
    (FirstShape.initial G.graph _ _)
    (by change n < (Array.replicate (n + 2) (-1 : Int)).size; simp)
    (by change n + 1 < (Array.replicate (n + 2) 0).size; simp)
    rfl (by exact Array.size_replicate) (TraceOk.initial G _ _) (by omega) hlen hc
  refine ⟨fs, bs, ?_⟩
  rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
  simpa only [Nat.sub_self, List.take_zero] using hr

/-- Updating row storage does not change the two settled code machines
or their parsed labels and native key bound. -/
theorem ReturnCodes.store {G : Hex.SparseGraph n} {cs bs fs : List Nat} {st : State n}
    (h : ReturnCodes G cs bs fs st) (storage : Storage n) (same : Nat) :
    ReturnCodes G cs bs fs { st with canong := storage, samerows := same } := by
  obtain ⟨codes, hp, hm, hf⟩ := h.machine
  exact ⟨⟨codes, hp, hm.congr rfl rfl rfl rfl, hf⟩, h.nonempty, h.lower⟩

/-- Final native row installation retains the proved comparison result. -/
theorem runColored_codes (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    ∃ fs bs, ReturnCodes G.graph [] bs fs (runColored G) := by
  obtain ⟨fs, bs, hr⟩ := runState_codes G hn
  exact ⟨fs, bs, hr.store _ n⟩

/-- The completed nonempty sparse run has a readable incumbent whose
label is parsed from the actual canonical-label array. -/
theorem runColored_incumbent (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    ∃ key, State.best G.graph (runColored G) = some key := by
  obtain ⟨fs, bs, hr⟩ := runColored_codes G hn
  obtain ⟨f, c, _, hc, _⟩ := hr.lower
  rw [hr.read]
  simp only [State.key, hr.nonempty, ite_false, hc, Option.map_some]
  exact ⟨_, rfl⟩

end Hex.GraphIso.Nauty.Sparse
