/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetBest
public import HexGraphIso.Nauty.Sparse.IndexSet

public section

namespace Hex.GraphIso.Nauty.Sparse.Target

/-- The target selector's native row count is the number of neighbours in
the specified cell. This connects its index representation to equitability. -/
theorem count_cell (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level : Nat) (s : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hc : IsCell ptn level a len) (hb : a + len ≤ n) (hn : 1 < len) (hf : first < n) :
    (row (.ofGraph G) lab s first).count a =
      (worksetOf n lab a (a + len - 1)).cardInter ((Graph.context G).g[lab[first]!]!) := by
  let u : Fin n := ⟨lab[first]!, perm_bound hp hf⟩
  have hr : row (.ofGraph G) lab s first =
      ((Graph.ofGraph G).row u.val).map (fun v => s.cellstart[v]!) := by
    simp only [row, Graph.row, List.map_map, Function.comp_def, u]
  have hm : ∀ v, ((Graph.context G).g[u.val]!).mem v = true ↔ v ∈ (Graph.ofGraph G).row u.val := by
    intro v
    change ((Array.ofFn fun w : Fin n => VSet.ofList ((Graph.ofGraph G).row w.val))[u.val]!).mem v = true ↔ _
    rw [getElem!_pos _ u.val (by simp), Array.getElem_ofFn, VSet.mem_ofList]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
    exact ⟨And.right, fun hv => ⟨Graph.row_bound G u v hv, hv⟩⟩
  rw [hr, VSet.cardInter_comm, cardInter_list _ _ ((Graph.ofGraph G).row u.val) (Graph.row_nodup G u) hm]
  rw [List.count_eq_countP, List.countP_map, ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro v hv
  dsimp only [Function.comp_def]
  rw [hi.mem_cell hp hs hend hc hb hn (Graph.row_bound G u v hv)]

/-- On each enumerated nontrivial cell the cached endpoint and the shared
set-valued count describe the same partial join. -/
theorem count_workset (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level : Nat) (s : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (ha : a ∈ nontrivial (cells ptn level n)) (hf : first < n) :
    (row (.ofGraph G) lab s first).count a =
      (worksetOf n lab a s.cellend[a]!).cardInter ((Graph.context G).g[lab[first]!]!) := by
  obtain ⟨b, hmem, hlt⟩ := mem_iff.mp ha
  have hend' : ptn[ptn.size - 1]! ≤ level := by simpa only [hs] using hend
  have hc := cells_isCell (Nat.le_of_eq hs.symm) hend' (a, b) hmem
  have hb := cells_end_lt_of_end (Nat.le_of_eq hs.symm) hend' hend (a, b) hmem
  have he := hi.ends_eq a (b + 1 - a) hc (by omega) (by omega)
  have hh := count_cell G lab ptn level s hp hs hend hi hc (by omega) (by omega) hf
  simpa only [he, show a + (b + 1 - a) - 1 = b by omega] using hh

end Hex.GraphIso.Nauty.Sparse.Target
