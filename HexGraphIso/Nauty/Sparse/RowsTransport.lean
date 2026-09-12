/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RowTransport

public section

namespace Hex.GraphIso.Nauty.Sparse.Graph

/-- Concatenating native rows transports the neighbour multiset even when
both the splitter order and individual native row orders change. -/
theorem rows_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (vertices visits : List Nat) (hb : ∀ v ∈ vertices, v < n)
    (hp : visits.Perm (vertices.map (renamingOf p).toFun)) :
    (visits.flatMap (Graph.ofGraph H).row).Perm
      ((vertices.flatMap (Graph.ofGraph G).row).map (renamingOf p).toFun) := by
  apply (hp.flatMap_right (Graph.ofGraph H).row).trans
  clear hp visits
  induction vertices with
  | nil => simp
  | cons v vs ih =>
    have hv := hb v (by simp)
    simp only [List.map_cons, List.flatMap_cons, List.map_append]
    apply List.Perm.append
    · simpa only [renamingOf_lt p hv] using row_map G H p hiso ⟨v, hv⟩
    · exact ih (fun v hv => hb v (by simp [hv]))

/-- The native row sequence of a whole partition cell transports under
renaming and arbitrary permutations within the original cells. -/
theorem cell_rows_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    {lab out ptn : Array Nat}
    (hp : lab.toList.Perm (List.range n)) (hb : first + len ≤ n)
    (hc : IsCell ptn level first len)
    (hperm : cellsPerm ptn level out (lab.map (renamingOf p).toFun)) :
    ((List.range' first len).flatMap fun q => (Graph.ofGraph H).row out[q]!).Perm
      (((List.range' first len).flatMap fun q => (Graph.ofGraph G).row lab[q]!).map
        (renamingOf p).toFun) := by
  have hl : lab.size = n := by simpa using hp.length_eq
  have h := hperm first len hc
  rw [segN_map_of_le _ _ _ _ (by omega)] at h
  have hr := rows_map G H p hiso (segN lab first len) (segN out first len) (by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := mem_segN_iff.mp hv
    exact perm_bound hp (by omega)) h
  simpa only [segN, List.flatMap_map, List.range'_eq_map_range, List.map_map,
    Function.comp_def] using hr

end Hex.GraphIso.Nauty.Sparse.Graph
