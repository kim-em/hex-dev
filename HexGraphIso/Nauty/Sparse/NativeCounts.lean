/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountBound
public import HexGraphIso.Nauty.Sparse.CountCells
public import HexGraphIso.Nauty.Equitable.Basic

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A set-valued interpretation of native rows for the shared equitability
predicates. It is used only in proofs, never by the sparse search. -/
@[expose] def Graph.context (G : Hex.SparseGraph n) : Ctx n :=
  ⟨Array.ofFn fun v : Fin n => VSet.ofList ((Graph.ofGraph G).row v.val)⟩

theorem Graph.context_mem (G : Hex.SparseGraph n) (u v : Fin n) :
    ((Graph.context G).g[u.val]!).mem v.val = G.adj u v := by
  change ((Array.ofFn fun w : Fin n => VSet.ofList ((Graph.ofGraph G).row w.val))[u.val]!).mem v.val = _
  rw [getElem!_pos _ u.val (by simp), Array.getElem_ofFn, VSet.mem_ofList]
  apply Bool.eq_iff_iff.mpr
  simpa only [v.isLt, decide_true, Bool.true_and, List.contains_iff_mem, Graph.row, Graph.ofGraph]
    using Graph.neighbor_mem G u v

/-- Counting a set intersection can use any duplicate-free enumeration of
the first set, independently of its packed representation. -/
theorem cardInter_list (s t : VSet n) (xs : List Nat) (hn : xs.Nodup)
    (hm : ∀ v, s.mem v = true ↔ v ∈ xs) :
    s.cardInter t = (xs.filter t.mem).length := by
  have hp : ((List.range n).filter s.mem).Perm xs := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hn).mpr
    intro v
    simp only [List.mem_filter, List.mem_range]
    exact ⟨fun h => (hm v).mp h.2, fun h =>
      ⟨VSet.mem_lt ((hm v).mpr h), (hm v).mpr h⟩⟩
  rw [VSet.cardInter_eq, VSet.card_eq_countBelow, VSet.countBelow, List.countP_eq_length_filter]
  have he : (List.range n).filter (s.inter t).mem = ((List.range n).filter s.mem).filter t.mem := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro v hv
    simp only [VSet.mem_inter, Bool.and_comm]
  rw [he]
  exact (hp.filter _).length_eq

/-- Native neighbour accumulation agrees with counting the adjacent vertices
in the captured splitter list. Symmetry supplies the row orientation. -/
theorem Graph.count_context (G : Hex.SparseGraph n) (vertices : List Nat)
    (hb : ∀ u ∈ vertices, u < n) (v : Fin n) :
    (vertices.flatMap fun u => (Graph.ofGraph G).row u).count v.val =
      (vertices.filter fun u => ((Graph.context G).g[v.val]!).mem u).length := by
  induction vertices with
  | nil => simp
  | cons u us ih =>
    have hu : u < n := hb u (by simp)
    have ht := ih (fun u hu => hb u (by simp [hu]))
    have hm := Graph.context_mem G v ⟨u, hu⟩
    rw [G.adj_symm] at hm
    simp only [List.flatMap_cons, List.count_append, Graph.row_count G ⟨u, hu⟩ v,
      ht, List.filter_cons, hm]
    split <;> simp_all <;> omega

/-- A bounded interval of a labelling permutation has no repeated vertices. -/
theorem segN_nodup {lab : Array Nat} (hp : lab.toList.Perm (List.range n))
    (hb : first + len ≤ n) : (segN lab first len).Nodup := by
  have hs : lab.size = n := by simpa using hp.length_eq
  rw [segN_extract _ _ _ (by omega), Array.toList_extract]
  exact ((hp.nodup_iff.mpr List.nodup_range).drop).take

/-- Native accumulated counts into a captured label interval are exactly
the shared equitability predicate's set-intersection cardinalities. -/
theorem Graph.count_workset (G : Hex.SparseGraph n) (lab : Array Nat)
    (hp : lab.toList.Perm (List.range n)) (hf : first ≤ last) (hb : last < n) (v : Fin n) :
    ((List.range' first (last + 1 - first)).flatMap fun q =>
      (Graph.ofGraph G).row lab[q]!).count v.val =
      (worksetOf n lab first last).cardInter ((Graph.context G).g[v.val]!) := by
  have hverts : ∀ u ∈ segN lab first (last + 1 - first), u < n := by
    intro u hu
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
    have hq := List.mem_range.mp hq
    exact perm_bound hp (by omega)
  rw [cardInter_list _ _ (segN lab first (last + 1 - first)) (segN_nodup hp (by omega)) (by
    intro u
    rw [mem_worksetOf_iff]
    exact ⟨And.right, fun hu => ⟨hverts u hu, hu⟩⟩)]
  have he : (List.range' first (last + 1 - first)).flatMap (fun q => (Graph.ofGraph G).row lab[q]!) =
      (segN lab first (last + 1 - first)).flatMap (Graph.ofGraph G).row := by
    rw [segN, List.flatMap_map, List.range'_eq_map_range]
    simp only [List.flatMap_map]
  rw [he]
  exact Graph.count_context G _ hverts v

/-- Constant native counts imply the shared set-valued cell predicate. -/
theorem Graph.constOn_workset (G : Hex.SparseGraph n) (lab out : Array Nat)
    (hp : lab.toList.Perm (List.range n)) (hout : out.toList.Perm (List.range n))
    (hf : first ≤ last) (hb : last < n) (ha : a + len ≤ n)
    (hc : ∀ q r, a ≤ q → q < a + len → a ≤ r → r < a + len →
      ((List.range' first (last + 1 - first)).flatMap fun j =>
        (Graph.ofGraph G).row lab[j]!).count out[q]! =
      ((List.range' first (last + 1 - first)).flatMap fun j =>
        (Graph.ofGraph G).row lab[j]!).count out[r]!) :
    ConstOn (Graph.context G) (worksetOf n lab first last) (segN out a len) := by
  intro x hx y hy
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
  have hq := List.mem_range.mp hq
  have hr := List.mem_range.mp hr
  rw [← Graph.count_workset G lab hp hf hb ⟨out[a + q]!, perm_bound hout (by omega)⟩,
    ← Graph.count_workset G lab hp hf hb ⟨out[a + r]!, perm_bound hout (by omega)⟩]
  exact hc _ _ (by omega) (by omega) (by omega) (by omega)

end Hex.GraphIso.Nauty.Sparse
