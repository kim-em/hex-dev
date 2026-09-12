/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstUpper
public import HexGraphIso.Nauty.Sparse.FirstPath
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.SubtreeKey
import all HexGraphIso.Nauty.Sparse.SpecTree
import all HexGraphIso.Nauty.Sparse.CodeRead
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The root's depth-derived subtree bound is the declared sparse
maximum: sufficient-fuel stability identifies the two enumerations. -/
theorem Max.Frame.initial_key (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    (⟨1, p.2.length, [], initial (.ofGraph G.graph) p.1 p.2⟩ : Max.Frame n).key G.graph 100 =
      canonSpecKey G := by
  intro p
  have h := (NodeInv.initial G hn).spec
  have hd : 1 ≤ p.2.length := h.depth
  have he := specLeaves_add G.graph 100 n 2 1 p.1 (initPtn n (n + 2) p.2)
    (initActive n p.2) p.2.length h.label h.node h.count h.depth (by omega)
  have hr : rootLeaves G = specLeaves G.graph 100 n 1 p.1 (initPtn n (n + 2) p.2)
      (initActive n p.2) p.2.length := by
    rw [rootLeaves, ite_eq_right (by omega : n ≠ 0)]
    exact he
  rw [← root_maximum, hr]
  simp only [Max.Frame.key, Nat.add_sub_cancel, subtreeKey, prefixKey, List.nil_append]
  rfl

/-- Every key read from the executed production search is at most the
declarative sparse maximum. No search-correctness premise is required;
the order-zero run has no installed code chain. -/
theorem runState_upper (G : GraphIso.Sparse.Colored n k) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    Bounded (canonSpecKey G) none
      (State.best G.graph (runState (.ofGraph G.graph) p.1 p.2).2) := by
  intro p
  by_cases hz : n = 0
  · unfold runState
    rw [beq_iff_eq.mpr hz]
    change Bounded (canonSpecKey G) none none
    exact Bounded.refl _ _
  · have hn : 0 < n := by omega
    have h := Max.FirstEntry.initial G hn
    obtain ⟨last, leaf, path, _, _⟩ := initial_path G hn
    have hb := h.upper path
      (Max.Scope.root G 100 p.2.length (initial (.ofGraph G.graph) p.1 p.2)
        (initial (.ofGraph G.graph) p.1 p.2) []) (by change n + 1 ≤ 1 + (n + 2); omega)
    rw [Max.Frame.initial_key G hn] at hb
    unfold runState
    rw [beq_eq_false_iff_ne.mpr hz]
    exact hb

/-- Finishing the pending native row cache leaves the proved key bound
unchanged, so the actual public search pipeline retains it. -/
theorem run_upper (G : GraphIso.Sparse.Colored n k) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    Bounded (canonSpecKey G) none
      (State.best G.graph (run (.ofGraph G.graph) p.1 p.2)) := by
  exact runState_upper G

end Hex.GraphIso.Nauty.Sparse
