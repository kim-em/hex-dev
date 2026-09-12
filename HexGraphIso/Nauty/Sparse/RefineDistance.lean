/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineInitial
public import HexGraphIso.Nauty.Sparse.DistanceCert
public import HexGraphIso.Nauty.Sparse.DistanceMap

public section

namespace Hex.GraphIso.Nauty.Sparse.Refinement

/-- The complete native distance branch transports from its actual sole
queued singleton, including BFS initialization and every distance split. -/
theorem distance_equiv (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (level : Nat) (s t : RefineSt n)
    (hs : RefineSt.Valid level s) (ht : RefineSt.Valid level t)
    (he : RefineSt.Equiv (renamingOf p) level s t)
    (hq : s.queue.size = 1) (hsingle : s.ptn[s.queue[0]!]! ≤ level) :
    let a := distance level (distanceStart (.ofGraph G) s)
    let b := distance level (distanceStart (.ofGraph H) t)
    RefineSt.Valid level a ∧ RefineSt.Valid level b ∧ RefineSt.Equiv (renamingOf p) level a b := by
  have hpos : 0 < s.queue.size := by omega
  have hcell := hs.queue_cell hpos
  have hc : IsCell s.ptn level s.queue[0]! 1 :=
    ⟨by omega, hcell.2.1.2.1, by intro q hq hu; omega, by simpa using hsingle⟩
  have hroot := perm_bound hs.lab hcell.1
  let root : Fin n := ⟨s.lab[s.queue[0]!]!, hroot⟩
  have hl : s.lab.size = n := by simpa using hs.lab.length_eq
  have hvertex : t.lab[t.queue[0]!]! = (p.get root).val := by
    rw [← he.queue, cellsPerm_singleton he.cells hc, getElem!_map_of_lt _ _ (by omega),
      renamingOf_lt p hroot]
  have ha : RefineSt.Valid level (distanceStart (.ofGraph G) s) := hs.distance_start G hq
  have hb : RefineSt.Valid level (distanceStart (.ofGraph H) t) :=
    ht.distance_start H (he.queue ▸ hq)
  have hv : ∀ v, v < n → (distanceStart (.ofGraph G) s).hits[v]! ≤ n :=
    fun v hv => (distvals_correct G root).bound ⟨v, hv⟩
  have hw : ∀ v, v < n → (distanceStart (.ofGraph H) t).hits[v]! ≤ n := by
    intro v hv
    change (distvals (.ofGraph H) t.lab[t.queue[0]!]!)[v]! ≤ n
    rw [hvertex]
    exact (distvals_correct H (p.get root)).bound ⟨v, hv⟩
  have hk : ∀ v, v < n → (distanceStart (.ofGraph H) t).hits[(renamingOf p) v]! =
      (distanceStart (.ofGraph G) s).hits[v]! := by
    intro v hv
    change (distvals (.ofGraph H) t.lab[t.queue[0]!]!)[(renamingOf p) v]! =
      (distvals (.ofGraph G) root.val)[v]!
    rw [hvertex, renamingOf_lt p hv]
    exact distvals_map G H p hiso root ⟨v, hv⟩
  have hstart : RefineSt.Equiv (renamingOf p) level
      (distanceStart (.ofGraph G) s) (distanceStart (.ofGraph H) t) := by
    refine ⟨he.ptn, he.cells, ?_, he.count⟩
    simp only [distanceStart, CountTrace.control, he.active, he.queue, he.code]
  exact ⟨(split_distances level _ ha hv).valid, (split_distances level _ hb hw).valid,
    split_distances_equiv (renamingOf p) level _ _ ha hb hv hw hk hstart⟩

end Hex.GraphIso.Nauty.Sparse.Refinement
