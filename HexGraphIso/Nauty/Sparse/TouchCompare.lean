/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RowTransport
public import HexGraphIso.Nauty.Sparse.SingletonMarks

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A sorted first-touch list is determined by the observed cell multiset,
independently of the generation number and retained mark storage. -/
theorem Touched.eq_of_order (hs : Touched n stamp before marks touched seen)
    (ht : Touched n next old newmarks other visits)
    (ho : touched.toList.Pairwise (· ≤ ·)) (ho' : other.toList.Pairwise (· ≤ ·))
    (hp : seen.Perm visits) : touched = other := by
  apply Array.toList_inj.mp
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ => Nat.le_antisymm) ho ho'
  apply (List.perm_ext_iff_of_nodup hs.nodup ht.nodup).mpr
  intro v
  rw [hs.members, ht.members, hp.mem_iff]

/-- Native singleton marking records exactly the same sorted cell starts
under isomorphism, using the executed neighbour scan's `Touched` contract. -/
theorem Touched.neighbors_eq (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v) (vertex : Fin n)
    (hi : Index.Valid n lab ptn level starts ends)
    (hj : Index.Valid n out ptn level other final)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hc : cellsPerm ptn level out (lab.map (renamingOf p).toFun))
    (hm : Touched n stamp before marks touched
      (((Graph.ofGraph G).row vertex.val).map (fun v => starts[v]!)))
    (hn : Touched n next old newmarks visits
      (((Graph.ofGraph H).row (p.get vertex).val).map (fun v => other[v]!)))
    (ho : touched.toList.Pairwise (· ≤ ·)) (ho' : visits.toList.Pairwise (· ≤ ·)) :
    touched = visits :=
  hm.eq_of_order hn ho ho' (Graph.cell_row_map G H p hiso vertex hi hj hp hs hend hc).symm

end Hex.GraphIso.Nauty.Sparse
