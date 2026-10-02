/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.NontrivialTrace
public import HexGraphIso.Nauty.Sparse.CountPassEquiv
public import HexGraphIso.Nauty.Sparse.ScanTransport

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The complete executed nontrivial pass commutes with graph renaming and
permutations within input cells. All scalar and control observations agree
literally, with independently allocated caches and retained scratch. -/
theorem splitNontrivial_equiv (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (level split len : Nat) (s t : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hq : t.lab.toList.Perm (List.range n))
    (hs : s.ptn.size = n) (he : t.ptn = s.ptn) (hend : s.ptn[n - 1]! ≤ level)
    (hc : IsCell s.ptn level split len) (hb : split + len ≤ n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hj : Index.Valid n t.lab t.ptn level t.cellstart t.cellend)
    (hperm : cellsPerm s.ptn level t.lab (s.lab.map (renamingOf p).toFun))
    (hm : Scratch.Marks n s.stamp s.marks) (hh : s.hits.size = n)
    (hn : Scratch.Marks n t.stamp t.marks) (hk : t.hits.size = n)
    (hcontrol : CountTrace.control s = CountTrace.control t) (hnum : s.numcells = t.numcells) :
    let a := splitNontrivial (.ofGraph G) level split s
    let b := splitNontrivial (.ofGraph H) level split t
    a.ptn = b.ptn ∧ cellsPerm a.ptn level b.lab (a.lab.map (renamingOf p).toFun) ∧
      CountTrace.control a = CountTrace.control b ∧ a.numcells = b.numcells := by
  have hlen := hc.1
  have hj' := hj
  rw [he] at hj'
  have hse : s.cellend[split]! + 1 = split + len := by
    have := hi.ends_eq split len hc hb (by omega)
    omega
  have hte : t.cellend[split]! + 1 = split + len := by
    have := hj'.ends_eq split len hc hb (by omega)
    omega
  have hleft := splitNontrivial_trace G level split len s hp hs hend hi hc hb hm hh
  have hright := splitNontrivial_trace H level split len t hq (he ▸ hs) (he ▸ hend)
    hj (he ▸ hc) hb hn hk
  have hscan := count_neighbors_map G H p hiso s t s.ptn level split len hi hj'
    hp hq hs hend hc hb hperm hm hh hn hk
  dsimp only at hleft hright hscan ⊢
  rw [hse] at hleft
  rw [hte, ← hscan.1] at hright
  apply hleft.equiv (renamingOf p) hright hp hq hs he hi hj hperm ?_ ?_ hnum
  · intro v _hv
    have hrows := Graph.cell_rows_map G H p hiso hp hb hc hperm
    simpa only [Nat.add_sub_cancel_left, count_map] using hrows.count_eq ((renamingOf p) v)
  · change (CountTrace.control s).hash _ = (CountTrace.control t).hash _
    rw [hcontrol]

end Hex.GraphIso.Nauty.Sparse
