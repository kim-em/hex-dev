/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SingletonTrace

public section

namespace Hex.GraphIso.Nauty.Sparse

set_option maxHeartbeats 1000000

/-- The full executed singleton pass commutes with graph renaming and
permutations within input cells. Hashes, ordered queues, active sets,
partition entries and cell counts agree literally. The two valid caches,
mark generations and native row orders may differ. -/
theorem splitSingleton_equiv (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (level split : Nat) (s t : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hq : t.lab.toList.Perm (List.range n))
    (hs : s.ptn.size = n) (he : t.ptn = s.ptn) (hend : s.ptn[n - 1]! ≤ level)
    (hsp : split < n) (hc : IsCell s.ptn level split 1)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hj : Index.Valid n t.lab t.ptn level t.cellstart t.cellend)
    (hperm : cellsPerm s.ptn level t.lab (s.lab.map (renamingOf p).toFun))
    (hm : Scratch.Marks n s.stamp s.marks) (hv : Scratch.Marks n s.stamp s.vmarks)
    (hn : Scratch.Marks n t.stamp t.marks) (hw : Scratch.Marks n t.stamp t.vmarks)
    (hcontrol : CountTrace.control s = CountTrace.control t) (hnum : s.numcells = t.numcells) :
    let a := splitSingleton (.ofGraph G) level split s
    let b := splitSingleton (.ofGraph H) level split t
    a.ptn = b.ptn ∧ cellsPerm a.ptn level b.lab (a.lab.map (renamingOf p).toFun) ∧
      CountTrace.control a = CountTrace.control b ∧ a.numcells = b.numcells := by
  have hl : s.lab.size = n := by simpa using hp.length_eq
  have hroot : s.lab[split]! < n := perm_bound hp hsp
  have hvertex : t.lab[split]! = (p.get ⟨s.lab[split]!, hroot⟩).val := by
    rw [cellsPerm_singleton hperm hc, getElem!_map_of_lt _ _ (by omega), renamingOf_lt p hroot]
  have hj' := hj
  rw [he] at hj'
  have hleft := splitSingleton_trace G level split s hp hs hend hsp hi hm hv
  have hright := splitSingleton_trace H level split t hq (he ▸ hs) (he ▸ hend) hsp hj hn hw
  have hmark := mark_neighbors_map G H p hiso ⟨s.lab[split]!, hroot⟩ s t s.ptn level
    hi hj' hp hq hs hend hperm hm hv hn hw
  dsimp only at hleft hright hmark ⊢
  rw [hvertex, ← hmark.1] at hright
  apply hleft.equiv (renamingOf p).toFun hright hp hq hs he hi hj hperm ?_ ?_ hnum
  · intro v hb
    simpa only [RefineSt.hash, renamingOf_lt p hb] using hmark.2 ⟨v, hb⟩
  · change (CountTrace.control s).hash _ = (CountTrace.control t).hash _
    rw [hcontrol]

end Hex.GraphIso.Nauty.Sparse
