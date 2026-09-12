/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryPass
public import HexGraphIso.Nauty.Sparse.BinaryCongr
public import HexGraphIso.Nauty.Sparse.IndexTransport

public section

namespace Hex.GraphIso.Nauty.Sparse.Binary

/-- The complete executed singleton-cell fold returns literally equal
labels from equal input labels and partitions. Valid caches, retained
marks and generation numbers may differ between the two traversals. -/
theorem Pass.lab_eq {s a : RefineSt n} (h : Pass level stamp xs s a) :
    ∀ {t b : RefineSt n} {otherStamp : Nat}, Pass level otherStamp xs t b →
    s.lab.toList.Perm (List.range n) → s.ptn.size = n →
    t.lab = s.lab → t.ptn = s.ptn →
    Index.Valid n s.lab s.ptn level s.cellstart s.cellend →
    Index.Valid n t.lab t.ptn level t.cellstart t.cellend →
    (∀ v, v < n → (s.vmarks[v]! == stamp) = (t.vmarks[v]! == otherStamp)) →
    a.lab = b.lab := by
  induction h with
  | nil =>
    intro t b otherStamp ht hp hs hl he hi hj hmarks
    cases ht
    exact hl.symm
  | cons hc hf hb hstep hrest ih =>
    intro t b otherStamp ht hp hs hl he hi hj hmarks
    cases ht with
    | cons hc' hf' hb' hstep' hrest' =>
      have hj' := hj
      rw [he] at hj'
      have hends := hi.ends_congr hj' hc (by omega)
      have hcell' := hstep'
      rw [← hends] at hcell'
      have hlabel := hstep.lab_eq hcell' hl (by omega) (by
        intro v hv
        apply (hmarks v ?_).symm
        rw [seen_eq] at hv
        obtain ⟨i, hi, rfl⟩ := mem_segN_iff.mp hv
        exact perm_bound hp (by omega))
      have hptn := hstep.ptn_eq hcell' hl he (by
        intro v hv
        apply (hmarks v ?_).symm
        rw [seen_eq] at hv
        obtain ⟨i, hi, rfl⟩ := mem_segN_iff.mp hv
        exact perm_bound hp (by omega))
      have hv := hstep.valid hp hs hi hc (by omega)
      have hq : t.lab.toList.Perm (List.range n) := hl.symm ▸ hp
      have hv' := hstep'.valid hq (by rw [he]; exact hs) hj hc' (by omega)
      exact ih hrest' hv.1 hv.2.1 hlabel.symm hptn.symm hv.2.2 hv'.2.2
        (fun v hv => by simpa only [hstep.frame.vmarks, hstep'.frame.vmarks] using hmarks v hv)

end Hex.GraphIso.Nauty.Sparse.Binary
