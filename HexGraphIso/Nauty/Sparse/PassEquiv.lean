/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryPass
public import HexGraphIso.Nauty.Sparse.IndexTransport

public section

namespace Hex.GraphIso.Nauty.Sparse.Binary

/-- Paired touched-cell traces preserve ordered partition, cell contents,
hash, active set, ordered queue and exact cell count. Their caches and
mark generations may differ. -/
theorem Pass.equiv {s a : RefineSt n} (f : Nat → Nat) (h : Pass level stamp xs s a) :
    ∀ {t b : RefineSt n} {otherStamp : Nat}, Pass level otherStamp xs t b →
    s.lab.toList.Perm (List.range n) → t.lab.toList.Perm (List.range n) →
    s.ptn.size = n → t.ptn = s.ptn →
    Index.Valid n s.lab s.ptn level s.cellstart s.cellend →
    Index.Valid n t.lab t.ptn level t.cellstart t.cellend →
    cellsPerm s.ptn level t.lab (s.lab.map f) →
    (∀ v, v < n → (s.vmarks[v]! == stamp) = (t.vmarks[f v]! == otherStamp)) →
    CountTrace.control s = CountTrace.control t → s.numcells = t.numcells →
    a.ptn = b.ptn ∧ cellsPerm a.ptn level b.lab (a.lab.map f) ∧
      CountTrace.control a = CountTrace.control b ∧ a.numcells = b.numcells := by
  induction h with
  | nil =>
    intro t b otherStamp ht hp hq hs he hi hj hperm hmarks hcontrol hnum
    cases ht
    exact ⟨he.symm, hperm, hcontrol, hnum⟩
  | cons hc hf hb hstep hrest ih =>
    intro t b otherStamp ht hp hq hs he hi hj hperm hmarks hcontrol hnum
    cases ht with
    | cons hc' hf' hb' hstep' hrest' =>
      have hj' := hj
      rw [he] at hj'
      have hends := hi.ends_congr hj' hc (by omega)
      have hcell' := hstep'
      rw [← hends] at hcell'
      have hobs := hstep.equiv f hcell' (by simpa using hp.length_eq)
        (by simpa using hq.length_eq) hs he (by omega) hc hperm (by
          intro v hv
          apply (hmarks v ?_).symm
          rw [seen_eq] at hv
          obtain ⟨i, hi, rfl⟩ := mem_segN_iff.mp hv
          exact perm_bound hp (by omega)) hcontrol hnum
      have hv := hstep.valid hp hs hi hc (by omega)
      have hv' := hstep'.valid hq (by rw [he]; exact hs) hj hc' (by omega)
      exact ih hrest' hv.1 hv'.1 hv.2.1 hobs.1.symm hv.2.2 hv'.2.2 hobs.2.1
        (fun v hv => by simpa only [hstep.frame.vmarks, hstep'.frame.vmarks] using hmarks v hv)
        hobs.2.2.1 hobs.2.2.2

end Hex.GraphIso.Nauty.Sparse.Binary
