/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountPass
public import HexGraphIso.Nauty.Sparse.IndexTransport

public section

namespace Hex.GraphIso.Nauty.Sparse.CountTrace

/-- Count-split traces transport all observations when their semantic
counts commute with renaming. Only processed cells constrain scratch hits. -/
theorem Pass.equiv {s a : RefineSt n} (σ : Renaming n)
    (h : Pass level distance key xs s a) :
    ∀ {t b : RefineSt n} {other : Nat → Nat}, Pass level distance other xs t b →
    s.lab.toList.Perm (List.range n) → t.lab.toList.Perm (List.range n) →
    s.ptn.size = n → t.ptn = s.ptn →
    Index.Valid n s.lab s.ptn level s.cellstart s.cellend →
    Index.Valid n t.lab t.ptn level t.cellstart t.cellend →
    cellsPerm s.ptn level t.lab (s.lab.map σ.toFun) →
    (∀ v, v < n → other (σ v) = key v) →
    control s = control t → s.numcells = t.numcells →
    a.ptn = b.ptn ∧ cellsPerm a.ptn level b.lab (a.lab.map σ.toFun) ∧
      control a = control b ∧ a.numcells = b.numcells := by
  induction h with
  | nil =>
    intro t b other ht hp hq hs he hi hj hperm hkey hcontrol hnum
    cases ht
    exact ⟨he.symm, hperm, hcontrol, hnum⟩
  | @cons first rest s a hc hf hb hk hv hrest ih =>
    intro t b other ht hp hq hs he hi hj hperm hkey hcontrol hnum
    cases ht with
    | cons hc' hf' hb' hk' hv' hrest' =>
      have hj' := hj
      rw [he] at hj'
      have hends := hi.ends_congr hj' hc (by omega)
      have hl : s.lab.size = n := by simpa using hp.length_eq
      have hobs := splitCounts_equiv σ level first s.cellend[first]! distance s t hp hq hs he
        rfl hends.symm hf hb hk (fun q hq hu => hk' q hq (by omega)) (by
          intro v hm
          have hmem : σ v ∈ segN t.lab first (t.cellend[first]! + 1 - first) := by
            rw [← hends]
            apply (hperm _ _ hc).mem_iff.mpr
            rw [segN_map_of_le _ _ _ _ (by omega)]
            exact List.mem_map.mpr ⟨v, hm, rfl⟩
          rw [hv' _ hmem, hv _ hm]
          obtain ⟨i, hi, rfl⟩ := mem_segN_iff.mp hm
          exact hkey _ (perm_bound hp (by omega))) hc hperm hcontrol hnum
      have hs' := split_valid level first distance s hp hs hi hc hf hb hk
      have ht' := split_valid level first distance t hq (he ▸ hs) hj hc' hf' hb' hk'
      exact ih hrest' hs'.1 ht'.1 hs'.2.1 hobs.1.symm hs'.2.2 ht'.2.2 hobs.2.1
        hkey hobs.2.2.1 hobs.2.2.2

end Hex.GraphIso.Nauty.Sparse.CountTrace
