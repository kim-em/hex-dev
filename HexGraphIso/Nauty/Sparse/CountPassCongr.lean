/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountPass
public import HexGraphIso.Nauty.Sparse.CountLab
public import HexGraphIso.Nauty.Sparse.IndexTransport

public section

namespace Hex.GraphIso.Nauty.Sparse.CountTrace

/-- The complete touched-cell fold gives identical labels from identical
input arrays and semantic counts. Only processed cells constrain hits. -/
theorem Pass.lab_eq {s a : RefineSt n} (h : Pass level distance key xs s a) :
    ∀ {t b : RefineSt n}, Pass level distance key xs t b →
    s.lab.toList.Perm (List.range n) → s.ptn.size = n →
    t.lab = s.lab → t.ptn = s.ptn →
    Index.Valid n s.lab s.ptn level s.cellstart s.cellend →
    Index.Valid n t.lab t.ptn level t.cellstart t.cellend → a.lab = b.lab := by
  induction h with
  | nil =>
    intro t b ht hp hs hl he hi hj
    cases ht
    exact hl.symm
  | @cons first rest s a hc hf hb hk hv hrest ih =>
    intro t b ht hp hs hl he hi hj
    cases ht with
    | cons hc' hf' hb' hk' hv' hrest' =>
      have hj' := hj
      rw [he] at hj'
      have hends := hi.ends_congr hj' hc (by omega)
      have hsize : s.lab.size = n := by simpa using hp.length_eq
      have hkeys (v : Nat) (hm : v ∈ segN s.lab first (s.cellend[first]! + 1 - first)) :
          s.hits[v]! = t.hits[v]! := by
        have hm' : v ∈ segN t.lab first (t.cellend[first]! + 1 - first) := by
          rw [hl, ← hends]
          exact hm
        rw [hv v hm, hv' v hm']
      have hlabel := splitCounts_lab level first distance s t hl hends.symm hf (by omega) (by
        intro q hq hq'
        apply hkeys
        apply mem_segN_iff.mpr
        exact ⟨q - first, by omega, by simp only [show first + (q - first) = q by omega]⟩)
      have hptn := splitCounts_ptn level first s.cellend[first]! distance s t
        hsize (by rw [hl]; exact hsize) hs he rfl hends.symm hf hb hk
        (fun q hq hq' => hk' q hq (by omega)) (by
          rw [hl]
          apply List.Perm.of_eq
          exact List.map_congr_left hkeys)
      have hq : t.lab.toList.Perm (List.range n) := hl.symm ▸ hp
      have hs' := split_valid level first distance s hp hs hi hc hf hb hk
      have ht' := split_valid level first distance t hq (he ▸ hs) hj hc' hf' hb' hk'
      exact ih hrest' hs'.1 hs'.2.1 hlabel.symm hptn.symm hs'.2.2 ht'.2.2

end Hex.GraphIso.Nauty.Sparse.CountTrace
