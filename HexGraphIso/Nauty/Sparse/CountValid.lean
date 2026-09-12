/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountIndex

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Count splitting preserves a valid partition index. The cache supplies the
executed endpoint and the original vertex indices; callers need only identify
the bounded cell and supply the local hit bound. -/
theorem splitCounts_index (level first len : Nat) (distance : Bool) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hc : IsCell s.ptn level first len) (hb : first + len ≤ n)
    (hk : ∀ q, first ≤ q → q < first + len → s.hits[s.lab[q]!]! < n + 2) :
    let t := splitCounts level first distance s
    Index.Valid n t.lab t.ptn level t.cellstart t.cellend := by
  have hpos := hc.1
  have hend := hi.ends_eq first len hc hb (by omega)
  have hf : first ≤ s.cellend[first]! := by omega
  have he : s.cellend[first]! < n := by omega
  have hlen : s.cellend[first]! + 1 - first = len := by omega
  have hkey : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2 :=
    fun q hq hu => hk q hq (by omega)
  have hcache := splitCounts_cache level first distance s hp hi.starts_size hi.ends_size hf he
    (by
      intro q hq hu
      rw [hi.starts_eq first len hc hb (by omega) q hq (by omega)]
      have hh : (len = 1) ↔ (first = s.cellend[first]!) := by omega
      simp only [hh]) hkey
  have hl : s.lab.size = n := by simpa using hp.length_eq
  exact hcache.valid (splitCounts_partition level first distance s hl hs hf he hkey)
    (by simpa only [hlen] using hc) hi

end Hex.GraphIso.Nauty.Sparse
