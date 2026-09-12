/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountRuns
public import HexGraphIso.Nauty.Sparse.CountCells

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Each fragment produced by the executed splitter has a constant semantic
key whenever the incoming hit array represents that key on the split cell.
Only those vertices need a count interpretation; other scratch is unrestricted. -/
theorem splitCounts_constant (level first : Nat) (distance : Bool) (s : RefineSt n)
    (key : Nat → Nat) (hl : s.lab.size = n) (hs : s.ptn.size = n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (hv : ∀ v ∈ segN s.lab first (s.cellend[first]! + 1 - first), s.hits[v]! = key v)
    (a len : Nat)
    (ho : IsCell (splitCounts level first distance s).ptn level a len)
    (ha : first ≤ a) (he : a + len ≤ s.cellend[first]! + 1) :
    ∀ q r, a ≤ q → q < a + len → a ≤ r → r < a + len →
      key (splitCounts level first distance s).lab[q]! =
        key (splitCounts level first distance s).lab[r]! := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  have hpart := splitCounts_partition level first distance s hl hs hf hb hk
  have hconst := ((hpart.cell_iff hc ha ho.1 he).mp ho).2.1
  have hperm := splitCounts_cells level first distance s hf (by omega) hc first _ hc
  have hkey (q : Nat) (hq : first ≤ q) (he : q ≤ s.cellend[first]!) :
      s.hits[(splitCounts level first distance s).lab[q]!]! =
        key (splitCounts level first distance s).lab[q]! := by
    apply hv
    apply hperm.mem_iff.mp
    apply List.mem_map.mpr
    exact ⟨q - first, List.mem_range.mpr (by omega), by rw [Nat.add_sub_cancel' hq]⟩
  intro q r hq hq' hr hr'
  rw [← hkey q (by omega) (by omega), ← hkey r (by omega) (by omega),
    hconst q hq hq', hconst r hr hr']

end Hex.GraphIso.Nauty.Sparse
