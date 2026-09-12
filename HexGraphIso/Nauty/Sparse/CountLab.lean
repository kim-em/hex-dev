/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MinimaCongr
public import HexGraphIso.Nauty.Sparse.CountFinish

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Equal input labels and observed cell counts give literally equal
output labels in the executed count splitter. All other scratch entries
and the unrelated partition, queue and hash fields may differ. -/
theorem splitCounts_lab (level first : Nat) (distance : Bool) (s t : RefineSt n)
    (hl : t.lab = s.lab) (he : t.cellend[first]! = s.cellend[first]!)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! →
      s.hits[s.lab[q]!]! = t.hits[s.lab[q]!]!) :
    (splitCounts level first distance s).lab = (splitCounts level first distance t).lab := by
  have h : Sort.Agree s.hits t.hits first (s.cellend[first]! + 1) s.lab :=
    ⟨by omega, fun q hq hq' => hk q hq (by omega)⟩
  have hp := CountSort.firstRun_congr h (by omega)
  have hm := CountSort.minima_congr h hp.2 (n + 2)
  rw [splitCounts_parts, splitCounts_parts]
  dsimp only [RefineSt.hash]
  rw [hl, he, ← hp.1]
  split
  · rfl
  · rw [CountSort.finish_lab, CountSort.finish_lab, ← hm.1]
    dsimp only
    split
    · rfl
    · split
      · rfl
      · apply Sort.indirect_congr
        have bounds := hm.2.2
        exact hm.2.1.mono (by omega) (by omega)

end Hex.GraphIso.Nauty.Sparse
