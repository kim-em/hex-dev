/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexTwo
public import HexGraphIso.Nauty.Sparse.IndexFrame
public import HexGraphIso.Nauty.Sparse.CellCut

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

variable {n first cut last : Nat} {lab oldlab oldstarts starts oldends ends : Array Nat}

/-- The singleton splitter normalizes singleton sentinels after its reverse
scatter has assigned the second fragment's start. -/
theorem Two.of_scatter (h : Scatter n lab oldstarts starts cut last cut)
    (hp : lab.toList.Perm (List.range n))
    (_hf : first < cut) (hl : cut < last) (hb : last ≤ n)
    (hc : ∀ q, first ≤ q → q < cut → oldstarts[lab[q]!]! = first) :
    let middle := if cut = first + 1 then starts.setIfInBounds lab[first]! n else starts
    let out := if last = cut + 1 then middle.setIfInBounds lab[cut]! n else middle
    Two n first cut last last lab out := by
  have ht := Two.initial (v3 := last) h.size (by omega : cut ≤ n)
    (fun _ hi => perm_bound hp hi) (by
      intro q hq hu
      rw [h.get q (by omega), ite_eq_right (by omega)]
      exact hc q hq hu)
  dsimp only
  by_cases he : last = cut + 1
  · rw [ite_eq_left he]
    have hh := ht.step (fun _ hi => perm_bound hp hi)
      (fun _ _ hi hj he => perm_injective hp hi hj he) (Nat.le_refl _) (by omega)
    simpa only [he, ite_true] using hh
  · rw [ite_eq_right he]
    refine ⟨ht.size, ht.minimum, ?_⟩
    intro q hq hu
    rw [ite_eq_right he]
    split
    · rw [← Array.set!_eq_setIfInBounds,
        Array.getElem!_set!_ne _ _ _ _ (fun heq => by
          have hh := perm_injective hp (show first < n by omega) (show q < n by omega) heq
          omega)]
      rw [h.get q (by omega), ite_eq_left ⟨hq, hu⟩]
    · rw [h.get q (by omega), ite_eq_left ⟨hq, hu⟩]

/-- Sentinel normalization retains all cache entries outside the split. -/
theorem Frame.sentinels (h : Frame n first (last - 1) oldlab lab oldstarts starts oldends ends)
    (hp : lab.toList.Perm (List.range n))
    (hf : first < cut) (hl : cut < last) (hb : last ≤ n) :
    let middle := if cut = first + 1 then starts.setIfInBounds lab[first]! n else starts
    let out := if last = cut + 1 then middle.setIfInBounds lab[cut]! n else middle
    Frame n first (last - 1) oldlab lab oldstarts out oldends ends := by
  have hmid : Frame n first (last - 1) oldlab lab oldstarts
      (if cut = first + 1 then starts.setIfInBounds lab[first]! n else starts) oldends ends := by
    split
    · exact h.set_start (fun _ _ hi hj he => perm_injective hp hi hj he) ⟨by omega, by omega⟩ (by omega)
    · exact h
  dsimp only
  split
  · exact hmid.set_start (fun _ _ hi hj he => perm_injective hp hi hj he) ⟨by omega, by omega⟩ (by omega)
  · exact hmid

end Hex.GraphIso.Nauty.Sparse.Index
