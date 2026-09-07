/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Control
import all HexGraphIso.Nauty.Search.Refine

public section

namespace Hex.GraphIso.Nauty

namespace Generation

variable {n : Nat}

/-- The child selected at an ancestor is already a singleton at the level
immediately below that ancestor, not merely at the current search level. -/
theorem picked_singleton {ctx : Ctx n} {level target : Nat}
    {st : SearchSt n} {trail : FrameTrail} {entry : TrailEntry}
    (h : TrailOk ctx level st trail) (hlt : target < level)
    (he : trail target = some entry) :
    IsCell st.ptn (target + 1) entry.frame.tc 1 := by
  obtain ⟨len, hc, hoff, hsplit, _, _⟩ := h.picked target entry hlt he
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rcases hc.2.1 with hz | hs
    · exact Or.inl hz
    · right
      rw [h.frozen target entry hlt he _ hs]
      omega
  · intro i hi hj
    omega
  · simpa using Nat.le_of_eq hsplit

/-- An implicit pair frozen below an ancestor fixes that ancestor's
selected child as well. This is the extra fixed point needed when a
guiding child returns a short-prune request to its parent. -/
theorem picked_fix {ctx : Ctx n} {level target saved : Nat}
    {st : SearchSt n} {trail : FrameTrail} {entry : TrailEntry}
    (h : TrailOk ctx level st trail) (hlt : target < level)
    (he : trail target = some entry) (hdeep : target < saved)
    (hsize : st.ptn.size = n) (hend : st.ptn[st.ptn.size - 1]! ≤ saved)
    (htc : entry.frame.tc < n) (hv : st.lab[entry.frame.tc]! < n) :
    (fmptn st.lab st.ptn saved n).1.mem
      entry.frame.rsLab[entry.frame.tc + entry.offset]! = true := by
  obtain ⟨_, _, _, _, _, hat⟩ := h.picked target entry hlt he
  have hs := isCell_one_mono (picked_singleton h hlt he) (by omega : target + 1 ≤ saved)
  have hm := isCell_mem_cells hs (by omega : n ≤ st.ptn.size) hend htc
  have hm' : (entry.frame.tc, entry.frame.tc) ∈ cells st.ptn saved n := by
    simpa using hm
  rw [← hat]
  exact fmptn_singleton hm' hv

end Generation

end Hex.GraphIso.Nauty
