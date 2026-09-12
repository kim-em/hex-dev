/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountConstant

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A left-to-right cell pass leaves its unprocessed original partition
suffix unchanged and begins that suffix at an original cell start. -/
structure RefinePrefix (level first : Nat) (before ptn : Array Nat) : Prop where
  start : first = 0 ∨ before[first - 1]! ≤ level
  tail : ∀ q, first ≤ q → ptn[q]! = before[q]!

variable {n : Nat} {s : RefineSt n}

namespace RefinePrefix

theorem initial (ptn : Array Nat) (level : Nat) : RefinePrefix level 0 ptn ptn :=
  ⟨Or.inl rfl, fun _ _ => rfl⟩

theorem cell (h : RefinePrefix level first before ptn)
    (hc : IsCell ptn level first len) : IsCell before level first len := by
  refine ⟨hc.1, h.start, ?_, ?_⟩
  · intro q hq hq'
    rw [← h.tail q hq]
    exact hc.2.2.1 q hq hq'
  · rw [← h.tail (first + len - 1) (by have := hc.1; omega)]
    exact hc.2.2.2

theorem advance (h : RefinePrefix level first before ptn)
    (hc : IsCell ptn level first len) : RefinePrefix level (first + len) before ptn := by
  have hpos := hc.1
  refine ⟨Or.inr (h.cell hc).2.2.2, fun q hq => h.tail q (by omega)⟩

theorem counts (h : RefinePrefix level first before s.ptn)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (distance : Bool) :
    RefinePrefix level (s.cellend[first]! + 1) before (splitCounts level first distance s).ptn := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  have hp := splitCounts_partition level first distance s hl hs hf hb hk
  refine ⟨Or.inr ?_, ?_⟩
  · simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel' (show first ≤ s.cellend[first]! + 1 by omega)]
      using (h.cell hc).2.2.2
  · intro q hq
    rw [hp.tail q (by omega), h.tail q (by omega)]

end RefinePrefix

/-- Every complete cell in the processed prefix has a constant semantic key. -/
@[expose] def ConstantPrefix (n level upto : Nat) (key : Nat → Nat) (lab ptn : Array Nat) : Prop :=
  ∀ a len, IsCell ptn level a len → a + len ≤ n → a + len ≤ upto →
    ∀ q r, a ≤ q → q < a + len → a ≤ r → r < a + len → key lab[q]! = key lab[r]!

namespace ConstantPrefix

theorem initial (lab ptn : Array Nat) (n level : Nat) (key : Nat → Nat) :
    ConstantPrefix n level 0 key lab ptn := by
  intro a len hc hb hf
  have := hc.1
  omega

theorem singleton (h : ConstantPrefix n level first key lab ptn)
    (hc : IsCell ptn level first 1) : ConstantPrefix n level (first + 1) key lab ptn := by
  intro a len ha hb hf
  rcases isCell_disjoint_or_eq hc ha with hd | hd | ⟨rfl, rfl⟩
  · exact h a len ha hb hd
  · have := ha.1; omega
  · intro q r hq hq' hr hr'
    have he : q = r := by omega
    rw [he]

theorem counts (h : ConstantPrefix n level first key s.lab s.ptn)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (hv : ∀ v ∈ segN s.lab first (s.cellend[first]! + 1 - first), s.hits[v]! = key v)
    (distance : Bool) :
    ConstantPrefix n level (s.cellend[first]! + 1) key
      (splitCounts level first distance s).lab (splitCounts level first distance s).ptn := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  have hp := splitCounts_partition level first distance s hl hs hf hb hk
  intro a len ha hab hau
  rcases hp.nesting hc ha with hd | hd | hd
  · have hold := hp.cell_outside ha (Or.inl hd)
    intro q r hq hq' hr hr'
    rw [splitCounts_outside level first distance s hf (by omega) q (Or.inl (by omega)),
      splitCounts_outside level first distance s hf (by omega) r (Or.inl (by omega))]
    exact h a len hold hab hd q r hq hq' hr hr'
  · have := ha.1; omega
  · exact splitCounts_constant level first distance s key hl hs hc hb hk hv a len ha hd.1 hd.2

theorem done (h : ConstantPrefix n level n key lab ptn) :
    ∀ a len, IsCell ptn level a len → a + len ≤ n →
      ∀ q r, a ≤ q → q < a + len → a ≤ r → r < a + len → key lab[q]! = key lab[r]! :=
  fun a len hc hb => h a len hc hb hb

end ConstantPrefix
end Hex.GraphIso.Nauty.Sparse
