/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.SmallCell.Transitive
import all HexGraphIso.Nauty.SmallCell.Transitive

public section

namespace Hex.GraphIso.Nauty

private theorem cell_parent {n base level : Nat} {ptn out : Array Nat}
    (hs : ptn.size = n) (ht : out.size = n) (hend : ptn[n - 1]! ≤ base)
    (hg : ∀ q : Nat, ptn[q]! ≤ base → out[q]! ≤ level)
    {f : Nat × Nat} (hf : f ∈ cells out level n) :
    ∃ c ∈ cells ptn base n, c.1 ≤ f.1 ∧ f.2 ≤ c.2 := by
  have hend' : out[out.size - 1]! ≤ level := by rw [ht]; exact hg _ hend
  have hfl := cells_le f hf
  have hfb := cells_bound (Nat.le_of_eq ht.symm) hend' f hf
  have hfc := cells_isCell (Nat.le_of_eq ht.symm) hend' f hf
  obtain ⟨c, hc, hca, hcb⟩ := cells_cover (ptn := ptn) (level := base) (nn := n) f.1 (by omega)
  have hc' := cells_isCell (Nat.le_of_eq hs.symm) (by simpa only [hs] using hend) c hc
  have hcl := cells_le c hc
  refine ⟨c, hc, hca, ?_⟩
  by_cases hn : f.2 ≤ c.2
  · exact hn
  exfalso
  have hclosed : ptn[c.2]! ≤ base := by
    have he := hc'.2.2.2
    simpa only [show c.1 + (c.2 + 1 - c.1) - 1 = c.2 from by omega] using he
  have hnew := hg _ hclosed
  have hopen := hfc.2.2.1 c.2 (by omega) (by omega)
  omega

/-- Adding boundaries can only shrink cells. A surviving triple fills its
unique old triple, so the small-cell shape is preserved at any later level. -/
theorem SmallShape.mono {n base level : Nat} {ptn out : Array Nat}
    (hs : ptn.size = n) (ht : out.size = n) (hend : ptn[n - 1]! ≤ base)
    (hg : ∀ q : Nat, ptn[q]! ≤ base → out[q]! ≤ level) (h : SmallShape n base ptn) :
    SmallShape n level out := by
  intro f hf
  obtain ⟨c, hc, hca, hcb⟩ := cell_parent hs ht hend hg hf
  have hfl := cells_le f hf
  have hcl := cells_le c hc
  rcases h c hc with htwo | ⟨hthree, huniq⟩
  · exact Or.inl (by omega)
  · by_cases htwo : f.2 + 1 - f.1 ≤ 2
    · exact Or.inl htwo
    · have hfa : f.1 = c.1 := by omega
      have hfb : f.2 = c.2 := by omega
      refine Or.inr ⟨by omega, ?_⟩
      intro f' hf' hthree'
      obtain ⟨c', hc', hca', hcb'⟩ := cell_parent hs ht hend hg hf'
      have hfl' := cells_le f' hf'
      have hcl' := cells_le c' hc'
      rcases h c' hc' with htwo' | ⟨hthree'', _⟩
      · omega
      · have he := huniq c' hc' hthree''
        have hfa' : f'.1 = c'.1 := by omega
        have hfb' : f'.2 = c'.2 := by omega
        apply Prod.ext
        · rw [hfa', he, hfa]
        · rw [hfb', he, hfb]

/-- Both shapes admitted by the cheap guard survive boundary refinement.
This proof uses no graph dispatch or refinement implementation. -/
theorem NodeShape.mono {n base level : Nat} {ptn out : Array Nat}
    (hs : ptn.size = n) (ht : out.size = n) (hend : ptn[n - 1]! ≤ base)
    (hg : ∀ q : Nat, ptn[q]! ≤ base → out[q]! ≤ level) (h : NodeShape n base ptn) :
    NodeShape n level out := by
  rcases h with hsmall | hdef
  · exact Or.inl (hsmall.mono hs ht hend hg)
  · apply Or.inr
    have hc := bcount_mono (nn := n) hg
    rw [cells_length_eq_bcount hs (by simpa only [hs] using hend)] at hdef
    rw [cells_length_eq_bcount ht (by rw [ht]; exact hg _ hend)]
    omega

end Hex.GraphIso.Nauty
