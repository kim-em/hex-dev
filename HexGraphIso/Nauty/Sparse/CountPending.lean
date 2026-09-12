/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountSemantics

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Cells not covered by the remaining touched-cell windows already have
constant semantic counts. The windows use the captured original endpoints. -/
@[expose] def Pending (n level : Nat) (key : Nat → Nat) (ends : Array Nat)
    (todo : List Nat) (lab ptn : Array Nat) : Prop :=
  ∀ a len, IsCell ptn level a len → a + len ≤ n →
    (∃ c ∈ todo, c ≤ a ∧ a + len ≤ ends[c]! + 1) ∨
    ∀ q r, a ≤ q → q < a + len → a ≤ r → r < a + len → key lab[q]! = key lab[r]!

namespace Pending

/-- Singleton cells and untouched cells already have constant counts before
the touched-cell fold starts. -/
theorem initial {lab ptn starts ends before marks touched hits : Array Nat}
    {n stamp level : Nat} {seen : List Nat}
    (h : CountScan n stamp before marks touched starts hits seen)
    (hi : Index.Valid n lab ptn level starts ends) :
    Pending n level seen.count ends touched.toList lab ptn := by
  intro a len hc hb
  have he := hi.ends_eq a len hc hb (by have := hc.1; omega)
  by_cases hl : 1 < len
  · by_cases ht : a ∈ touched.toList
    · exact Or.inl ⟨a, ht, Nat.le_refl _, by omega⟩
    · right
      have hz := h.cell_zero hi hc hl hb ht
      intro q r hq hq' hr hr'
      change seen.count lab[q]! = seen.count lab[r]!
      rw [hz lab[q]! (List.mem_map.mpr ⟨q - a, List.mem_range.mpr (by omega),
        by rw [Nat.add_sub_cancel' hq]⟩),
        hz lab[r]! (List.mem_map.mpr ⟨r - a, List.mem_range.mpr (by omega),
        by rw [Nat.add_sub_cancel' hr]⟩)]
  · right
    intro q r hq hq' hr hr'
    have he : q = r := by have := hc.1; omega
    rw [he]

/-- Processing the head touched cell establishes constant counts on its
fragments and retains the guarantees of every disjoint completed cell. -/
theorem step {key : Nat → Nat} {ends : Array Nat} {todo : List Nat}
    (level first : Nat) (s : RefineSt n)
    (h : Pending n level key ends (first :: todo) s.lab s.ptn)
    (hl : s.lab.size = n) (hs : s.ptn.size = n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hb : s.cellend[first]! < n) (he : s.cellend[first]! = ends[first]!)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (hv : ∀ v ∈ segN s.lab first (s.cellend[first]! + 1 - first), s.hits[v]! = key v) :
    Pending n level key ends todo (splitCounts level first false s).lab
      (splitCounts level first false s).ptn := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  have hpart := splitCounts_partition level first false s hl hs hf hb hk
  intro a len ha hab
  rcases hpart.nesting hc ha with hd | hd | hd
  · have hold := hpart.cell_outside ha (Or.inl hd)
    rcases h a len hold hab with ⟨c, hm, hlo, hhi⟩ | hconst
    · left
      refine ⟨c, ?_, hlo, hhi⟩
      rcases List.mem_cons.mp hm with heq | hm
      · have := ha.1; subst c; omega
      · exact hm
    · right
      intro q r hq hq' hr hr'
      rw [splitCounts_outside level first false s hf (by omega) q (Or.inl (by omega)),
        splitCounts_outside level first false s hf (by omega) r (Or.inl (by omega))]
      exact hconst q r hq hq' hr hr'
  · have hold := hpart.cell_outside ha (Or.inr hd)
    rcases h a len hold hab with ⟨c, hm, hlo, hhi⟩ | hconst
    · left
      refine ⟨c, ?_, hlo, hhi⟩
      rcases List.mem_cons.mp hm with heq | hm
      · have := ha.1; subst c; omega
      · exact hm
    · right
      intro q r hq hq' hr hr'
      rw [splitCounts_outside level first false s hf (by omega) q (Or.inr (by omega)),
        splitCounts_outside level first false s hf (by omega) r (Or.inr (by omega))]
      exact hconst q r hq hq' hr hr'
  · exact Or.inr (splitCounts_constant level first false s key hl hs hc hb hk hv a len ha hd.1 hd.2)

/-- Exhausting the touched-cell list establishes constant counts everywhere. -/
theorem done {n level : Nat} {key : Nat → Nat} {ends lab ptn : Array Nat}
    (h : Pending n level key ends [] lab ptn) :
    ∀ a len, IsCell ptn level a len → a + len ≤ n →
      ∀ q r, a ≤ q → q < a + len → a ≤ r → r < a + len → key lab[q]! = key lab[r]! := by
  intro a len hc hb
  rcases h a len hc hb with ⟨c, hc, _⟩ | h
  · cases hc
  · exact h

end Pending
end Hex.GraphIso.Nauty.Sparse
