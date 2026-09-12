/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountPending
public import HexGraphIso.Nauty.Sparse.CompactKeys
public import HexGraphIso.Nauty.Sparse.CompactScan

public section

namespace Hex.GraphIso.Nauty.Sparse.Pending

/-- Marking alone identifies every nontrivial cell that can have a nonzero
native neighbour count. No interpretation of retained scratch counts is needed. -/
theorem touched {lab ptn starts ends before marks cells : Array Nat}
    {n stamp level : Nat} {seen : List Nat}
    (h : Touched n stamp before marks cells (seen.map fun v => starts[v]!))
    (hi : Index.Valid n lab ptn level starts ends) :
    Pending n level seen.count ends cells.toList lab ptn := by
  intro a len hc hb
  have he := hi.ends_eq a len hc hb (by have := hc.1; omega)
  by_cases hl : 1 < len
  · by_cases ht : a ∈ cells.toList
    · exact Or.inl ⟨a, ht, Nat.le_refl _, by omega⟩
    · right
      have hz : ∀ q, a ≤ q → q < a + len → seen.count lab[q]! = 0 := by
        intro q hq hq'
        apply List.count_eq_zero.mpr
        intro hm
        have hk := hi.starts_eq a len hc hb (by omega) q hq hq'
        rw [ite_eq_right (by omega)] at hk
        apply ht ((h.members a).mpr ⟨by omega, ?_⟩)
        exact List.mem_map.mpr ⟨lab[q]!, hm, hk⟩
      intro q r hq hq' hr hr'
      exact (hz q hq hq').trans (hz r hr hr').symm
  · right
    intro q r hq hq' hr hr'
    have he : q = r := by have := hc.1; omega
    rw [he]

/-- A binary split discharges its cell once both predicate classes have
constant keys. The equal-endpoint cases perform no boundary write. -/
theorem binary {key : Nat → Nat} {ends lab out ptn : Array Nat}
    {n level first cut last : Nat} {todo : List Nat}
    (h : Pending n level key ends (first :: todo) lab ptn)
    (hc : IsCell ptn level first (last - first))
    (hf : first ≤ cut) (hl : cut ≤ last) (hb : last ≤ ptn.size)
    (he : last = ends[first]! + 1)
    (ho : ∀ q, q < first ∨ last ≤ q → out[q]! = lab[q]!)
    (hleft : ∀ q r, first ≤ q → q < cut → first ≤ r → r < cut → key out[q]! = key out[r]!)
    (hright : ∀ q r, cut ≤ q → q < last → cut ≤ r → r < last → key out[q]! = key out[r]!) :
    Pending n level key ends todo out
      (if cut ≠ last ∧ cut ≠ first then ptn.setIfInBounds (cut - 1) level else ptn) := by
  have outside : ∀ a len, (a + len ≤ first ∨ last ≤ a) → IsCell ptn level a len →
      a + len ≤ n →
      (∃ c ∈ todo, c ≤ a ∧ a + len ≤ ends[c]! + 1) ∨
      ∀ q r, a ≤ q → q < a + len → a ≤ r → r < a + len → key out[q]! = key out[r]! := by
    intro a len hd ha hab
    rcases h a len ha hab with ⟨c, hm, hlo, hhi⟩ | hconst
    · left
      refine ⟨c, ?_, hlo, hhi⟩
      rcases List.mem_cons.mp hm with heq | hm
      · have := ha.1; subst c; omega
      · exact hm
    · right
      intro q r hq hq' hr hr'
      rw [ho q (by omega), ho r (by omega)]
      exact hconst q r hq hq' hr hr'
  intro a len ha hab
  by_cases hd : cut ≠ last ∧ cut ≠ first
  · rw [ite_eq_left hd] at ha
    rcases CellCut.cells hc (by omega) (by omega) (by omega) ha with
      ⟨hdis, hold⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact outside a len hdis hold hab
    · right
      intro q r hq hq' hr hr'
      exact hleft q r hq (by omega) hr (by omega)
    · right
      intro q r hq hq' hr hr'
      exact hright q r hq (by omega) hr (by omega)
  · rw [ite_eq_right hd] at ha
    rcases isCell_disjoint_or_eq hc ha with hdis | hdis | ⟨rfl, rfl⟩
    · exact outside a len (Or.inl hdis) ha hab
    · exact outside a len (Or.inr (by omega)) ha hab
    · right
      intro q r hq hq' hr hr'
      by_cases heq : cut = first
      · exact hright q r (by omega) (by omega) (by omega) (by omega)
      · exact hleft q r hq (by omega) hr (by omega)

/-- The executed compaction and reverse fill provide the two constant
classes required by the binary-cell argument. -/
theorem compact {key : Nat → Nat} {p : Nat → Bool}
    {ends before lab hit out ptn : Array Nat}
    {n level first cut last : Nat} {todo : List Nat}
    (h : Pending n level key ends (first :: todo) before ptn)
    (hc : Compact before p first last
      ((before.toList.drop first).take (last - first)) lab hit cut)
    (hr : Fill lab hit.toList.reverse cut hit.toList.reverse.length out)
    (hp : before.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hcell : IsCell ptn level first (last - first)) (he : last = ends[first]! + 1)
    (hk : ∀ v w, v < n → w < n → p v = p w → key v = key w) :
    Pending n level key ends todo out
      (if cut ≠ last ∧ cut ≠ first then ptn.setIfInBounds (cut - 1) level else ptn) := by
  have bounds := hc.bounds
  have hsize : before.size = n := by simpa using hp.length_eq
  have hw := hc.restore rfl hr
  have hout := hw.perm.trans hp
  have hsep := hc.separated (by
    simp only [List.length_take, List.length_drop, Array.length_toList]; omega) hr
  apply h.binary hcell (by omega) (by omega) (by omega) he hw.outside
  · intro q r hq hq' hr hr'
    exact hk _ _ (perm_bound hout (by omega)) (perm_bound hout (by omega))
      ((hsep.1 q hq hq').trans (hsep.1 r hr hr').symm)
  · intro q r hq hq' hr hr'
    exact hk _ _ (perm_bound hout (by omega)) (perm_bound hout (by omega))
      ((hsep.2 q hq hq').trans (hsep.2 r hr hr').symm)

end Hex.GraphIso.Nauty.Sparse.Pending
