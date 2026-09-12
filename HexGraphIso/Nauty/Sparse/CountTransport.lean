/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountInvariant
public import HexGraphIso.Nauty.Sparse.ContextMap

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Transporting vertices and their keys preserves the segment's count
multiset, including a further permutation within the segment. -/
theorem segment_keys_map (σ : Renaming n) (lab out hits keys : Array Nat)
    (hp : lab.toList.Perm (List.range n)) (hb : first + len ≤ n)
    (hc : (segN out first len).Perm (segN (lab.map σ.toFun) first len))
    (hk : ∀ v ∈ segN lab first len, keys[σ v]! = hits[v]!) :
    ((segN out first len).map fun v => keys[v]!).Perm
      ((segN lab first len).map fun v => hits[v]!) := by
  have hs : lab.size = n := by simpa using hp.length_eq
  have hm := hc.map (fun v => keys[v]!)
  rw [segN_map_of_le _ _ _ _ (by omega), List.map_map] at hm
  apply hm.trans (List.Perm.of_eq ?_)
  apply List.map_congr_left
  intro v hv
  exact hk v hv

/-- Count classes commute with vertex transport. This law permits
different admissible index storage and different orders within a cell. -/
theorem splitCounts_map (σ : Renaming n) (level first last : Nat) (distance : Bool)
    (s t : RefineSt n)
    (hsl : s.lab.toList.Perm (List.range n)) (htl : t.lab.toList.Perm (List.range n))
    (hsp : s.ptn.size = n) (htp : t.ptn = s.ptn)
    (hse : s.cellend[first]! = last) (hte : t.cellend[first]! = last)
    (hf : first ≤ last) (hb : last < n)
    (hsk : ∀ q, first ≤ q → q ≤ last → s.hits[s.lab[q]!]! < n + 2)
    (htk : ∀ q, first ≤ q → q ≤ last → t.hits[t.lab[q]!]! < n + 2)
    (hk : ∀ v ∈ segN s.lab first (last + 1 - first), t.hits[σ v]! = s.hits[v]!)
    (hc : IsCell s.ptn level first (last + 1 - first))
    (hp : cellsPerm s.ptn level t.lab (s.lab.map σ.toFun)) :
    (splitCounts level first distance s).ptn = (splitCounts level first distance t).ptn ∧
      cellsPerm (splitCounts level first distance s).ptn level
        (splitCounts level first distance t).lab ((splitCounts level first distance s).lab.map σ.toFun) := by
  have hs : s.lab.size = n := by simpa using hsl.length_eq
  have ht : t.lab.size = n := by simpa using htl.length_eq
  have hkeys := (segment_keys_map σ s.lab t.lab s.hits t.hits hsl (by omega) (hp _ _ hc) hk).symm
  have heq := splitCounts_ptn level first last distance s t hs ht hsp htp hse hte hf hb hsk htk hkeys
  have hsize := perm_size (splitCounts_perm level first distance s (by omega) (by omega))
  have hext (q : Nat) (hq : q < first ∨ last < q) :
      ((splitCounts level first distance s).lab.map σ.toFun)[q]! = (s.lab.map σ.toFun)[q]! := by
    by_cases hqn : q < n
    · rw [getElem!_map_of_lt _ _ (by omega), getElem!_map_of_lt _ _ (by omega),
        splitCounts_outside level first distance s (by omega) (by omega) q (by omega)]
    · rw [getElem!_neg ((splitCounts level first distance s).lab.map σ.toFun) q
        (by simp only [Array.size_map]; omega),
        getElem!_neg (s.lab.map σ.toFun) q (by simp only [Array.size_map]; omega)]
  refine ⟨heq, ?_⟩
  intro a len ha
  have hpart := splitCounts_partition level first distance s hs hsp (by omega) (by omega)
    (fun q hq he => hsk q hq (by omega))
  rw [hse] at hpart
  rcases hpart.nesting hc ha with hleft | hright | ⟨hfirst, hlast⟩
  · have hc' := hpart.cell_outside ha (Or.inl hleft)
    have hs' := segN_congr (lo := a) (len := len) (fun i hi => hext (a + i) (by omega))
    have ht' := segN_congr (lo := a) (len := len) (fun i hi =>
      splitCounts_outside level first distance t (by omega) (by omega) (a + i) (by omega))
    rw [hs', ht']
    exact hp a len hc'
  · have hc' := hpart.cell_outside ha (Or.inr hright)
    have hs' := segN_congr (lo := a) (len := len) (fun i hi => hext (a + i) (by omega))
    have ht' := segN_congr (lo := a) (len := len) (fun i hi =>
      splitCounts_outside level first distance t (by omega) (by omega) (a + i) (by omega))
    rw [hs', ht']
    exact hp a len hc'
  · have hs' := splitCounts_class level first distance s hsl hsp (by omega) (by omega)
      (fun q hq he => hsk q hq (by omega)) (by simpa only [hse] using hc)
      hfirst ha.1 (by omega) ha
    have ht' := splitCounts_class level first distance t htl (by rw [htp]; exact hsp)
      (by omega) (by omega) (fun q hq he => htk q hq (by omega))
      (by simpa only [hte, htp] using hc) hfirst ha.1 (by omega) (by rw [← heq]; exact ha)
    have hkey := splitCounts_keys level first last distance s t hs ht hse hte hf hb
      (hsk first (by omega) hf) (htk first (by omega) hf) hkeys hfirst (by have := ha.1; omega)
    rw [hse] at hs'
    rw [hte, ← hkey] at ht'
    rw [segN_map_of_le _ _ _ _ (by have := ha.1; omega)]
    apply ht'.trans
    apply ((hp _ _ hc).filter _).trans
    rw [segN_map_of_le _ _ _ _ (by omega), List.filter_map]
    have hfilter : (segN s.lab first (last + 1 - first)).filter
        (fun v => t.hits[σ v]! == s.hits[(splitCounts level first distance s).lab[a]!]!) =
        (segN s.lab first (last + 1 - first)).filter
        (fun v => s.hits[v]! == s.hits[(splitCounts level first distance s).lab[a]!]!) := by
      apply List.filter_congr
      intro v hv
      rw [hk v hv]
    change (((segN s.lab first (last + 1 - first)).filter
      (fun v => t.hits[σ v]! == s.hits[(splitCounts level first distance s).lab[a]!]!)).map σ.toFun).Perm _
    rw [hfilter]
    exact (hs'.map σ.toFun).symm

end Hex.GraphIso.Nauty.Sparse
