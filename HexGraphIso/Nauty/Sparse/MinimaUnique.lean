/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountTransport
public import HexGraphIso.Nauty.Sparse.MinimaPerm

public section

namespace Hex.GraphIso.Nauty.Sparse.Minima

variable {keys : Array Nat}

/-- The first two runs determine their minimum keys and cut positions.
The nonempty second run is the branch used after a nonuniform cell scan. -/
theorem unique (h : Minima lab hits first v2 v3 last w1 w2)
    (h' : Minima out keys first u2 u3 last z1 z2)
    (hv : v2 < v3) (hu : u2 < u3)
    (hk : ∀ q, first ≤ q → q < last → hits[lab[q]!]! = keys[out[q]!]!) :
    w1 = z1 ∧ v2 = u2 ∧ w2 = z2 ∧ v3 = u3 := by
  have bounds := h.bounds
  have bounds' := h'.bounds
  have hw : w1 = z1 := by
    rw [← h.minimum first (by omega) (by omega), hk first (by omega) (by omega),
      h'.minimum first (by omega) (by omega)]
  have first_lt (q : Nat) (hq : v2 ≤ q) (he : q < last) : w1 < hits[lab[q]!]! := by
    by_cases hqv : q < v3
    · rw [h.second q hq hqv]
      exact h.keys
    · exact Nat.lt_trans h.keys (h.larger q (by omega) he)
  have first_lt' (q : Nat) (hq : u2 ≤ q) (he : q < last) : z1 < keys[out[q]!]! := by
    by_cases hqu : q < u3
    · rw [h'.second q hq hqu]
      exact h'.keys
    · exact Nat.lt_trans h'.keys (h'.larger q (by omega) he)
  have hc : v2 = u2 := by
    by_cases hlo : v2 < u2
    · have hx := first_lt v2 (by omega) (by omega)
      rw [hk v2 (by omega) (by omega), h'.minimum v2 (by omega) hlo, ← hw] at hx
      omega
    · by_cases hhi : u2 < v2
      · have hx := first_lt' u2 (by omega) (by omega)
        rw [← hk u2 (by omega) (by omega), h.minimum u2 (by omega) hhi, hw] at hx
        omega
      · omega
  have hw' : w2 = z2 := by
    rw [← h.second v2 (by omega) hv, hk v2 (by omega) (by omega), hc,
      h'.second u2 (by omega) hu]
  refine ⟨hw, hc, hw', ?_⟩
  by_cases hlo : v3 < u3
  · have hx := h.larger v3 (by omega) (by omega)
    rw [hk v3 (by omega) (by omega), h'.second v3 (by omega) hlo, ← hw'] at hx
    omega
  · by_cases hhi : u3 < v3
    · have hx := h'.larger u3 (by omega) (by omega)
      rw [← hk u3 (by omega) (by omega), h.second u3 (by omega) hhi, hw'] at hx
      omega
    · omega

/-- Permuting the input count multiset cannot change the two minimum
keys or either cutoff found by the executed insertion. Sorting the tail
is used only in this proof to compare the two completed invariants. -/
theorem data_eq (h : Minima lab hits first v2 v3 last w1 w2)
    (h' : Minima out keys first u2 u3 last z1 z2)
    (hb : last ≤ lab.size) (hb' : last ≤ out.size)
    (hv : v2 < v3) (hu : u2 < u3)
    (hp : ((segN lab first (last - first)).map fun v => hits[v]!).Perm
      ((segN out first (last - first)).map fun v => keys[v]!)) :
    w1 = z1 ∧ v2 = u2 ∧ w2 = z2 ∧ v3 = u3 := by
  have bounds := h.bounds
  have bounds' := h'.bounds
  have hs := h.indirect hb
  have ht := h'.indirect hb'
  have hsord := h.sort_tail hb
  have htord := h'.sort_tail hb'
  have sp := (Sort.Window.refl lab first last).indirect (by omega) (by omega) hb
    (hits := hits) (start := v3) (len := last - v3)
  have tp := (Sort.Window.refl out first last).indirect (by omega) (by omega) hb'
    (hits := keys) (start := u3) (len := last - u3)
  have hsp := Sort.segment_perm ⟨by omega, hb⟩ sp.perm sp.outside
  have htp := Sort.segment_perm ⟨by omega, hb'⟩ tp.perm tp.outside
  have hsp' : (segN (Sort.indirect lab hits v3 (last - v3)) first (last - first)).Perm
      (segN lab first (last - first)) := by
    rw [segN_extract _ _ _ (by have := sp.size; omega), segN_extract _ _ _ (by omega),
      show first + (last - first) = last by omega]
    exact hsp
  have htp' : (segN (Sort.indirect out keys u3 (last - u3)) first (last - first)).Perm
      (segN out first (last - first)) := by
    rw [segN_extract _ _ _ (by have := tp.size; omega), segN_extract _ _ _ (by omega),
      show first + (last - first) = last by omega]
    exact htp
  exact hs.unique ht hv hu (fun q hq he => hsord.keys_eq htord
    ((hsp'.map _).trans (hp.trans (htp'.map _).symm)) hq (by omega))

/-- A one-class insertion result implies that the original cell was
uniform. This rules out the redundant late uniform-return guard after
the first unequal input count has been found. -/
theorem Permuted.constant (h : Permuted before lab hits first last v2 v3 last w1 w2 cap)
    (he : v2 = last) (hq : first ≤ q) (hb : q < last) :
    hits[before[q]!]! = hits[before[first]!]! := by
  have bounds := h.bounds
  have size := h.size
  have hsize := h.window.size
  have hp := Sort.segment_perm ⟨by omega, by omega⟩ h.window.perm h.window.outside
  have key (q : Nat) (hq : first ≤ q) (hb : q < last) : hits[before[q]!]! = w1 := by
    obtain ⟨r, hr, hr', hh⟩ := Sort.segment_mem (by omega) hp.symm ⟨hq, hb⟩
    rw [hh]
    exact h.minimum r hr (by omega)
  rw [key q hq hb, key first (by omega) (by omega)]

end Hex.GraphIso.Nauty.Sparse.Minima
