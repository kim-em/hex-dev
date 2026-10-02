/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.WindowCells
public import HexGraphIso.Nauty.Spec.Equivariance

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Mapping vertex names preserves the support of a label permutation,
including the default reads beyond both arrays. -/
theorem Sort.Window.map (h : Sort.Window before after first last) (f : Nat → Nat) :
    Sort.Window (before.map f) (after.map f) first last := by
  refine ⟨by simpa only [Array.toList_map] using h.perm.map f, ?_⟩
  intro q hq
  have hs := h.size
  by_cases hb : q < before.size
  · rw [getElem!_map_of_lt f after (by omega), getElem!_map_of_lt f before hb, h.outside q hq]
  · rw [getElem!_neg (after.map f) q (by simp only [Array.size_map]; omega),
      getElem!_neg (before.map f) q (by simp only [Array.size_map]; omega)]

/-- Two transported binary fragments and their exterior windows determine
cell equivalence for the entire updated partition. Uniform classes retain
the old partition and use the whole-window permutation contract. -/
theorem binary_cells_map (f : Nat → Nat)
    (hs : Sort.Window before lab first last) (ht : Sort.Window other out first last)
    (hbs : last ≤ before.size) (hbt : last ≤ other.size) (hbp : last ≤ ptn.size)
    (hc : IsCell ptn level first (last - first)) (hf : first ≤ cut) (he : cut ≤ last)
    (hp : cellsPerm ptn level other (before.map f))
    (hl : (segN out first (cut - first)).Perm (segN (lab.map f) first (cut - first)))
    (hr : (segN out cut (last - cut)).Perm (segN (lab.map f) cut (last - cut))) :
    cellsPerm (if cut ≠ last ∧ cut ≠ first then ptn.set! (cut - 1) level else ptn)
      level out (lab.map f) := by
  have hmap := hs.map f
  have hlast : first + (last - first) = last := by omega
  have outside (a len : Nat) (ha : IsCell ptn level a len)
      (hd : a + len ≤ first ∨ last ≤ a) :
      (segN out a len).Perm (segN (lab.map f) a len) := by
    have hs' := segN_congr (lo := a) (len := len)
      (fun i hi => hmap.outside (a + i) (by omega))
    have ht' := segN_congr (lo := a) (len := len)
      (fun i hi => ht.outside (a + i) (by omega))
    rw [hs', ht']
    exact hp a len ha
  by_cases hh : cut ≠ last ∧ cut ≠ first
  · rw [ite_eq_left hh]
    have hcut : cut - 1 + 1 = cut := by omega
    apply cellsPerm_set! hc (by omega) (by omega) (by omega)
    · simpa only [hcut] using hl
    · simpa only [hcut, hlast] using hr
    · intro a len ha hd
      exact outside a len ha (by simpa only [hlast] using hd)
  · rw [ite_eq_right hh]
    intro a len ha
    exact (ht.cells (by omega) hbt hc a len ha).trans ((hp a len ha).trans
      (hmap.cells (by omega) (by simpa only [Array.size_map] using hbs) hc a len ha).symm)

end Hex.GraphIso.Nauty.Sparse
