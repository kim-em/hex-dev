/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Fill

public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

/-- Collected and retained vertices together fill the scanned interval. -/
theorem extent (h : Compact before p first upto seen lab hit next)
    (hs : seen.length = upto - first) : next + hit.size = upto := by
  have bounds := h.bounds
  have hc := h.count
  have hh := congrArg List.length h.hits
  have hp := (List.filter_append_perm p seen).length_eq
  simp only [Array.length_toList, List.length_append] at hh hp
  omega

/-- After reverse reinsertion, compaction is a permutation of exactly the
original interval. This includes both uniform-predicate cases. -/
theorem restore (h : Compact before p first last seen lab hit next)
    (hs : seen = (before.toList.drop first).take (last - first))
    (hr : Fill lab hit.toList.reverse next hit.toList.reverse.length out) :
    Sort.Window before out first last := by
  have bounds := h.bounds
  have hseen : seen.length = last - first := by
    rw [hs]
    simp only [List.length_take, List.length_drop, Array.length_toList]
    omega
  have hextent := h.extent hseen
  have htail := drop_eq h.size (fun q hq hlast => h.exterior q hq (Or.inr hlast))
  have hout := hr.finish
  simp only [List.length_reverse, Array.length_toList, hextent] at hout
  rw [h.kept, htail, h.hits] at hout
  have hsrc : before.toList = before.toList.take first ++ seen ++ before.toList.drop last := by
    have hh := congrArg (fun xs => before.toList.take first ++ xs)
      (List.take_append_drop (last - first) (before.toList.drop first))
    conv at hh => rhs; rw [List.take_append_drop]
    simpa only [← hs, List.append_assoc, List.drop_drop,
      show first + (last - first) = last by omega] using hh.symm
  refine ⟨?_, ?_⟩
  · rw [hout]
    apply List.Perm.trans (l₂ := before.toList.take first ++ seen ++ before.toList.drop last)
    · apply List.Perm.append_right
      rw [List.append_assoc]
      apply List.Perm.append_left
      have hp := List.filter_append_perm (fun v => !p v) seen
      simp only [Bool.not_not] at hp
      exact ((List.Perm.refl _).append (List.reverse_perm _)).trans hp
    · exact List.Perm.of_eq hsrc.symm
  · intro q hq
    have hsize : out.size = before.size := hr.size.trans h.size
    by_cases hb : q < before.size
    · rw [hr.exterior q (by simp only [List.length_reverse, Array.length_toList]; omega)]
      exact h.exterior q hb (by omega)
    · rw [getElem!_neg out q (by omega), getElem!_neg before q hb]

end Hex.GraphIso.Nauty.Sparse.Compact
