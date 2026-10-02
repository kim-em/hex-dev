/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Spec.CellPerm
public import HexGraphIso.Nauty.Sparse.CompactKeys
public import HexGraphIso.Nauty.Sparse.CompactTransport

public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

/-- The first restored fragment is literally the retained source order. -/
theorem kept_segment (h : Compact before p first last seen lab hit cut)
    (hr : Fill lab hit.toList.reverse cut hit.toList.reverse.length out) :
    segN out first (cut - first) = seen.filter (fun v => !p v) := by
  have bounds := h.bounds
  have count := h.count
  apply List.ext_getElem
  · simp only [segN_length]
    omega
  · intro i hi hj
    have hi' : i < cut - first := by simpa only [segN_length] using hi
    have hread := prefix_read h.kept (q := first + i)
      (by simp only [List.length_take, Array.length_toList]; omega) (by omega)
      (by rw [h.size]; omega)
    simp only [List.length_take, Array.length_toList,
      Nat.min_eq_left (show first ≤ before.size by omega), Nat.add_sub_cancel_left] at hread
    have he : out[first + i]! = (seen.filter fun v => !p v)[i]! := by
      rw [hr.exterior (first + i) (Or.inl (by omega))]
      exact hread
    simpa [segN, hi', hj] using he

/-- The second restored fragment is literally the reverse of the collected
source order, as in sparse nauty's descending hit-buffer traversal. -/
theorem hit_segment (h : Compact before p first last seen lab hit cut)
    (hlen : seen.length = last - first)
    (hr : Fill lab hit.toList.reverse cut hit.toList.reverse.length out) :
    segN out cut (last - cut) = (seen.filter p).reverse := by
  have bounds := h.bounds
  have extent := h.extent hlen
  have hhit := congrArg List.length h.hits
  simp only [Array.length_toList] at hhit
  apply List.ext_getElem
  · simp only [segN_length, List.length_reverse]
    omega
  · intro i hi hj
    have hi' : i < last - cut := by simpa only [segN_length] using hi
    have he := hr.read (q := cut + i) (by omega)
      (by simp only [List.length_reverse, Array.length_toList]; omega)
    rw [h.hits, Nat.add_sub_cancel_left, getElem!_pos (seen.filter p).reverse i hj] at he
    simpa [segN, hi', hj] using he

/-- Both fragments of the executed compaction and reverse fill transport
as vertex multisets, with identical cut and collected-hit count. -/
theorem fragments_map (f : Nat → Nat)
    (hs : Compact before p first last seen lab hit cut)
    (ht : Compact other q first last visits temp collected next)
    (hfill : Fill lab hit.toList.reverse cut hit.toList.reverse.length out)
    (hfill' : Fill temp collected.toList.reverse next collected.toList.reverse.length final)
    (hlen : seen.length = last - first)
    (hp : visits.Perm (seen.map f)) (hk : ∀ v ∈ seen, q (f v) = p v) :
    cut = next ∧ hit.size = collected.size ∧
      (segN final first (next - first)).Perm ((segN out first (cut - first)).map f) ∧
      (segN final next (last - next)).Perm ((segN out cut (last - cut)).map f) := by
  obtain ⟨hcut, hhit⟩ := hs.counts_map f ht hp hk
  have hlen' : visits.length = last - first := by
    have he := hp.length_eq
    simpa only [List.length_map, hlen] using he
  refine ⟨hcut, hhit, ?_, ?_⟩
  · rw [ht.kept_segment hfill', hs.kept_segment hfill]
    exact filter_transport f (fun v => !p v) (fun v => !q v) hp
      (fun v hv => congrArg Bool.not (hk v hv))
  · rw [ht.hit_segment hlen' hfill', hs.hit_segment hlen hfill]
    exact (List.reverse_perm _).trans ((filter_transport f p q hp hk).trans
      ((List.reverse_perm _).map f).symm)

end Hex.GraphIso.Nauty.Sparse.Compact
