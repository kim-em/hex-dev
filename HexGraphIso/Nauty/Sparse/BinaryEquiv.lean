/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryCell

public section

namespace Hex.GraphIso.Nauty.Sparse.Binary

/-- The compaction cut lies in its input interval, including empty classes. -/
theorem cut_bounds (lab : Array Nat) (pred : Nat → Bool) (hf : first ≤ last) :
    first ≤ cut lab pred first last ∧ cut lab pred first last ≤ last := by
  have hlen : (seen lab first last).length = last - first := by simp only [seen, List.length_map, List.length_range']
  have hsum := (List.filter_append_perm pred (seen lab first last)).length_eq
  simp only [List.length_append] at hsum
  unfold cut
  omega

/-- Complete singleton-cell observations transport under a mapped input
permutation and predicate. The updated partition's every cell, its literal
control and the exact cell count agree. -/
theorem Cell.equiv {s t a b : RefineSt n} (f : Nat → Nat)
    (hs : Cell level first last pred s a) (ht : Cell level first last other t b)
    (hsl : s.lab.size = n) (htl : t.lab.size = n) (hsp : s.ptn.size = n)
    (htp : t.ptn = s.ptn) (hb : last ≤ n)
    (hcell : IsCell s.ptn level first (last - first))
    (hp : cellsPerm s.ptn level t.lab (s.lab.map f))
    (hk : ∀ v ∈ seen s.lab first last, other (f v) = pred v)
    (hcontrol : CountTrace.control s = CountTrace.control t) (hnum : s.numcells = t.numcells) :
    a.ptn = b.ptn ∧ cellsPerm a.ptn level b.lab (a.lab.map f) ∧
      CountTrace.control a = CountTrace.control b ∧ a.numcells = b.numcells := by
  have hlen := hcell.1
  have hf : first ≤ last := by omega
  have hseen : (seen t.lab first last).Perm ((seen s.lab first last).map f) := by
    rw [seen_eq, seen_eq, ← segN_map_of_le f s.lab first (last - first) (by omega)]
    exact hp _ _ hcell
  have hkeep := (filter_transport f (fun v => !pred v) (fun v => !other v) hseen
    (fun v hv => congrArg Bool.not (hk v hv))).length_eq
  have hhit := (filter_transport f pred other hseen hk).length_eq
  simp only [List.length_map] at hkeep hhit
  have hcut : cut s.lab pred first last = cut t.lab other first last := by unfold cut; omega
  have hcount : hits s.lab pred first last = hits t.lab other first last := by unfold hits; omega
  have heq : a.ptn = b.ptn := by rw [hs.ptn, ht.ptn, htp, hcut]
  have bounds := cut_bounds s.lab pred hf
  refine ⟨heq, ?_, ?_, ?_⟩
  · rw [hs.ptn]
    apply binary_cells_map f hs.window ht.window (by omega) (by omega) (by omega)
      hcell bounds.1 bounds.2 hp
    · rw [segN_map_of_le f a.lab first (cut s.lab pred first last - first)
        (by have := hs.frame.lab_size; omega), hs.retained, hcut, ht.retained]
      exact filter_transport f (fun v => !pred v) (fun v => !other v) hseen
        (fun v hv => congrArg Bool.not (hk v hv))
    · rw [segN_map_of_le f a.lab (cut s.lab pred first last) (last - cut s.lab pred first last)
        (by have := hs.frame.lab_size; omega), hs.collected, hcut, ht.collected]
      exact (List.reverse_perm _).trans ((filter_transport f pred other hseen hk).trans
        ((List.reverse_perm _).map f).symm)
  · rw [hs.control, ht.control, hcontrol, hcut, hcount]
  · rw [hs.count, ht.count, hcut, hnum]

end Hex.GraphIso.Nauty.Sparse.Binary
