/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetCounts
public import HexGraphIso.Nauty.Sparse.TargetSelect
public import HexGraphIso.LabelArray
public import HexGraphIso.Nauty.Equitable.Step

public section

namespace Hex.GraphIso.Nauty.Sparse.Target

/-- In an equitable partition the partial-join score is unchanged by
reordering vertices inside cells, even when the representative changes. -/
theorem score_perm (G : Hex.SparseGraph n) (lab out ptn : Array Nat) (level : Nat) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hq : out.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n out ptn level t.cellstart t.cellend)
    (heq : Equitable (Graph.context G) level lab ptn) (hperm : cellsPerm ptn level lab out)
    (hf : first ∈ nontrivial (cells ptn level n)) :
    score (.ofGraph G) lab s (nontrivial (cells ptn level n)) first =
      score (.ofGraph G) out t (nontrivial (cells ptn level n)) first := by
  have hfirst := bound hs hend hf
  obtain ⟨last, hsource, hlt⟩ := mem_iff.mp hf
  have hend' : ptn[ptn.size - 1]! ≤ level := by simpa only [hs] using hend
  have hcell := cells_isCell (Nat.le_of_eq hs.symm) hend' (first, last) hsource
  have hm1 : lab[first]! ∈ segN lab first (last + 1 - first) :=
    mem_segN_iff.mpr ⟨0, by omega, by simp⟩
  have hm2 : out[first]! ∈ segN lab first (last + 1 - first) :=
    (hperm first (last + 1 - first) hcell).mem_iff.mpr
      (mem_segN_iff.mpr ⟨0, by omega, by simp⟩)
  unfold score
  apply List.countP_congr
  intro a ha
  obtain ⟨b, htarget, hab⟩ := mem_iff.mp ha
  have hc := cells_isCell (Nat.le_of_eq hs.symm) hend' (a, b) htarget
  have hb := cells_end_lt_of_end (Nat.le_of_eq hs.symm) hend' hend (a, b) htarget
  have hs' : s.cellend[a]! = b := by
    have hh := hi.ends_eq a (b + 1 - a) hc (by omega) (by omega)
    omega
  have ht' : t.cellend[a]! = b := by
    have hh := hj.ends_eq a (b + 1 - a) hc (by omega) (by omega)
    omega
  have hset := worksetOf_congr_perm (n := n) (hperm a (b + 1 - a) hc)
  have hconst := (splitDone_iff_constOn.mp (heq (first, last) hsource (a, b) htarget)) _ hm1 _ hm2
  simp only [Join.qualifies, count_workset G lab ptn level s hp hs hend hi ha hfirst,
    count_workset G out ptn level t hq hs hend hj ha hfirst, hs', ht', ← hset, hconst]

end Hex.GraphIso.Nauty.Sparse.Target
