/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetPerm
public import HexGraphIso.Nauty.Sparse.TargetValid

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Equal scores on the candidate list give the same first maximum. -/
theorem Target.best_congr (keys : List Nat) (left right : Nat → Nat) (empty : Nat)
    (h : ∀ a ∈ keys, left a = right a) : best keys left empty = best keys right empty := by
  have hf : ∀ (xs : List Nat) (acc : Nat × Nat), (∀ a ∈ xs, left a = right a) →
      xs.foldl (select left) acc = xs.foldl (select right) acc := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons a xs ih =>
      intro acc hh
      rw [List.foldl_cons, List.foldl_cons]
      have he : select left acc a = select right acc a := by simp only [select, hh a List.mem_cons_self]
      rw [he]
      exact ih _ (fun a ha => hh a (List.mem_cons_of_mem _ ha))
  unfold best
  split
  · rfl
  · rw [hf keys _ h]

/-- The executed fresh best-cell selector is invariant under reordering
inside equitable cells. Cache witnesses are supplied by the proved indexer. -/
theorem bestcell_perm (G : Hex.SparseGraph n) (lab out ptn : Array Nat) (level : Nat) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hq : out.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n out ptn level t.cellstart t.cellend)
    (heq : Equitable (Graph.context G) level lab ptn) (hperm : cellsPerm ptn level lab out) :
    bestcell (.ofGraph G) lab ptn level = bestcell (.ofGraph G) out ptn level := by
  obtain ⟨l, hl⟩ := Label.ofArray?_exists hp
  obtain ⟨m, hm⟩ := Label.ofArray?_exists hq
  rw [bestcell_spec G lab ptn level s l hl hs hend hi,
    bestcell_spec G out ptn level t m hm hs hend hj]
  exact Target.best_congr _ _ _ _ (fun a ha => Target.score_perm G lab out ptn level s t
    hp hq hs hend hi hj heq hperm ha)

/-- Valid hints, best-cell selection, and the depth cutoff all respect
within-cell permutations of an equitable partition. -/
theorem targetcell_perm (G : Hex.SparseGraph n) (lab out ptn : Array Nat)
    (level tcLevel : Nat) (hint : Int) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hq : out.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n out ptn level t.cellstart t.cellend)
    (heq : Equitable (Graph.context G) level lab ptn) (hperm : cellsPerm ptn level lab out) :
    targetcell (.ofGraph G) lab ptn level tcLevel hint = targetcell (.ofGraph G) out ptn level tcLevel hint := by
  unfold targetcell
  split
  · rfl
  · split
    · exact bestcell_perm G lab out ptn level s t hp hq hs hend hi hj heq hperm
    · rfl

/-- Target position, vertex set, and size are all invariant under
within-cell permutations of an equitable nondiscrete partition. -/
theorem maketargetcell_perm (G : Hex.SparseGraph n) (lab out ptn : Array Nat)
    (level tcLevel : Nat) (hint : Int) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hq : out.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n out ptn level t.cellstart t.cellend)
    (heq : Equitable (Graph.context G) level lab ptn) (hperm : cellsPerm ptn level lab out)
    (hc : bcount ptn level n < n) :
    maketargetcell (.ofGraph G) lab ptn level tcLevel hint = maketargetcell (.ofGraph G) out ptn level tcLevel hint := by
  have ht := targetcell_perm G lab out ptn level tcLevel hint s t hp hq hs hend hi hj heq hperm
  have hm := targetcell_nontrivial G lab ptn level tcLevel hint hp hs hend hc
  obtain ⟨b, hm, hlt⟩ := Target.mem_iff.mp hm
  have hend' : ptn[ptn.size - 1]! ≤ level := by simpa only [hs] using hend
  have hcell := cells_isCell (Nat.le_of_eq hs.symm) hend' _ hm
  have he := ((mem_cells_iff (Nat.le_of_eq hs.symm) hend').mp hm).2.2
  have hset := worksetOf_congr_perm (n := n) (hperm _ _ hcell)
  rw [he] at hset
  simp only [maketargetcell, ← ht, hset]

end Hex.GraphIso.Nauty.Sparse
