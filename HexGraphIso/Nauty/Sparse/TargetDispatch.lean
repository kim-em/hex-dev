/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetSelect

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every dispatch arm selects a nontrivial cell: valid hints, the shallow
partial-join maximum, and the first open position at greater depth. -/
theorem targetcell_mem (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (s : Scratch) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hptn : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hidx : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hne : Target.nontrivial (cells ptn level n) ≠ []) :
    targetcell (.ofGraph G) lab ptn level tcLevel hint ∈ Target.nontrivial (cells ptn level n) := by
  unfold targetcell
  split
  · next hh =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
    have hb : hint.toNat < n := by
      by_cases hi : hint.toNat < n
      · exact hi
      · have he : ptn[hint.toNat]! = 0 := getElem!_neg _ _ (by omega)
        rw [he] at hh
        omega
    apply Target.mem_of_open hptn hend hb hh.1.2
    rcases hh.2 with hh | hh
    · left; rw [hh]; rfl
    · exact Or.inr hh
  · split
    · rw [bestcell_spec G lab ptn level s l hl hptn hend hidx]
      exact (Target.best_max _ _ n hne).mem
    · exact Target.first_mem hptn hend hne

/-- Cached dispatch has exactly the fresh target position, vertex set, and
size, including hints and both sides of the configured depth cutoff. -/
theorem maketargetCached_eq (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (s : Scratch) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hptn : ptn.size = n) (hend : ptn[n - 1]! ≤ level) (hs : Scratch.Valid n lab ptn level s)
    (hne : Target.nontrivial (cells ptn level n) ≠ []) :
    let out := maketargetCached (.ofGraph G) lab ptn level tcLevel hint s
    (out.1, out.2.1, out.2.2.1) = maketargetcell (.ofGraph G) lab ptn level tcLevel hint := by
  unfold maketargetCached
  simp only [Id.run, pure]
  split
  · rfl
  · next hindexed =>
    have hi : s.indexed = true := by simpa using hindexed
    have hidx := hs.indices hi
    have ht := targetcell_mem G lab ptn level tcLevel hint s l hl hptn hend hidx hne
    have hb := Target.bound hptn hend ht
    have hc := (Target.open_of_mem hptn hend ht).2
    have he := hidx.end_eq hptn hend hb hc
    split
    · next hh =>
      simp only [targetcell, ite_eq_left hh] at he
      simp only [maketargetcell, targetcell, ite_eq_left hh, he]
    · next hh =>
      split
      · next hd =>
        have hs' := bestcellCached_scratch (.ofGraph G) lab s
        have hend' : (bestcellCached (.ofGraph G) lab s).2.cellend = s.cellend := by
          rw [hs'.1]
        have hbest := bestcellCached_eq G lab ptn level s l hl hptn hend hidx hs.hits_size
        simp only [targetcell, ite_eq_right hh, ite_eq_left hd] at he
        simp only [maketargetcell, targetcell, ite_eq_right hh, ite_eq_left hd,
          hend', hbest, he]
      · next hd =>
        simp only [maketargetcell, he]

end Hex.GraphIso.Nauty.Sparse
