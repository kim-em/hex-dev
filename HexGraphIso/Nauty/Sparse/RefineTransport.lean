/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineDistance

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Full production refinement commutes with graph renaming and arbitrary
orders within input cells. All partition and control observations agree,
independently of bounded incoming scratch, stale hits and cache generations.
The proof includes empty queues, index rebuilding, shallow native distance
splitting, both main-loop branches and final hash cleanup. -/
theorem refineWith_equiv (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (level : Nat) (lab out ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hq : out.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n s) (hc : Scratch.Bounded n t)
    (hcell : cellsPerm ptn level out (lab.map (renamingOf p).toFun)) :
    RefineSt.Equiv (renamingOf p) level
      (refineWith (.ofGraph G) level lab ptn active numcells s)
      (refineWith (.ofGraph H) level out ptn active numcells t) := by
  let a := Refinement.indexed level (Refinement.start lab ptn active numcells s)
  let b := Refinement.indexed level (Refinement.start out ptn active numcells t)
  have hva : RefineSt.Valid level a := Refinement.initial_valid level lab ptn active numcells s hp hs hend ha hb
  have hvb : RefineSt.Valid level b := Refinement.initial_valid level out ptn active numcells t hq hs hend ha hc
  have he : RefineSt.Equiv (renamingOf p) level a b :=
    Refinement.initial_equiv (renamingOf p) level lab out ptn active numcells s t hcell
  rw [refineWith_parts, refineWith_parts]
  dsimp +instances only [Refinement.start]
  by_cases hempty : (Refinement.queue active).isEmpty = true
  · simp only [hempty, ite_true]
    exact ⟨rfl, hcell, rfl, rfl⟩
  · simp only [Bool.eq_false_iff.mpr hempty, Bool.false_eq_true, ite_false]
    split
    · rename_i hd
      try simp only [hd, ite_true]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
      have hdist := Refinement.distance_equiv G H p hiso level a b hva hvb he hd.1.1.2 hd.1.2
      exact Refinement.finish_equiv
        (refine_loop_equiv G H p hiso level _ _ hdist.1 hdist.2.1 hdist.2.2)
    · rename_i hd
      try simp only [Bool.eq_false_iff.mpr hd, Bool.false_eq_true, ite_false]
      exact Refinement.finish_equiv (refine_loop_equiv G H p hiso level a b hva hvb he)

end Hex.GraphIso.Nauty.Sparse
