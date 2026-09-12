/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.DistanceCongr
public import HexGraphIso.Nauty.Sparse.RefineTransport
import all HexGraphIso.Nauty.Spec.SpecIso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Reusing any bounded scratch gives the same literal refinement result:
labels, partition, active set, ordered queue, cell count and hash all agree.
The retained scratch arrays and generations themselves need not coincide.
This follows the executed index rebuild, shallow BFS branch, singleton and
count splitters, main loop and final cleanup. -/
theorem refineWith_congr (G : Hex.SparseGraph n) (level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n s) (hc : Scratch.Bounded n t) :
    let a := refineWith (.ofGraph G) level lab ptn active numcells s
    let b := refineWith (.ofGraph G) level lab ptn active numcells t
    a.lab = b.lab ∧ a.ptn = b.ptn ∧ a.active = b.active ∧ a.queue = b.queue ∧
      a.numcells = b.numcells ∧ a.longcode = b.longcode := by
  have hid : (renamingOf (Perm.id n)).toFun = id := by funext v; simp [renamingOf]
  have hcell : cellsPerm ptn level lab (lab.map (renamingOf (Perm.id n)).toFun) := by
    rw [hid, Array.map_id]
    exact cellsPerm_refl _ _ _
  have hobs := refineWith_equiv G G (Perm.id n) (by intro u v; simp)
    level lab lab ptn active numcells s t hp hp hs hend ha hb hc hcell
  refine ⟨?_, hobs.ptn.symm, hobs.active, hobs.queue, hobs.count, hobs.code⟩
  let a := Refinement.indexed level (Refinement.start lab ptn active numcells s)
  let b := Refinement.indexed level (Refinement.start lab ptn active numcells t)
  have hva : a.Valid level := Refinement.initial_valid level lab ptn active numcells s hp hs hend ha hb
  have hvb : b.Valid level := Refinement.initial_valid level lab ptn active numcells t hp hs hend ha hc
  have he : RefineSt.Equiv (renamingOf (Perm.id n)) level a b :=
    Refinement.initial_equiv (renamingOf (Perm.id n)) level lab lab ptn active numcells s t hcell
  rw [refineWith_parts, refineWith_parts]
  dsimp +instances only [Refinement.start]
  by_cases hempty : (Refinement.queue active).isEmpty = true
  · simp only [hempty, ite_true]
  · simp only [Bool.eq_false_iff.mpr hempty, Bool.false_eq_true, ite_false]
    split
    · rename_i hd
      try simp only [hd, ite_true]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
      have hdist := Refinement.distance_equiv G G (Perm.id n) (by intro u v; simp)
        level a b hva hvb he hd.1.1.2 hd.1.2
      have hl := Refinement.shallow_lab G level a b hva hvb he rfl hd.1.1.2
      exact Refinement.loop_lab G level _ _ hdist.1 hdist.2.1 hdist.2.2 hl.symm
    · rename_i hd
      try simp only [Bool.eq_false_iff.mpr hd, Bool.false_eq_true, ite_false]
      exact Refinement.loop_lab G level a b hva hvb he rfl

end Hex.GraphIso.Nauty.Sparse
