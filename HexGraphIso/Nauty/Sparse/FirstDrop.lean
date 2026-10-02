/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstCount
public import HexGraphIso.Nauty.Sparse.FirstSweep
import all HexGraphIso.Nauty.Sparse.MaxFirstSweep
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Lowering the native all-same boundary requires the actual completed
sweep to count its whole target and the guiding child's boundary to reach
its entry. The order accumulator update has no effect on this implication. -/
theorem first_drop {G : Hex.SparseGraph n} {inf tcLevel fuel level numcells last tv : Nat}
    {st leaf : State n}
    (hopen : (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).1 ≠ n)
    (htv : (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true level
      (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.2.2).orbits[tv]! = tv)
    (hp : let r := Generic.prepareFirst (.ofGraph G) tcLevel level numcells st
      Generic.FirstPath (.ofGraph G) tcLevel fuel (level + 1) (r.1 + 1)
        ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) last leaf)
    (hsame : (Generic.node true (.ofGraph G) inf tcLevel (fuel + 1) level numcells st).2.allsamelevel ≤ level) :
    let r := Generic.prepareFirst (.ofGraph G) tcLevel level numcells st
    let ch := Generic.node true (.ofGraph G) inf tcLevel fuel (level + 1) (r.1 + 1)
      ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))
    let sr := Generic.sweep true (.ofGraph G) inf tcLevel fuel (n + 1) level r.1 r.2.1.toNat tv (some tv)
      r.2.2.1 0 (cheapCheck true level r.2.2.2.2)
    sr.1 = .done ∧ r.2.2.2.1 = sr.2.1 ∧ ch.2.allsamelevel = level + 1 := by
  have hfloor := (firstPath_floor (inf := inf) hp).1
  have hloop := firstSweep_same (ctx := .ofGraph G) (tcLevel := tcLevel) (level := level)
    (inf := inf) (fuel := fuel) (cfuel := n) (index := 0)
    (numcells := (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).1)
    (tc := (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.1.toNat)
    (cell := (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.1) horbit
  rw [Generic.node, Frame.first_sweep_step (f := ⟨level, numcells, [], st⟩) _ hopen] at hsame
  dsimp only at hsame
  rw [htv] at hsame
  simp only [Option.getD_some] at hsame
  dsimp only
  generalize hs : Generic.sweep true (.ofGraph G) inf tcLevel fuel (n + 1) level
    (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).1
    (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.1.toNat tv (some tv)
    (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.1 0
    (cheapCheck true level (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.2.2) = result
    at hsame hloop ⊢
  obtain ⟨exit, index, out⟩ := result
  cases exit with
  | fuel => dsimp only at hsame hloop; omega
  | unwind => dsimp only at hsame hloop; omega
  | done =>
    dsimp only at hsame hloop ⊢
    change (Nauty.afterSweep true level
      (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.2.1 index out).allsamelevel ≤ level at hsame
    unfold Nauty.afterSweep at hsame
    split at hsame
    · rename_i hc
      simp only [Bool.true_and, Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, hc.1, hloop.symm.trans hc.2⟩
    · omega

/-- A native first call either lowers the all-same boundary to its own
level or retains precisely the guiding child's boundary. -/
theorem first_boundary {G : Hex.SparseGraph n} {inf tcLevel fuel level numcells tv : Nat}
    {st : State n}
    (hopen : (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).1 ≠ n)
    (htv : (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true level
      (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.2.2).orbits[tv]! = tv) :
    let r := Generic.prepareFirst (.ofGraph G) tcLevel level numcells st
    let ch := Generic.node true (.ofGraph G) inf tcLevel fuel (level + 1) (r.1 + 1)
      ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))
    let out := Generic.node true (.ofGraph G) inf tcLevel (fuel + 1) level numcells st
    out.2.allsamelevel = level ∨ out.2.allsamelevel = ch.2.allsamelevel := by
  have hloop := firstSweep_same (ctx := .ofGraph G) (tcLevel := tcLevel) (level := level)
    (inf := inf) (fuel := fuel) (cfuel := n) (index := 0)
    (numcells := (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).1)
    (tc := (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.1.toNat)
    (cell := (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.1) horbit
  dsimp only
  rw [Generic.node, Frame.first_sweep_step (f := ⟨level, numcells, [], st⟩) _ hopen]
  dsimp only
  rw [htv]
  simp only [Option.getD_some]
  generalize hs : Generic.sweep true (.ofGraph G) inf tcLevel fuel (n + 1) level
    (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).1
    (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.1.toNat tv (some tv)
    (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.1 0
    (cheapCheck true level (Generic.prepareFirst (.ofGraph G) tcLevel level numcells st).2.2.2.2) = result
    at hloop ⊢
  obtain ⟨exit, index, out⟩ := result
  cases exit with
  | fuel => exact Or.inr hloop
  | unwind => exact Or.inr hloop
  | done =>
    change (Nauty.afterSweep true level _ index out).allsamelevel = level ∨
      (Nauty.afterSweep true level _ index out).allsamelevel = _
    unfold Nauty.afterSweep
    split
    · rename_i hc
      simp only [Bool.true_and, Bool.and_eq_true, beq_iff_eq] at hc
      left
      dsimp only
      omega
    · exact Or.inr hloop

end Hex.GraphIso.Nauty.Sparse.Max
