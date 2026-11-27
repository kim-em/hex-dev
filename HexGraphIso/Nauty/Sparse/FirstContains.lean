/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstSuffix
public import HexGraphIso.Nauty.Sparse.TraceContains
public import HexGraphIso.Nauty.Sparse.Emission
import all HexGraphIso.Nauty.Sparse.MaxFirstSweep
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

open Emission

/-- The closing first-path node retains the log of its executed child sweep. -/
theorem Frame.first_log {G : Hex.SparseGraph n} {tcLevel fuel tv : Nat}
    {f : Frame n}
    (hopen : (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).1 ≠ n)
    (htv : (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv) :
    let r := Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry
    log (Generic.node true (.ofGraph G) (n + 2) tcLevel (fuel + 1)
      f.level f.numcells f.entry).2 =
    log (Generic.sweep true (.ofGraph G) (n + 2) tcLevel fuel (n + 1) f.level
      r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 (cheapCheck true f.level r.2.2.2.2)).2.2 := by
  intro r
  rw [Generic.node, f.first_sweep_step _ hopen]
  dsimp only
  rw [htv]
  simp only [Option.getD_some]
  let swept := Generic.sweep true (.ofGraph G) (n + 2) tcLevel fuel (n + 1) f.level
    r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 (cheapCheck true f.level r.2.2.2.2)
  change log (match swept.1 with
    | .done => (Generic.Exit.unwind (f.level - 1) false,
        (policy (n := n)).afterSweep true f.level r.2.2.2.1 swept.2.1 swept.2.2)
    | _ => (swept.1, swept.2.2)).2 = log swept.2.2
  cases he : swept.1 with
  | done => exact afterSweep_emission true f.level r.2.2.2.1 swept.2.1 swept.2.2
  | fuel => rfl
  | unwind target short => rfl

/-- Closing an actual first sweep retains every generator it emitted,
including the branch that updates the stabilizer index product. -/
theorem Frame.first_contains {G : Hex.SparseGraph n} {tcLevel fuel tv : Nat}
    {f : Frame n} {gamma : Array Nat}
    (hopen : (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).1 ≠ n)
    (htv : (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv) :
    let r := Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry
    gamma ∈ (Generic.sweep true (.ofGraph G) (n + 2) tcLevel fuel (n + 1) f.level
      r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 (cheapCheck true f.level r.2.2.2.2)).2.2.genTrace →
    gamma ∈ (Generic.node true (.ofGraph G) (n + 2) tcLevel (fuel + 1)
      f.level f.numcells f.entry).2.genTrace := by
  intro r hgamma
  have he := congrArg Log.trace (f.first_log (fuel := fuel) hopen htv)
  dsimp only [log] at he
  rwa [he]

end Hex.GraphIso.Nauty.Sparse.Max
