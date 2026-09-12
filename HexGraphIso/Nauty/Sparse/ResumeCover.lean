/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FrozenPrune
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.CursorCover
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Native recovery changes neither the readable incumbent nor its code array. -/
theorem recover_best (G : Hex.SparseGraph n) (inf level : Nat) (st : State n) :
    State.best G ((policy (n := n)).recover inf level st) = State.best G st := by
  have hf : let out := (policy (n := n)).recover inf level st
      out.canonlevel = st.canonlevel ∧ out.canoncode = st.canoncode ∧ out.canonlab = st.canonlab := by
    change (recoverLevels level (recoverPtn inf level st)).canonlevel = st.canonlevel ∧
      (recoverLevels level (recoverPtn inf level st)).canoncode = st.canoncode ∧
      (recoverLevels level (recoverPtn inf level st)).canonlab = st.canonlab
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.canonlevel,
      apply_ite SearchState.canoncode, apply_ite SearchState.canonlab, ite_self]
    trivial
  simp only [State.best, hf.1, hf.2.1, hf.2.2]

/-- The native long filter observes the same fixed set and workspace before
and after recovery, including its cache invalidation. -/
theorem recover_long (inf level : Nat) (st : State n) (cell : VSet n) :
    (policy (n := n)).longprune cell ((policy (n := n)).recover inf level st) =
      (policy (n := n)).longprune cell st := by
  have hf : let out := (policy (n := n)).recover inf level st
      out.fixedpts = st.fixedpts ∧ out.autos = st.autos := by
    change (recoverLevels level (recoverPtn inf level st)).fixedpts = st.fixedpts ∧
      (recoverLevels level (recoverPtn inf level st)).autos = st.autos
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.fixedpts,
      apply_ite SearchState.autos, ite_self]
    trivial
  change Nauty.longprune cell _ _ = Nauty.longprune cell _ _
  rw [hf.1, hf.2]

namespace Max

/-- The actual native resumption supplies the next continuation with
coverage of its literal cursor and filtered target. Pair validity is used
after recovery; the filter observes identical fields before recovery. -/
theorem Cell.Cover.resume {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {c : Cell n} {out : State n} {cell : VSet n} {tv tv1 index : Nat} {first : Bool}
    {next : Generic.SweepFn (State n) n} {result : Exit × Nat × State n → Prop}
    (h : c.Cover G.graph tcLevel (Remaining (cell.nextElem (some tv)) cell) (State.best G.graph out))
    (hc : c.Valid G)
    (he : FrameOut G c.level c.level c.entry ((policy (n := n)).recover (n + 2) c.level out))
    (hp : PairsReady G tcLevel c.level c.numcells ((policy (n := n)).recover (n + 2) c.level out))
    (hs : ∀ v, cell.mem v = true → c.vertices.mem v = true)
    (hnext : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
      c.Cover G.graph tcLevel (Remaining (smaller.nextElem (some tv)) smaller)
        (State.best G.graph ((policy (n := n)).recover (n + 2) c.level out)) →
      result (next first c.level c.numcells c.tc tv1 (smaller.nextElem (some tv)) smaller index
        ((policy (n := n)).recover (n + 2) c.level out))) :
    result (Generic.resume (n + 2) next first c.level c.numcells c.tc tv1 tv cell index out) := by
  let back := (policy (n := n)).recover (n + 2) c.level out
  have hr : c.Cover G.graph tcLevel (Remaining (cell.nextElem (some tv)) cell) (State.best G.graph back) := by
    rw [recover_best]
    exact h
  have hlong := hr.long hc he hp (fun v hv => hs v hv.1) (fun _ hv => hv.1)
  rw [recover_long] at hlong
  have hsub : ∀ v, ((policy (n := n)).longprune cell out).mem v = true → cell.mem v = true :=
    fun _ hv => Nauty.longprune_subset hv
  unfold Generic.resume
  simp only [Id.run_pure, apply_ite Id.run]
  split
  · exact hnext _ hsub _ (hlong.filtered hsub)
  · exact hnext cell (fun _ hv => hv) _ hr

end Max
end Hex.GraphIso.Nauty.Sparse
