/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Pairs
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Off-path entry facts needed to validate every pruning-pair admission. -/
structure PairsEntry (G : GraphIso.Sparse.Colored n k) (tcLevel level numcells : Nat) (st : State n) : Prop
    extends TraceEntry G tcLevel level numcells st where
  path : PathInv G level st
  pairs : PairsOk G st
  boundary : CheapBoundary G level st
  bound : st.noncheaplevel ≤ level

/-- A sweep carries a valid workspace and a boundary advanced through its
cheap guard. The path and trace histories justify subsequent child admissions. -/
structure PairsReady (G : GraphIso.Sparse.Colored n k) (tcLevel level numcells : Nat) (st : State n) : Prop
    extends TraceReady G tcLevel level numcells st where
  path : PathInv G level st
  pairs : PairsOk G st
  boundary : CheapBoundary G (level + 1) st
  bound : st.noncheaplevel ≤ level + 1

/-- The actual guard parks a failed boundary at the next child's level. -/
theorem cheap_bound {level : Nat} {st : State n} (first : Bool) (h : st.noncheaplevel ≤ level) :
    (cheapCheck first level st).noncheaplevel ≤ level + 1 := by
  unfold cheapCheck
  split
  · exact Nat.le_refl _
  · exact Nat.le_trans h (Nat.le_succ _)

/-- Recovery always bounds the revived boundary by the next child's level. -/
theorem recover_bound (level : Nat) (st : State n) :
    ((policy (n := n)).recover (n + 2) level st).noncheaplevel ≤ level + 1 := by
  change (Nauty.recover (n + 2) level st).noncheaplevel ≤ level + 1
  rw [recover_noncheap]
  split <;> omega

/-- Native off-path preparation preserves the path, root workspace and
saved-pair boundary while establishing the admission history. -/
theorem PairsEntry.prepare {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat} {st : State n}
    (h : PairsEntry G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    let r := prepareOther (.ofGraph G.graph) tcLevel level numcells st
    TraceReady G tcLevel level r.1 r.2.2.2.2.2 ∧ PathInv G level r.2.2.2.2.2 ∧
      PairsOk G r.2.2.2.2.2 ∧ CheapBoundary G level r.2.2.2.2.2 ∧
      r.2.2.2.2.2.noncheaplevel ≤ level := by
  let v := visit (.ofGraph G.graph) level numcells st
  refine ⟨h.toTraceEntry.prepare hn hl,
    ((h.path.visit h.node).compare v.2.1).target false tcLevel v.1,
    ((h.pairs.visit level numcells).compare level v.2.1).target false tcLevel level v.1,
    ((h.boundary.visit hn hl h.node).compare v.2.1).target false tcLevel v.1, ?_⟩
  change (chooseTarget false (.ofGraph G.graph) tcLevel level v.1
    (compareCodes level v.2.1 v.2.2)).2.2.2.noncheaplevel ≤ level
  rw [(chooseTarget_controls false (.ofGraph G.graph) tcLevel level v.1
    (compareCodes level v.2.1 v.2.2)).2]
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]
  exact h.bound

/-- Classifying and acting on a prepared leaf preserves both explicit and
implicit pair validity, using the executed classifier's sound workspace. -/
theorem classified_pairs {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat} {st : State n}
    (h : TraceReady G tcLevel level numcells st) (hn : 0 < n)
    (hp : PairsOk G st) (hb : CheapBoundary G level st) (hl : st.noncheaplevel ≤ level) :
    let c := classify (.ofGraph G.graph) level numcells st
    PairsOk G (leafExit c.1 level c.2).2 := by
  let c := classify (.ofGraph G.graph) level numcells st
  apply (hp.classify level numcells).leaf hn c.1 level (hb.classify numcells)
  · change c.2.noncheaplevel ≤ level
    rw [(classify_controls (.ofGraph G.graph) level numcells st).2]
    exact hl
  · exact classify_auto hn h.ready h.history h.saved.store h.saved.canonical h.saved.first h.saved.work

namespace PairsReady

variable {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat} {st : State n}

/-- Child entry extends the path and keeps the inherited pair boundary. -/
theorem child (h : PairsReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first : Bool) {tc tv : Nat} {cell : VSet n} (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) (hrecord : CheapRecorded level tc st) :
    PairsEntry G tcLevel (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st) := by
  refine ⟨h.toTraceReady.child hn hl first ht hv hrecord, h.path.child hn hl h.ready first ht hv,
    h.pairs.child first level tc tv, h.boundary.child hl first ht hv, ?_⟩
  cases first <;> exact h.bound

/-- A returned workspace combines with independent trace, frame, fixed-set
and boundary theorems to establish the next actual sibling state. -/
theorem child_return (h : PairsReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first : Bool) (fuel : Nat) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hrecord : CheapRecorded level tc st)
    (hp : PairsOk G (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2) :
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    let result := (policy (n := n)).recover (n + 2) level ((policy (n := n)).leaveChild tv out)
    PairsReady G tcLevel level numcells result ∧ CheapRecorded level tc result := by
  let ch := (policy (n := n)).child first level tc tv st
  let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).2
  let left := (policy (n := n)).leaveChild tv out
  have hi := h.child hn hl first ht hv hrecord
  have ht' := node_trace G hn tcLevel fuel (level + 1) (numcells + 1) ch (by omega) hi.toTraceEntry
  have hr := h.toTraceReady.child_return hn hl first fuel ht hv ht'
  have hb := hi.boundary.node hn (by omega) hi.node tcLevel fuel
  have hbl : CheapBoundary G (level + 1) left := hb.congr rfl rfl rfl
  refine ⟨⟨hr.1, h.path.child_return hn hl h.ready first false tcLevel fuel tc tv cell ht hv,
    (hp.leave tv).recover (n + 2) level, hbl.recover_child hl ?_, recover_bound level left⟩,
    hr.2 hrecord⟩
  have hh := Nat.le_trans h.ready.ok.bc (bcount_le _ _ _)
  omega

end PairsReady
end Hex.GraphIso.Nauty.Sparse
