/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ComparePrefix
public import HexGraphIso.Nauty.Sparse.DispatchFrame
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- A store with the graph's edge capacity is a valid empty prefix for
every other labelling of the same graph. No rows are read. -/
theorem Rows.Prefix.relabel_zero {G : Hex.SparseGraph n} {R : Rows n} {l c : Label n} {same : Nat}
    (h : R.Prefix (G.relabel c.perm) same) : R.Prefix (G.relabel l.perm) 0 :=
  (h.mono (Nat.zero_le _)).agreement (by simp) (fun _ hi => by omega)

/-- Native classification retains the incumbent's valid row prefix. A
better verdict carries exactly the candidate prefix needed by installation,
including the zero-prefix code-order branches and raw unsorted cached rows. -/
theorem classify_prefix (G : Hex.SparseGraph n) (level numcells : Nat) (st : State n)
    (l c : Label n) (hl : Label.ofArray? n st.lab = some l) (hc : Label.ofArray? n st.canonlab = some c)
    (h : st.canong.toRows.Prefix (G.relabel c.perm) st.samerows) :
    let r := classify (.ofGraph G) level numcells st
    r.2.canong.toRows.Prefix (G.relabel c.perm) r.2.samerows ∧
      ∀ sr, r.1 = .better sr → r.2.canong.toRows.Prefix (G.relabel l.perm) sr := by
  have hz : st.canong.toRows.Prefix (G.relabel l.perm) 0 := h.relabel_zero
  have hu := updatecan_relabel G st.canong.toRows st.canonlab c st.samerows hc h
  have ht := testcanlab_prefix G (G.relabel c.perm)
    (updatecan (.ofGraph G) st.canong.toRows st.canonlab st.samerows) st.lab l hl hu (by simp)
  unfold classify
  apply Id.of_wp_run_eq rfl (fun r : Leaf × State n =>
    r.2.canong.toRows.Prefix (G.relabel c.perm) r.2.samerows ∧
      ∀ sr, r.1 = .better sr → r.2.canong.toRows.Prefix (G.relabel l.perm) sr)
  mvcgen
  all_goals simp_all +zetaDelta [scatter_eq, Storage.update]

end Hex.GraphIso.Nauty.Sparse
