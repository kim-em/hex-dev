/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstFields
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Native target selection preserves canonical comparison storage and
both reference labels, including when it borrows the cached scratch. -/
theorem chooseTarget_codes (first : Bool) (g : Graph n)
    (tcLevel level numcells : Nat) (st : State n) :
    let out := (chooseTarget first g tcLevel level numcells st).2.2.2
    out.canoncode = st.canoncode ∧ out.canonlevel = st.canonlevel ∧
      out.eqlevCanon = st.eqlevCanon ∧ out.compCanon = st.compCanon ∧
      out.canonlab = st.canonlab ∧ out.firstlab = st.firstlab := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.canoncode = st.canoncode ∧ out.2.2.2.canonlevel = st.canonlevel ∧
      out.2.2.2.eqlevCanon = st.eqlevCanon ∧ out.2.2.2.compCanon = st.compCanon ∧
      out.2.2.2.canonlab = st.canonlab ∧ out.2.2.2.firstlab = st.firstlab)
  mvcgen
  all_goals simp_all +zetaDelta

/-- First preparation leaves the preallocated incumbent code array intact. -/
theorem prepareFirst_canoncode (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2.canoncode = st.canoncode := by
  unfold Generic.prepareFirst
  exact (chooseTarget_codes true g tcLevel level _ _).1

/-- Every first-path descent reaches its leaf with the original canonical
code allocation. Only leaf installation begins writing incumbent codes. -/
theorem firstPath_canoncode {g : Graph n} {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf) :
    leaf.canoncode = st.canoncode := by
  induction path with
  | leaf fuel level numcells st hdisc => exact prepareFirst_canoncode g tcLevel level numcells st
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    rw [ih]
    change (cheapCheck true level (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2).canoncode = _
    unfold cheapCheck
    split <;> exact prepareFirst_canoncode g tcLevel level numcells st

end Hex.GraphIso.Nauty.Sparse
