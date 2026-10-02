/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Reference
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- First-path target selection writes exactly its current target slot,
while retaining the code array. Scratch borrowing does not affect either. -/
theorem chooseFirst_store (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    let r := chooseTarget true g tcLevel level numcells st
    r.2.2.2.firstcode = st.firstcode ∧ r.2.2.2.firsttc = st.firsttc.set! level r.1 := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.firstcode = st.firstcode ∧ out.2.2.2.firsttc = st.firsttc.set! level out.1)
  mvcgen
  all_goals simp_all +zetaDelta

/-- Preparation records the actual cached refinement code and native target
in their depth-indexed slots. -/
theorem prepareFirst_store (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    let r := Generic.prepareFirst g tcLevel level numcells st
    r.2.2.2.2.firstcode = st.firstcode.set! level (visit g level numcells st).2.1 ∧
      r.2.2.2.2.firsttc = st.firsttc.set! level r.2.1 := by
  unfold Generic.prepareFirst
  exact chooseFirst_store g tcLevel level _ _

/-- The actual first descent retains both reference-array allocations. -/
theorem firstPath_storeSize {g : Graph n} {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf) :
    (leaf.firstcode.size, leaf.firsttc.size) = (st.firstcode.size, st.firsttc.size) := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    obtain ⟨hc, ht⟩ := prepareFirst_store g tcLevel level numcells st
    simp only [hc, ht, Array.size_set!]
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    rw [ih]
    change ((cheapCheck true level (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2).firstcode.size,
      (cheapCheck true level (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2).firsttc.size) = _
    obtain ⟨hc, ht⟩ := prepareFirst_store g tcLevel level numcells st
    unfold cheapCheck
    split <;> simp only [hc, ht, Array.size_set!]

/-- A deeper first-path visit preserves both code and target entries of
every earlier ancestor. -/
theorem firstPath_before {g : Graph n} {tcLevel fuel level numcells last slot : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf) (hs : slot < level) :
    (leaf.firstcode[slot]!, leaf.firsttc[slot]!) = (st.firstcode[slot]!, st.firsttc[slot]!) := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    obtain ⟨hc, ht⟩ := prepareFirst_store g tcLevel level numcells st
    rw [hc, ht, Array.getElem!_set!_ne _ _ _ _ (by omega), Array.getElem!_set!_ne _ _ _ _ (by omega)]
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    rw [ih (by omega)]
    change ((cheapCheck true level (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2).firstcode[slot]!,
      (cheapCheck true level (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2).firsttc[slot]!) = _
    obtain ⟨hc, ht⟩ := prepareFirst_store g tcLevel level numcells st
    unfold cheapCheck
    split
    all_goals try dsimp only
    all_goals rw [hc, ht, Array.getElem!_set!_ne _ _ _ _ (by omega),
      Array.getElem!_set!_ne _ _ _ _ (by omega)]

/-- The sentinel installed immediately below the actual first leaf survives
the complete search, at the unchanged allocated position. -/
theorem firstPath_sentinel {g : Graph n} {inf tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf)
    (hs : last + 1 < st.firstcode.size) :
    (Generic.node true g inf tcLevel fuel level numcells st).2.firstcode[last + 1]! = codeSentinel := by
  have hc := congrArg Prod.fst (firstPath_reference (inf := inf) path)
  change (Generic.node true g inf tcLevel fuel level numcells st).2.firstcode =
    leaf.firstcode.set! (last + 1) codeSentinel at hc
  rw [hc]
  apply Array.getElem!_set!_self
  have he := congrArg Prod.fst (firstPath_storeSize path)
  change leaf.firstcode.size = st.firstcode.size at he
  omega

end Hex.GraphIso.Nauty.Sparse
