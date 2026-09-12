/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonFrame
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Native cached target dispatch retains the canonical ancestor. -/
theorem chooseTarget_ancestor (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.gcaCanon = st.gcaCanon := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n => out.2.2.2.gcaCanon = st.gcaCanon)
  mvcgen
  all_goals simp_all +zetaDelta

/-- Native row comparison and automorphism tests retain the canonical
ancestor; installing a better label belongs to the subsequent leaf action. -/
theorem classify_ancestor (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.gcaCanon = st.gcaCanon := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.gcaCanon, ite_self]

end Hex.GraphIso.Nauty.Sparse
