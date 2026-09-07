/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CodeState
public import HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- Canonical fields affected by a leaf verdict. Admission and return
bookkeeping preserve this projection. -/
@[expose] def Search.canonical (st : Search n) :=
  (st.canoncode, st.canonlevel, st.eqlevCanon, st.compCanon, st.canonlab,
    st.canong, st.samerows)

private theorem pushAuto_canonical (st : Search n) (pair : VSet n × VSet n) :
    (pushAuto st pair).canonical = st.canonical := by
  unfold pushAuto
  split <;> rfl

private theorem admit_canonical (st : Search n) :
    (admit st).canonical = st.canonical := by
  unfold admit
  simp only [Id.run_pure]
  change (pushAuto _ _).canonical = _
  rw [pushAuto_canonical]
  rfl

private theorem pruneReturn_canonical (level : Nat) (st : Search n) :
    (pruneReturn level st).2.canonical = st.canonical := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run,
    apply_ite (fun r : Exit × Search n => r.2.canonical)]
  split
  · exact pushAuto_canonical _ _
  · rfl

/-- The canonical effect of a classified leaf, independent of its exit. -/
@[expose] def resolve (level : Nat) (r : Leaf × Search n) : Search n :=
  match r.1 with
  | .better sr => install level sr r.2
  | _ => r.2

/-- Only a better verdict changes canonical fields after classification. -/
theorem leafExit_canonical (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.canonical = (resolve level (leaf, st)).canonical := by
  unfold leafExit
  cases leaf <;> simp only [resolve, Id.run_pure, apply_ite Id.run,
    apply_ite (fun r : Exit × Search n => r.2.canonical), pruneReturn_canonical,
    admit_canonical]
  all_goals repeat' split
  all_goals first | exact admit_canonical _ | rfl

/-- Canonical-field equality preserves the settled comparison machine. -/
theorem Settled.canonical {cs bs : List Nat} {st out : Search n}
    (h : Settled cs bs st) (he : out.canonical = st.canonical) : Settled cs bs out := by
  exact h.congr (congrArg Prod.fst he)
    (congrArg (fun r => r.2.1) he) (congrArg (fun r => r.2.2.1) he)
    (congrArg (fun r => r.2.2.2.1) he)

/-- Canonical-field equality preserves every ghost incumbent. -/
theorem key_canonical {ctx : Ctx n} {bs : List Nat} {st out : Search n}
    (he : out.canonical = st.canonical) : out.key ctx bs = st.key ctx bs := by
  have hl : out.canonlab = st.canonlab := congrArg (fun r => r.2.2.2.2.1) he
  simp only [Search.key, incKey, hl]

end Hex.GraphIso.Nauty.Engine
