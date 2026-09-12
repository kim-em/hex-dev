/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Scatter
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The canonical-comparison part of the native classifier, after the
first-reference admission is inapplicable or has failed. -/
@[expose] def canonVerdict (g : Graph n) (level : Nat) (st : State n) : Leaf × State n := Id.run do
  let mut st := st
  let mut sr := 0
  if st.compCanon == 0 then
    if level < st.canonlevel then st := { st with compCanon := 1 }
    else
      st := { st with canong := st.canong.update g st.canonlab st.samerows, samerows := n }
      let (c, s) := testcanlab g st.canong.toRows st.lab
      st := { st with compCanon := c }
      sr := s
  if st.compCanon == 0 then return (.autoCanon, scatter st.canonlab st)
  else if st.compCanon > 0 then return (.better sr, st)
  else return (.bad, st)

theorem canonVerdict_ne (g : Graph n) (level : Nat) (st : State n) :
    (canonVerdict g level st).1 ≠ .autoFirst := by
  unfold canonVerdict
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
  repeat' split
  all_goals intro h; cases h

/-- This decomposition is definitionally the executed sparse classifier. -/
theorem classify_eq (g : Graph n) (level numcells : Nat) (st : State n) :
    classify g level numcells st =
      if st.eqlevFirst != level && st.compCanon < 0 then (.bad, st)
      else if numcells != n then (.internal, st)
      else if st.eqlevFirst == level then
        let sc := scatter st.firstlab st
        if sc.gcaFirst >= sc.noncheaplevel || isautom g sc.workperm then (.autoFirst, sc)
        else canonVerdict g level sc
      else canonVerdict g level st := by
  rfl

/-- First-reference admission scatters the saved first label and takes
exactly one of the cheap-boundary and explicit-scan guards. -/
theorem classify_first {g : Graph n} {level numcells : Nat} {st out : State n}
    (hauto : classify g level numcells st = (.autoFirst, out)) :
    numcells = n ∧ st.eqlevFirst = level ∧ out = scatter st.firstlab st ∧
      (st.noncheaplevel ≤ st.gcaFirst ∨ isautom g out.workperm = true) := by
  rw [classify_eq] at hauto
  split at hauto
  · cases hauto
  · split at hauto
    · cases hauto
    · rename_i hnc
      split at hauto
      · rename_i heq
        dsimp only at hauto
        split at hauto
        · rename_i hguard
          have hout : out = scatter st.firstlab st := (Prod.mk.inj hauto).2.symm
          refine ⟨by simpa using hnc, by simpa using heq, hout, ?_⟩
          rw [hout]
          simpa only [scatter_eq, Bool.or_eq_true, decide_eq_true_eq] using hguard
        · exact (canonVerdict_ne g level _ (congrArg Prod.fst hauto)).elim
      · exact (canonVerdict_ne g level _ (congrArg Prod.fst hauto)).elim

end Hex.GraphIso.Nauty.Sparse
