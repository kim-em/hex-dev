/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Classify
public import HexGraphIso.Nauty.Sparse.DispatchFrame
public import HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Sparse.Classify
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

variable {n : Nat}

/-- A canonical automorphism verdict stores the scatter from the
canonical labelling to the current labelling. -/
theorem canonVerdict_map {g : Graph n} {level : Nat} {st : State n}
    (he : (canonVerdict g level st).1 = .autoCanon)
    (hw : st.workperm.size = n) (hs : st.canonlab.size = n)
    (hp : st.canonlab.toList.Perm (List.range n)) :
    ∀ i, i < n → (canonVerdict g level st).2.workperm[st.canonlab[i]!]! = st.lab[i]! := by
  have hm := scatter_map (st := st) hw hs hp
  unfold canonVerdict at he ⊢
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd] at he ⊢
  repeat' split at he
  all_goals simp_all only [reduceCtorEq, ite_true, ite_false]
  all_goals simpa only [scatter_eq] using hm

/-- The full classifier's canonical verdict has the same scatter relation,
even when it first attempted an unsuccessful first-reference admission. -/
theorem classify_canon_map {g : Graph n} {level numcells : Nat} {st : State n}
    (he : (classify g level numcells st).1 = .autoCanon)
    (hw : st.workperm.size = n) (hs : st.canonlab.size = n)
    (hp : st.canonlab.toList.Perm (List.range n)) :
    ∀ i, i < n → (classify g level numcells st).2.workperm[st.canonlab[i]!]! = st.lab[i]! := by
  rw [classify_eq] at he ⊢
  simp only [apply_ite Prod.fst, apply_ite Prod.snd] at he ⊢
  repeat' split at he
  all_goals simp_all only [reduceCtorEq, ite_true, ite_false]
  all_goals first
    | exact canonVerdict_map he hw hs hp
    | exact canonVerdict_map he ((scatter_size _ _).trans hw)
        (by simpa only [scatter_eq] using hs) (by simpa only [scatter_eq] using hp)

/-- The scatter relation is readable entirely from the classified state;
its scratch allocation and canonical reference are the only size premises. -/
theorem classify_canon_out {g : Graph n} {level numcells : Nat} {st : State n}
    (he : (classify g level numcells st).1 = .autoCanon) :
    let out := (classify g level numcells st).2
    out.workperm.size = n → out.canonlab.size = n →
      out.canonlab.toList.Perm (List.range n) →
      ∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]! := by
  intro out hw hs hp
  have hl := (classify_frame g level numcells st).1
  have hc := (classify_frame g level numcells st).2.2.2
  rw [hc] at hs hp
  rw [classify_workSize] at hw
  dsimp only [out]
  rw [hc, hl]
  exact classify_canon_map he hw hs hp

end Hex.GraphIso.Nauty.Sparse
