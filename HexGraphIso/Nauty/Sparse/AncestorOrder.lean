/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonCalls
public import HexGraphIso.Nauty.Sparse.Controls
public import HexGraphIso.Nauty.Policy.Generic.FirstBounded
import all HexGraphIso.Nauty.Sparse.CanonFrame
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Native installation and recovery preserve a lower bound on the
canonical ancestor while the traversal stays below that bound. -/
theorem canonFloor (g : Graph n) (inf tcLevel bound : Nat) :
    Generic.BoundedPolicy g inf tcLevel bound (fun st : State n => bound ≤ st.gcaCanon) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st _ h
    change bound ≤ (compareCodes level code st).gcaCanon
    rwa [compare_canon]
  target := by
    intro level numcells st _ h
    change bound ≤ (chooseTarget false g tcLevel level numcells st).2.2.2.gcaCanon
    rwa [chooseTarget_ancestor]
  classify := by
    intro level numcells st h
    change bound ≤ (classify g level numcells st).2.gcaCanon
    rwa [classify_ancestor]
  leaf := by
    intro leaf level st hl h
    have hf := (canon_leaf leaf level st).floor
    change min level st.gcaCanon ≤ (leafExit leaf level st).2.gcaCanon at hf
    change bound ≤ (leafExit leaf level st).2.gcaCanon
    omega
  cheap := by
    intro first level st _ h
    change bound ≤ (cheapCheck first level st).gcaCanon
    rwa [cheap_canon]
  child := by intro first level tc tv st h; cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st hl h
    change bound ≤ (Nauty.recover inf level st).gcaCanon
    rw [recover_canon]
    change bound ≤ min level st.gcaCanon
    omega
  afterSweep := by
    intro first level size index st _ h
    change bound ≤ (if first then { Nauty.afterSweep first level size index st with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st).gcaCanon
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals unfold Nauty.afterSweep; split <;> exact h

/-- The first leaf installs its ancestor at its actual depth, and the
rest of that first-path call retains every older receiving lower bound. -/
theorem firstPath_canon {g : Graph n} {inf tcLevel fuel level numcells last bound : Nat}
    {st leaf : State n} (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf)
    (hb : bound ≤ level) :
    bound ≤ (Generic.node true g inf tcLevel fuel level numcells st).2.gcaCanon := by
  have hlast : level ≤ last := by
    induction path with
    | leaf => exact Nat.le_refl _
    | step _ _ _ _ ih => omega
  apply path.bounded (canonFloor g inf tcLevel bound) (fun _ _ _ h => h) hb
  change bound ≤ last
  omega

/-- Every native off-path call preserves the order of the two ancestor
counters. The canonical lower bound follows from executed provenance. -/
theorem node_order {G : GraphIso.Sparse.Colored n k} {tcLevel fuel level numcells : Nat}
    {st : State n} (hn : 0 < n) (hl : 1 ≤ level) (hi : NodeInv G level numcells st)
    (hf : st.gcaFirst ≤ level) (ho : st.gcaFirst ≤ st.gcaCanon) :
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2
    out.gcaFirst = st.gcaFirst ∧ out.gcaFirst ≤ out.gcaCanon := by
  intro out
  have he : out.gcaFirst = st.gcaFirst :=
    node_gca (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st
  have hb := (node_canon G hn false tcLevel fuel level numcells st hl hi).floor
  change min level st.gcaCanon ≤ out.gcaCanon at hb
  exact ⟨he, by rw [he]; omega⟩

end Hex.GraphIso.Nauty.Sparse
