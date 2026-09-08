/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CanonCalls
public import HexGraphIso.Nauty.Policy.FirstBounded
import all HexGraphIso.Nauty.Policy.CanonCalls
import all HexGraphIso.Nauty.Policy.CanonFrame
import all HexGraphIso.Nauty.Policy.FirstBounded
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- Below a fixed level, installations and recovery retain that lower
bound on the canonical ancestor. -/
theorem canonFloor (ctx : Ctx n) (inf tcLevel bound : Nat) :
    Generic.BoundedPolicy ctx inf tcLevel bound (fun st : Search n => bound ≤ st.gcaCanon) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st _ h
    change bound ≤ (compareCodes level code st).gcaCanon
    rwa [compare_canon]
  target := by
    intro level numcells st _ h
    change bound ≤ (chooseTarget false ctx tcLevel level numcells st).2.2.2.gcaCanon
    rwa [target_canon]
  classify := by
    intro level numcells st h
    change bound ≤ (classify ctx level numcells st).2.gcaCanon
    rwa [classify_canon]
  leaf := by
    intro leaf level st hl h
    have hf := (canon_leaf leaf level st).floor
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
    change bound ≤ (recoverLevels level (recoverPtn inf level st)).gcaCanon
    rw [recover_canon]
    change bound ≤ min level st.gcaCanon
    omega
  afterSweep := by
    intro first level size index st _ h
    change bound ≤ (afterSweep first level size index st).gcaCanon
    unfold afterSweep
    split <;> exact h

/-- The actual first leaf installs a canonical ancestor below every
strictly older receiving loop, and the remaining traversal preserves it. -/
theorem firstPath_canon {ctx : Ctx n} {inf tcLevel fuel level numcells last bound : Nat}
    {st leaf : Search n} (path : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hb : bound < level) :
    bound ≤ (Engine.node true ctx inf tcLevel fuel level numcells st).2.gcaCanon := by
  have hlast : level ≤ last := by
    induction path with
    | leaf => exact Nat.le_refl _
    | step _ _ _ _ ih => omega
  have h := path.bounded (canonFloor ctx inf tcLevel bound) (fun _ _ _ h => h) (Nat.le_of_lt hb)
    (show bound ≤ (firstterminal last leaf).gcaCanon from by change bound ≤ last; omega)
  rwa [← node_eq_generic] at h

/-- An off-path call preserves the ordering of its two ancestor counters. -/
theorem node_order {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {st : Search n} (hn0 : 0 < n) (hl : 1 ≤ level)
    (hok : SearchOk G level numcells st.view) (hgf : st.gcaFirst < level)
    (horder : st.gcaFirst ≤ st.gcaCanon) :
    let out := (Engine.node false ctx (n + 2) tcLevel fuel level numcells st).2
    out.gcaFirst = st.gcaFirst ∧ out.gcaFirst ≤ out.gcaCanon := by
  intro out
  have he : out.gcaFirst = st.gcaFirst := node_gca ctx (n + 2) tcLevel fuel level numcells st
  have hf := (node_canon (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) false hn0 hl hok).floor
  change min level st.gcaCanon ≤ out.gcaCanon at hf
  exact ⟨he, by rw [he]; omega⟩

end Hex.GraphIso.Nauty.Engine.Max
