/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Boundary
public import HexGraphIso.Nauty.Policy.FirstBounded
public import HexGraphIso.Nauty.Policy.FirstCheap
import all HexGraphIso.Nauty.Policy.FirstBounded
import all HexGraphIso.Nauty.Policy.Leftmost
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- The first descent changes its boundary only at a deeper failed guard. -/
theorem firstLeaf_boundary {ctx : Ctx n} {tcLevel fuel level numcells last bound saved : Nat}
    {st leaf : Search n} (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hlevel : bound < level) (hin : st.noncheaplevel = saved ∨ bound < st.noncheaplevel) :
    leaf.noncheaplevel = saved ∨ bound < leaf.noncheaplevel := by
  induction hpath with
  | leaf fuel level numcells st hdisc =>
    rw [prepareFirst_noncheap]
    exact hin
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    apply ih (by omega)
    change (cheapCheck true level (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).noncheaplevel = saved ∨
      bound < (cheapCheck true level (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).noncheaplevel
    unfold cheapCheck
    split
    · exact Or.inr (show bound < level + 1 by omega)
    · rw [prepareFirst_noncheap]
      exact hin

/-- A full first-path call retains every surviving older boundary. -/
theorem firstPath_boundary {ctx : Ctx n} {inf tcLevel fuel level numcells last : Nat}
    {st leaf : Search n} (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hlevel : 0 < level) :
    (Engine.node true ctx inf tcLevel fuel level numcells st).2.noncheaplevel = st.noncheaplevel ∨
      level ≤ (Engine.node true ctx inf tcLevel fuel level numcells st).2.noncheaplevel := by
  have hterminal := firstLeaf_boundary hpath (bound := level - 1) (by omega) (Or.inl rfl)
  have h := hpath.bounded (boundaryPolicy ctx inf tcLevel (level - 1) st.noncheaplevel)
    (fun _ _ _ h => h) (by omega) hterminal
  rw [← node_eq_generic] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- A first child returns with the implicit pair at every surviving older boundary. -/
theorem Boundary.firstPath {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n} (h : Boundary G ctx level st) (hn0 : 0 < n) (hlevel : 1 < level)
    (hok : SearchOk G level numcells st.view)
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf) :
    Boundary G ctx level (Engine.node true ctx (n + 2) tcLevel fuel level numcells st).2 :=
  h.of_out hlevel (node_out true hn0 (by omega) hok)
    (firstPath_noncheap hpath (bound := 0) (by omega) h.positive) (firstPath_boundary hpath (by omega))

end Hex.GraphIso.Nauty.Engine
