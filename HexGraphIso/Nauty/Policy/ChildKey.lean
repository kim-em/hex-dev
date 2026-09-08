/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Prepared
public import HexGraphIso.Nauty.Invariant.Child
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- The current child of a recovered sweep has the specification key of
the same vertex in the parent frame, irrespective of its current offset. -/
theorem SweepPre.child_key {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv len offset : Nat} {first : Bool}
    {cell : VSet n} {base st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hframe : SearchOut G level level base.view st.view)
    (hbase : SearchOk G level numcells base.view) (hn0 : 0 < n)
    (hcell : IsCell base.ptn level tc len) (hlen : 2 ≤ len) (hrange : tc + len ≤ n)
    (ho : offset < len) (hv : base.lab[tc + offset]! = tv)
    (hfuel : level + 1 + fuel ≤ n + 1) :
    childKey ctx tcLevel fuel level base.lab base.ptn tc numcells offset =
      specNode ctx tcLevel fuel (level + 1)
        (Engine.child first level tc tv st).lab (Engine.child first level tc tv st).ptn
        (Engine.child first level tc tv st).active (numcells + 1) := by
  apply SearchOut.child_key (child := (Engine.child first level tc tv st).view)
    hframe hbase h.partition hn0 h.positive hcell hlen hrange ho
  · change (Engine.child first level tc tv st).lab = _
    change (Engine.child first level tc tv st).lab =
      (breakout n st.lab st.ptn (level + 1) tc base.lab[tc + offset]!).1
    rw [hv]
    cases first <;> rfl
  · change (Engine.child first level tc tv st).ptn =
      (breakout n st.lab st.ptn (level + 1) tc base.lab[tc + offset]!).2.1
    rw [hv]
    cases first <;> rfl
  · change (Engine.child first level tc tv st).active =
      (breakout n st.lab st.ptn (level + 1) tc base.lab[tc + offset]!).2.2
    rw [hv]
    cases first <;> rfl
  · cases first <;> rfl
  · exact hfuel

end Hex.GraphIso.Nauty.Engine
