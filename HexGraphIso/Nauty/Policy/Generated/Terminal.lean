/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Generated.Tail
public import HexGraphIso.Nauty.Policy.First.Complete
import all HexGraphIso.Nauty.Policy.Generated.Tail
import all HexGraphIso.Nauty.Policy.Generated.Cover
import all HexGraphIso.Nauty.Policy.Generated.Trace
import all HexGraphIso.Nauty.Policy.First.Complete
import all HexGraphIso.Nauty.Policy.First.Tail
import all HexGraphIso.Nauty.Policy.First.Witness
import all HexGraphIso.Nauty.Policy.First.Bounds
import all HexGraphIso.Nauty.Policy.First.History
import all HexGraphIso.Nauty.Policy.First.Ref
import all HexGraphIso.Nauty.Policy.Max.First
import all HexGraphIso.Nauty.Policy.Max.Position
import all HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Init
import all HexGraphIso.Nauty.Policy.Max.Node
import all HexGraphIso.Nauty.Policy.Max.ReturnTrace
import all HexGraphIso.Nauty.Policy.Max.Receive
import all HexGraphIso.Nauty.Policy.Max.Resume
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.TraceContains
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Generation.Frame
import all HexGraphIso.Nauty.Generation.RefPath
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.Generic

import all HexGraphIso.Nauty.Policy.First.Entry
import all HexGraphIso.Nauty.Policy.Max.Prepare
import all HexGraphIso.Nauty.Generation.Stabilizer

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- First-node preparation leaves the individualized base unchanged. -/
theorem first_fixed (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    (cheapCheck true level (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).fixedpts =
      st.fixedpts := by
  unfold cheapCheck
  split
  all_goals change (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.fixedpts = st.fixedpts
  all_goals unfold Generic.prepareFirst
  all_goals change (chooseTarget true ctx tcLevel level _ _).2.2.2.fixedpts = st.fixedpts
  all_goals rw [chooseFirst_fields]
  all_goals rfl

/-- A discrete first node has trivial point stabilizer. -/
theorem first_terminal {G : Colored n k} {tcLevel fuel level numcells : Nat} {st : Search n}
    {cs bs fs : List Nat} {parents : Parents n}
    (hi : NodeInput G { g := rowsOf G } tcLevel fuel true ⟨level, numcells, cs, st⟩ bs fs parents)
    {base : List (Fin n)}
    (hbase : ∀ b : Fin n, st.fixedpts.mem b.val = true ↔ b ∈ base)
    (hdisc : (Generic.prepareFirst { g := rowsOf G } tcLevel level numcells st).1 = n)
    {p : Perm n} (hp : IsIso G G p) (hfix : Perm.Fixes base p) : p = Perm.id n := by
  let ctx : Ctx n := { g := rowsOf G }
  let l : Loop n := ⟨⟨level, numcells, cs, st⟩, true⟩
  let ready := (l.prepare ctx tcLevel).2.2.2.2
  have hn0 : 0 < n := by have := hi.frame.positive; have := hi.frame.depth; omega
  have hok := l.prepare_ok (ctx := ctx) (tcLevel := tcLevel) hi.frame
  have hpath := (hi.entry.1.prepare_path hn0 (size_rowsOf G) tcLevel).cheap true
  have he : ready.fixedpts = st.fixedpts := first_fixed ctx tcLevel level numcells st
  apply Nauty.Generation.terminal hpath.stab hok.labSize
    (achieved_perm_range hok.labSize hn0 hok.reach) hok.ptnSize
    (searchOk_end hn0 hok hi.frame.positive) _ hp
    (fun b hb => hfix b ((hbase b).mp (by change ready.fixedpts.mem b.val = true at hb; rwa [he] at hb)))
  apply (discreteAt_iff_bcount hok.ptnSize.symm (searchOk_end hn0 hok hi.frame.positive)).mpr
  rw [← hok.count]
  exact hdisc

end Hex.GraphIso.Nauty.Max
