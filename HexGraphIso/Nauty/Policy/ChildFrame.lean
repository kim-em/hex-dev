/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CallState
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Policy.Fixed
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Leaving an actual child restores the parent's fixed set and preserves
its partition frame, before any pruning or partition recovery occurs. -/
theorem child_frame {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SearchOk G level numcells st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hpath : FixedCells level st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (ht : cell.mem tv = true)
    (childFirst : Bool) :
    let raw := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    let out := { raw with fixedpts := raw.fixedpts.erase tv }
    SearchOut G level level st out ∧ out.fixedpts = st.fixedpts := by
  intro raw out
  have hc := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hlevel h htarget ht
  dsimp only [policy, Generic.Policy.child] at hc
  have hfixed := fixed_child first hn0 h hpath htarget ht
  have ho := node_out (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) childFirst hn0
    (by omega) hc.1
  have hf := node_fixed (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) childFirst hn0
    (by omega) hc.1 hfixed.2
  have hp := hc.2 raw (by simpa only [Nat.add_sub_cancel] using ho)
  refine ⟨hp.congr rfl rfl rfl rfl, ?_⟩
  apply fixed_restore (base := st) (out := raw) ?_ hfixed.1
  exact hf.trans (by cases first <;> rfl)

/-- Later siblings restore their fixed set before applying the returned filter. -/
theorem SweepPre.child_frame {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (childFirst : Bool) :
    let raw := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    let out := { raw with fixedpts := raw.fixedpts.erase tv }
    SearchOut G level level st out ∧ out.fixedpts = st.fixedpts :=
  Nauty.child_frame h.partition hn0 h.positive h.path.fixed h.target (h.cursor_mem tv rfl) childFirst

end Hex.GraphIso.Nauty
