/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CheapHistory
public import HexGraphIso.Nauty.Policy.RouteHistory
import all HexGraphIso.Nauty.Policy.CheapHistory
import all HexGraphIso.Nauty.Policy.RouteHistory
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.FirstRef
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The live first-path history retains a general guided descent and the
stronger small-cell descent whenever its common ancestor is cheap. -/
structure History (ctx : Ctx n) (tcLevel level agreed numcells : Nat) (st : Search n) : Prop where
  cheapHistory : CheapHistory ctx tcLevel level agreed numcells st
  route : RouteHistory ctx tcLevel level agreed numcells st

/-- The chosen sweep target follows either the canonical selector or the
saved first path, and agrees with the saved path at cheap ancestors. -/
structure Recorded (ctx : Ctx n) (tcLevel level tc : Nat) (st : Search n) : Prop where
  cheapRecorded : CheapRecorded level tc st
  choice : Choice ctx tcLevel level tc st

/-- Code comparison retains the frozen ancestor and activates the pending node history. -/
theorem History.compare {ctx : Ctx n} {tcLevel level numcells code : Nat} {st : Search n}
    (h : History ctx tcLevel level (level - 1) numcells st)
    (hlevel : 0 < level) (hcode : code < codeSentinel) :
    History ctx tcLevel level level numcells (compareCodes level code st) := by
  exact ⟨h.cheapHistory.compare hlevel hcode, h.route.compare hlevel⟩

/-- A retained target comparison preserves its history and saved sentinel bound. -/
theorem History.target {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : History ctx tcLevel level level numcells st) :
    History ctx tcLevel level level numcells (chooseTarget false ctx tcLevel level numcells st).2.2.2 := by
  exact ⟨h.cheapHistory.target, h.route.target⟩

/-- Classification preserves the live first-path history. -/
theorem History.classify {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : History ctx tcLevel level level numcells st) :
    History ctx tcLevel level level numcells (Nauty.classify ctx level numcells st).2 := by
  exact ⟨h.cheapHistory.classify, h.route.classify⟩

/-- Leaf actions preserve the live first-path history until the receiving frame recovers it. -/
theorem History.leaf {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : History ctx tcLevel level level numcells st) (leaf : Leaf) :
    History ctx tcLevel level level numcells (leafExit leaf level st).2 := by
  exact ⟨h.cheapHistory.leaf leaf, h.route.leaf leaf⟩

/-- A failed guard below the first ancestor cannot make that ancestor cheap. -/
theorem History.cheap {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : History ctx tcLevel level level numcells st) (first : Bool)
    (hg : st.gcaFirst ≤ level) :
    History ctx tcLevel level level numcells (cheapCheck first level st) := by
  exact ⟨h.cheapHistory.cheap first hg, h.route.cheap first⟩

/-- A cheap-boundary update retains the recorded target when its ancestor remains cheap. -/
theorem Recorded.cheap {ctx : Ctx n} {tcLevel level tc : Nat} {st : Search n}
    (h : Recorded ctx tcLevel level tc st) (first : Bool) (hg : st.gcaFirst ≤ level) :
    Recorded ctx tcLevel level tc (cheapCheck first level st) := by
  exact ⟨h.cheapRecorded.cheap first hg, h.choice.cheap first⟩

/-- A target selected at a cheap ancestor is the stored target position. -/
theorem History.recorded {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : History ctx tcLevel level level numcells st) (hnc : numcells < n) (hlevel : 0 < level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let r := chooseTarget false ctx tcLevel level numcells st
    Recorded ctx tcLevel level r.1.toNat r.2.2.2 := by
  exact ⟨h.cheapHistory.recorded hnc hlevel hgsz hsymm hloop,
    h.route.choice hnc hlevel hsymm⟩

/-- A sweep's stored target prepares the next actual child history. -/
theorem History.child {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells tc tv : Nat}
    {st : Search n} {cell : VSet n}
    (h : History ctx tcLevel level level numcells st) (first : Bool)
    (hsize : ctx.g.size = n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true)
    (hrecord : Recorded ctx tcLevel level tc st) :
    let next := Nauty.child first level tc tv st
    let r := visit ctx (level + 1) (numcells + 1) next
    History ctx tcLevel (level + 1) level r.1 r.2.2 := by
  exact ⟨h.cheapHistory.child first hsize hlevel hok htarget htv hrecord.cheapRecorded,
    h.route.child hrecord.choice first hsize hlevel hok htarget htv⟩

/-- Recovering an actual child preserves the history at its receiving ancestor. -/
theorem History.child_return {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv : Nat} {st : Search n} {cell : VSet n}
    (h : History ctx tcLevel level level numcells st) (first : Bool)
    (hg : st.gcaFirst ≤ level) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st)).2
    let result := recoverLevels level (recoverPtn (n + 2) level
      { out with fixedpts := out.fixedpts.erase tv })
    History ctx tcLevel level level numcells result ∧ (Recorded ctx tcLevel level tc st → Recorded ctx tcLevel level tc result) := by
  have hc := h.cheapHistory.child_return (fuel := fuel) first hg hlevel hok htarget htv
  have hr := h.route.child_return (fuel := fuel) first hlevel hok htarget htv
  exact ⟨⟨hc.1, hr.1⟩, fun hrecord => ⟨hc.2 hrecord.cheapRecorded, hr.2 hrecord.choice⟩⟩

/-- The live history supplies the restored first-leaf admission test at every prepared node. -/
theorem History.first_checked {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st out : Search n} (h : History ctx tcLevel level level numcells st)
    (hinv : RunInv G ctx st) (hn0 : 0 < n) (hok : SearchOk G level numcells st)
    (hauto : Nauty.classify ctx level numcells st = (.autoFirst, out))
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    checkAutom ctx.g out.workperm = true := by
  exact h.cheapHistory.first_checked hinv hn0 hok hauto hgsz hsymm hloop

/-- Both automorphism classifications produce a checked scratch permutation. -/
theorem History.checked {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (h : History ctx tcLevel level level numcells st)
    (hinv : RunInv G ctx st) (hn0 : 0 < n) (hok : SearchOk G level numcells st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let r := Nauty.classify ctx level numcells st
    r.1 = .autoFirst ∨ r.1 = .autoCanon → checkAutom ctx.g r.2.workperm = true := by
  exact h.cheapHistory.checked hinv hn0 hok hgsz hsymm hloop

end Hex.GraphIso.Nauty
