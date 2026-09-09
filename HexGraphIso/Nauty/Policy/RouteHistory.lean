/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Choice
import all HexGraphIso.Nauty.Policy.Choice
import all HexGraphIso.Nauty.Policy.Tracking
import all HexGraphIso.Nauty.Policy.FirstRef
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Retain the first descent and the current guided descent at their
common ancestor, including outside the cheap-automorphism region. -/
def RouteHistory (ctx : Ctx n) (tcLevel level agreed numcells : Nat) (st : Search n) : Prop :=
  ∃ root, ∃ _ : FirstRef ctx tcLevel st.gcaFirst root st,
    IterOk ctx st.gcaFirst root ∧ Equitable ctx st.gcaFirst root.lab root.ptn ∧
      bcount root.ptn st.gcaFirst n = root.numcells ∧
      GuidedState ctx tcLevel st.gcaFirst root level agreed numcells st

/-- Operations preserving the reference and common ancestor transport
the guided current descent through their local field changes. -/
theorem RouteHistory.transport {ctx : Ctx n}
    {tcLevel level agreed numcells level' agreed' numcells' : Nat} {st out : Search n}
    (h : RouteHistory ctx tcLevel level agreed numcells st)
    (hr : out.reference = st.reference) (hg : out.gcaFirst = st.gcaFirst)
    (ha : ∀ root, GuidedState ctx tcLevel st.gcaFirst root level agreed numcells st →
      GuidedState ctx tcLevel st.gcaFirst root level' agreed' numcells' out) :
    RouteHistory ctx tcLevel level' agreed' numcells' out := by
  obtain ⟨root, href, hi, he, hc, hroute⟩ := h
  unfold RouteHistory
  rw [hg]
  exact ⟨root, href.congr hr, hi, he, hc, ha root hroute⟩

/-- Comparing a node activates its pending guided history. -/
theorem RouteHistory.compare {ctx : Ctx n} {tcLevel level numcells code : Nat} {st : Search n}
    (h : RouteHistory ctx tcLevel level (level - 1) numcells st) (hlevel : 0 < level) :
    RouteHistory ctx tcLevel level level numcells (compareCodes level code st) :=
  h.transport ((referencePolicy ctx 0 tcLevel).compare level code st)
    ((gcaPolicy ctx 0 tcLevel).compare level code st) (fun _ ha => ha.compare hlevel)

/-- Selecting a target retains every live guided history. -/
theorem RouteHistory.target {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : RouteHistory ctx tcLevel level level numcells st) :
    RouteHistory ctx tcLevel level level numcells
      (chooseTarget false ctx tcLevel level numcells st).2.2.2 :=
  h.transport ((referencePolicy ctx 0 tcLevel).target level numcells st)
    ((gcaPolicy ctx 0 tcLevel).target level numcells st) (fun _ ha => ha.target)

/-- Classification retains the guided current partition. -/
theorem RouteHistory.classify {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : RouteHistory ctx tcLevel level level numcells st) :
    RouteHistory ctx tcLevel level level numcells (Nauty.classify ctx level numcells st).2 :=
  h.transport (classify_reference ctx level numcells st)
    ((gcaPolicy ctx 0 tcLevel).classify level numcells st) (fun _ ha => ha.classify)

/-- Leaf actions retain the guided history until an ancestor receives the exit. -/
theorem RouteHistory.leaf {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : RouteHistory ctx tcLevel level level numcells st) (leaf : Leaf) :
    RouteHistory ctx tcLevel level level numcells (leafExit leaf level st).2 :=
  h.transport (leafExit_reference leaf level st) (leafExit_gca leaf level st)
    (fun _ ha => ha.leaf leaf)

/-- The cheap guard changes neither the guided history nor its common ancestor. -/
theorem RouteHistory.cheap {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : RouteHistory ctx tcLevel level level numcells st) (first : Bool) :
    RouteHistory ctx tcLevel level level numcells (cheapCheck first level st) :=
  h.transport ((referencePolicy ctx 0 tcLevel).cheap first level st)
    ((gcaPolicy ctx 0 tcLevel).cheap first level st) (fun _ ha => ha.cheap first)

/-- Retained target agreement satisfies the guided canonical-or-saved rule. -/
theorem RouteHistory.choice {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : RouteHistory ctx tcLevel level level numcells st) (hnc : numcells < n) (hlevel : 0 < level)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    let r := chooseTarget false ctx tcLevel level numcells st
    Choice ctx tcLevel level r.1.toNat r.2.2.2 := by
  obtain ⟨root, _, hi, he, hc, ha⟩ := h
  exact ha.choice hi he hc hnc hlevel hsymm

/-- Individualizing a guided target prepares the child's pending route. -/
theorem RouteHistory.child {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells tc tv : Nat} {st : Search n} {cell : VSet n}
    (h : RouteHistory ctx tcLevel level level numcells st)
    (hchoice : Choice ctx tcLevel level tc st) (first : Bool)
    (hsize : ctx.g.size = n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    let next := Nauty.child first level tc tv st
    let r := visit ctx (level + 1) (numcells + 1) next
    RouteHistory ctx tcLevel (level + 1) level r.1 r.2.2 := by
  intro next r
  have hg : r.2.2.gcaFirst = st.gcaFirst := by cases first <;> rfl
  have hr : r.2.2.reference = st.reference := by cases first <;> rfl
  obtain ⟨root, href, hi, he, hc, ha⟩ := h
  unfold RouteHistory
  rw [hg]
  exact ⟨root, href.congr hr, hi, he, hc,
    ha.child first hsize hi hlevel hok htarget htv hchoice⟩

/-- The actual child return restores its parent's guided history and
canonical-or-saved target, using the independent frame and divergence proofs. -/
theorem RouteHistory.child_return {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv : Nat} {st : Search n} {cell : VSet n}
    (h : RouteHistory ctx tcLevel level level numcells st) (first : Bool)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st)).2
    let result := recoverLevels level (recoverPtn (n + 2) level
      { out with fixedpts := out.fixedpts.erase tv })
    RouteHistory ctx tcLevel level level numcells result ∧
      (Choice ctx tcLevel level tc st → Choice ctx tcLevel level tc result) := by
  let ch := Nauty.child first level tc tv st
  let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).2
  let left := { out with fixedpts := out.fixedpts.erase tv }
  let result := recoverLevels level (recoverPtn (n + 2) level left)
  have hrch : ch.reference = st.reference := by cases first <;> rfl
  have hrout : out.reference = st.reference :=
    (node_reference ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).trans hrch
  have hr : result.reference = st.reference :=
    ((referencePolicy ctx (n + 2) tcLevel).recover level left).trans hrout
  have hgout : out.gcaFirst = st.gcaFirst := by
    have hc : ch.gcaFirst = st.gcaFirst := by cases first <;> rfl
    exact (node_gca ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).trans hc
  have hg : result.gcaFirst = st.gcaFirst :=
    ((gcaPolicy ctx (n + 2) tcLevel).recover level left).trans hgout
  obtain ⟨root, href, hi, he, hc, ha⟩ := h
  constructor
  · change RouteHistory ctx tcLevel level level numcells result
    unfold RouteHistory
    rw [hg]
    exact ⟨root, href.congr hr, hi, he, hc, ha.child_return first hlevel hok htarget htv⟩
  · intro hchoice
    exact hchoice.child_return ha.bound first hlevel hok htarget htv

end Hex.GraphIso.Nauty
