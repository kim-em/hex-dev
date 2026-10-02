/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RouteTarget
public import HexGraphIso.Nauty.Sparse.RouteKey
import all HexGraphIso.Nauty.Sparse.RouteTarget
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The saved selected reference and the current guided native history at
the actual first ancestor. This invariant applies outside cheap subtrees. -/
def RouteHistory (G : Hex.SparseGraph n) (tcLevel level agreed numcells : Nat) (st : State n) : Prop :=
  ∃ root, ∃ _ : FirstRef G tcLevel st.gcaFirst root st,
    RefineSt.Ready G st.gcaFirst root ∧ RouteAligned G tcLevel st.gcaFirst root level agreed numcells st

namespace RouteHistory

variable {G : Hex.SparseGraph n} {tcLevel level agreed numcells : Nat} {st : State n}

theorem bound (h : RouteHistory G tcLevel level agreed numcells st) : st.eqlevFirst ≤ agreed := by
  obtain ⟨_, _, _, ha⟩ := h
  exact ha.bound

theorem transport {out : State n} {level' agreed' numcells' : Nat}
    (h : RouteHistory G tcLevel level agreed numcells st)
    (hr : out.reference = st.reference) (hg : out.gcaFirst = st.gcaFirst)
    (ha : ∀ root, RouteAligned G tcLevel st.gcaFirst root level agreed numcells st →
      RouteAligned G tcLevel st.gcaFirst root level' agreed' numcells' out) :
    RouteHistory G tcLevel level' agreed' numcells' out := by
  obtain ⟨root, href, hready, halign⟩ := h
  rw [RouteHistory, hg]
  exact ⟨root, href.congr hr, hready, ha root halign⟩

theorem compare (h : RouteHistory G tcLevel level (level - 1) numcells st)
    (hl : 0 < level) (code : Nat) :
    RouteHistory G tcLevel level level numcells (compareCodes level code st) :=
  h.transport ((referencePolicy (.ofGraph G) 0 tcLevel).compare level code st)
    ((gcaPolicy (.ofGraph G) 0 tcLevel).compare level code st) (fun _ ha => ha.compare hl code)

theorem target (h : RouteHistory G tcLevel level level numcells st) :
    RouteHistory G tcLevel level level numcells (chooseTarget false (.ofGraph G) tcLevel level numcells st).2.2.2 :=
  h.transport (chooseTarget_reference (.ofGraph G) tcLevel level numcells st)
    (chooseTarget_controls false (.ofGraph G) tcLevel level numcells st).1 (fun _ ha => ha.target)

theorem classify (h : RouteHistory G tcLevel level level numcells st) :
    RouteHistory G tcLevel level level numcells (Sparse.classify (.ofGraph G) level numcells st).2 :=
  h.transport (classify_reference (.ofGraph G) level numcells st)
    (classify_controls (.ofGraph G) level numcells st).1 (fun _ ha => ha.classify)

theorem leaf (h : RouteHistory G tcLevel level level numcells st) (leaf : Leaf) :
    RouteHistory G tcLevel level level numcells (leafExit leaf level st).2 :=
  h.transport (leafExit_reference leaf level st) (leafExit_gca leaf level st) (fun _ ha => ha.leaf leaf)

theorem cheap (h : RouteHistory G tcLevel level level numcells st) (first : Bool) :
    RouteHistory G tcLevel level level numcells (cheapCheck first level st) :=
  h.transport ((referencePolicy (.ofGraph G) 0 tcLevel).cheap first level st)
    ((gcaPolicy (.ofGraph G) 0 tcLevel).cheap first level st) (fun _ ha => ha.cheap first)

end RouteHistory

/-- Guided target choices extend both reference histories through the
actual individualized child and its cached refinement. -/
theorem RouteHistory.child {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells tc tv : Nat}
    {st : State n} {cell : VSet n}
    (h : RouteHistory G.graph tcLevel level level numcells st) (first : Bool)
    (hok : Ready G level numcells st) (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) (hrecord : RouteRecorded G.graph tcLevel level tc st) :
    let next := (policy (n := n)).child first level tc tv st
    let r := visit (.ofGraph G.graph) (level + 1) (numcells + 1) next
    RouteHistory G.graph tcLevel (level + 1) level r.1 r.2.2 := by
  intro next r
  have hg : r.2.2.gcaFirst = st.gcaFirst := by cases first <;> rfl
  have hr : r.2.2.reference = st.reference := by cases first <;> rfl
  obtain ⟨root, href, hready, ha⟩ := h
  rw [RouteHistory, hg]
  exact ⟨root, href.congr hr, hready, ha.child first hready hok ht hv hrecord⟩

/-- An actual off-path child retains the guided history and target choice
at its recovered parent. The proof uses full-call frame and divergence
results, including for a truncated child call. -/
theorem RouteHistory.child_return {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv : Nat} {st : State n} {cell : VSet n}
    (h : RouteHistory G.graph tcLevel level level numcells st) (first : Bool)
    (hl : 1 ≤ level) (hok : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st)).2
    let result := (policy (n := n)).recover (n + 2) level ((policy (n := n)).leaveChild tv out)
    RouteHistory G.graph tcLevel level level numcells result ∧
      (RouteRecorded G.graph tcLevel level tc st → RouteRecorded G.graph tcLevel level tc result) := by
  let ch := (policy (n := n)).child first level tc tv st
  let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).2
  let left := (policy (n := n)).leaveChild tv out
  let result := (policy (n := n)).recover (n + 2) level left
  have hrch : ch.reference = st.reference := by cases first <;> rfl
  have hrout : out.reference = st.reference :=
    (node_reference (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).trans hrch
  have hr : result.reference = st.reference :=
    ((referencePolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left).trans hrout
  have hgout : out.gcaFirst = st.gcaFirst := by
    have hc : ch.gcaFirst = st.gcaFirst := by cases first <;> rfl
    exact (node_gca (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).trans hc
  have hgr : result.gcaFirst = st.gcaFirst :=
    ((gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left).trans hgout
  obtain ⟨root, href, hready, ha⟩ := h
  refine ⟨?_, ?_⟩
  · change RouteHistory G.graph tcLevel level level numcells result
    rw [RouteHistory, hgr]
    exact ⟨root, href.congr hr, hready, ha.child_return first fuel hl hok ht hv⟩
  · intro hrecord hmatch
    change result.eqlevFirst = level at hmatch
    have heq : st.eqlevFirst = level := by
      by_cases he : st.eqlevFirst = level
      · exact he
      · have hb := ha.bound
        have hch : ch.eqlevFirst < level := by cases first <;> change st.eqlevFirst < level <;> omega
        have ho : out.eqlevFirst < level := node_diverged (by omega) hch
        have hle := recover_le (n + 2) level left
        change result.eqlevFirst ≤ out.eqlevFirst at hle
        omega
    rcases hrecord heq with hchoice | hchoice
    · left
      have hn : 0 < n := by have := VSet.mem_lt hv; omega
      have hch := hok.child hn hl first ht hv
      have ho := node_frame G hn false tcLevel fuel (level + 1) (numcells + 1) ch (by omega) hch
      have hf := hok.child_frame hn hl first ht hv (by simpa only [Nat.add_sub_cancel] using ho)
      exact hchoice.trans (hok.target_recover hn hl (hf.leave tv)).symm
    · right
      have htc := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) hr
      change result.firsttc = st.firsttc at htc
      rw [htc]
      exact hchoice

end Hex.GraphIso.Nauty.Sparse
