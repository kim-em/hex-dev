/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.AlignedTarget
public import HexGraphIso.Nauty.Sparse.Controls
public import HexGraphIso.Nauty.Sparse.CheapAdmission
import all HexGraphIso.Nauty.Sparse.DescentAt
import all HexGraphIso.Nauty.Sparse.FirstRef
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Whenever the cheap guard admits the frozen first ancestor, its actual
saved descent and the current aligned native descent remain available. -/
def CheapHistory (G : Hex.SparseGraph n) (tcLevel level agreed numcells : Nat) (st : State n) : Prop :=
  st.noncheaplevel ≤ st.gcaFirst →
    ∃ root, ∃ href : FirstRef G tcLevel st.gcaFirst root st,
      Depth href.last st ∧ RefineSt.Ready G st.gcaFirst root ∧ NodeShape n st.gcaFirst root.ptn ∧
        Aligned G st.gcaFirst root level agreed numcells st

namespace CheapHistory

variable {G : Hex.SparseGraph n} {tcLevel level agreed numcells : Nat} {st : State n}

theorem transport {out : State n} {level' agreed' numcells' : Nat}
    (h : CheapHistory G tcLevel level agreed numcells st)
    (hr : out.reference = st.reference) (hg : out.gcaFirst = st.gcaFirst)
    (hn : out.noncheaplevel ≤ st.gcaFirst → st.noncheaplevel ≤ st.gcaFirst)
    (hd : ∀ last, Depth last st → Depth last out)
    (ha : ∀ root, Aligned G st.gcaFirst root level agreed numcells st →
      Aligned G st.gcaFirst root level' agreed' numcells' out) :
    CheapHistory G tcLevel level' agreed' numcells' out := by
  intro hcheap
  rw [hg] at hcheap ⊢
  obtain ⟨root, href, hdepth, hready, hshape, halign⟩ := h (hn hcheap)
  exact ⟨root, href.congr hr, hd href.last hdepth, hready, hshape, ha root halign⟩

theorem compare (h : CheapHistory G tcLevel level (level - 1) numcells st)
    (hl : 0 < level) {code : Nat} (hc : code < codeSentinel) :
    CheapHistory G tcLevel level level numcells (compareCodes level code st) := by
  apply h.transport (out := compareCodes level code st)
    ((referencePolicy (.ofGraph G) 0 tcLevel).compare level code st)
    ((gcaPolicy (.ofGraph G) 0 tcLevel).compare level code st)
  · unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]
    exact id
  · intro last hd
    exact compareCodes_depth hd hc
  · intro root ha
    exact ha.compare hl code

theorem target (h : CheapHistory G tcLevel level level numcells st) :
    CheapHistory G tcLevel level level numcells (chooseTarget false (.ofGraph G) tcLevel level numcells st).2.2.2 := by
  have hr := chooseTarget_reference (.ofGraph G) tcLevel level numcells st
  have hc := chooseTarget_controls false (.ofGraph G) tcLevel level numcells st
  apply h.transport hr hc.1
  · rw [hc.2]; exact id
  · intro last hd
    exact hd.mono (chooseTarget_le (.ofGraph G) tcLevel level numcells st) hr
  · intro root ha
    exact ha.target tcLevel

theorem classify (h : CheapHistory G tcLevel level level numcells st) :
    CheapHistory G tcLevel level level numcells (Sparse.classify (.ofGraph G) level numcells st).2 := by
  have hr := classify_reference (.ofGraph G) level numcells st
  have hc := classify_controls (.ofGraph G) level numcells st
  apply h.transport hr hc.1
  · rw [hc.2]; exact id
  · intro last hd
    exact hd.mono (Nat.le_of_eq (classify_eqlev (.ofGraph G) level numcells st)) hr
  · intro root ha
    exact ha.classify

theorem leaf (h : CheapHistory G tcLevel level level numcells st) (leaf : Leaf) :
    CheapHistory G tcLevel level level numcells (leafExit leaf level st).2 := by
  apply h.transport (leafExit_reference leaf level st) (leafExit_gca leaf level st)
  · rw [leafExit_noncheap]; exact id
  · intro last hd
    exact hd.mono (Nat.le_of_eq (leafExit_eqlev leaf level st)) (leafExit_reference leaf level st)
  · intro root ha
    exact ha.leaf leaf

theorem cheap (h : CheapHistory G tcLevel level level numcells st) (first : Bool)
    (hg : st.gcaFirst ≤ level) :
    CheapHistory G tcLevel level level numcells (cheapCheck first level st) := by
  apply h.transport (out := cheapCheck first level st)
    ((referencePolicy (.ofGraph G) 0 tcLevel).cheap first level st)
    ((gcaPolicy (.ofGraph G) 0 tcLevel).cheap first level st)
  · unfold cheapCheck
    split
    · change level + 1 ≤ st.gcaFirst → _; omega
    · exact id
  · intro last hd
    unfold cheapCheck
    split <;> exact hd
  · intro root ha
    exact ha.cheap first

end CheapHistory

/-- A sweep target agrees with the first target when its ancestor is cheap
and the live code comparison still reaches this level. -/
def CheapRecorded (level tc : Nat) (st : State n) : Prop :=
  st.noncheaplevel ≤ st.gcaFirst → st.eqlevFirst = level → st.firsttc[level]! = Int.ofNat tc

theorem CheapRecorded.cheap {level tc : Nat} {st : State n}
    (h : CheapRecorded level tc st) (first : Bool) (hg : st.gcaFirst ≤ level) :
    CheapRecorded level tc (cheapCheck first level st) := by
  unfold cheapCheck
  split
  · intro hc
    change level + 1 ≤ st.gcaFirst at hc
    omega
  · exact h

/-- The native cached selector records the target needed for every next
child whenever its frozen cheap history stays active. -/
theorem CheapHistory.recorded {G : Hex.SparseGraph n} {tcLevel level numcells : Nat} {st : State n}
    (h : CheapHistory G tcLevel level level numcells st) (hnc : numcells < n)
    (hs : Scratch.Valid n st.lab st.ptn level st.canong.scratch) :
    let r := chooseTarget false (.ofGraph G) tcLevel level numcells st
    CheapRecorded level r.1.toNat r.2.2.2 := by
  intro r hcheap hkeep
  have hc := chooseTarget_controls false (.ofGraph G) tcLevel level numcells st
  have ht := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
    (chooseTarget_reference (.ofGraph G) tcLevel level numcells st)
  change r.2.2.2.firsttc = st.firsttc at ht
  obtain ⟨root, href, hd, hr, hshape, ha⟩ := h (by rwa [hc.1, hc.2] at hcheap)
  have hpos := ha.target_eq href hd hkeep hnc hr hshape hs
  have hold : st.eqlevFirst = level := by
    have hb := ha.bound
    have hle := chooseTarget_le (.ofGraph G) tcLevel level numcells st
    change r.2.2.2.eqlevFirst ≤ st.eqlevFirst at hle
    omega
  change r.2.2.2.firsttc[level]! = Int.ofNat r.1.toNat
  rw [ht, chooseTarget_cast hnc hold]
  exact hpos.symm

/-- A stored sweep target extends the current history through the actual
native individualization and its cached child refinement. -/
theorem CheapHistory.child {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells tc tv : Nat}
    {st : State n} {cell : VSet n}
    (h : CheapHistory G.graph tcLevel level level numcells st) (first : Bool)
    (hok : Ready G level numcells st) (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) (hrecord : CheapRecorded level tc st) :
    let next := (policy (n := n)).child first level tc tv st
    let r := visit (.ofGraph G.graph) (level + 1) (numcells + 1) next
    CheapHistory G.graph tcLevel (level + 1) level r.1 r.2.2 := by
  intro next r hcheap
  have hg : r.2.2.gcaFirst = st.gcaFirst := by cases first <;> rfl
  have hn : r.2.2.noncheaplevel = st.noncheaplevel := by cases first <;> rfl
  have hr : r.2.2.reference = st.reference := by cases first <;> rfl
  have hc : st.noncheaplevel ≤ st.gcaFirst := by rwa [hg, hn] at hcheap
  obtain ⟨root, href, hd, hready, hshape, ha⟩ := h hc
  rw [hg]
  refine ⟨root, href.congr hr, ?_, hready, hshape, ?_⟩
  · cases first <;> exact hd
  · exact ha.child first hready hok ht hv (hrecord hc)

/-- An actual off-path child preserves both the frozen cheap history and
the parent's recorded target after leaving the child and recovering the
native partition and cache. This holds even for a truncated child call. -/
theorem CheapHistory.child_return {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv : Nat} {st : State n} {cell : VSet n}
    (h : CheapHistory G.graph tcLevel level level numcells st) (first : Bool)
    (hg : st.gcaFirst ≤ level) (hl : 1 ≤ level) (hok : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st)).2
    let result := (policy (n := n)).recover (n + 2) level ((policy (n := n)).leaveChild tv out)
    CheapHistory G.graph tcLevel level level numcells result ∧
      (CheapRecorded level tc st → CheapRecorded level tc result) := by
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
  have cheapBack : result.noncheaplevel ≤ result.gcaFirst → st.noncheaplevel ≤ st.gcaFirst := by
    intro hcheap
    by_cases hc : st.noncheaplevel ≤ st.gcaFirst
    · exact hc
    · have hch : st.gcaFirst < ch.noncheaplevel := by cases first <;> exact Nat.lt_of_not_ge hc
      have ho : st.gcaFirst < out.noncheaplevel := node_noncheap (by omega) hch
      have he : result.noncheaplevel = if level < left.noncheaplevel then level + 1 else left.noncheaplevel :=
        recover_noncheap (n + 2) level left
      rw [hgr, he] at hcheap
      change st.gcaFirst < left.noncheaplevel at ho
      split at hcheap <;> omega
  change CheapHistory G.graph tcLevel level level numcells result ∧
    (CheapRecorded level tc st → CheapRecorded level tc result)
  constructor
  · intro hcheap
    obtain ⟨root, href, hd, hready, hshape, ha⟩ := h (cheapBack hcheap)
    rw [hgr]
    refine ⟨root, href.congr hr, ?_, hready, hshape, ha.child_return first tcLevel fuel hl hok ht hv⟩
    have hdch : Depth href.last ch := by cases first <;> exact hd
    have hdout : Depth href.last out := node_depth hdch
    exact hdout.mono (recover_le (n + 2) level left)
      ((referencePolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left)
  · intro hrecord hcheap hmatch
    have hc := cheapBack hcheap
    obtain ⟨root, href, hd, hready, hshape, ha⟩ := h hc
    have heq : st.eqlevFirst = level := by
      by_cases he : st.eqlevFirst = level
      · exact he
      · have hb := ha.bound
        have hch : ch.eqlevFirst < level := by cases first <;> change st.eqlevFirst < level <;> omega
        have ho : out.eqlevFirst < level := node_diverged (by omega) hch
        have hle := recover_le (n + 2) level left
        change result.eqlevFirst ≤ out.eqlevFirst at hle
        omega
    have htc := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) hr
    change result.firsttc = st.firsttc at htc
    rw [htc]
    exact hrecord hc heq

/-- The retained native history justifies first-reference admission in
both guard arms. The saved sentinel supplies the depth bound independently
of the incumbent comparison invariant. -/
theorem CheapHistory.first_iso {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {st out : State n} {l f : Label n}
    (h : CheapHistory G.graph tcLevel level level numcells st)
    (hauto : Sparse.classify (.ofGraph G.graph) level numcells st = (.autoFirst, out))
    (hw : st.workperm.size = n) (hl : Label.ofArray? n st.lab = some l)
    (hf : Label.ofArray? n st.firstlab = some f)
    (hrl : CellsReach G.toDense st.lab) (hrf : CellsReach G.toDense st.firstlab) :
    GraphIso.Sparse.IsIso G G (l.perm.comp f.perm.inv) ∧
      ∀ v : Fin n, out.workperm[v.val]! = ((l.perm.comp f.perm.inv).get v).val := by
  by_cases hcheap : st.noncheaplevel ≤ st.gcaFirst
  · obtain ⟨root, href, hd, hr, hshape, ha⟩ := h hcheap
    obtain ⟨hnc, heq, hout, _⟩ := classify_first hauto
    obtain ⟨current, hc, hp, hcl, hcp, hcount⟩ := ha.descent heq
    have hdisc : discreteAt current.ptn level n = true := by
      apply (discreteAt_iff_bcount hc.spec.node.ptnSize.symm hc.spec.node.ptnEnd).mpr
      rw [← hc.spec.count, hcount, hnc]
    have hgraph := (href.leaf_follows (by have := hd.1; omega) hr hc hshape hp hdisc hf
      (by rw [hcl]; exact hl)).2
    rw [hout]
    exact ⟨label_pair_iso G hl hf hrl hrf hgraph, scatter_perm hw hf hl⟩
  · exact classify_first_scan G hauto (by omega) hw hl hf hrl hrf

end Hex.GraphIso.Nauty.Sparse
