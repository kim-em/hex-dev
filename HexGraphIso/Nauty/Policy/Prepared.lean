/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CallState
public import HexGraphIso.Nauty.Policy.Calls
public import HexGraphIso.Nauty.Policy.EquitableState
public import HexGraphIso.Nauty.Policy.PathState
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.HistoryState
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- Refinement, comparison and target selection at an off-path node. -/
@[expose] def prepareOther (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    Nat × Nat × (Int × VSet n × Nat × Search n) :=
  let r := visit ctx level numcells st
  (r.1, r.2.1, chooseTarget false ctx tcLevel level r.1 (compareCodes level r.2.1 r.2.2))

/-- A target selected from a non-discrete reached partition contains a vertex. -/
theorem maketargetcell_nonempty {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {st : Search n} (hint : Int)
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st.view)
    (hnc : numcells < n) :
    (maketargetcell ctx st.lab st.ptn level tcLevel hint).2.1 ≠ VSet.empty := by
  have hend := searchOk_end hn0 hok hlevel
  have hlive : bcount st.ptn level n < n := by
    have hc := hok.count
    change numcells = bcount st.ptn level n at hc
    omega
  obtain ⟨tc, len, hr, _, hlen, hrange⟩ :=
    maketargetcell_open (ctx := ctx) (lab := st.lab) (ptn := st.ptn) (tcLevel := tcLevel) (hint := hint)
      hlevel hok.ptnSize hend hlive
  rw [hr]
  have hmem : (worksetOf n st.lab tc (tc + len - 1)).mem st.lab[tc]! = true := by
    apply mem_worksetOf_iff.mpr
    refine ⟨labOk_of_reach hok.labSize hok.reach tc (by rw [hok.labSize]; omega), ?_⟩
    apply mem_segN_iff.mpr
    exact ⟨0, by omega, by simp⟩
  intro he
  dsimp only at he
  rw [he] at hmem
  simp at hmem

/-- A continuing node with an upward comparison has a first child to
settle that comparison before any sibling filter can run. -/
theorem chooseTarget_phase {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st.view) :
    let t := chooseTarget false ctx tcLevel level numcells st
    (classify ctx level numcells t.2.2.2).1 = .internal →
      t.2.2.2.compCanon ≤ 0 ∨ (t.2.1.nextElem none).isSome := by
  dsimp only
  intro hi
  by_cases hc : st.compCanon ≤ 0
  · left
    rwa [chooseTarget_fields]
  · right
    have hnc : numcells < n := by
      have hne := ((classify_internal _ _ _ _).mp hi).2
      have hcount := hok.count
      have hbound := bcount_le st.ptn level n
      change numcells = bcount st.ptn level n at hcount
      omega
    have hn : (chooseTarget false ctx tcLevel level numcells st).2.1 ≠ VSet.empty := by
      unfold chooseTarget
      simp only [Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and,
        hnc, decide_true, show ¬st.compCanon < 0 by omega, decide_false,
        show 0 ≤ st.compCanon by omega, Bool.or_true, Bool.and_self, ite_true]
      exact maketargetcell_nonempty _ hn0 hlevel hok hnc
    rw [VSet.nextElem_none_eq_minElem hn]
    rfl

/-- An off-path node enters its sweep with a settled comparison or a
nonempty target whose first child will settle it. -/
theorem NodePre.phase {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (h : NodePre G ctx tcLevel level numcells st) (hn0 : 0 < n) :
    let p := prepareOther ctx tcLevel level numcells st
    let t := p.2.2
    (classify ctx level p.1 t.2.2.2).1 = .internal →
      t.2.2.2.compCanon ≤ 0 ∨ (t.2.1.nextElem none).isSome := by
  have hv := ((reachPolicy G ctx tcLevel hn0).visit level numcells st h.positive h.partition).1
  have hc := ((reachPolicy G ctx tcLevel hn0).compare level
    (visit ctx level numcells st).2.1 (visit ctx level numcells st).1
    (visit ctx level numcells st).2.2 hv).ok
  exact chooseTarget_phase hn0 h.positive hc

/-- Preparing an off-path node supplies the checked leaf action and the
complete sweep precondition whenever classification continues. -/
theorem NodePre.prepare {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (hin : NodePre G ctx tcLevel level numcells st)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let p := prepareOther ctx tcLevel level numcells st
    let t := p.2.2
    let state := t.2.2.2
    SearchOk G level p.1 state.view ∧ RunInv G ctx state ∧
      History ctx tcLevel level level p.1 state ∧
      (let c := classify ctx level p.1 state
       RunInv G ctx (leafExit c.1 level c.2).2) ∧
      ((classify ctx level p.1 state).1 = .internal →
        SweepPre G ctx tcLevel false level p.1 t.1.toNat
          ((t.2.1.nextElem none).getD 0) (t.2.1.nextElem none) t.2.1
          (cheapCheck false level state)) := by
  have hv := ((reachPolicy G ctx tcLevel hn0).visit level numcells st hin.positive hin.partition).1
  dsimp only [policy, Generic.Policy.visit] at hv
  have hvpath := hin.path.visit hn0 hin.positive hgsz hin.partition hin.starts
  have hvi := hin.stored.visit level numcells
  have hve : Equitable ctx level (visit ctx level numcells st).2.2.lab
      (visit ctx level numcells st).2.2.ptn := hin.equitable
  have hvb := hin.boundary.visit (numcells := numcells) hin.positive
  have hvn : (visit ctx level numcells st).2.2.noncheaplevel ≤ level := hin.cheapBound
  have hvl : (visit ctx level numcells st).2.2.lab = (st.refined ctx level numcells).lab := rfl
  have hvp : (visit ctx level numcells st).2.2.ptn = (st.refined ctx level numcells).ptn := rfl
  have hvh := hin.history
  have hvg : (visit ctx level numcells st).2.2.gcaFirst < level := hin.ancestor
  have hcode := refine_longcode_lt ctx level st.lab st.ptn st.active numcells
  change (visit ctx level numcells st).2.1 < codeSentinel at hcode
  unfold prepareOther
  generalize hvval : visit ctx level numcells st = r at hv hvi hvh hvg hcode hve hvb hvn hvl hvp hvpath ⊢
  obtain ⟨nc, code, refined⟩ := r
  dsimp only
  let compared := compareCodes level code refined
  have hci := hvi.compare level code
  have hch := hvh.compare hin.positive hcode
  have hcp := ((reachPolicy G ctx tcLevel hn0).compare level code nc refined hv).ok
  have hcg : compared.gcaFirst < level := by
    rw [show compared.gcaFirst = refined.gcaFirst from (gcaPolicy ctx 0 tcLevel).compare level code refined]
    exact hvg
  have htpath := (hvpath.compare code).target false tcLevel nc
  have ht := (reachPolicy G ctx tcLevel hn0).target false level nc compared hin.positive hcp
  dsimp only [policy, Generic.Policy.chooseTarget] at ht
  have htb := (hvb.compare code).target false tcLevel nc
  have htn : (chooseTarget false ctx tcLevel level nc compared).2.2.2.noncheaplevel ≤ level := by
    rw [target_noncheap, compare_noncheap]
    exact hvn
  have htl := (chooseTarget_frame false ctx tcLevel level nc compared).1.trans
    ((compareCodes_frame level code refined).1.trans hvl)
  have htp := (chooseTarget_frame false ctx tcLevel level nc compared).2.1.trans
    ((compareCodes_frame level code refined).2.1.trans hvp)
  have hti := hci.target tcLevel level nc
  have hte : Equitable ctx level (chooseTarget false ctx tcLevel level nc compared).2.2.2.lab
      (chooseTarget false ctx tcLevel level nc compared).2.2.2.ptn := by
    rw [(chooseTarget_frame false ctx tcLevel level nc compared).1,
      (chooseTarget_frame false ctx tcLevel level nc compared).2.1,
      (compareCodes_frame level code refined).1, (compareCodes_frame level code refined).2.1]
    exact hve
  have hth := hch.target
  have htg : (chooseTarget false ctx tcLevel level nc compared).2.2.2.gcaFirst < level := by
    rw [show (chooseTarget false ctx tcLevel level nc compared).2.2.2.gcaFirst = compared.gcaFirst from
      (gcaPolicy ctx 0 tcLevel).target level nc compared]
    exact hcg
  have hrecord : nc < n → Recorded ctx tcLevel level (chooseTarget false ctx tcLevel level nc compared).1.toNat
      (chooseTarget false ctx tcLevel level nc compared).2.2.2 :=
    fun hnc => hch.recorded hnc hin.positive hgsz hsymm hloop
  generalize htval : chooseTarget false ctx tcLevel level nc compared = t at ht hti hth htg hrecord hte htb htn htl htp htpath ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  change targeted.gcaFirst < level at htg
  obtain ⟨htlocal, htarget⟩ := ht
  have hclb := htb.classify nc
  have hcln : (classify ctx level nc targeted).2.noncheaplevel ≤ level := by
    rw [classify_noncheap]; exact htn
  have hcli := hti.classify level nc
  have hclp := ((reachPolicy G ctx tcLevel hn0).classify level nc targeted htlocal.ok).ok
  dsimp only [policy, Generic.Policy.classify] at hclp
  have hclv := classify_store hti.cache (level := level) (numcells := nc)
  have hcheck := hth.checked hti hn0 htlocal.ok hgsz hsymm hloop
  have hcolor := classify_stab hn0 hti.scratch hti.firstSize hti.firstReach
    hti.canonical.1 hti.canonical.2 htlocal.ok.reach (ctx := ctx) (level := level) (numcells := nc)
  refine ⟨htlocal.ok, hti, hth, ?_, ?_⟩
  · exact hcli.leaf (classify ctx level nc targeted).1 hclp hclv.2 hcheck hcolor hn0 hclb hcln
  intro hcfirst
  have hnc : nc < n := by
    have hne := ((classify_internal ctx level nc targeted).mp hcfirst).2
    have hb := bcount_le targeted.ptn level n
    have hc := htlocal.ok.count
    change nc = bcount targeted.ptn level n at hc
    omega
  have hcheap := (reachPolicy G ctx tcLevel hn0).cheap false level nc targeted htlocal.ok
  have hcheapBoundary : Boundary G ctx (level + 1) (cheapCheck false level targeted) := by
    apply htb.cheap false hin.positive
    intro hguard
    rw [htp] at hguard
    rw [htl, htp]
    exact refined_pair hn0 hin.positive hin.partition hin.equitable hgsz hsymm hloop hguard
  have hnextPre : SweepPre G ctx tcLevel false level nc tc.toNat
      ((cell.nextElem none).getD 0) (cell.nextElem none) cell (cheapCheck false level targeted) :=
    ⟨(by intro hf; cases hf), hin.positive, hcheap.ok, htarget.of_out hcheap.effect,
      (fun _ hv => VSet.nextElem_mem hv), hti.cheap false level,
      (by rw [show (cheapCheck false level targeted).gcaFirst = targeted.gcaFirst from
            (gcaPolicy ctx 0 tcLevel).cheap false level targeted]; omega),
      hth.cheap false (by change targeted.gcaFirst ≤ level; omega),
      (hrecord hnc).cheap false (by change targeted.gcaFirst ≤ level; omega),
      (by unfold cheapCheck; split <;> exact hte), hcheapBoundary, cheap_bound false htn, htpath.cheap false⟩
  exact hnextPre

/-- An eligible sweep entry supplies the precondition of its off-path child. -/
theorem SweepPre.child {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells tc tv1 tv : Nat}
    {first : Bool} {cell : VSet n} {st : Search n}
    (hin : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    NodePre G ctx tcLevel (level + 1) (numcells + 1) (Engine.child first level tc tv st) := by
  have htv := hin.cursor_mem tv rfl
  have hch := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hin.positive hin.partition hin.target htv
  dsimp only [policy, Generic.Policy.child] at hch
  have hnodePre : NodePre G ctx tcLevel (level + 1) (numcells + 1) (Engine.child first level tc tv st) :=
    ⟨(by have := hin.positive; omega), hch.1, hin.stored.child first level tc tv,
      (by cases first <;> change st.gcaFirst < level + 1 <;> have := hin.ancestor <;> omega),
      (by simpa only [Nat.add_sub_cancel] using
        hin.history.child first hgsz hin.positive hin.partition hin.target htv hin.recorded),
      child_equitable first hn0 hin.positive hin.partition hin.equitable hin.target htv hsymm,
      hin.boundary.child first hin.positive hin.target htv, (by cases first <;> exact hin.cheapBound),
      hin.path.child first hn0 hin.positive hin.partition hin.target htv, child_starts first hin.target htv⟩
  exact hnodePre

/-- Advancing to a surviving larger entry retains the sweep's local invariants. -/
theorem SweepPre.next {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells tc tv1 tv : Nat}
    {first : Bool} {cell smaller : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hsub : ∀ v, smaller.mem v = true → cell.mem v = true) :
    SweepPre G ctx tcLevel first level numcells tc tv1 (smaller.nextElem (some tv)) smaller st :=
  ⟨Generic.Past.next (fun hf => h.past hf tv rfl), h.positive, h.partition, h.target.subset hsub,
    (fun _ hv => VSet.nextElem_mem hv), h.stored, h.ancestor, h.history, h.recorded,
    h.equitable, h.boundary, h.cheapBound, h.path⟩

/-- Returning from the actual off-path child restores the parent
history, fixed points, and local stabilizer ledger. -/
theorem SweepPre.restore {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool} {cell : VSet n} {st : Search n}
    (hin : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hstored : RunInv G ctx (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2) :
    let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2
    let left := { out with fixedpts := out.fixedpts.erase tv }
    SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell
      (recoverLevels level (recoverPtn (n + 2) level left)) := by
  have htv := hin.cursor_mem tv rfl
  have hnodePre := hin.child hn0 hgsz hsymm
  have hch := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hin.positive hin.partition hin.target htv
  dsimp only [policy, Generic.Policy.child] at hch
  have hfixout := node_fixed (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) false hn0
    (by have := hin.positive; omega) hch.1 hnodePre.path.fixed
  have hfresh := (fixed_child first hn0 hin.partition hin.path.fixed hin.target htv).1
  have ho := node_out (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) false hn0
    (by have := hin.positive; omega) hch.1
  have hbout := hnodePre.boundary.node (fuel := fuel) (tcLevel := tcLevel) hn0
    (by have := hin.positive; omega) hch.1
  have hframe := hch.2 _ (by simpa only [Nat.add_sub_cancel] using ho)
  have hhist := hin.history.child_return (fuel := fuel) first hin.ancestor hin.positive
    hin.partition hin.target htv
  dsimp only at hhist
  have hgca : (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2.gcaFirst = st.gcaFirst := by
    rw [node_gca]
    cases first <;> rfl
  generalize hcall : node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
    (Engine.child first level tc tv st) = result at hstored hframe hhist hgca hbout hfixout ⊢
  obtain ⟨exit, out⟩ := result
  let left := { out with fixedpts := out.fixedpts.erase tv }
  have hleft : RunInv G ctx left := hstored.leave tv
  have hrestore : left.fixedpts = st.fixedpts := by
    apply fixed_restore (base := st) (out := out) _ hfresh
    exact hfixout.trans (by cases first <;> rfl)
  have hleftFrame : SearchOut G level level st.view left.view := hframe.congr rfl rfl rfl rfl
  have hr := (reachPolicy G ctx tcLevel hn0).recover level numcells st left
    hin.positive hin.partition hleftFrame
  have hready : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell
      (recoverLevels level (recoverPtn (n + 2) level left)) :=
    ⟨hin.past, hin.positive, hr.ok, hin.target.of_out hr.effect, hin.cursor_mem,
      hleft.recover (n + 2) level,
      (by rw [show (recoverLevels level (recoverPtn (n + 2) level left)).gcaFirst = left.gcaFirst from
            (gcaPolicy ctx (n + 2) tcLevel).recover level left]
          change out.gcaFirst ≤ level
          change out.gcaFirst = st.gcaFirst at hgca
          rw [hgca]
          exact hin.ancestor),
      hhist.1, hhist.2 hin.recorded, recover_equitable hn0 hin.positive hin.partition hin.equitable hleftFrame,
      (hbout.congr (out := left) rfl rfl rfl).recover_child hin.positive
        (by have := Nat.le_trans hin.partition.bc (bcount_le _ _ _); omega),
      recover_bound level left, hin.path.recover hn0 hin.positive hin.partition hleftFrame hrestore⟩
  exact hready

end Hex.GraphIso.Nauty.Engine
