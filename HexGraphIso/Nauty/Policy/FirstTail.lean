/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstWitness
public import HexGraphIso.Nauty.Policy.ReferenceDescent
import all HexGraphIso.Nauty.Generation.Reorder
import all HexGraphIso.Nauty.Generation.Cheap
import all HexGraphIso.Nauty.Policy.FirstWitness
import all HexGraphIso.Nauty.Policy.ReferenceDescent
import all HexGraphIso.Nauty.Policy.MaxReturnTrace
import all HexGraphIso.Nauty.Policy.MaxRestore
import all HexGraphIso.Nauty.Policy.MaxResume
import all HexGraphIso.Nauty.Policy.MaxReceive
import all HexGraphIso.Nauty.Policy.MaxSkip
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.EarlyReturn
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.FirstBounds
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.MaxExit
import all HexGraphIso.Nauty.Policy.MaxControl
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Passing the guiding vertex selects the initialized sibling phase. -/
theorem SweepInput.past_phase {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel true level numcells tc tv1 (some tv)
      cell index st l bs fs parents) (hpast : tv1 < tv) :
    Nauty.SweepPre G ctx tcLevel true level numcells tc tv1 (some tv) cell st ∧
      Comparison ctx (l.codes ctx) bs fs st := by
  rcases h.phase with ⟨_, _, _, _, hcell, hcursor, _⟩ | ⟨hp, hc, _⟩
  · have he : tv1 = tv := by rw [h.tv1_eq, ← hcell, ← hcursor]; rfl
    omega
  · exact ⟨hp, hc⟩

/-- Reordering a cheap receiving frame preserves the reference in every
target child. Its actual off-path call therefore returns to this frame. -/
theorem SweepInput.cheap_visit {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel true level numcells tc tv1 (some tv)
      cell index st l bs fs parents) (hpast : tv1 < tv)
    {R : RefineSt n} {targets : List Nat} {key : Key n}
    (hit : IterOk ctx level R)
    (hlab : R.lab = (l.prepare ctx tcLevel).2.2.2.2.lab)
    (hptn : R.ptn = (l.prepare ctx tcLevel).2.2.2.2.ptn) (hnc : R.numcells = numcells)
    (href : Generation.HasLeaf ctx tcLevel level R targets key)
    (hm : Generation.Matches ctx level st targets key)
    (hg : st.gcaFirst = level) (heq : st.eqlevFirst = level)
    (hcheap : st.noncheaplevel ≤ level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    (Nauty.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child true level tc tv st)).1 = .unwind level false := by
  have hp := (h.past_phase hpast).1
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hcurrent : st.ptn = R.ptn := (h.effect.ptn_eq h.base h.partition).trans hptn.symm
  let U := { R with lab := st.lab }
  have hperm : StPerm level U R := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hit.ok.labSize.trans h.partition.labSize.symm, ?_⟩
    change cellsPerm R.ptn level st.lab R.lab
    rw [hlab, hptn]
    exact cellsPerm_symm h.effect.perm
  have hleaf := href.ofPerm hgsz hit hperm
  have hS : SubtreeOk ctx level U := (h.small hcheap).ofFrames rfl hcurrent.symm hnc
  have hc := hp.child hn0 hgsz hsymm
  have hlt : level < n := by
    have hh := hc.partition.bc
    have hh' := bcount_le (child true level tc tv st).ptn (level + 1) n
    omega
  obtain ⟨len, htcell, hseg⟩ := h.target
  obtain ⟨hcell, hlen, hrange⟩ := htcell (mem_ne_empty (h.cursor_mem tv rfl))
  have hcellU : (tc, tc + len - 1) ∈ cells U.ptn level n := by
    apply isCell_mem_cells
    · change IsCell R.ptn level tc len
      rwa [← hcurrent]
    · rw [hS.it.ok.ptnSize]; exact Nat.le_refl _
    · exact hS.it.ok.ptnEnd
    · omega
  obtain ⟨offset, hoffset, hat⟩ := mem_segN_iff.mp (hseg tv (h.cursor_mem tv rfl))
  change st.lab[tc + offset]! = tv at hat
  rcases hleaf.cases with ⟨hdisc, _, _⟩ |
      ⟨tc', e, o, rest, tail, _, hcell', hne, ho, _, hchildLeaf, rfl, rfl⟩
  · have hopen := target_open hS.it.ok.ptnSize hS.it.ok.ptnEnd hcellU tc (Nat.le_refl _) (by omega)
    have hh := hdisc tc (by omega)
    omega
  · have ht : tc' = tc := by
      have hh := hm.targets 0 (by simp)
      have hr := hp.recorded.cheapRecorded (by rwa [hg]) heq
      simp only [List.getElem!_cons_zero, Nat.add_zero] at hh
      change Int.ofNat tc' = st.firsttc[level]! at hh
      rw [hr] at hh
      exact Int.ofNat.inj hh
    rw [ht] at hcell' hne ho hchildLeaf hm
    have he : e = tc + len - 1 := cells_eq_of_start
      (by rw [hS.it.ok.ptnSize]; exact Nat.le_refl _) hS.it.ok.ptnEnd hcell' hcellU
    have ho' : offset ≤ e - tc := by omega
    have href' := hchildLeaf.smallChild hS hlt hgsz hsymm hloop hcell' hne ho ho'
    have hs' := subtreeOk_child hS hlt hsymm hcell' hne ho'
    have hfields : (child true level tc tv st).refined ctx (level + 1) (numcells + 1) =
        childSt ctx level U tc U.lab[tc + offset]! := by
      change refine ctx (level + 1) (breakout n st.lab st.ptn (level + 1) tc tv).1
        (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1) = _
      change _ = childSt ctx level U tc st.lab[tc + offset]!
      rw [hat, childSt]
      dsimp only [U]
      rw [← hcurrent, hnc]
    have hr := Nauty.cheap_reference (n + 2) tcLevel hgsz hsymm hloop
      fuel (level + 1) (numcells + 1) (child true level tc tv st) rest tail
      (by rw [hfields]; exact hs') hp.stored.scratch hp.stored.firstSize hp.stored.first
      (hm.tail.stateEq rfl rfl rfl) (by rw [hfields]; exact href')
      (by change st.eqlevFirst = level + 1 - 1; omega)
      (by change st.gcaFirst < level + 1; omega) (by have := h.fuel; omega)
    simpa only [show (child true level tc tv st).gcaFirst = level from hg] using hr.1

/-- Every remaining first-path sibling returns to its receiver. The
cheap case uses occurrence, while the other case uses the return bounds. -/
theorem SweepInput.visit_level {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {level numcells tc tv1 tv index target : Nat} {short : Bool} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel true level numcells tc tv1 (some tv)
      cell index st l bs fs parents) (hpast : tv1 < tv)
    {R : RefineSt n} {targets : List Nat} {key : Key n}
    (hit : IterOk ctx level R)
    (hlab : R.lab = (l.prepare ctx tcLevel).2.2.2.2.lab)
    (hptn : R.ptn = (l.prepare ctx tcLevel).2.2.2.2.ptn) (hnc : R.numcells = numcells)
    (href : Generation.HasLeaf ctx tcLevel level R targets key)
    (hm : Generation.Matches ctx level st targets key)
    (hg : st.gcaFirst = level) (heq : st.eqlevFirst = level) (hsame : level < st.allsamelevel)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (he : (Nauty.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child true level tc tv st)).1 = .unwind target short) : target = level := by
  by_cases hc : st.noncheaplevel ≤ level
  · have hr := h.cheap_visit hpast hit hlab hptn hnc href hm hg heq hc hgsz hsymm hloop
    rw [he] at hr
    cases hr
    rfl
  · obtain ⟨hp, hcmp⟩ := h.past_phase hpast
    have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
    have horder := (h.counters (comparison_positive hcmp)).2
    have hr := (hp.child hn0 hgsz hsymm).return_eq
      (by change level + 1 - 1 ≤ st.gcaFirst; omega)
      (by change level + 1 - 1 ≤ st.gcaCanon; omega)
      (by change level + 1 - 1 < st.noncheaplevel; omega)
      (by change level + 1 - 1 < st.allsamelevel; omega) he
    omega

/-- The actual sibling suffix completes, including both short-prune
flags. Recovery preserves the frozen reference and first agreement. -/
theorem SweepInput.tail_done {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {level numcells tc tv1 index : Nat} {cursor : Option Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel cfuel true level numcells tc tv1 cursor
      cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    (hpast : Generic.Past true tv1 cursor)
    {R : RefineSt n} {targets : List Nat} {key : Key n}
    (hit : IterOk { g := rowsOf G } level R)
    (hlab : R.lab = (l.prepare { g := rowsOf G } tcLevel).2.2.2.2.lab)
    (hptn : R.ptn = (l.prepare { g := rowsOf G } tcLevel).2.2.2.2.ptn) (hnc : R.numcells = numcells)
    (href : Generation.HasLeaf { g := rowsOf G } tcLevel level R targets key)
    (hm : Generation.Matches { g := rowsOf G } level st targets key)
    (hg : st.gcaFirst = level) (heq : st.eqlevFirst = level) (hsame : level < st.allsamelevel) :
    (Nauty.sweep true { g := rowsOf G } (n + 2) tcLevel fuel cfuel
      level numcells tc tv1 cursor cell index st).1 = .done := by
  induction cfuel generalizing cursor cell index st bs fs with
  | zero =>
    cases cursor with
    | none => rw [Nauty.sweep]
    | some tv =>
      have hh := h.cursor_fuel tv rfl
      have ht := VSet.mem_lt (h.cursor_mem tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none => rw [Nauty.sweep]
    | some tv =>
      have htv := hpast rfl tv rfl
      have hf : (true && tv == tv1) = false := by simp only [Bool.true_and, beq_eq_false_iff_ne]; omega
      have hnext : ∀ cell : VSet n, Generic.Past true tv1 (cell.nextElem (some tv)) := by
        intro cell _ v hv
        have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
        change tv + 1 ≤ v at hh
        omega
      by_cases hv : (!true || st.orbits[tv]! == tv) = true
      · obtain ⟨target, short, out, hcall⟩ := h.child_exit
          (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
        have he := congrArg Prod.fst hcall
        rw [hf] at he
        have ht := h.visit_level htv hit hlab hptn hnc href hm hg heq hsame
          (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) he
        subst target
        let ctx : Ctx n := { g := rowsOf G }
        let left := { out with fixedpts := out.fixedpts.erase tv }
        let ready := recoverLevels level (recoverPtn (n + 2) level left)
        let filtered := if short then shortprune cell left else cell
        obtain ⟨hgen, hanc⟩ := h.received_generators hn hcall
        obtain ⟨bs', fs', hi, _, _⟩ := h.received_input hn hv hcall hgen hanc
        simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.true_and] at hi
        change SweepInput G ctx tcLevel fuel cfuel true level numcells tc tv1
          (filtered.nextElem (some tv)) filtered
          (if ready.orbits[tv]! == tv1 then index + 1 else index) ready l bs' fs' parents at hi
        have hc : Nauty.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
            (child true level tc tv st) = (.unwind level short, out) := by
          simpa only [hf] using hcall
        have hr : ready.reference = st.reference := by
          have hh := node_reference ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
            (child true level tc tv st)
          rw [hc] at hh
          exact ((referencePolicy ctx (n + 2) tcLevel).recover level left).trans hh
        have hsame' : level < ready.allsamelevel := by
          have hh := node_same ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
            (child true level tc tv st)
          rw [hc] at hh
          rw [recover_same]
          change level < out.allsamelevel
          rw [hh]
          exact hsame
        have heq' : ready.eqlevFirst = level := by
          have hh := Generic.node_bounded (firstFloor ctx (n + 2) tcLevel level)
            fuel (level + 1) (numcells + 1) (child true level tc tv st) (by omega)
            (show level ≤ st.allsamelevel ∧ level ≤ st.eqlevFirst from ⟨by omega, by omega⟩)
          rw [← node_eq_generic, hc] at hh
          rw [recover_eqlev]
          change min out.eqlevFirst level = level
          exact Nat.min_eq_right hh.2
        have hg' : ready.gcaFirst = level := by
          have hh := h.recovered_control
          rw [hcall] at hh
          simpa only [hf, Bool.false_eq_true, ↓reduceIte] using hh.1 rfl
        have hh := ih hi (hnext filtered) (matches_reference hm hr) hg' heq' hsame'
        have he := (h.receive_call hn hv hcall
          (Generic.sweepCall ctx (n + 2) tcLevel fuel cfuel)).1
        unfold Generic.nodeCall Generic.sweepCall at he
        rw [sweep_eq_generic, Generic.sweep, he]
        simpa only [hf, ctx, filtered, ready, left, Generic.sweepCall, ← sweep_eq_generic,
          Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.true_and] using hh
      · have hs : (!true || st.orbits[tv]! == tv) = false := Bool.eq_false_iff.mpr hv
        have hi := h.skip_input (size_rowsOf G) hs
        have hh := ih hi (hnext cell) hm hg heq hsame
        rw [Nauty.sweep]
        simpa only [hs, Bool.false_eq_true, ↓reduceIte, Id.run_pure, Bool.true_and] using hh

end Hex.GraphIso.Nauty.Max
