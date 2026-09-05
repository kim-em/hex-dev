/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.FirstPath.Loop
import all HexGraphIso.Nauty.Search.Search

public section

/-!
The first-path sibling sweep, part two: the hypotheses carried through the
sweep after its guiding child has been absorbed, and their transport across
an off-path child that stays at the loop level.

This module builds on `Correct.FirstPath.Loop`.  `Correct.FirstPath.Sweep`
runs the cursor-fuel induction over `FirstSweepHyp`.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Hypotheses of the sweep after its guiding child -/

/-- The coset cursor plays no role in the reach relation. -/
theorem SearchOut.ofCoset {G : Colored n k} {B lev coset : Nat}
    {st out : SearchSt n}
    (h : SearchOut G B lev { st with cosetindex := coset } out) :
    SearchOut G B lev st out :=
  ⟨h.labSize, h.ptnSize, h.reach, h.low, h.perm, h.firstStore,
    h.canonStore, h.canon⟩

/-- Every generator recorded by an event is a checked automorphism. -/
theorem EventOut.checkGen {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    ∀ γ ∈ out.genTrace.toList, checkAutom ctx.g γ = true := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ =>
      intro γ hγ
      exact event.genTraceOk.check hγ

/-- A canonical reference that is a cell permutation of the current
labelling at the current level reaches every active ancestor frame and
picks the same child there. -/
theorem CanonTrail.ofPerm {ctx : Ctx n} {level : Nat} {st out : SearchSt n}
    {trail : FrameTrail}
    (htrail : TrailOk ctx level st trail)
    (hlab : st.lab.size = n) (hptn : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hperm : cellsPerm st.ptn level st.lab out.canonlab)
    (hcsz : out.canonlab.size = n) :
    CanonTrail ctx level out trail := by
  constructor
  · intro target entry hlt hentry
    have h1 := htrail.reach target entry hlt hentry
    have h2 : cellsPerm entry.frame.rsPtn target st.lab out.canonlab := by
      apply cellsPerm_coarsen (ptnF := st.ptn) (levF := level)
      · rw [htrail.ptnSize target entry hlt hentry, hptn]
      · rw [hlab, hptn]
      · rw [hcsz, hptn]
      · exact hperm
      · exact hend
      · exact htrail.endClosed target entry hlt hentry
      · intro q hq
        rw [htrail.frozen target entry hlt hentry q hq]
        omega
    exact cellsPerm_trans h1 h2
  · intro target entry hlt hentry
    obtain ⟨len, hcell, hoff, _, hsingle, hat⟩ :=
      htrail.picked target entry hlt hentry
    refine ⟨len, hcell, hoff, ?_⟩
    rw [← cellsPerm_singleton hperm hsingle]
    exact hat

/-- What the first-path sweep knows at every cursor position after its
guiding child: the loop invariant, the live package with frame
stabilization, path facts, both reference histories below the loop, the
first-path controls, orbit and coset facts, first-leaf domination, and the
cheap-cell boundary discipline relative to the node entry boundary `e`. -/
structure FirstSweepHyp (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel level : Nat) (codes bs fs : List Nat)
    (numcells : Nat) (rsLab rsPtn : Array Nat) (tc len : Nat) (tcell : VSet n)
    (cursor : Option Nat) (e tv1 : Nat) (base st : SearchSt n)
    (best : Option (Key n)) (trail : FrameTrail) : Prop where
  inv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab
    rsPtn tc len tcell cursor base st best trail
  live : FirstLive ctx level st trail rsLab rsPtn
  path : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
    (initialPartition G).1 level st
  after : ∃ v, cursor = some v ∧ tv1 ≤ v
  cursorLt : ∀ v, cursor = some v → v < n
  sign : st.compCanon ≤ 0
  guide : st.gcaFirst = level
  firstTrail : FirstTrail ctx level st trail
  canonTrail : CanonTrail ctx level st trail
  orbits : OrbSound (OrbConn st.genTrace.toList n) st.orbits n
  coset : st.cosetindex < n
  firstDom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b
  desc : CheapDesc ctx level st.noncheaplevel
    (LoopInv.frame rsLab rsPtn numcells)
  bnd : st.noncheaplevel ≤ level + 1
  park : cheapautom rsPtn level n = false → st.noncheaplevel ≠ level
  keep : st.noncheaplevel < level → st.noncheaplevel = e

/-- What a finished first-path sweep preserves for its enclosing node. -/
structure FirstSweepKeep (ctx : Ctx n) (level e : Nat) (fs : List Nat)
    (st out : SearchSt n) (outBest : Option (Key n)) : Prop where
  dom : ∀ b, outBest = some b → keyLe (pathLeafKey ctx fs out.firstlab) b
  firstlab : out.firstlab = st.firstlab
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  coset : out.cosetindex < n
  boundary : out.noncheaplevel < level → out.noncheaplevel = e

/-- The small-cell descent invariant of a child, when the loop boundary is
merely known to avoid the loop level. -/
theorem LoopInv.childDescWeak {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hbnd : st.noncheaplevel ≤ level + 1)
    (hpark : cheapautom rsPtn level n = false →
      st.noncheaplevel ≠ level)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv) :
    CheapDesc ctx (level + 1) st.noncheaplevel
      (refine ctx (level + 1) (breakout n st.lab st.ptn (level + 1) tc tv).1
        (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        (breakout n st.lab st.ptn (level + 1) tc tv).2.2 (numcells + 1)) := by
  have hok := h.run.searchOk
  have hsz : st.lab.size = n := hok.labSize
  have hpsz : rsPtn.size = n := h.frozenPtnSize
  have hlabOk : LabOk st.lab n :=
    labOk_of_reach hok.labSize hok.reach
  have hinj : LabInj st.lab n :=
    labInj_of_reach hok.labSize h.nonempty hok.reach
  let cur : RefineSt n := { LoopInv.frame rsLab rsPtn numcells with lab := st.lab }
  have hcur : CheapDesc ctx level st.noncheaplevel cur := by
    intro hlt
    exact (hdesc hlt).ofCellsPerm h.labPerm hsz hlabOk hinj
  have hend : rsPtn[rsPtn.size - 1]! ≤ level := h.frozenEnd
  have hit : IterOk ctx level cur := by
    refine ⟨⟨hsz, hlabOk, hpsz, hend⟩, hinj, ?_, ?_⟩
    · intro q hq
      exact h.values q
    · exact Nat.le_of_lt h.levelLt
  have heq : Equitable ctx level cur.lab cur.ptn := by
    change Equitable ctx level st.lab rsPtn
    rw [← h.ptnEq]
    exact h.currentEquitable
  have hcount : bcount cur.ptn level n = cur.numcells := by
    change bcount rsPtn level n = numcells
    rw [← h.ptnEq]
    exact hok.count.symm
  have hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
    rw [hg]
    exact rowsOf_symm G
  have hchild := hcur.child hit heq hcount hsymm h.levelLt h.cell h.lenTwo
    h.range hcurrent
  have hboundary : (if st.noncheaplevel ≥ level ∧
      ¬cheapautom cur.ptn level n then level + 1
      else st.noncheaplevel) = st.noncheaplevel := by
    change (if st.noncheaplevel ≥ level ∧
      ¬cheapautom rsPtn level n then level + 1
      else st.noncheaplevel) = st.noncheaplevel
    rcases hc : cheapautom rsPtn level n with _ | _
    · have := hpark hc
      rcases Decidable.em (st.noncheaplevel ≥ level) with hge | hge
      · rw [ite_eq_left ⟨hge, by simp⟩]
        omega
      · rw [ite_eq_right (fun h => hge h.1)]
    · simp
  rw [hboundary] at hchild
  have hcurLab : cur.lab[tc + currentOffset]! = tv := hat
  rw [hcurLab] at hchild
  have hptn : st.ptn = rsPtn := h.ptnEq
  change CheapDesc ctx (level + 1) st.noncheaplevel
    (refine ctx (level + 1) (breakout n st.lab rsPtn (level + 1) tc tv).1
      (rsPtn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1)) at hchild
  rw [breakout_ptn, hptn]
  exact hchild

/-- The small-cell subtree fact at the frozen frame, when the boundary is
merely known to avoid the loop level. -/
theorem LoopInv.subtreeAtWeak {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hpark : cheapautom rsPtn level n = false →
      st.noncheaplevel ≠ level)
    (hle : st.noncheaplevel ≤ level) :
    SubtreeOk ctx level
      { lab := rsLab, ptn := rsPtn, active := base.active,
        numcells := numcells, hint := 0, maxpos := 0,
        longcode := numcells } := by
  have hsub : SubtreeOk ctx level (LoopInv.frame rsLab rsPtn numcells) := by
    apply hdesc.atLevel
    · refine ⟨⟨h.frozenLabSize, h.frozenLabOk, h.frozenPtnSize, h.frozenEnd⟩, ?_, ?_, ?_⟩
      · rw [← h.baseLab]
        exact labInj_of_reach h.baseOk.labSize h.nonempty h.baseOk.reach
      · intro q hq
        exact h.values q
      · exact Nat.le_of_lt h.levelLt
    · exact h.equitable
    · change bcount rsPtn level n = numcells
      rw [← h.basePtn]
      exact h.baseOk.count.symm
    · exact hle
    · intro heq
      rcases hc : cheapautom rsPtn level n with _ | _
      · exact (hpark hc heq).elim
      · exact hc
  exact hsub.setActive

namespace FirstSweepHyp

/-- The cheap-cell ledger is ready for the next child. -/
theorem cheapOk {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {e tv1 : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} (hg : ctx.g = rowsOf G)
    (h : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e tv1 base st best trail) :
    CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) (level + 1) st := by
  apply BoundaryOk.nextCheap _ h.inv.run
  rcases hc : cheapautom rsPtn level n with _ | _
  · intro heq
    exact (h.park hc heq).elim
  · apply BoundaryOk.ofCheap hg h.inv
    rw [h.inv.ptnEq]
    exact hc

/-- Filtering the live set leaves every other hypothesis unchanged. -/
theorem filter {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell tcell' : VSet n} {e tv1 : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e tv1 base st best trail)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab
      rsPtn tc len tcell' cursor base st best trail) :
    FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell' cursor e tv1 base st best trail :=
  ⟨hinv, h.live, h.path, h.after, h.cursorLt, h.sign, h.guide, h.firstTrail,
    h.canonTrail, h.orbits, h.coset, h.firstDom, h.desc, h.bnd, h.park,
    h.keep⟩

end FirstSweepHyp

/-- The reach relation depends on its input state only through the
labelling and partition. -/
theorem SearchOut.inputEq {G : Colored n k} {B lev : Nat}
    {st st' out : SearchSt n} (h : SearchOut G B lev st out)
    (hlab : st'.lab = st.lab) (hptn : st'.ptn = st.ptn)
    (hfirst : st'.firstlab = st.firstlab)
    (hcanon : st'.canonlab = st.canonlab) :
    SearchOut G B lev st' out :=
  ⟨by rw [hlab]; exact h.labSize, by rw [hptn]; exact h.ptnSize, h.reach,
    fun q hq => by rw [hptn]; exact h.low q (by rw [hptn] at hq; exact hq),
    by rw [hlab, hptn]; exact h.perm,
    by rw [hlab, hptn, hfirst]; exact h.firstStore,
    by rw [hlab, hptn, hcanon]; exact h.canonStore,
    by rw [hcanon]; exact h.canon⟩

/-- A new canonical reference installed below a child is a cell
permutation of the loop labelling at the loop level. -/
theorem LoopInv.childCanonPerm {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {canonlab : Array Nat}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv)
    (hcsz : canonlab.size = n)
    (hnew : cellsPerm (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      (level + 1) (breakout n st.lab st.ptn (level + 1) tc tv).1 canonlab) :
    cellsPerm st.ptn level st.lab canonlab := by
  let child : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
  have hnew' : cellsPerm child.ptn (level + 1) child.lab canonlab := by
    change cellsPerm (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + currentOffset]!).2.1 (level + 1)
      (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1 canonlab
    rw [hat]
    exact hnew
  have hstPtnSize : st.ptn.size = n := by
    exact hinv.run.searchOk.ptnSize
  have htcPtn : tc < st.ptn.size := by
    rw [hstPtnSize]
    exact Nat.lt_of_lt_of_le (by omega : tc < tc + len) hinv.range
  have hrangePtn : tc + len ≤ st.ptn.size := by
    rw [hstPtnSize]
    exact hinv.range
  have hchildPtn : child.ptn = st.ptn.set! tc (level + 1) :=
    breakout_ptn (n := n) st.lab st.ptn (level + 1) tc st.lab[tc + currentOffset]!
  have hchildOk : SearchOk G (level + 1) (numcells + 1) child := by
    apply breakout_searchOk hinv.nonempty hinv.run.searchOk hinv.positive
      hinv.currentCell hinv.lenTwo
      hinv.range hcurrent
    · rfl
    · exact hchildPtn
    · rfl
  have hfine : cellsPerm st.ptn level child.lab canonlab := by
    apply cellsPerm_coarsen (ptnF := child.ptn) (levF := level + 1)
    · rw [hchildPtn, Array.size_set!]
    · exact hchildOk.labSize.trans hchildOk.ptnSize.symm
    · rw [hcsz, hchildOk.ptnSize]
    · exact hnew'
    · exact searchOk_end hinv.nonempty hchildOk (by omega)
    · exact searchOk_end hinv.nonempty hinv.run.searchOk hinv.positive
    · intro q hq
      rw [hchildPtn]
      rcases Decidable.em (tc = q) with rfl | hne
      · rw [Array.getElem!_set!_self _ _ _ htcPtn]
        exact Nat.le_refl _
      · rw [Array.getElem!_set!_ne _ _ _ _ hne]
        omega
  have hbreak : cellsPerm st.ptn level st.lab child.lab := by
    change cellsPerm st.ptn level st.lab
      (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
    exact breakout_cellsPerm hinv.currentCell hrangePtn
      (by rw [hinv.run.searchOk.labSize, hinv.run.searchOk.ptnSize])
      hcurrent
  exact cellsPerm_trans hbreak hfine

namespace FirstSweepHyp

set_option maxHeartbeats 1600000 in
/-- An off-path child that stays at the loop level rebuilds every sweep
hypothesis for the recursive tail on the recovered state. -/
theorem next {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tv offset currentOffset e tv1 : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best childBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hh : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e tv1 base st best trail)
    (hcodesLen : codes.length = level) (hfuel : runFuel ≠ 0)
    (hnext : tcell.nextElem cursor = some tv)
    (hoffset : offset < len) (hcurrent : currentOffset < len)
    (hatFrozen : rsLab[tc + offset]! = tv)
    (hat : st.lab[tc + currentOffset]! = tv)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      out (numcells + 1) best childBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hkeep : OtherKeep ctx (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } out)
    (hstay : ¬ r < Int.ofNat level)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } out)
    (clear : Bool)
    (hshort : (clearShortIf clear
      { out with fixedpts := out.fixedpts.erase tv }).needshortprune =
        false) :
    ∃ bs', FirstSweepHyp G ctx tcLevel specFuel level codes bs' fs numcells
      rsLab rsPtn tc len tcell (some tv) e tv1 base
      (recover n inf level
        (clearShortIf clear { out with fixedpts := out.fixedpts.erase tv }))
      childBest eventTrail := by
  let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
  let cleared := clearShortIf clear cleaned
  let recSt := recover n inf level cleared
  obtain ⟨hfix, hcos, hcomp, hgen, horb, hfl, hncl, hgf, hgc, hcl, -⟩ :=
    clearShortIf_fields clear cleaned
  have hgsz : ctx.g.size = n := by
    rw [hg]
    exact size_rowsOf G
  have hreturn : r = Int.ofNat level :=
    hchild.node.toOutcome.parentEq hfuel hstay
  have hgrows : IncGrows best childBest := hchild.grows hfuel
  have hstFirst : ({ st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv
      cosetindex := tv } : SearchSt n).gcaFirst = level := hh.guide
  have houtFirst : out.gcaFirst = level := hchild.firstGuide.trans hstFirst
  -- coverage
  have hret := NodeOutcome.parentReturn hchild.node.toOutcome hfuel hstay
  have heq0 := hh.inv.childKeyAll hoffset hatFrozen hat
  have heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := st.fixedpts.insert tv
            cosetindex := tv }
          (numcells + 1) := by
    intro o ho h
    exact (heq0 o ho h).trans (nodeKey_congr rfl rfl rfl).symm
  have hinj : LabInj rsLab rsLab.size := by
    rw [← hh.inv.baseLab, hh.inv.baseOk.labSize]
    exact labInj_of_reach hh.inv.baseOk.labSize hh.inv.nonempty
      hh.inv.baseOk.reach
  have hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc
      len numcells tcell (some tv) childBest :=
    SweepCover.receipt hh.inv.cover hnext hchild.node.toOutcome.receipt hfuel
      hret heq hoffset hatFrozen hchild.coset hgsz
      hchild.node.event.checkGen hh.inv.frozenLabSize hinj
      hh.inv.frozenLabOk hh.inv.frozenPtnSize hh.inv.frozenEnd
      hh.inv.frozenVals hh.inv.cell hh.inv.range hh.inv.fuelBound
  -- recovery
  have hout' : SearchOut G level (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      out := by
    rw [hat]
    exact hout.inputEq rfl rfl rfl rfl
  have hfixedChild : out.fixedpts =
      st.fixedpts.insert st.lab[tc + currentOffset]! := by
    rw [hchild.node.fixed, hat]
  have hrecovered := hh.inv.recoverChild hinf hcurrent hout'
  rw [hat] at hrecovered
  have hpathRec := hh.inv.recoverPath hh.path hout' hfixedChild hinf hcurrent
  rw [hat] at hpathRec
  have hrecEq : recSt = clearShortIf clear (recover n inf level cleaned) :=
    recover_clearShortIf n inf level clear cleaned
  have heffect : SearchOut G level level base recSt := by
    rw [hrecEq]
    cases clear
    · exact hrecovered.1
    · exact hrecovered.1.congr rfl rfl rfl rfl
  have hok : SearchOk G level numcells recSt := by
    rw [hrecEq]
    cases clear
    · exact hrecovered.2
    · exact {
        labSize := hrecovered.2.labSize
        ptnSize := hrecovered.2.ptnSize
        reach := hrecovered.2.reach
        init1 := hrecovered.2.init1
        vals := hrecovered.2.vals
        count := hrecovered.2.count
        bc := hrecovered.2.bc
        canon := hrecovered.2.canon }
  have hpath : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level recSt := by
    rw [hrecEq]
    exact hpathRec.1.clearShortIf clear
  have hfixedRec : recSt.fixedpts = st.fixedpts := by
    rw [hrecEq, (clearShortIf_fields clear _).1]
    exact hpathRec.2
  have hev : EventOut G ctx tcLevel codes fs cleared childBest eventTrail
      r := by
    cases clear
    · exact hchild.node.event.setFixed _
    · exact (hchild.node.event.setFixed _).clearShort
  have hfirstLe : cleared.gcaFirst ≤ level := by
    rw [hgf]
    exact Nat.le_of_eq houtFirst
  have hinfLevel : level < inf := by
    rw [hinf]
    have hle : level ≤ n := Nat.le_trans hh.inv.run.searchOk.bc
      (bcount_le st.ptn level n)
    omega
  obtain ⟨bs', hrun, hstable, hhistory⟩ := hev.recoverRun hreturn hcodesLen
    hh.inv.positive hinfLevel hfirstLe hok
  -- frames of the recovered state
  have hframes := recover_frames n inf level cleared
  have hgfRec : recSt.gcaFirst = level := by
    rw [show recSt = recover n inf level cleared from rfl,
      hframes.2.2.2.2.2.2.1, hgf]
    exact houtFirst
  have horderOut : level ≤ out.gcaCanon := by
    rw [← houtFirst]
    exact hchild.order
  have hgcRec : level ≤ recSt.gcaCanon := by
    rw [show recSt = recover n inf level cleared from rfl,
      recover_gcaCanon, hgc]
    change level ≤ if level < out.gcaCanon then level else out.gcaCanon
    split <;> omega
  have hfirstlabRec : recSt.firstlab = st.firstlab := by
    rw [show recSt = recover n inf level cleared from rfl,
      hframes.2.2.2.2.1, hfl]
    exact hkeep.firstlab
  have hcanonlabRec : recSt.canonlab = out.canonlab := by
    rw [show recSt = recover n inf level cleared from rfl, hframes.1, hcl]
  have hext : TrailExt level trail eventTrail :=
    TrailExt.ofPush hchild.node.preserved
  have hentry : eventTrail level = some
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩ :=
    hchild.node.preserved.pushAt
  have hlive : FirstLive ctx level recSt eventTrail rsLab rsPtn := by
    refine ⟨⟨hhistory, ?_, hstable⟩, ?_⟩
    · rw [hgfRec]
      exact hgcRec
    · intro γ hγ
      exact hstable level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
        (by rw [hgfRec]; exact Int.le_refl _) hentry γ hγ
  have hfirstTrail : FirstTrail ctx level recSt eventTrail :=
    hh.firstTrail.retrail hfirstlabRec hext
  have hstLab : st.lab.size = n := by
    exact hh.inv.run.searchOk.labSize
  have hstPtn : st.ptn.size = n := by
    exact hh.inv.run.searchOk.ptnSize
  have hstEnd : st.ptn[st.ptn.size - 1]! ≤ level :=
    searchOk_end hh.inv.nonempty hh.inv.run.searchOk hh.inv.positive
  have hcsz : out.canonlab.size = n := by
    exact hchild.node.event.canonSize
  have hcanonTrail : CanonTrail ctx level recSt eventTrail := by
    rcases hchild.canonGuide with hold | hnew
    · apply hh.canonTrail.retrail _ hext
      rw [hcanonlabRec, hold.2]
    · have hperm := hh.inv.childCanonPerm hcurrent hat hcsz hnew.2
      exact (CanonTrail.ofPerm hh.inv.run.trailOk hstLab hstPtn hstEnd hperm
        hcsz).retrail hcanonlabRec hext
  -- frame references
  have hrefs : FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells recSt childBest := by
    constructor
    · intro _
      obtain ⟨o, ho, hdone, hatRef, hperm⟩ :=
        (hh.inv.refs.grow hgrows).first hh.guide
      refine ⟨o, ho, hdone, ?_, ?_⟩
      · rw [hfirstlabRec]
        exact hatRef
      · rw [hfirstlabRec]
        exact hperm
    · intro heqc
      have hcanonRec := recover_gcaCanon n inf level cleared
      rcases hchild.canonGuide with hold | hnew
      · have hcanonEq : st.gcaCanon = level := by
          rw [show recSt = recover n inf level cleared from rfl,
            hcanonRec, hgc] at heqc
          change (if level < out.gcaCanon then level else out.gcaCanon) =
            level at heqc
          rw [hold.1] at heqc
          change (if level < st.gcaCanon then level else st.gcaCanon) =
            level at heqc
          rw [ite_eq_right (Nat.not_lt_of_ge hh.inv.run.canonBound)] at heqc
          exact heqc
        obtain ⟨o, ho, hdone, hatRef, hperm⟩ :=
          (hh.inv.refs.grow hgrows).canon hcanonEq
        refine ⟨o, ho, hdone, ?_, ?_⟩
        · rw [hcanonlabRec, hold.2]
          exact hatRef
        · rw [hcanonlabRec, hold.2]
          exact hperm
      · have hmem : tcell.mem rsLab[tc + offset]! = true := by
          rw [hatFrozen]
          exact VSet.nextElem_mem hnext
        have hdone : ChildDone ctx tcLevel specFuel level codes rsLab rsPtn
            tc numcells childBest offset :=
          hcover.past offset hoffset hmem (by
            simp only [After, hatFrozen]
            omega)
        have hstInj : LabInj st.lab st.lab.size := by
          rw [hh.inv.run.searchOk.labSize]
          exact labInj_of_reach hh.inv.run.searchOk.labSize hh.inv.nonempty
            hh.inv.run.searchOk.reach
        have hcurrentPos : tc + currentOffset < st.lab.size := by
          rw [hstLab]
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcurrent tc)
            hh.inv.range
        have htcPtn : tc < st.ptn.size := by
          rw [hstPtn]
          exact Nat.lt_of_lt_of_le (by omega : tc < tc + len) hh.inv.range
        have hchildAt : (breakout n st.lab st.ptn (level + 1) tc tv).1[tc]! =
            tv := by
          rw [← hat, breakout_at_target hstInj hcurrentPos]
        have hchildCell : IsCell (breakout n st.lab st.ptn (level + 1) tc
            tv).2.1 (level + 1) tc 1 := by
          rw [breakout_ptn]
          exact isCell_breakout_target (n := n) (lab := st.lab) (tv := tv) htcPtn
            hh.inv.currentCell.2.1
        have houtAt : out.canonlab[tc]! = tv := by
          rw [← hchildAt]
          exact (cellsPerm_singleton hnew.2 hchildCell).symm
        have hperm := hh.inv.childCanonPerm hcurrent hat hcsz hnew.2
        have hperm' : cellsPerm rsPtn level rsLab out.canonlab := by
          rw [hh.inv.ptnEq] at hperm
          exact cellsPerm_trans hh.inv.labPerm hperm
        refine ⟨offset, hoffset, hdone, ?_, ?_⟩
        · rw [hcanonlabRec, houtAt, hatFrozen]
        · rw [hcanonlabRec]
          exact hperm'
  have hshortRec : recSt.needshortprune = false := by
    rw [show recSt = recover n inf level cleared from rfl,
      recover_needshortprune]
    exact hshort
  have hnclRec : recSt.noncheaplevel = if level < out.noncheaplevel
      then level + 1 else out.noncheaplevel := by
    rw [show recSt = recover n inf level cleared from rfl,
      recover_noncheaplevel, hncl]
  have hboundaryChild : out.noncheaplevel < level + 1 →
      out.noncheaplevel = st.noncheaplevel := hkeep.boundary
  refine ⟨bs', ?_⟩
  refine ⟨?_, hlive, hpath, ?_, ?_, ?_, hgfRec, hfirstTrail, hcanonTrail,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact {
      nonempty := hh.inv.nonempty
      positive := hh.inv.positive
      baseOk := hh.inv.baseOk
      run := hrun
      effect := heffect
      baseLab := hh.inv.baseLab
      basePtn := hh.inv.basePtn
      equitable := hh.inv.equitable
      cell := hh.inv.cell
      lenTwo := hh.inv.lenTwo
      range := hh.inv.range
      values := hh.inv.values
      members := hh.inv.members
      cover := hcover
      refs := hrefs
      shortClear := hshortRec
      fuelBound := hh.inv.fuelBound }
  · obtain ⟨v, hv, hle⟩ := hh.after
    have ha := nextElem_after hnext
    rw [hv] at ha
    simp only [After] at ha
    exact ⟨tv, rfl, by omega⟩
  · intro v hv
    cases hv
    exact hh.inv.nextLt hnext
  · apply recover_nonpositive
    rw [hcomp]
    exact hchild.node.event.nonpositive
  · rw [recover_orbits, recover_genTrace, horb, hgen]
    exact hkeep.orbits
  · rw [recover_coset, hcos]
    change out.cosetindex < n
    rw [hchild.coset]
    exact hh.inv.nextLt hnext
  · intro b hb
    obtain ⟨b0, hb0⟩ : ∃ b0, best = some b0 :=
      ⟨_, hh.inv.run.incumbent⟩
    obtain ⟨b', hb', hle⟩ := hgrows b0 hb0
    have hbb : b = b' := Option.some.inj (hb.symm.trans hb')
    subst hbb
    rw [hfirstlabRec]
    exact keyLe_trans (hh.firstDom b0 hb0) hle
  · intro hlt
    rw [hnclRec] at hlt
    rcases Decidable.em (level < out.noncheaplevel) with hc | hc
    · rw [ite_eq_left hc] at hlt
      exfalso
      omega
    · rw [ite_eq_right hc] at hlt
      rw [hboundaryChild (by omega)] at hlt
      exact hh.desc hlt
  · rw [hnclRec]
    rcases Decidable.em (level < out.noncheaplevel) with hc | hc
    · exact Nat.le_of_eq (ite_eq_left hc)
    · rw [ite_eq_right hc]
      omega
  · intro hpark
    rw [hnclRec]
    rcases Decidable.em (level < out.noncheaplevel) with hc | hc
    · rw [ite_eq_left hc]
      omega
    · rw [ite_eq_right hc]
      rw [hboundaryChild (by omega)]
      exact hh.park hpark
  · intro hlt
    rw [hnclRec] at hlt ⊢
    rcases Decidable.em (level < out.noncheaplevel) with hc | hc
    · rw [ite_eq_left hc] at hlt
      exfalso
      omega
    · rw [ite_eq_right hc] at hlt ⊢
      rw [hboundaryChild (by omega)] at hlt ⊢
      exact hh.keep hlt

end FirstSweepHyp

/-- Clearing the request keeps the labelling and partition. -/
theorem clearShortIf_lab (clear : Bool) (st : SearchSt n) :
    (clearShortIf clear st).lab = st.lab := by
  cases clear <;> rfl

theorem clearShortIf_ptn (clear : Bool) (st : SearchSt n) :
    (clearShortIf clear st).ptn = st.ptn := by
  cases clear <;> rfl

/-- The receiving-loop validity of a child's live short-prune pair, from
the child's return bound alone. -/
theorem shortPairAtReceiver {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    {fix mcr : VSet n}
    (hpathCodes : level = codes.length)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hrBelow : r < Int.ofNat (level + 1))
    (hevent : EventOut G ctx tcLevel codes fs out outBest eventTrail r)
    (hpreserved : TrailExt (level + 1)
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail)
    (hsource : ShortSource G ctx out eventTrail r)
    (hstay : ¬ r < Int.ofNat level)
    (hback : out.autos.back? = some (fix, mcr)) :
    PairOk ctx.g rsPtn rsLab level fix mcr := by
  cases hsource with
  | explicit target sourceFix sourceMcr returned back valid =>
      have htargetBelow : target < level + 1 := by
        rw [returned] at hrBelow
        exact Int.ofNat_lt.mp hrBelow
      have hlevelLe : level ≤ target := by
        rw [returned] at hstay
        exact Int.ofNat_le.mp (Int.le_of_not_gt hstay)
      have htarget : target = level := by omega
      subst target
      have hp := valid
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
        hpreserved.pushAt
      have heq : (sourceFix, sourceMcr) = (fix, mcr) := by
        apply Option.some.inj
        rw [← back, ← hback]
      cases heq
      simpa only [sweepFrame] using hp
  | implicit target returned below back root =>
      have htargetBelow : target < level + 1 := by
        rw [returned] at hrBelow
        exact Int.ofNat_lt.mp hrBelow
      have hlevelLe : level ≤ target := by
        rw [returned] at hstay
        exact Int.ofNat_le.mp (Int.le_of_not_gt hstay)
      have htarget : target = level := by omega
      subst target
      have hp := hinv.fmptnPair hpathCodes hpath hevent hpreserved
        (Nat.le_of_lt below) root
      have heq :
          (fmptn out.lab out.ptn out.noncheaplevel n) = (fix, mcr) := by
        apply Option.some.inj
        rw [← back, ← hback]
      rw [heq] at hp
      exact hp

/-- Clearing the request exactly when it is raised leaves none. -/
theorem clearShortIf_self (st : SearchSt n) :
    (clearShortIf st.needshortprune st).needshortprune = false := by
  rcases h : st.needshortprune <;> simp [clearShortIf, h]

namespace FirstSweepHyp

/-- Both reference histories below the loop after an off-path child,
whatever its return. -/
theorem childTrails {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len tv offset currentOffset e tv1 : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best childBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
   
    (hh : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e tv1 base st best trail)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      out (numcells + 1) best childBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hfirstlab : out.firstlab = st.firstlab) :
    FirstTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
        eventTrail ∧
      CanonTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
        eventTrail := by
  have hext : TrailExt level trail eventTrail :=
    TrailExt.ofPush hchild.node.preserved
  refine ⟨hh.firstTrail.retrail hfirstlab hext, ?_⟩
  have hstLab : st.lab.size = n := by
    exact hh.inv.run.searchOk.labSize
  have hstPtn : st.ptn.size = n := by
    exact hh.inv.run.searchOk.ptnSize
  have hstEnd : st.ptn[st.ptn.size - 1]! ≤ level :=
    searchOk_end hh.inv.nonempty hh.inv.run.searchOk hh.inv.positive
  have hcsz : out.canonlab.size = n := by
    exact hchild.node.event.canonSize
  rcases hchild.canonGuide with hold | hnew
  · apply hh.canonTrail.retrail _ hext
    exact hold.2
  · have hperm := hh.inv.childCanonPerm hcurrent hat hcsz hnew.2
    exact (CanonTrail.ofPerm hh.inv.run.trailOk hstLab hstPtn hstEnd hperm
      hcsz).retrail rfl hext

end FirstSweepHyp

end Hex.GraphIso.Nauty
