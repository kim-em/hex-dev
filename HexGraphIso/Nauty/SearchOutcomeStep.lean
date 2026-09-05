/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeGate
import all HexGraphIso.Nauty.Search

public section

/-!
Per-child transport for the off-path sibling sweep: the guide relation to
the frozen loop entry, the small-cell descent invariant into each
individualized child, and the key identification used by every early
exit.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Key identification -/

/-- The node key reads only the labelling, partition, and active set. -/
theorem nodeKey_congr {ctx : Ctx} {tcLevel fuel level numcells : Nat}
    {cs : List Nat} {st st' : SearchSt}
    (hlab : st'.lab = st.lab) (hptn : st'.ptn = st.ptn)
    (hactive : st'.active = st.active) :
    nodeKey ctx tcLevel fuel level cs st' numcells =
      nodeKey ctx tcLevel fuel level cs st numcells := by
  unfold nodeKey
  rw [hlab, hptn, hactive]

/-- Every frozen offset carrying the selected vertex has the key of the
executable child built from it. -/
theorem LoopInv.childKeyAll {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell tv offset currentOffset
      : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hoffset : offset < len)
    (hfrozen : rsLab[tc + offset]! = tv)
    (hcurrent : currentOffset < len)
    (hcurrentAt : st.lab[tc + currentOffset]! = tv) :
    ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := insert st.fixedpts tv }
          (numcells + 1) := by
  intro o ho hotv
  have hinj : LabInj rsLab ctx.n := by
    rw [← h.baseLab, h.nodeCount]
    exact labInj_of_reach h.baseOk.labSize h.nonempty h.baseOk.reach
  have hoo : o = offset := by
    have := hinj.eq_of_getElem! (i := tc + o) (j := tc + offset)
      (by have := h.range; omega) (by have := h.range; omega)
      (hotv.trans hfrozen.symm)
    omega
  subst hoo
  have hkey := h.childKey (coset := st.cosetindex) ho hotv hcurrentAt
  rw [hcurrentAt] at hkey
  rw [hkey]

/-- The start of a sweep always has a first vertex. -/
theorem nextElem_windowSet_some {lab : Array Nat} {tc len : Nat}
    (hlen : 1 ≤ len) :
    ∃ v, nextElem (windowSet lab tc len) none = some v := by
  rcases hnext : nextElem (windowSet lab tc len) none with _ | v
  · exfalso
    have hmem : elem (windowSet lab tc len) lab[tc]! = true := by
      rw [elem_windowSet]
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), by simp⟩
    exact no_child_after hnext lab[tc]! hmem trivial
  · exact ⟨v, rfl⟩

/-! # Guide relation across one child -/

namespace GuideRel

/-- The guide relation depends only on the guide controls and the two
reference labellings. -/
theorem stateEq {level : Nat} {base st st' : SearchSt}
    (h : GuideRel level base st)
    (hfirst : st'.gcaFirst = st.gcaFirst)
    (hcanon : st'.gcaCanon = st.gcaCanon)
    (hcanonlab : st'.canonlab = st.canonlab) :
    GuideRel level base st' := by
  refine ⟨hfirst.trans h.first, ?_, ?_⟩
  · rw [hfirst, hcanon]
    exact h.order
  · rw [hcanon, hcanonlab]
    exact h.canon

/-- A completed or early-returning off-path child of a sweep keeps the
guide relation to the sweep's frozen entry. -/
theorem ofChild {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells tc len tcell tv currentOffset
      : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hguide : GuideRel level base st)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }
      out (numcells + 1) best outBest receiptTrail eventTrail r) :
    GuideRel level base out := by
  have hn := hinv.nodeCount
  subst n
  let child : SearchSt :=
    { st with
      lab := (breakout st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := insert st.fixedpts tv }
  have hfirst : out.gcaFirst = st.gcaFirst := hchild.firstGuide
  refine ⟨hfirst.trans hguide.first, hchild.order, ?_⟩
  rcases hchild.canonGuide with hold | hnew
  · rw [hold.1, hold.2]
    exact hguide.canon
  · right
    refine ⟨Nat.le_trans (Nat.le_succ level) hnew.1, ?_⟩
    have hok := hinv.run.searchOk
    have hstSize : st.lab.size = ctx.n := hok.labSize
    have hstPtnSize : st.ptn.size = ctx.n := hok.ptnSize
    have htcPtn : tc < st.ptn.size := by
      rw [hstPtnSize]
      exact Nat.lt_of_lt_of_le (by omega : tc < tc + len) hinv.range
    have hrangePtn : tc + len ≤ st.ptn.size := by
      rw [hstPtnSize]
      exact hinv.range
    have hchildPtn : child.ptn = st.ptn.set! tc (level + 1) :=
      breakout_ptn st.lab st.ptn (level + 1) tc tv
    have hchildOk : SearchOk G (level + 1) (numcells + 1) child := by
      apply breakout_searchOk hinv.nonempty hok hinv.positive
        hinv.currentCell hinv.lenTwo hinv.range hcurrent
      · change (breakout st.lab st.ptn (level + 1) tc tv).1 = _
        rw [hat]
      · exact breakout_ptn st.lab st.ptn (level + 1) tc tv
      · rfl
    have hfine : cellsPerm st.ptn level child.lab out.canonlab := by
      apply cellsPerm_coarsen (ptnF := child.ptn) (levF := level + 1)
      · rw [hchildPtn, Array.size_set!]
      · exact hchildOk.labSize.trans hchildOk.ptnSize.symm
      · rw [hchild.node.event.canonSize, hchildOk.ptnSize]
      · exact hnew.2
      · exact searchOk_end hinv.nonempty hchildOk (by omega)
      · exact searchOk_end hinv.nonempty hok hinv.positive
      · intro q hq
        rw [hchildPtn]
        rcases Decidable.em (tc = q) with rfl | hne
        · rw [Array.getElem!_set!_self _ _ _ htcPtn]
          exact Nat.le_refl _
        · rw [Array.getElem!_set!_ne _ _ _ _ hne]
          omega
    have hbreak : cellsPerm st.ptn level st.lab child.lab := by
      change cellsPerm st.ptn level st.lab
        (breakout st.lab st.ptn (level + 1) tc tv).1
      rw [← hat]
      exact breakout_cellsPerm hinv.currentCell hrangePtn
        (by rw [hstSize, hstPtnSize]) hcurrent
    have hperm : cellsPerm st.ptn level st.lab out.canonlab :=
      cellsPerm_trans hbreak hfine
    have hbasePtn : st.ptn = base.ptn := by
      rw [hinv.ptnEq, hinv.basePtn]
    rw [hbasePtn] at hperm
    have hbasePerm : cellsPerm base.ptn level base.lab st.lab :=
      hinv.effect.perm
    exact cellsPerm_trans hbasePerm hperm

/-- Recovery to the sweep level keeps the guide relation once the
sweep entry's canonical control is at most the sweep level. -/
theorem recover {ctx : Ctx} {level inf : Nat} {base out : SearchSt}
    (h : GuideRel level base out) (hbase : base.gcaCanon ≤ level)
    (horder : (Nauty.recover ctx.n inf level out).gcaFirst ≤
      (Nauty.recover ctx.n inf level out).gcaCanon) :
    GuideRel level base (Nauty.recover ctx.n inf level out) := by
  have hframes := recover_frames ctx.n inf level out
  refine ⟨hframes.2.2.2.2.2.2.1.trans h.first, horder, ?_⟩
  rw [recover_gcaCanon, hframes.1]
  rcases h.canon with hold | hnew
  · left
    refine ⟨?_, hold.2⟩
    rw [hold.1]
    exact ite_eq_right (Nat.not_lt_of_ge hbase)
  · right
    refine ⟨?_, hnew.2⟩
    split
    · exact Nat.le_refl level
    · exact hnew.1

end GuideRel

/-! # Small-cell descent into a child -/

/-- The subtree facts survive a change of the recorded active set. -/
theorem SubtreeOk.setActive {ctx : Ctx} {level : Nat} {r : RefineSt}
    {a : Nat} (h : SubtreeOk ctx level r) (ha : a < 2 ^ ctx.n) :
    SubtreeOk ctx level { r with active := a } :=
  ⟨⟨⟨h.it.ok.labSize, h.it.ok.labOk, h.it.ok.ptnSize, ha,
    h.it.ok.ptnEnd⟩, h.it.inj, h.it.vals, h.it.lvl⟩, h.eqt, h.acc,
    h.shape⟩

/-- The frozen frame of a sweep, as a refinement state. -/
@[expose] def LoopInv.frame (rsLab rsPtn : Array Nat) (numcells : Nat) :
    RefineSt :=
  { lab := rsLab, ptn := rsPtn, active := 0, numcells := numcells,
    hint := 0, maxpos := 0, longcode := numcells }

/-- A sweep frame with a live target cell has an open position. -/
theorem LoopInv.levelLt {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    level < ctx.n := by
  have hn := h.nodeCount
  subst hn
  have hbc := h.run.searchOk.bc
  rw [h.ptnEq] at hbc
  have hopen : rsPtn[tc]! > level := by
    have := h.cell.2.2.1 tc (Nat.le_refl tc) (by have := h.lenTwo; omega)
    omega
  have htc : tc < ctx.n := by
    have := h.range
    have := h.lenTwo
    omega
  have hne : bcount rsPtn level ctx.n ≠ ctx.n := by
    intro heq
    rw [bcount] at heq
    have hall := List.countP_eq_length.mp (by
      rw [heq, List.length_range])
    have := of_decide_eq_true (hall tc (List.mem_range.mpr htc))
    omega
  have hle := bcount_le rsPtn level ctx.n
  omega

/-- The small-cell descent invariant at the frozen frame transports to
the individualized child of the current recovered state. -/
theorem LoopInv.childDesc {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell tv currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hpark : cheapautom rsPtn level ctx.n = false →
      st.noncheaplevel = level + 1)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv) :
    CheapDesc ctx (level + 1) st.noncheaplevel
      (refine ctx (level + 1) (breakout st.lab st.ptn (level + 1) tc tv).1
        (breakout st.lab st.ptn (level + 1) tc tv).2.1
        (breakout st.lab st.ptn (level + 1) tc tv).2.2 (numcells + 1)) := by
  have hn := h.nodeCount
  subst hn
  have hok := h.run.searchOk
  have hsz : st.lab.size = ctx.n := hok.labSize
  have hpsz : rsPtn.size = ctx.n := h.frozenPtnSize
  have hlabOk : LabOk st.lab ctx.n :=
    labOk_of_reach hok.labSize hok.reach
  have hinj : LabInj st.lab ctx.n :=
    labInj_of_reach hok.labSize h.nonempty hok.reach
  let cur : RefineSt := { LoopInv.frame rsLab rsPtn numcells with lab := st.lab }
  have hcur : CheapDesc ctx level st.noncheaplevel cur := by
    intro hlt
    exact (hdesc hlt).ofCellsPerm h.labPerm hsz hlabOk hinj
  have hend : rsPtn[rsPtn.size - 1]! ≤ level := h.frozenEnd
  have hit : IterOk ctx level cur := by
    refine ⟨⟨hsz, hlabOk, hpsz, Nat.two_pow_pos ctx.n, hend⟩, hinj, ?_, ?_⟩
    · intro q hq
      exact h.values q
    · exact Nat.le_of_lt h.levelLt
  have heq : Equitable ctx level cur.lab cur.ptn := by
    change Equitable ctx level st.lab rsPtn
    rw [← h.ptnEq]
    exact h.currentEquitable
  have hcount : bcount cur.ptn level ctx.n = cur.numcells := by
    change bcount rsPtn level ctx.n = numcells
    rw [← h.ptnEq]
    exact hok.count.symm
  have hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u := by
    rw [hg]
    exact rowsOf_symm G
  have hchild := hcur.child hit heq hcount hsymm h.levelLt h.cell h.lenTwo
    h.range hcurrent
  have hboundary : (if st.noncheaplevel ≥ level ∧
      ¬cheapautom cur.ptn level ctx.n then level + 1
      else st.noncheaplevel) = st.noncheaplevel := by
    change (if st.noncheaplevel ≥ level ∧
      ¬cheapautom rsPtn level ctx.n then level + 1
      else st.noncheaplevel) = st.noncheaplevel
    rcases hc : cheapautom rsPtn level ctx.n with _ | _
    · rw [hpark hc]
      simp
    · simp
  rw [hboundary] at hchild
  have hcurLab : cur.lab[tc + currentOffset]! = tv := hat
  rw [hcurLab] at hchild
  have hptn : st.ptn = rsPtn := h.ptnEq
  change CheapDesc ctx (level + 1) st.noncheaplevel
    (refine ctx (level + 1) (breakout st.lab rsPtn (level + 1) tc tv).1
      (rsPtn.set! tc (level + 1)) (insert 0 tc) (numcells + 1)) at hchild
  rw [breakout_ptn, hptn]
  exact hchild

/-- A small-cell subtree fact at the frozen frame, in the form the
sibling-sweep bound identification consumes. -/
theorem LoopInv.subtreeAt {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hpark : cheapautom rsPtn level ctx.n = false →
      st.noncheaplevel = level + 1)
    (hle : st.noncheaplevel ≤ level) (hact : base.active < 2 ^ ctx.n) :
    SubtreeOk ctx level
      { lab := rsLab, ptn := rsPtn, active := base.active,
        numcells := numcells, hint := 0, maxpos := 0,
        longcode := numcells } := by
  have hn := h.nodeCount
  subst hn
  have hsub : SubtreeOk ctx level (LoopInv.frame rsLab rsPtn numcells) := by
    apply hdesc.atLevel
    · refine ⟨⟨h.frozenLabSize, h.frozenLabOk, h.frozenPtnSize,
        Nat.two_pow_pos ctx.n, h.frozenEnd⟩, ?_, ?_, ?_⟩
      · rw [← h.baseLab]
        exact labInj_of_reach h.baseOk.labSize h.nonempty h.baseOk.reach
      · intro q hq
        exact h.values q
      · exact Nat.le_of_lt h.levelLt
    · exact h.equitable
    · change bcount rsPtn level ctx.n = numcells
      rw [← h.basePtn]
      exact h.baseOk.count.symm
    · exact hle
    · intro heq
      rcases hc : cheapautom rsPtn level ctx.n with _ | _
      · have := hpark hc
        omega
      · exact hc
  exact hsub.setActive hact

end Hex.GraphIso.Nauty
