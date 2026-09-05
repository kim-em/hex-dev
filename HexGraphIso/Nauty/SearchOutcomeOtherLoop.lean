/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeComplete
import all HexGraphIso.Nauty.Search

public section

/-!
Totality of one off-path sibling sweep, by induction on its cursor fuel,
assuming totality of every off-path child at the current executable
recursion fuel.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # State equations of one iteration -/

/-- Consume the one-shot short-prune request when it is raised. -/
@[expose] def clearShortIf (clear : Bool) (st : SearchSt n) : SearchSt n :=
  if clear then { st with needshortprune := false } else st

theorem clearShortIf_fields (clear : Bool) (st : SearchSt n) :
    (clearShortIf clear st).fixedpts = st.fixedpts ∧
    (clearShortIf clear st).cosetindex = st.cosetindex ∧
    (clearShortIf clear st).compCanon = st.compCanon ∧
    (clearShortIf clear st).genTrace = st.genTrace ∧
    (clearShortIf clear st).orbits = st.orbits ∧
    (clearShortIf clear st).firstlab = st.firstlab ∧
    (clearShortIf clear st).noncheaplevel = st.noncheaplevel ∧
    (clearShortIf clear st).gcaFirst = st.gcaFirst ∧
    (clearShortIf clear st).gcaCanon = st.gcaCanon ∧
    (clearShortIf clear st).canonlab = st.canonlab ∧
    (clearShortIf clear st).autos = st.autos := by
  cases clear <;> simp [clearShortIf]

/-- Recovering a cleared state is the cleared recovery. -/
theorem recover_clearShortIf (n inf level : Nat) (clear : Bool)
    (st : SearchSt n) :
    recover n inf level (clearShortIf clear st) =
      clearShortIf clear (recover n inf level st) := by
  cases clear
  · rfl
  · exact recover_clearShort n inf level st

/-- Path facts ignore the one-shot short-prune request. -/
theorem PathOk.clearShortIf {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level : Nat} {st : SearchSt n} (clear : Bool)
    (h : PathOk ctx rootPtn rootLab level st) :
    PathOk ctx rootPtn rootLab level (clearShortIf clear st) := by
  cases clear
  · exact h
  · exact h.stateEq rfl rfl rfl

/-- An early child return leaves the loop after cleaning the temporary
fixed vertex. -/
theorem otherChildLoop_early (ctx : Ctx n)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv : Nat) (tcell : VSet n)
    (st : SearchSt n) (value : Int) (out : SearchSt n)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (value, out))
    (hearly : value < Int.ofNat level) :
    otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell st =
      (some value, { out with fixedpts := out.fixedpts.erase tv }) := by
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_left hearly]

/-- A child that stays at the loop level continues with the recursive
tail on the recovered, possibly filtered, state. -/
theorem otherChildLoop_stay (ctx : Ctx n)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv : Nat) (tcell : VSet n)
    (st : SearchSt n) (value : Int) (out : SearchSt n)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (value, out))
    (hstay : ¬ value < Int.ofNat level) :
    let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
    let cleared := clearShortIf cleaned.needshortprune cleaned
    let tcell' := if cleaned.needshortprune then shortprune tcell cleared
      else tcell
    let tcell'' := if tv == tv1 then
      longprune tcell' cleared.fixedpts cleared.autos else tcell'
    otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell st =
      otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (tcell''.nextElem (some tv)) tcell'' (recover n inf level cleared) := by
  dsimp only
  conv =>
    lhs
    unfold otherChildLoop
    simp only [Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  unfold clearShortIf
  dsimp only
  split <;> split <;> rfl

/-! # Rebasing the receipt trail -/

namespace LoopExit

/-- A loop exit depends on its receipt trail only below the loop level. -/
theorem retrail {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tc len numcells : Nat} {tcell : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {source dest : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest source r) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell cursor bound st out best outBest dest r := by
  cases h with
  | done returned exact => exact .done returned exact
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below sound payload
        (located.retrail (htrail target below)) control
  | frozen value returned below exact freeze =>
      exact .frozen value returned below exact freeze
  | cheap boundary returned positive below saved exact =>
      exact .cheap boundary returned positive below saved exact
  | exhausted returned finalCursor progress bounded =>
      exact .exhausted returned finalCursor progress bounded

end LoopExit

namespace OtherLoopRun

/-- An off-path sweep result can be rebased onto any entry trail agreeing
below the loop level. -/
theorem retrail {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {source dest eventTrail : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest source eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      dest eventTrail r :=
  ⟨h.proof.retrail htrail, h.exit.retrail htrail, h.short⟩

end OtherLoopRun

/-! # Hypotheses shared by every state of one off-path sweep -/

/-- What an off-path sibling sweep knows at every cursor position:
the established loop invariant, the live package, path facts, guide and
orbit facts, and the cheap-cell boundary discipline relative to the node
entry boundary `e`. -/
structure OtherLoopHyp (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel level : Nat) (codes bs fs : List Nat)
    (numcells : Nat) (rsLab rsPtn : Array Nat) (tc len : Nat) (tcell : VSet n)
    (cursor : Option Nat) (e : Nat) (base st : SearchSt n)
    (best : Option (Key n)) (trail : FrameTrail) : Prop where
  inv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab
    rsPtn tc len tcell cursor base st best trail
  live : OtherLive ctx level st trail
  path : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
    (initialPartition G).1 level st
  cursorLt : ∀ v, cursor = some v → v < n
  sign : st.compCanon ≤ 0 ∨ cursor = none
  start : cursor = none → tcell = windowSet n rsLab tc len
  guide : GuideRel level base st
  baseCanon : base.gcaCanon ≤ level
  orbits : OrbSound (OrbConn st.genTrace.toList n) st.orbits n
  coset : st.cosetindex < n
  firstDom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b
  desc : CheapDesc ctx level st.noncheaplevel
    (LoopInv.frame rsLab rsPtn numcells)
  bnd : st.noncheaplevel ≤ level + 1
  park : cheapautom rsPtn level n = false → st.noncheaplevel = level + 1
  keep : st.noncheaplevel < level → st.noncheaplevel = e

/-- What a finished off-path sweep preserves for its enclosing node. -/
structure OtherLoopKeep (ctx : Ctx n) (level e : Nat) (st out : SearchSt n) :
    Prop where
  firstlab : out.firstlab = st.firstlab
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  boundary : out.noncheaplevel < level → out.noncheaplevel = e

namespace OtherLoopHyp

/-- The cheap-cell ledger is ready for the next child. -/
theorem cheapOk {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {e : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} (hg : ctx.g = rowsOf G)
    (h : OtherLoopHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e base st best trail) :
    CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) (level + 1) st := by
  apply BoundaryOk.nextCheap _ h.inv.run
  rcases hc : cheapautom rsPtn level n with _ | _
  · intro heq
    have := h.park hc
    omega
  · apply BoundaryOk.ofCheap hg h.inv
    rw [h.inv.ptnEq]
    exact hc

end OtherLoopHyp

/-! # The sweep induction -/

set_option maxHeartbeats 3200000 in
/-- Totality of an off-path sibling sweep at every cursor fuel exceeding
the remaining cursor range, given totality of its children. -/
theorem otherLoopTotal {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tv1 tail e : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat} {base : SearchSt n}
    {bound : Key n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hrun : n + 2 < level + 1 + runFuel)
    (hspec : level + 1 + specFuel = n + 1)
    (hpath : level = codes.length) (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1) :
    ∀ (loopFuel : Nat) (cursor : Option Nat) (tcell : VSet n) (st : SearchSt n)
      (best : Option (Key n)) (trail : FrameTrail) (bs : List Nat),
      OtherLoopHyp G ctx tcLevel specFuel level codes bs fs numcells rsLab
        rsPtn tc len tcell cursor e base st best trail →
      n < cursorRank cursor + loopFuel →
      ∃ outBest eventTrail,
        OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
            fs rsLab rsPtn tc len numcells tcell cursor bound st
            (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell st).2
            best outBest trail eventTrail
            (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell st).1 ∧
          GuideRel level base
            (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell st).2 ∧
          OtherLoopKeep ctx level e st
            (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell st).2 := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro cursor tcell st best trail bs hh hfuel
      exfalso
      have := cursorRank_le hh.cursorLt
      omega
  | succ loopFuel ihLoop =>
    intro cursor tcell st best trail bs hh hfuel
    have hgsz : ctx.g.size = n := by
      rw [hg]
      exact size_rowsOf G
    have hsymm : ∀ u v, u < n → v < n →
        (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
      rw [hg]
      exact rowsOf_symm G
    have hloopless : ∀ v, v < n → (ctx.g[v]!).mem v = false := by
      rw [hg]
      exact rowsOf_loopless G
    have hlevelLt : level < n := hh.inv.levelLt
    have hfuelNe : runFuel ≠ 0 := by
      intro h0
      rw [h0] at hrun
      omega
    have hcodesLen : codes.length = level := hpath.symm
    have hshorter : stem.length < codes.length := by
      rw [← hpath]
      exact hpast
    rcases hnext : tcell.nextElem cursor with _ | tv
    · -- the sweep is finished
      have hnp : st.compCanon ≤ 0 := by
        rcases hh.sign with h | hcur
        · exact h
        · exfalso
          have htcell := hh.start hcur
          subst hcur
          rw [htcell] at hnext
          obtain ⟨v, hv⟩ := nextElem_windowSet_some (lab := rsLab) (tc := tc)
            (len := len) (by omega) (hh.inv.frozenLabOk _ (by
              rw [hh.inv.frozenLabSize]
              have := hh.inv.range
              have := hh.inv.lenTwo
              omega))
          rw [hv] at hnext
          cases hnext
      have hsame : (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
          level numcells tc tv1 none tcell st).2 = st := by
        unfold otherChildLoop
        rfl
      refine ⟨best, trail, ?_, ?_, ?_⟩
      · exact OtherLoopRun.done (inf := inf) (runFuel := runFuel)
          (loopFuel := loopFuel) (tv1 := tv1) hpath hstem hpast hnext hnp
          hbound hlen hh.inv hh.live.toLive
      · rw [hsame]
        exact hh.guide
      · rw [hsame]
        exact ⟨rfl, hh.orbits, hh.keep⟩
    · -- one more child
      have hcheapOk := hh.cheapOk hg
      obtain ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen, hat,
          hnodeChild⟩ :=
        hh.inv.child (coset := st.cosetindex) hnext hcheapOk
      rw [hat] at hnodeChild
      have hlabOk : LabOk st.lab n := by
        exact labOk_of_reach hh.inv.run.searchOk.labSize
          hh.inv.run.searchOk.reach
      have hinj : LabInj st.lab n := by
        exact labInj_of_reach hh.inv.run.searchOk.labSize hh.inv.nonempty
          hh.inv.run.searchOk.reach
      have hsz : st.lab.size = n := by
        exact hh.inv.run.searchOk.labSize
      have hfresh : st.fixedpts.mem tv = false := by
        rw [← hat]
        exact hh.path.fixed.fresh hlabOk hinj hsz hh.inv.currentCell
          hh.inv.lenTwo hh.inv.range hcurrent
      -- the child and its packaged run
      let child : SearchSt n :=
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv }
      let childTrail := trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
      have hdescChild := hh.inv.childDesc hg hh.desc hh.park hcurrent hat
      have hliveChild : Live ctx (level + 1) child childTrail := by
        have := hh.inv.otherChildLive hh.live offset currentOffset
        rw [hat] at this
        exact this
      have hpathChild : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
          (initialPartition G).1 (level + 1) child := by
        have := hh.path.breakout hh.inv hcurrent
        rw [hat] at this
        exact this
      obtain ⟨childBest, eventTrail, hrunChild, hkeepChild⟩ :=
        ih specFuel (level + 1) (numcells + 1) codes bs fs child best
          childTrail hg hinf hn0 (by omega) (by omega) (by omega)
          (by omega) hh.bnd hdescChild hnodeChild hliveChild hpathChild
          hh.orbits hh.coset hh.firstDom
      let res := otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        child
      have hcall : otherNode ctx inf tcLevel runFuel (level + 1)
          (numcells + 1) child = (res.1, res.2) := rfl
      have heq := hh.inv.childKeyAll hoffset hatFrozen hat
      have hkeyLe : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
          child (numcells + 1)) bound := by
        rw [← heq offset hoffset hatFrozen]
        exact LoopInv.keyLeBound hbound hlen hoffset
      have hsoundChild : NodeSound ctx tcLevel specFuel (level + 1) codes
          child (numcells + 1) best childBest :=
        hrunChild.toProof.outcome.node.receipt.sound hfuelNe
      have hgrows : IncGrows best childBest := hrunChild.grows hfuelNe
      have hguideChild : GuideRel level base res.2 :=
        GuideRel.ofChild hh.inv hh.guide hcurrent hat hrunChild
      have hfirstlabChild : res.2.firstlab = st.firstlab :=
        hkeepChild.firstlab
      have hboundaryChild : res.2.noncheaplevel < level + 1 →
          res.2.noncheaplevel = st.noncheaplevel :=
        hkeepChild.boundary
      have htrailExt : TrailExt level trail eventTrail :=
        TrailExt.ofPush hrunChild.node.preserved
      by_cases hstay : res.1 < Int.ofNat level
      · -- early exit
        have hstate := otherChildLoop_early ctx inf tcLevel runFuel loopFuel
          level numcells tc tv1 tv tcell st res.1 res.2 hcall hstay
        have hguideOut : GuideRel level base
            (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
              numcells tc tv1 (some tv) tcell st).2 := by
          rw [hstate]
          exact hguideChild.stateEq rfl rfl rfl
        have hkeepOut : OtherLoopKeep ctx level e st
            (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
              numcells tc tv1 (some tv) tcell st).2 := by
          rw [hstate]
          refine ⟨hfirstlabChild, hkeepChild.orbits, ?_⟩
          intro hlt
          change res.2.noncheaplevel < level at hlt
          change res.2.noncheaplevel = e
          have hb := hboundaryChild (Nat.lt_succ_of_lt hlt)
          rw [hb] at hlt ⊢
          exact hh.keep hlt
        refine ⟨childBest, eventTrail, ?_, hguideOut, hkeepOut⟩
        rcases hexit : hrunChild.node.exit with
          ⟨returned, exact⟩ |
          ⟨target, returned, below, sound, payload, located, control⟩ |
          ⟨below, exact, freeze⟩ |
          ⟨boundary, returned, positive, atOrAbove, saved, exact⟩ |
          ⟨returned, state, incumbent, emptyFuel⟩
        · exfalso
          rw [returned] at hstay
          simp only [Int.ofNat_eq_natCast] at hstay
          omega
        · have hbelowNat : target < level := by
            rw [returned] at hstay
            exact Int.ofNat_lt.mp hstay
          exact OtherLoopRun.unwind hstem hshorter hsoundChild hkeyLe returned
            hbelowNat payload located control hrunChild hfresh
        · exact OtherLoopRun.childFrozen hpath hstem hshorter hcall hrunChild
            hstay freeze exact hkeyLe hbound hlen
            (hh.inv.cover.advanceKey hnext exact heq) hfresh
        · have hbelowNat : boundary ≤ level := by
            rw [returned] at hstay
            simp only [Int.ofNat_eq_natCast] at hstay
            omega
          have hle : st.noncheaplevel ≤ level := by
            have h1 := hboundaryChild (by rw [saved]; omega)
            rw [saved] at h1
            omega
          have hsmall := hh.inv.subtreeAt hh.desc hh.park hle
          have hboundEq : bound = nodeKey ctx tcLevel specFuel (level + 1)
              codes child (numcells + 1) := by
            rw [← heq offset hoffset hatFrozen]
            exact hh.inv.boundEq hsmall hgsz hsymm hloopless hbound hlen
              hoffset
          rw [returned] at hcall hrunChild
          exact OtherLoopRun.childCheap hstem hshorter hcall hrunChild positive
            hbelowNat saved hboundEq exact hfresh
        · exact (hfuelNe emptyFuel).elim
      · -- the child stays at the loop level
        have hstateEq := otherChildLoop_stay ctx inf tcLevel runFuel loopFuel
          level numcells tc tv1 tv tcell st res.1 res.2 hcall hstay
        dsimp only at hstateEq
        have hout : SearchOut G level (level + 1) child res.2 := by
          have := otherNode_ok G ctx inf hinf tcLevel hn0 runFuel
            (level + 1) (numcells + 1) child hnodeChild.run.searchOk
            (by omega) (by omega)
          rw [Nat.add_sub_cancel] at this
          exact this
        have hchildOutcome' : OtherOutcome G ctx tcLevel specFuel runFuel
            (level + 1) codes fs
            { st with
              lab := (breakout n st.lab st.ptn (level + 1) tc
                st.lab[tc + currentOffset]!).1
              ptn := (breakout n st.lab st.ptn (level + 1) tc
                st.lab[tc + currentOffset]!).2.1
              active := (breakout n st.lab st.ptn (level + 1) tc
                st.lab[tc + currentOffset]!).2.2
              fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
            res.2 (numcells + 1) best childBest childTrail eventTrail res.1 := by
          rw [hat]
          exact hrunChild.toProof.outcome
        have hout' : SearchOut G level (level + 1)
            { st with
              lab := (breakout n st.lab st.ptn (level + 1) tc
                st.lab[tc + currentOffset]!).1
              ptn := (breakout n st.lab st.ptn (level + 1) tc
                st.lab[tc + currentOffset]!).2.1
              active := (breakout n st.lab st.ptn (level + 1) tc
                st.lab[tc + currentOffset]!).2.2
              fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
            res.2 := by
          rw [hat]
          exact hout
        have heq' : ∀ o, o < len → rsLab[tc + o]! = tv →
            sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
              numcells o =
            nodeKey ctx tcLevel specFuel (level + 1) codes
              { st with
                lab := (breakout n st.lab st.ptn (level + 1) tc
                  st.lab[tc + currentOffset]!).1
                ptn := (breakout n st.lab st.ptn (level + 1) tc
                  st.lab[tc + currentOffset]!).2.1
                active := (breakout n st.lab st.ptn (level + 1) tc
                  st.lab[tc + currentOffset]!).2.2
                fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
              (numcells + 1) := by
          rw [hat]
          exact heq
        have hfixedChild : res.2.fixedpts =
            st.fixedpts.insert st.lab[tc + currentOffset]! := by
          rw [hrunChild.node.fixed, hat]
        have hpathRec := hh.inv.recoverPath hh.path hout' hfixedChild hinf
          hcurrent
        rw [hat] at hpathRec
        have hpre : LoopSound ctx bound best childBest :=
          LoopSound.ofNode hsoundChild hkeyLe
        have hnp : res.2.compCanon ≤ 0 := hrunChild.node.event.nonpositive
        have hcosetChild : res.2.cosetindex = st.cosetindex := hrunChild.coset
        let cleaned : SearchSt n := { res.2 with fixedpts := res.2.fixedpts.erase tv }
        -- the recursive tail, parametric in the filtered set and clearing
        have htail : ∀ (tcell' : VSet n) (clear : Bool) (bs' : List Nat),
            LoopInv G ctx tcLevel specFuel level codes bs' fs numcells rsLab
              rsPtn tc len tcell' (some tv) base
              (recover n inf level (clearShortIf clear cleaned)) childBest
              eventTrail →
            OtherLive ctx level
              (recover n inf level (clearShortIf clear cleaned))
              eventTrail →
            ∃ outBest eventTrail',
              OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
                  codes fs rsLab rsPtn tc len numcells tcell' (some tv) bound
                  (recover n inf level (clearShortIf clear cleaned))
                  (otherChildLoop ctx inf tcLevel runFuel loopFuel level
                    numcells tc tv1 (tcell'.nextElem (some tv)) tcell'
                    (recover n inf level (clearShortIf clear cleaned))).2
                  childBest outBest eventTrail eventTrail'
                  (otherChildLoop ctx inf tcLevel runFuel loopFuel level
                    numcells tc tv1 (tcell'.nextElem (some tv)) tcell'
                    (recover n inf level (clearShortIf clear cleaned))).1 ∧
                GuideRel level base
                  (otherChildLoop ctx inf tcLevel runFuel loopFuel level
                    numcells tc tv1 (tcell'.nextElem (some tv)) tcell'
                    (recover n inf level (clearShortIf clear cleaned))).2 ∧
                OtherLoopKeep ctx level e st
                  (otherChildLoop ctx inf tcLevel runFuel loopFuel level
                    numcells tc tv1 (tcell'.nextElem (some tv)) tcell'
                    (recover n inf level (clearShortIf clear cleaned))).2 := by
          intro tcell' clear bs' hinvRec hliveRec
          obtain ⟨hfix, hcos, hcomp, hgen, horb, hfl, hncl, hgf, hgc, hcl, -⟩ :=
            clearShortIf_fields clear cleaned
          let cleared := clearShortIf clear cleaned
          let recSt := recover n inf level cleared
          have hframes := recover_frames n inf level cleared
          have hnclRec : recSt.noncheaplevel = if level < res.2.noncheaplevel
              then level + 1 else res.2.noncheaplevel := by
            rw [show recSt = recover n inf level cleared from rfl,
              recover_noncheaplevel, hncl]
          have hhRec : OtherLoopHyp G ctx tcLevel specFuel level codes bs' fs
              numcells rsLab rsPtn tc len tcell' (some tv) e base recSt
              childBest eventTrail := by
            refine ⟨hinvRec, hliveRec, ?_, ?_, ?_, ?_, ?_, hh.baseCanon,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [show recSt = recover n inf level cleared from rfl,
                show cleared = clearShortIf clear cleaned from rfl,
                recover_clearShortIf]
              exact hpathRec.1.clearShortIf clear
            · intro v hv
              cases hv
              exact hh.inv.nextLt hnext
            · left
              rw [show recSt = recover n inf level cleared from rfl]
              exact recover_nonpositive (by rw [hcomp]; exact hnp)
            · intro h
              cases h
            · exact ((hguideChild.stateEq hgf hgc hcl).recover
                hh.baseCanon hliveRec.toLive.order)
            · rw [show recSt = recover n inf level cleared from rfl,
                recover_orbits, recover_genTrace, horb, hgen]
              exact hkeepChild.orbits
            · rw [show recSt = recover n inf level cleared from rfl,
                recover_coset, hcos]
              change res.2.cosetindex < n
              rw [hcosetChild]
              exact hh.coset
            · intro b hb
              obtain ⟨b0, hb0⟩ : ∃ b0, best = some b0 :=
                ⟨_, hh.inv.run.incumbent⟩
              obtain ⟨b', hb', hle⟩ := hgrows b0 hb0
              have hbb : b = b' := Option.some.inj (hb.symm.trans hb')
              subst hbb
              rw [show recSt = recover n inf level cleared from rfl,
                recover_firstlab, hfl]
              change keyLe (pathLeafKey ctx fs res.2.firstlab) b
              rw [hfirstlabChild]
              exact keyLe_trans (hh.firstDom b0 hb0) hle
            · intro hlt
              rw [hnclRec] at hlt
              rcases Decidable.em (level < res.2.noncheaplevel) with hc | hc
              · rw [ite_eq_left hc] at hlt
                exfalso
                omega
              · rw [ite_eq_right hc] at hlt
                rw [hboundaryChild (by omega)] at hlt
                exact hh.desc hlt
            · rw [hnclRec]
              rcases Decidable.em (level < res.2.noncheaplevel) with hc | hc
              · exact Nat.le_of_eq (ite_eq_left hc)
              · rw [ite_eq_right hc]
                omega
            · intro hpark
              rw [hnclRec]
              rcases Decidable.em (level < res.2.noncheaplevel) with hc | hc
              · rw [ite_eq_left hc]
              · rw [ite_eq_right hc]
                have := hboundaryChild (by omega)
                have := hh.park hpark
                omega
            · intro hlt
              rw [hnclRec] at hlt ⊢
              rcases Decidable.em (level < res.2.noncheaplevel) with hc | hc
              · rw [ite_eq_left hc] at hlt
                exfalso
                omega
              · rw [ite_eq_right hc] at hlt ⊢
                rw [hboundaryChild (by omega)] at hlt ⊢
                exact hh.keep hlt
          have hfuelRec : n < cursorRank (some tv) + loopFuel :=
            cursorFuel_step (nextElem_after hnext) hfuel
          obtain ⟨outBest, eventTrail', hrunTail, hguideTail, hkeepTail⟩ :=
            ihLoop (some tv) tcell' recSt childBest eventTrail bs' hhRec
              hfuelRec
          refine ⟨outBest, eventTrail', hrunTail, hguideTail, ?_⟩
          refine ⟨?_, hkeepTail.orbits, hkeepTail.boundary⟩
          rw [hkeepTail.firstlab,
            show recSt = recover n inf level cleared from rfl,
            recover_firstlab, hfl]
          exact hfirstlabChild
        have hfixedRec : ∀ clear,
            (recover n inf level (clearShortIf clear cleaned)).fixedpts =
              st.fixedpts := by
          intro clear
          rw [recover_clearShortIf, (clearShortIf_fields clear _).1]
          exact hpathRec.2
        have hcosetRec : ∀ clear,
            (recover n inf level (clearShortIf clear cleaned)).cosetindex =
              st.cosetindex := by
          intro clear
          rw [recover_clearShortIf, (clearShortIf_fields clear _).2.1,
            recover_coset]
          exact hcosetChild
        rcases hshortC : res.2.needshortprune with _ | _
        · -- no short-prune request
          obtain ⟨bs', hinvRec, hliveRec⟩ := OtherOutcome.next hh.inv hh.live
            hchildOutcome' hout' hinf hcodesLen hfuelNe hstay hnext hoffset
            hcurrent hatFrozen hat heq' hshortC
          rcases hother : (tv == tv1) with _ | _
          · -- ordinary child
            obtain ⟨outBest, eventTrail', hrunTail, hguideTail, hkeepTail⟩ :=
              htail tcell false bs' hinvRec hliveRec
            refine ⟨outBest, eventTrail', ?_, ?_, ?_⟩
            · exact (OtherLoopRun.next hnext hcall hstay hshortC hother rfl
                (hfixedRec false) (hcosetRec false) hpre rfl hrunTail).retrail
                htrailExt
            · rw [hstateEq]
              simp only [hshortC, Bool.false_eq_true, ite_false, hother]
              simpa only [cleaned, hshortC, clearShortIf, Bool.false_eq_true, ite_false,
                ite_true] using hguideTail
            · rw [hstateEq]
              simp only [hshortC, Bool.false_eq_true, ite_false, hother]
              simpa only [cleaned, hshortC, clearShortIf, Bool.false_eq_true, ite_false,
                ite_true] using hkeepTail
          · -- guiding child: long prune
            have hinvLong := hinvRec.longprune hgsz hpathRec.1
            rw [recover_fixedpts, (recover_store _ _ _ _).2] at hinvLong
            obtain ⟨outBest, eventTrail', hrunTail, hguideTail, hkeepTail⟩ :=
              htail (longprune tcell cleaned.fixedpts cleaned.autos) false bs'
                hinvLong hliveRec
            refine ⟨outBest, eventTrail', ?_, ?_, ?_⟩
            · exact (OtherLoopRun.nextLong hnext hcall hstay hshortC hother
                rfl rfl (hfixedRec false) (hcosetRec false) hpre rfl
                hrunTail).retrail htrailExt
            · rw [hstateEq]
              simp only [hshortC, Bool.false_eq_true, ite_false, hother,
                ite_true]
              simpa only [cleaned, hshortC, clearShortIf, Bool.false_eq_true, ite_false,
                ite_true] using hguideTail
            · rw [hstateEq]
              simp only [hshortC, Bool.false_eq_true, ite_false, hother,
                ite_true]
              simpa only [cleaned, hshortC, clearShortIf, Bool.false_eq_true, ite_false,
                ite_true] using hkeepTail
        · -- a short-prune request from the child
          obtain ⟨bs', hinvRec0, hliveRec⟩ := OtherOutcome.nextClear hh.inv
            hh.live hchildOutcome' hout' hinf hcodesLen hfuelNe hstay hnext
            hoffset hcurrent hatFrozen hat heq'
          have hlast : ∀ fix mcr : VSet n,
              (clearShortIf true cleaned).autos.back? = some (fix, mcr) →
                PairOk ctx.g rsPtn rsLab level fix mcr := by
            intro fix mcr hback
            apply LoopInv.ShortSource.atReceiver hpath hh.inv hh.path
              hrunChild.node.exit hrunChild.node.event
              hrunChild.node.preserved (hrunChild.node.short hshortC) hstay
            simpa only [clearShortIf, cleaned, ite_true] using hback
          have hinvRec := hinvRec0.shortpruneWith hgsz hlast
          rcases hother : (tv == tv1) with _ | _
          · obtain ⟨outBest, eventTrail', hrunTail, hguideTail, hkeepTail⟩ :=
              htail (shortprune tcell (clearShortIf true cleaned)) true bs'
                hinvRec hliveRec
            refine ⟨outBest, eventTrail', ?_, ?_, ?_⟩
            · exact (OtherLoopRun.nextShort hnext hcall hstay hshortC hother
                rfl rfl (hfixedRec true) (hcosetRec true) hpre rfl
                hrunTail).retrail htrailExt
            · rw [hstateEq]
              simp only [hshortC, ite_true, hother, Bool.false_eq_true,
                ite_false]
              simpa only [cleaned, hshortC, clearShortIf, Bool.false_eq_true, ite_false,
                ite_true] using hguideTail
            · rw [hstateEq]
              simp only [hshortC, ite_true, hother, Bool.false_eq_true,
                ite_false]
              simpa only [cleaned, hshortC, clearShortIf, Bool.false_eq_true, ite_false,
                ite_true] using hkeepTail
          · have hpathClear := hpathRec.1.clearShortIf true
            rw [← recover_clearShortIf] at hpathClear
            have hinvBoth := hinvRec.longprune hgsz hpathClear
            rw [recover_fixedpts, (recover_store _ _ _ _).2] at hinvBoth
            obtain ⟨outBest, eventTrail', hrunTail, hguideTail, hkeepTail⟩ :=
              htail (longprune (shortprune tcell (clearShortIf true cleaned))
                (clearShortIf true cleaned).fixedpts
                (clearShortIf true cleaned).autos) true bs' hinvBoth hliveRec
            refine ⟨outBest, eventTrail', ?_, ?_, ?_⟩
            · exact (OtherLoopRun.nextBoth hnext hcall hstay hshortC hother
                rfl rfl rfl (hfixedRec true) (hcosetRec true) hpre rfl
                hrunTail).retrail htrailExt
            · rw [hstateEq]
              simp only [hshortC, ite_true, hother]
              simpa only [cleaned, hshortC, clearShortIf, Bool.false_eq_true, ite_false,
                ite_true] using hguideTail
            · rw [hstateEq]
              simp only [hshortC, ite_true, hother]
              simpa only [cleaned, hshortC, clearShortIf, Bool.false_eq_true, ite_false,
                ite_true] using hkeepTail

end Hex.GraphIso.Nauty
