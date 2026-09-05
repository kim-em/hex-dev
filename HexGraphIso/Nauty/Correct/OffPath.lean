/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Sweep
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.Domination

public section

/-!
Totality of the off-path subtree.

One sibling sweep by induction on its cursor fuel, the leaves that skip
the first-path admission check together with those whose check fails, one
internal node assembled from its sweep, and the off-path node step of the
totality induction.
-/

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

/-!
Packaged runs for the off-path leaves that do not enter the first-path
admission gate.

The comparison arms of `processnode` at a discrete off-path leaf are the
frozen-downward prune, the row tie, and the install or rejection of the
leaf against the incumbent.  The first two already have corrected runs;
the install and rejection arms return to the saved cheap-cell boundary and
are classified here as cheap exits.  The admitted first-path-agreeing leaf
is packaged as well, with the nonpositive comparison it needs derived from
domination of the first leaf by the incumbent.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Frame equations of the install and rejection arms -/

private theorem pushAuto_genTrace'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_orbits'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).orbits = st.orbits := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_needshortprune'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).needshortprune = st.needshortprune := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_noncheaplevel'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).noncheaplevel = st.noncheaplevel := by
  rw [pushAuto]
  split <;> rfl

/-- A comparison leaf that is not a row tie records no generator. -/
theorem processnode_plain_genTrace {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hnt : ¬(st.compCanon = 0 ∧ ¬(level < st.canonlevel) ∧
      (testcanlab ctx (updatecan ctx st.canong st.canonlab st.samerows)
        st.lab).1 = 0)) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.genTrace),
    pushAuto_genTrace'', ite_self]
  by_cases hcc : st.compCanon = 0 <;>
    by_cases hcanon : level < st.canonlevel <;>
    by_cases htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0 <;>
    simp [hnc, hef, hcc, hcanon, htie] <;> omega

/-- A comparison leaf that is not a row tie leaves the orbits alone. -/
theorem processnode_plain_orbits {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hnt : ¬(st.compCanon = 0 ∧ ¬(level < st.canonlevel) ∧
      (testcanlab ctx (updatecan ctx st.canong st.canonlab st.samerows)
        st.lab).1 = 0)) :
    (processnode ctx level numcells st).2.orbits = st.orbits := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.orbits),
    pushAuto_orbits'', ite_self]
  by_cases hcc : st.compCanon = 0 <;>
    by_cases hcanon : level < st.canonlevel <;>
    by_cases htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0 <;>
    simp [hnc, hef, hcc, hcanon, htie] <;> omega

/-- A fresh short-prune request at such a leaf proves that the implicit
pair was admitted below the saved boundary. -/
theorem processnode_plain_short_ne {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hnt : ¬(st.compCanon = 0 ∧ ¬(level < st.canonlevel) ∧
      (testcanlab ctx (updatecan ctx st.canong st.canonlab st.samerows)
        st.lab).1 = 0))
    (hclear : st.needshortprune = false)
    (hshort : (processnode ctx level numcells st).2.needshortprune = true) :
    level ≠ st.noncheaplevel := by
  rw [processnode] at hshort
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.needshortprune),
    pushAuto_needshortprune'', pushAuto_noncheaplevel'', ite_self] at hshort
  by_cases hcc : st.compCanon = 0 <;>
    by_cases hcanon : level < st.canonlevel <;>
    by_cases htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0 <;>
    simp [hnc, hef, hcc, hcanon, htie, hclear] at hshort ⊢ <;>
    intro hncl <;> simp [hncl] at hshort <;> omega


/-! # Return and store of the install and rejection arms -/

/-- The shared prune tail returns the level just below the saved boundary
whenever the comparison depth is the current level. -/
theorem pruneReturn_at_level {noncheaplevel allsamelevel level : Nat}
    (hle : noncheaplevel ≤ level) :
    pruneReturn noncheaplevel allsamelevel (Int.ofNat level) =
      Int.ofNat noncheaplevel - 1 := by
  unfold pruneReturn
  simp only [Int.ofNat_eq_natCast]
  split <;> split <;> omega

/-- A comparison leaf that is not a row tie returns just below the saved
cheap-cell boundary. -/
theorem processnode_plain_return {nn : Nat} {ctx : Ctx n} {level numcells : Nat}
    {cs bs : List Nat} {st : SearchSt n}
    (hcinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel st.eqlevCanon
      st.compCanon)
    (hlen : cs.length = level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hnn : 0 ≤ st.compCanon)
    (hnt : ¬(st.compCanon = 0 ∧ ¬(level < st.canonlevel) ∧
      (testcanlab ctx (updatecan ctx st.canong st.canonlab st.samerows)
        st.lab).1 = 0))
    (hle : st.noncheaplevel ≤ level) :
    (processnode ctx level numcells st).1 =
        Int.ofNat st.noncheaplevel - 1 ∧
      (processnode ctx level numcells st).2.autos =
        pruneAutos level st := by
  rcases hcinv.tri with ⟨hcc, heql, -⟩ | ⟨j, -, -, -, -, -, ⟨hcc, -⟩ | ⟨hcc, -⟩⟩
  · by_cases hcanon : level < st.canonlevel
    · refine ⟨?_, processnode_shortInstall_autos hef hnc hcc hcanon⟩
      rw [(processnode_shortInstall hef hnc hcc hcanon).1]
      exact pruneReturn_at_level hle
    · rcases Int.lt_trichotomy (testcanlab ctx
          (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 0
        with hlt | htie | hgt
      · refine ⟨?_, processnode_rowReject_autos hef hnc hcc hcanon hlt⟩
        rw [(processnode_rowReject hef hnc hcc hcanon hlt).1, heql, hlen]
        exact pruneReturn_at_level hle
      · exact absurd ⟨hcc, hcanon, htie⟩ hnt
      · refine ⟨?_, processnode_rowInstall_autos hef hnc hcc hcanon hgt⟩
        rw [(processnode_rowInstall hef hnc hcc hcanon hgt).1]
        exact pruneReturn_at_level hle
  · omega
  · refine ⟨?_, processnode_upInstall_autos hef hnc hcc⟩
    rw [(processnode_upInstall hef hnc hcc).1]
    exact pruneReturn_at_level hle

/-- A first-path-agreeing leaf cannot compare above the incumbent when
the first leaf is dominated by that incumbent. -/
theorem CodeCmpInv.nonpos_of_dom {nn : Nat} {ctx : Ctx n} {cs bs fs : List Nat}
    {canoncode firstcode : Array Nat} {canonlevel : Nat}
    {eqlevCanon compCanon : Int} {canonlab firstlab : Array Nat}
    (hcinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon compCanon)
    (hfinv : FirstCodeInv nn cs fs firstcode cs.length)
    (hdom : keyLe (pathLeafKey ctx fs firstlab) (incKey ctx bs canonlab)) :
    compCanon ≤ 0 := by
  rcases Decidable.em (compCanon ≤ 0) with h | h
  · exact h
  exfalso
  have hcc : compCanon = 1 := by
    rcases hcinv.tri with ⟨hcc, -⟩ | ⟨j, -, -, -, -, -, ⟨hcc, -⟩ | ⟨hcc, -⟩⟩
    · omega
    · omega
    · exact hcc
  subst hcc
  have htake : fs.take cs.length = cs := by
    have hlenfs := hfinv.elev_fs
    refine List.ext_getElem ?_ fun i h1 h2 => ?_
    · rw [List.length_take]
      omega
    · rw [List.getElem_take]
      have h := hfinv.agree (i + 1) (by omega) (by omega)
      have h' : cs[i]! = fs[i]! := by simpa using h
      rw [getElem!_pos cs i h2, getElem!_pos fs i (by omega)] at h'
      exact h'.symm
  have hfs : fs = cs ++ fs.drop cs.length := by
    have h := List.take_append_drop cs.length fs
    rw [htake] at h
    exact h.symm
  apply hdom
  unfold pathLeafKey incKey
  rw [hfs, List.append_assoc]
  exact codeInv_keyCmp_gt hcinv _ _ _


/-! # Packaged leaf runs -/

/-- A comparison leaf that neither ties the incumbent nor sits in the
frozen-downward arm installs or rejects itself and returns to the saved
cheap-cell boundary. -/
theorem NodeInv.cheapLeaf {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hnn : 0 ≤ (otherLeafSt ctx level numcells st).compCanon)
    (hnt : ¬((otherLeafSt ctx level numcells st).compCanon = 0 ∧
      ¬(level < (otherLeafSt ctx level numcells st).canonlevel) ∧
      (testcanlab ctx (updatecan ctx
        (otherLeafSt ctx level numcells st).canong
        (otherLeafSt ctx level numcells st).canonlab
        (otherLeafSt ctx level numcells st).samerows)
        (otherLeafSt ctx level numcells st).lab).1 = 0))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  have hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true := by
    rw [← refine_discrete_iff hn0 hnode.run.searchOk hlevel]
    exact hnum
  have hnc : (n == n) = true := by simp
  obtain ⟨hreturn, hautos⟩ := processnode_plain_return hprep.codeInv
    hfull.symm hef hnc hnn hnt hcheap'
  have hgen := processnode_plain_genTrace (ctx := ctx) (numcells := n)
    hef hnc hnt
  have hearly : (processnode ctx level n leaf).1 < Int.ofNat level := by
    rw [hreturn]
    simp only [Int.ofNat_eq_natCast]
    omega
  obtain ⟨outBest, houtcome, hexact⟩ := hnode.plainLeaf
    (inf := inf) (specFuel := specFuel) (fuel := fuel) hn0
    hsymm hloop hlevel hpath hcheap hnum hdisc hef hgen hearly hlive
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hncl : (processnode ctx level n leaf).2.noncheaplevel =
      leaf.noncheaplevel :=
    (processnode_frames ctx level n leaf).2.2.2.2.2.2.2.1
  have hpositive : 0 < leaf.noncheaplevel := hprep.cheap.positive
  have hexit : NodeExit ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    rw [hout]
    exact NodeExit.cheap leaf.noncheaplevel hreturn hpositive hcheap' hncl
      hexact
  have hrun : NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs
      st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := {
    exit := hexit
    event := houtcome.event
    preserved := houtcome.preserved
    fixed := otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
      numcells st hnum hearly
    short := by
      rw [hout]
      intro hshort
      have hclear : leaf.needshortprune = false := by
        rw [otherLeafSt_short, hnode.shortClear]
      have hne : level ≠ leaf.noncheaplevel :=
        processnode_plain_short_ne hef hnc hnt hclear hshort
      apply ShortSource.implicit (leaf.noncheaplevel - 1)
      · rw [hreturn]
        simp only [Int.ofNat_eq_natCast]
        omega
      · rw [hncl]
        omega
      · rw [hautos, (processnode_frames ctx level n leaf).1,
          (processnode_frames ctx level n leaf).2.1, hncl]
        exact pruneAutos_back hprep.workspace hne
      · rw [(processnode_frames ctx level n leaf).1,
          (processnode_frames ctx level n leaf).2.1, hncl]
        exact hprep.cheap.ready hcheap' hne }
  exact ⟨outBest, hnode.earlyOther hn0 hlevel hpath hnum hearly hlive
    hrun⟩


/-- An early off-path leaf keeps the first labelling, orbit soundness,
and the saved cheap-cell boundary of its node. -/
theorem OtherRun.leafKeep {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel fuel level numcells : Nat}
    {codes fs : List Nat} {st : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail}
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (h : OtherRun G ctx tcLevel specFuel runFuel level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1) :
    OtherKeep ctx level st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  obtain ⟨-, -, -, -, -, hf6, hf7, hf8, hf9, -⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hcheck : ∀ γ ∈ (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace,
      checkAutom ctx.g γ = true := by
    have hev := h.node.event
    rw [hout] at hev
    rcases hev with ⟨_, _, _, event, _, _, _, _, _, _⟩
    exact fun γ hγ => event.genTraceOk.check (Array.mem_toList_iff.mpr hγ)
  rw [hout]
  refine ⟨?_, ?_, ?_⟩
  · rw [processnode_firstlab', hf6]
  · apply processnode_orbSound _ hcheck
    rw [hf7, hf8]
    exact hsound
  · intro _
    rw [processnode_noncheaplevel', hf9]

/-- Every off-path leaf outside the first-path admission gate is a
packaged run that keeps its node's carried facts. -/
theorem NodeInv.leafOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n) :
    ∃ outBest,
      OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
          numcells best outBest trail trail
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  have hgsz : ctx.g.size = n := by
    rw [hg]
    exact size_rowsOf G
  have hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
    rw [hg]
    exact rowsOf_symm G
  have hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false := by
    rw [hg]
    exact rowsOf_loopless G
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [hf9]
    exact hcheap
  have hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true := by
    rw [← refine_discrete_iff hn0 hnode.run.searchOk hlevel]
    exact hnum
  have hnc : (n == n) = true := by simp
  have hefNe : leaf.eqlevFirst ≠ level := by
    intro h
    apply hef
    simp only [leaf, h, beq_self_eq_true]
  rcases Decidable.em (leaf.compCanon < 0) with hneg | hnn
  · -- the frozen-downward arm
    have hgate : leaf.eqlevFirst ≠ level ∧ leaf.compCanon < 0 :=
      ⟨hefNe, hneg⟩
    have hearly := processnode_fast_below (ctx := ctx) (numcells := n)
      hgate hcheap'
    obtain ⟨outBest, hrun⟩ := hnode.negativeOther (inf := inf)
      (specFuel := specFuel) (fuel := fuel) hn0 hsymm hloop hlevel
      hpath hcheap hnum hdisc hef hneg
      (processnode_fast_genTrace (numcells := n) hgate) hearly hlive
    exact ⟨outBest, hrun, hrun.leafKeep hnum hearly hsound⟩
  rcases Decidable.em (leaf.compCanon = 0 ∧ ¬(level < leaf.canonlevel) ∧
      (testcanlab ctx (updatecan ctx leaf.canong leaf.canonlab
        leaf.samerows) leaf.lab).1 = 0) with ⟨hcc, hge, htie⟩ | hnt
  · -- the row tie
    have hcosetOut : (processnode ctx level n leaf).2.cosetindex <
        n := by
      rw [processnode_coset]
      change (otherLeafSt ctx level numcells st).cosetindex < n
      rw [hf4]
      exact hcoset
    have hcheck : ∀ γ ∈ (processnode ctx level n leaf).2.genTrace,
        checkAutom ctx.g γ = true := by
      obtain ⟨_, hevent, -⟩ := hprep.leaf hn0 hsymm hloop hlevel
        hfull hcheap' hef hnc
      exact fun γ hγ => hevent.genTraceOk.check (Array.mem_toList_iff.mpr hγ)
    have horbit : OrbSound (OrbConn (processnode ctx level n
        leaf).2.genTrace.toList n)
        (processnode ctx level n leaf).2.orbits n := by
      apply processnode_orbSound _ hcheck
      change OrbSound (OrbConn (otherLeafSt ctx level numcells
        st).genTrace.toList n) (otherLeafSt ctx level numcells st).orbits
        n
      rw [hf7, hf8]
      exact hsound
    have hrun := hnode.tiedOther (inf := inf) (specFuel := specFuel)
      (fuel := fuel) hn0 hgsz hsymm hloop hlevel hpath hcheap hnum
      hef hcc hge htie hcosetOut horbit hlive
    have hearly : (processnode ctx level n leaf).1 < Int.ofNat level := by
      rcases (processnode_rowTie hef hnc hcc hge htie).1 with h | h
      · rw [h]
        apply Int.ofNat_lt.mpr
        change (otherLeafSt ctx level numcells st).gcaFirst < level
        rw [hf1]
        exact hnode.firstBelow
      · rw [h]
        apply Int.ofNat_lt.mpr
        change (otherLeafSt ctx level numcells st).gcaCanon < level
        rw [hf2]
        exact hnode.canonBelow
    exact ⟨best, hrun, hrun.leafKeep hnum hearly hsound⟩
  · -- an install or a rejection
    have hnn' : 0 ≤ leaf.compCanon := Int.not_lt.mp hnn
    obtain ⟨outBest, hrun⟩ := hnode.cheapLeaf (inf := inf)
      (specFuel := specFuel) (fuel := fuel) hn0 hsymm hloop hlevel
      hpath hcheap hnum hef hnn' hnt hlive
    obtain ⟨hreturn, -⟩ := processnode_plain_return hprep.codeInv
      hfull.symm hef hnc hnn' hnt hcheap'
    have hearly : (processnode ctx level n leaf).1 < Int.ofNat level := by
      rw [hreturn]
      simp only [Int.ofNat_eq_natCast]
      omega
    exact ⟨outBest, hrun, hrun.leafKeep hnum hearly hsound⟩

/-- The admitted first-path-agreeing leaf is a packaged run that keeps its
node's carried facts; domination of the first leaf rules out a comparison
above the incumbent. -/
theorem NodeInv.leafFirstOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true)
    (hsent : (otherLeafSt ctx level numcells st).firstcode[level + 1]! =
      codeSentinel)
    (hpass : isautom ctx (firstScatter n
      (otherLeafSt ctx level numcells st).firstlab
      (otherLeafSt ctx level numcells st).lab) = true)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hdom : ∀ b, best = some b →
      keyLe (pathLeafKey ctx fs st.firstlab) b) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  have hgsz : ctx.g.size = n := by
    rw [hg]
    exact size_rowsOf G
  have hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
    rw [hg]
    exact rowsOf_symm G
  have hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false := by
    rw [hg]
    exact rowsOf_loopless G
  obtain ⟨hf1, -, -, -, -, -, -, -, -, -⟩ :=
    otherLeafSt_frames ctx level numcells st
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hnp : leaf.compCanon ≤ 0 := by
    have hfinv : FirstCodeInv n full fs leaf.firstcode full.length := by
      have h := hprep.firstInv
      rw [beq_iff_eq.mp heq, hfull] at h
      exact h
    exact CodeCmpInv.nonpos_of_dom (ctx := ctx) (firstlab := st.firstlab)
      hprep.codeInv hfinv (hdom _ hprep.incumbent)
  have hrun := hnode.firstOther (inf := inf) (specFuel := specFuel)
    (fuel := fuel) hn0 hgsz hsymm hloop hlevel hpath hnum hnp heq
    hsent hpass hlive
  have hearly : (processnode ctx level n leaf).1 < Int.ofNat level := by
    rw [(processnode_auto (ctx := ctx) (level := level) (numcells := n)
      (st := leaf) heq hsent (by simp) hpass).1]
    apply Int.ofNat_lt.mpr
    change (otherLeafSt ctx level numcells st).gcaFirst < level
    rw [hf1]
    exact hnode.firstBelow
  exact ⟨hrun, hrun.leafKeep hnum hearly hsound⟩

end Hex.GraphIso.Nauty

/-!
Off-path leaves whose first-path admission gate fails.

A leaf whose codes agree with the first path through its own level, but
whose stored first code is not the sentinel or whose first-leaf
relabelling is not an automorphism, runs the ordinary comparison arm of
`processnode`.  The corrected leaf lemmas are stated for leaves off the
first path, so this file transports their conclusions from the twin state
whose first-path agreement depth is zero: the two runs differ only in the
initial workspace permutation, which the canonical scatter overwrites, and
in the recorded agreement depth itself.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Overwrite the first-path agreement depth. -/
@[expose] def SearchSt.setEqlev (e : Nat) (st : SearchSt n) : SearchSt n :=
  { st with eqlevFirst := e }

private theorem id_run_eq {α : Type} (x : Id α) : x.run = x := rfl

private theorem forIn_range_eq3 {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [0:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

private theorem forIn_scatter_eq {flab lab : Array Nat} :
    ∀ (l : List Nat) (w : Array Nat),
      (forIn l w (fun i r =>
        pure (ForInStep.yield (r.set! flab[i]! lab[i]!))) :
          Id (Array Nat)) =
      l.foldl (fun r i => r.set! flab[i]! lab[i]!) w
  | [], _ => rfl
  | i :: l, w => by
    rw [List.forIn_cons]
    exact forIn_scatter_eq l _

private theorem firstScatter_fold (n : Nat) (flab lab : Array Nat) :
    (List.range n).foldl (fun w i => w.set! flab[i]! lab[i]!)
      (Array.replicate n 0) = firstScatter n flab lab := rfl

/-! # The comparison arm at a gate-failing leaf -/

set_option maxHeartbeats 4000000 in
/-- Failing the admission gate runs exactly the comparison arm of the
twin state with agreement depth zero; only the recorded depth differs. -/
theorem processnode_gateFail_state {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hcanonSize : st.canonlab.size = n)
    (hcanonOk : LabOk st.canonlab n)
    (hcanonInj : LabInj st.canonlab n)
    (hlevel : 1 ≤ level)
    (heq : (st.eqlevFirst == level) = true)
    (hnc : (numcells == n) = true)
    (hfail : st.firstcode[level + 1]! ≠ codeSentinel ∨
      isautom ctx (firstScatter n st.firstlab st.lab) = false) :
    processnode ctx level numcells st =
      Prod.map id (SearchSt.setEqlev st.eqlevFirst)
        (processnode ctx level numcells { st with eqlevFirst := 0 }) := by
  have hwork :
      (List.range n).foldl
          (fun r i => r.set! st.canonlab[i]! st.lab[i]!)
          (firstScatter n st.firstlab st.lab) =
        (List.range n).foldl
          (fun r i => r.set! st.canonlab[i]! st.lab[i]!)
          (Array.replicate n 0) :=
    scatter_eq_of_full (firstScatter_size ..) (Array.size_replicate ..)
      hcanonSize hcanonOk hcanonInj
  have hwork' :
      (List.range' 0 n).foldl
          (fun r i => r.set! st.canonlab[i]! st.lab[i]!)
          (firstScatter n st.firstlab st.lab) =
        (List.range' 0 n).foldl
          (fun r i => r.set! st.canonlab[i]! st.lab[i]!)
          (Array.replicate n 0) := by
    simpa [List.range_eq_range'] using hwork
  have hwork2 :
      (List.range' 0 n).foldl
          (fun r i => r.setIfInBounds st.canonlab[i]! st.lab[i]!)
          (firstScatter n st.firstlab st.lab) =
        (List.range' 0 n).foldl
          (fun r i => r.setIfInBounds st.canonlab[i]! st.lab[i]!)
          (Array.replicate n 0) := by
    simpa only [Array.set!_eq_setIfInBounds] using hwork'
  have hg : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0) := by
    intro h
    exact h.1 (beq_iff_eq.mp heq)
  have hl0 : (0 : Nat) ≠ level := by omega
  rcases hfail with hfail | hfail <;>
    rw [processnode, processnode] <;>
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite (Prod.map id (SearchSt.setEqlev st.eqlevFirst))] <;>
    rw [forIn_range_eq3, forIn_scatter_eq, firstScatter_fold] <;>
    simp [hg, hnc, heq, hfail, hl0, id_run_eq]
  all_goals by_cases hcc : st.compCanon = 0
  all_goals by_cases hcanon : level < st.canonlevel
  all_goals by_cases htie : (testcanlab ctx
    (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0
  all_goals by_cases hrow : 0 < (testcanlab ctx
    (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1
  all_goals by_cases hcomp : 0 < st.compCanon
  all_goals by_cases hncanon : st.noncheaplevel < st.canonlevel
  all_goals by_cases hm : st.maxlevel < level
  all_goals by_cases hncl : level = st.noncheaplevel
  all_goals by_cases hcap : st.autos.size = st.wsCap
  all_goals simp [hcc, hcanon, htie, hrow, hcomp, hncanon, hm, hncl,
    hcap, pushAuto, SearchSt.setEqlev]
  all_goals first
    | rfl
    | (intro _
       first
       | rfl
       | omega
       | (exfalso; omega)
       | simp only [hwork2])

/-- The paired form of `processnode_gateFail_state`. -/
theorem processnode_gateFail_pair {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hcanonSize : st.canonlab.size = n)
    (hcanonOk : LabOk st.canonlab n)
    (hcanonInj : LabInj st.canonlab n)
    (hlevel : 1 ≤ level)
    (heq : (st.eqlevFirst == level) = true)
    (hnc : (numcells == n) = true)
    (hfail : st.firstcode[level + 1]! ≠ codeSentinel ∨
      isautom ctx (firstScatter n st.firstlab st.lab) = false) :
    processnode ctx level numcells st =
      ((processnode ctx level numcells { st with eqlevFirst := 0 }).1,
        { (processnode ctx level numcells { st with eqlevFirst := 0 }).2 with
          eqlevFirst := st.eqlevFirst }) := by
  rw [processnode_gateFail_state hcanonSize hcanonOk hcanonInj hlevel heq hnc
    hfail]
  rfl

/-! # The twin leaf state -/

/-- Below the root, node preparation never raises a zero agreement depth,
so the twin leaf state is the leaf state with its depth overwritten. -/
theorem otherLeafSt_setEqlev (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) (hlevel : 2 ≤ level) :
    otherLeafSt ctx level numcells { st with eqlevFirst := 0 } =
      { otherLeafSt ctx level numcells st with eqlevFirst := 0 } := by
  have hne : ((0 : Nat) == level - 1) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  unfold otherLeafSt otherNodePrep
  simp only [Id.run_pure, apply_ite Id.run, hne, Bool.false_eq_true,
    false_and, ite_false]
  repeat' split
  all_goals rfl

/-- Leaf cleanup commutes with overwriting the agreement depth. -/
theorem leafFinish_setEqlev (level e : Nat) (st : SearchSt n) :
    leafFinish level { st with eqlevFirst := e } =
      { leafFinish level st with eqlevFirst := e } := by
  unfold leafFinish
  dsimp only
  split <;> split <;> rfl

/-- A gate-failing off-path leaf runs as its twin with the recorded
agreement depth restored. -/
theorem otherNode_gateFail_state (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hlevel : 2 ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hcanonSize : (otherLeafSt ctx level numcells st).canonlab.size = n)
    (hcanonOk : LabOk (otherLeafSt ctx level numcells st).canonlab n)
    (hcanonInj : LabInj (otherLeafSt ctx level numcells st).canonlab n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hfail : (otherLeafSt ctx level numcells st).firstcode[level + 1]! ≠
        codeSentinel ∨
      isautom ctx (firstScatter n
        (otherLeafSt ctx level numcells st).firstlab
        (otherLeafSt ctx level numcells st).lab) = false) :
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      Prod.map id
        (SearchSt.setEqlev (otherLeafSt ctx level numcells st).eqlevFirst)
        (otherNode ctx inf tcLevel (fuel + 1) level numcells
          { st with eqlevFirst := 0 }) := by
  let pre := otherLeafSt ctx level numcells st
  have hpre' : otherLeafSt ctx level numcells { st with eqlevFirst := 0 } =
      { pre with eqlevFirst := 0 } :=
    otherLeafSt_setEqlev ctx level numcells st hlevel
  have hproc : processnode ctx level n pre =
      Prod.map id (SearchSt.setEqlev pre.eqlevFirst)
        (processnode ctx level n { pre with eqlevFirst := 0 }) :=
    processnode_gateFail_state hcanonSize hcanonOk hcanonInj (by omega) heq
      (beq_self_eq_true _) hfail
  have hnum' : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n := hnum
  have hret : (processnode ctx level n pre).1 =
      (processnode ctx level n { pre with eqlevFirst := 0 }).1 := by
    rw [hproc]
    rfl
  by_cases hearly : (processnode ctx level n pre).1 < Int.ofNat level
  · have hearly' : (processnode ctx level n
        (otherLeafSt ctx level numcells { st with eqlevFirst := 0 })).1 <
          Int.ofNat level := by
      rw [hpre', ← hret]
      exact hearly
    rw [otherNode_leaf_early ctx inf tcLevel fuel level numcells st hnum
      hearly, otherNode_leaf_early ctx inf tcLevel fuel level numcells
      { st with eqlevFirst := 0 } hnum' hearly', hpre']
    exact hproc
  · have hdone' : ¬ (processnode ctx level n
        (otherLeafSt ctx level numcells { st with eqlevFirst := 0 })).1 <
          Int.ofNat level := by
      rw [hpre', ← hret]
      exact hearly
    rw [otherNode_leaf_done_state ctx inf tcLevel fuel level numcells st hnum
      hearly, otherNode_leaf_done_state ctx inf tcLevel fuel level numcells
      { st with eqlevFirst := 0 } hnum' hdone', hpre', hproc]
    show (_, leafFinish level
        (SearchSt.setEqlev pre.eqlevFirst
          (processnode ctx level n { pre with eqlevFirst := 0 }).2)) = _
    unfold SearchSt.setEqlev
    rw [leafFinish_setEqlev]
    rfl

/-! # Transporting the invariants to the twin -/

/-- Lowering the first-path agreement depth preserves the stable
invariant. -/
theorem RunInv.setEqlevFirst {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells e : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunInv G ctx tcLevel level codes bs fs numcells st best trail)
    (he : e ≤ st.eqlevFirst) :
    RunInv G ctx tcLevel level codes bs fs numcells
      { st with eqlevFirst := e } best trail := by
  let st' : SearchSt n := { st with eqlevFirst := e }
  have hok : SearchOk G level numcells st' := by
    refine ⟨h.searchOk.labSize, h.searchOk.ptnSize, h.searchOk.reach,
      h.searchOk.init1, h.searchOk.vals, h.searchOk.count, h.searchOk.bc,
      h.searchOk.canon⟩
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  refine ⟨hok, h.codeInv, firstCodeInv_mono h.firstInv he, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- Lowering the first-path agreement depth preserves the node
invariant. -/
theorem NodeInv.setEqlevFirst {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells e : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (he : e ≤ st.eqlevFirst) :
    NodeInv G ctx tcLevel level codes bs fs numcells
      { st with eqlevFirst := e } best trail :=
  ⟨h.run.setEqlevFirst he, h.cert, h.activeStarts, h.firstBelow,
    h.canonBelow, h.shortClear⟩

/-! # Transporting the run package back -/

namespace Unwind

/-- Overwriting the agreement depth does not touch an unwind payload. -/
@[expose] def setEqlev {ctx : Ctx n} {tcLevel target : Nat} {out : SearchSt n}
    {best : Option (Key n)} (e : Nat) :
    Unwind ctx tcLevel target out best →
      Unwind ctx tcLevel target { out with eqlevFirst := e } best
  | .first anchor carrier => .first anchor carrier
  | .canon anchor carrier => .canon anchor carrier
  | .orbit payload => .orbit ⟨payload.positive, payload.bound,
      payload.currentLt, payload.smaller, payload.sound⟩

/-- Location evidence survives the transport. -/
theorem Located.setEqlev {ctx : Ctx n} {tcLevel target : Nat}
    {out : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    {payload : Unwind ctx tcLevel target out best} (e : Nat)
    (h : payload.Located trail) : (payload.setEqlev e).Located trail := by
  cases h with
  | first anchor carrier located =>
      exact Unwind.Located.first (out := { out with eqlevFirst := e })
        anchor carrier located
  | canon anchor carrier located =>
      exact Unwind.Located.canon (out := { out with eqlevFirst := e })
        anchor carrier located
  | orbit payload =>
      exact Unwind.Located.orbit (out := { out with eqlevFirst := e }) _

end Unwind

/-- A frozen comparison does not read the agreement depth. -/
theorem FrozenOut.setEqlev {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r)
    (e : Nat) :
    FrozenOut ctx stem { out with eqlevFirst := e } best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  exact ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
    hfloor⟩

/-- A short-prune source does not read the agreement depth. -/
theorem ShortSource.setEqlev {G : Colored n k} {ctx : Ctx n} {out : SearchSt n}
    {trail : FrameTrail} {r : Int}
    (h : ShortSource G ctx out trail r) (e : Nat) :
    ShortSource G ctx { out with eqlevFirst := e } trail r := by
  cases h with
  | explicit target fix mcr returned back valid =>
      exact .explicit target fix mcr returned back valid
  | implicit target returned below back root =>
      exact .implicit target returned below back root

/-- Semantic soundness only reads the frame of the entry state. -/
theorem NodeSound.setEqlev {ctx : Ctx n} {tcLevel specFuel level numcells : Nat}
    {codes : List Nat} {st : SearchSt n} {best out : Option (Key n)}
    (h : NodeSound ctx tcLevel specFuel level codes
      { st with eqlevFirst := 0 } numcells best out) :
    NodeSound ctx tcLevel specFuel level codes st numcells best out := by
  have hkey : nodeKey ctx tcLevel specFuel level codes
      { st with eqlevFirst := 0 } numcells =
      nodeKey ctx tcLevel specFuel level codes st numcells :=
    nodeKey_congr rfl rfl rfl
  refine ⟨?_, h.grows⟩
  intro b hb
  have := h.upper b hb
  rwa [hkey] at this

/-- The corrected exit classification transports from the twin. -/
theorem NodeExit.setEqlev {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells e : Nat} {codes : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)} {trail : FrameTrail}
    {r : Int} (hfuel : runFuel ≠ 0)
    (h : NodeExit ctx tcLevel specFuel runFuel level codes
      { st with eqlevFirst := 0 } out numcells best outBest trail r) :
    NodeExit ctx tcLevel specFuel runFuel level codes st
      { out with eqlevFirst := e } numcells best outBest trail r := by
  have hkey : nodeKey ctx tcLevel specFuel level codes
      { st with eqlevFirst := 0 } numcells =
      nodeKey ctx tcLevel specFuel level codes st numcells :=
    nodeKey_congr rfl rfl rfl
  cases h with
  | done returned exact =>
      exact .done returned (by rwa [hkey] at exact)
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below sound.setEqlev (payload.setEqlev e)
        (located.setEqlev e) control
  | frozen below exact freeze =>
      exact .frozen below (by rwa [hkey] at exact) (freeze.setEqlev e)
  | cheap boundary returned positive atOrAbove saved exact =>
      exact .cheap boundary returned positive atOrAbove saved
        (by rwa [hkey] at exact)
  | exhausted returned state incumbent emptyFuel =>
      exact (hfuel emptyFuel).elim

/-! # The gate-failing leaf -/

set_option maxHeartbeats 800000 in
/-- The corrected off-path result of a gate-failing leaf follows from the
result of its twin.  The event package is rebuilt directly from the leaf
comparison, because the twin's event only records agreement depth zero. -/
theorem OtherRun.ofGateFail {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hfail : (otherLeafSt ctx level numcells st).firstcode[level + 1]! ≠
        codeSentinel ∨
      isautom ctx (firstScatter n
        (otherLeafSt ctx level numcells st).firstlab
        (otherLeafSt ctx level numcells st).lab) = false)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (h : OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs
      { st with eqlevFirst := 0 }
      (otherNode ctx inf tcLevel (fuel + 1) level numcells
        { st with eqlevFirst := 0 }).2
      numcells best outBest trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells
        { st with eqlevFirst := 0 }).1)
    (hkeep : OtherKeep ctx level { st with eqlevFirst := 0 }
      (otherNode ctx inf tcLevel (fuel + 1) level numcells
        { st with eqlevFirst := 0 }).2) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  have hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
    rw [hg]
    exact rowsOf_symm G
  have hloopless : ∀ v, v < n → (ctx.g[v]!).mem v = false := by
    rw [hg]
    exact rowsOf_loopless G
  let pre := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs n pre best
      trail := by
    simpa only [full, pre, hnum] using
      hnode.run.otherLeaf hn0 (by omega) hpath
  have hbound : pre.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  have hcanonSize : pre.canonlab.size = n := by
    exact hprep.leafRefs.canonSize
  have hcanonOk : LabOk pre.canonlab n := by
    exact labOk_of_reach hprep.leafRefs.canonSize hprep.leafRefs.canonReach
  have hcanonInj : LabInj pre.canonlab n := by
    exact labInj_of_reach hprep.leafRefs.canonSize hn0
      hprep.leafRefs.canonReach
  have hstate := otherNode_gateFail_state ctx inf tcLevel fuel level numcells
    st hlevel hnum hcanonSize hcanonOk hcanonInj heq hfail
  obtain ⟨bs', hevent, hmax, hret⟩ := hprep.leafFirst hn0 hsymm
    hloopless (by omega) hfull hbound heq hfail (beq_self_eq_true _)
  let P := processnode ctx level n pre
  let twin := otherNode ctx inf tcLevel (fuel + 1) level numcells
    { st with eqlevFirst := 0 }
  have hout : (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 =
      { twin.2 with eqlevFirst := pre.eqlevFirst } := by
    rw [hstate]
    rfl
  have hr : (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 =
      twin.1 := by
    rw [hstate]
    rfl
  have hlivePre : Live ctx level pre trail := hlive.otherLeaf
  have hreturned : P.1 ≤ Int.ofNat level := by
    rcases hret with hr1 | hr2 | hr3 | hr4
    · rw [hr1]
      have := pruneReturn_lt (noncheaplevel := pre.noncheaplevel)
        (allsamelevel := pre.allsamelevel) (eqlevCanon := pre.eqlevCanon)
      have hb : Int.ofNat pre.noncheaplevel ≤ Int.ofNat level :=
        Int.ofNat_le.mpr hbound
      exact Int.le_of_lt (Int.lt_of_lt_of_le this hb)
    · rw [hr2]
      have := pruneReturn_lt (noncheaplevel := pre.noncheaplevel)
        (allsamelevel := pre.allsamelevel)
        (eqlevCanon := Int.ofNat full.length)
      have hb : Int.ofNat pre.noncheaplevel ≤ Int.ofNat level :=
        Int.ofNat_le.mpr hbound
      exact Int.le_of_lt (Int.lt_of_lt_of_le this hb)
    · rw [hr3]
      exact Int.ofNat_le.mpr hprep.firstBound
    · rw [hr4]
      exact Int.ofNat_le.mpr hprep.canonBound
  -- the executable output in terms of the leaf comparison
  have hleaf : otherNode ctx inf tcLevel (fuel + 1) level numcells st = P ∨
      otherNode ctx inf tcLevel (fuel + 1) level numcells st =
        (Int.ofNat level - 1, leafFinish level P.2) := by
    by_cases hearly : P.1 < Int.ofNat level
    · exact Or.inl (otherNode_leaf_early ctx inf tcLevel fuel level numcells
        st hnum hearly)
    · exact Or.inr (otherNode_leaf_done_state ctx inf tcLevel fuel level
        numcells st hnum hearly)
  -- the event package for the actual output
  have hread' : stInc ctx twin.2 = outBest := h.node.event.read
  have hstableTwin : ReturnStab trail
      (min twin.1 (Int.ofNat twin.2.gcaFirst)) twin.2 := by
    rcases h.node.event with ⟨_, _, _, _, _, _, _, _, stable, _⟩
    exact stable
  have heventOut : EventOut G ctx tcLevel codes fs
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 outBest
      trail (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    have hstable : ReturnStab trail
        (min (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1
          (Int.ofNat (otherNode ctx inf tcLevel (fuel + 1) level numcells
            st).2.gcaFirst))
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
      rw [hout, hr]
      exact hstableTwin.ofGenTraceEq rfl
    have hstIncEq : stInc ctx
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 =
          stInc ctx twin.2 := by
      rw [hout]
      rfl
    rcases hleaf with hleaf | hleaf
    · have hbest : outBest = some (incKey ctx bs' P.2.canonlab) := by
        rw [← hread', ← hstIncEq, hleaf]
        exact hevent.read
      rw [hleaf] at hstable ⊢
      rw [hbest]
      exact EventOut.intro level full bs' hevent hfull hstem (by omega)
        hreturned hstable
        (hlivePre.processnode hprep.trailOk hprep.firstBound).1
    · have hbest : outBest = some (incKey ctx bs' P.2.canonlab) := by
        rw [← hread', ← hstIncEq, hleaf]
        show stInc ctx (leafFinish level P.2) = _
        rw [stInc_leafFinish]
        exact hevent.read
      rw [hleaf] at hstable ⊢
      rw [hbest]
      dsimp only at hstable ⊢
      exact EventOut.intro level full bs'
        (hevent.leafFinish (level := level)) hfull hstem
        (by omega) (by simp only [Int.ofNat_eq_natCast]; omega) hstable
        ((hlivePre.processnode hprep.trailOk hprep.firstBound).1.leafFinish)
  refine ⟨?_, ?_⟩
  · rw [hout, hr]
    rw [hout, hr] at heventOut
    exact {
      node := {
        exit := h.node.exit.setEqlev (by omega)
        event := heventOut
        preserved := h.node.preserved
        fixed := h.node.fixed
        short := fun hshort => (h.node.short hshort).setEqlev _ }
      firstGuide := h.firstGuide
      order := h.order
      canonGuide := h.canonGuide
      coset := h.coset }
  · rw [hout]
    exact ⟨hkeep.firstlab, hkeep.orbits, hkeep.boundary⟩

end Hex.GraphIso.Nauty

/-!
Totality of one off-path internal node, assembled from the totality of
its sibling sweep.

An off-path internal node either exits at once (the frozen gate and the
hinted target-cell mismatch), sweeps the specification's target cell, or,
when the path is frozen below the incumbent but still agrees with the
first path, sweeps the first path's hinted target cell.  The hinted sweep
does not compute the node key, so its loop bound is converted through the
common incumbent that dominates both.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Loop exits as node exits, through a common incumbent -/

namespace LoopExit

/-- An early integer-valued loop exit becomes a node exit whenever the
loop bound and the node key produce the same incumbent maximum. -/
theorem toNodeSomeInc {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail} {value : Int}
    (hinc : incMax best bound =
      incMax best (nodeKey ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
        nodeNumcells))
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail (some value)) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail value := by
  cases h with
  | done returned => cases returned
  | unwind target returned below sound payload located control =>
      refine NodeExit.unwind (target := target)
        (returned := Option.some.inj returned) (below := below)
        (sound := ?_) (payload := payload) located control
      constructor
      · intro b hb
        rw [← hinc]
        exact sound.upper b hb
      · exact sound.grows
  | frozen value returned below exact freeze =>
      cases Option.some.inj returned
      apply NodeExit.frozen
      · exact below
      · rw [← hinc]
        exact exact
      · exact freeze.shrink hprefix
  | cheap boundary returned positive below saved exact =>
      apply NodeExit.cheap boundary (Option.some.inj returned) positive below
      · exact saved
      rw [← hinc]
      exact exact
  | exhausted returned => cases returned

/-- A sufficiently fuelled `none` loop exit becomes the node's ordinary
return whenever the loop bound and the node key produce the same incumbent
maximum. -/
theorem toNodeNoneInc {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail}
    (hinc : incMax best bound =
      incMax best (nodeKey ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
        nodeNumcells))
    (hfuel : n < cursorRank cursor + loopFuel)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail none) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail (Int.ofNat level - 1) := by
  cases h with
  | done _ exact =>
      apply NodeExit.done rfl
      rw [← hinc]
      exact exact
  | unwind _ returned => cases returned
  | frozen _ returned => cases returned
  | cheap _ returned => cases returned
  | exhausted _ finalCursor progress bounded =>
      exact (LoopResult.exhaustion_false hfuel progress bounded).elim

end LoopExit

namespace OtherLoopRun

/-- An early integer-valued off-path sweep becomes its enclosing off-path
node, given the guide relation between the node entry and the sweep
result. -/
theorem toNodeSomeInc {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (hinc : incMax best bound =
      incMax best (nodeKey ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
        nodeNumcells))
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (hcoset : loopSt.cosetindex = nodeSt.cosetindex)
    (hguide : GuideRel level nodeSt out)
    (h : OtherLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out best outBest receiptTrail eventTrail (some r)) :
    OtherRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells best outBest receiptTrail eventTrail r where
  node := {
    exit := h.exit.toNodeSomeInc hinc hprefix
    event := h.proof.loop.outcome.event
    preserved := h.proof.loop.outcome.preserved
    fixed := h.proof.loop.fixed.trans hfixed
    short := by
      intro hshort
      obtain ⟨value, hreturned, hsource⟩ := h.short hshort
      cases Option.some.inj hreturned
      exact hsource }
  firstGuide := hguide.first
  order := hguide.order
  canonGuide := hguide.canon
  coset := h.proof.coset.trans hcoset

/-- A sufficiently fuelled `none` off-path sweep is genuine completion and
becomes its enclosing off-path node's ordinary return. -/
theorem toNodeNoneInc {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    (hinc : incMax best bound =
      incMax best (nodeKey ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
        nodeNumcells))
    (hfuel : n < cursorRank cursor + loopFuel)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (hcoset : loopSt.cosetindex = nodeSt.cosetindex)
    (hguide : GuideRel level nodeSt out)
    (h : OtherLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out best outBest receiptTrail eventTrail none) :
    OtherRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells best outBest receiptTrail eventTrail
      (Int.ofNat level - 1) where
  node := {
    exit := h.exit.toNodeNoneInc hinc hfuel
    event := h.proof.loop.outcome.event
    preserved := h.proof.loop.outcome.preserved
    fixed := h.proof.loop.fixed.trans hfixed
    short := by
      intro hshort
      obtain ⟨value, hreturned, _⟩ := h.short hshort
      cases hreturned }
  firstGuide := hguide.first
  order := hguide.order
  canonGuide := hguide.canon
  coset := h.proof.coset.trans hcoset

/-- The ordinary case: the loop bound is the node key itself. -/
theorem toNodeSome {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (hcoset : loopSt.cosetindex = nodeSt.cosetindex)
    (hguide : GuideRel level nodeSt out)
    (h : OtherLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out best outBest receiptTrail eventTrail (some r)) :
    OtherRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells best outBest receiptTrail eventTrail r :=
  h.toNodeSomeInc (by rw [hbound]) hprefix hfixed hcoset hguide

/-- The ordinary case: the loop bound is the node key itself. -/
theorem toNodeNone {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hfuel : n < cursorRank cursor + loopFuel)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (hcoset : loopSt.cosetindex = nodeSt.cosetindex)
    (hguide : GuideRel level nodeSt out)
    (h : OtherLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out best outBest receiptTrail eventTrail none) :
    OtherRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells best outBest receiptTrail eventTrail
      (Int.ofNat level - 1) :=
  h.toNodeNoneInc (by rw [hbound]) hfuel hfixed hcoset hguide

end OtherLoopRun

/-! # The prepared node frame -/

/-- The node preparation leaves the active set alone. -/
theorem otherNodePrep_active (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).active = st.active := by
  rw [otherNodePrep]
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchSt.active,
    ite_self]

/-- The refined off-path frame before its target cell is chosen. -/
theorem otherLeafSt_active (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).active =
      (refine ctx level st.lab st.ptn st.active numcells).active := by
  unfold otherLeafSt
  rw [otherNodePrep_active]

theorem otherLeafSt_lab (ctx : Ctx n) (level numcells : Nat) (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
  unfold otherLeafSt
  exact (otherNodePrep_frames _ _ _).2.2.2.2.2.2.2.2.2.2.2.1

theorem otherLeafSt_ptn (ctx : Ctx n) (level numcells : Nat) (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).ptn =
      (refine ctx level st.lab st.ptn st.active numcells).ptn := by
  unfold otherLeafSt
  exact (otherNodePrep_frames _ _ _).2.2.2.2.2.2.2.2.2.2.2.2

/-- The sweep entry state: the prepared frame charged with the target
cell size and, when the cheap-automorphism test fails, parked one level
below. -/
@[expose] def sweepStart (ctx : Ctx n) (level numcells len : Nat)
    (st : SearchSt n) : SearchSt n :=
  let pre := otherLeafSt ctx level numcells st
  let base : SearchSt n := { pre with tctotal := pre.tctotal + len }
  if cheapautom base.ptn level n then base
  else { base with noncheaplevel := level + 1 }

/-- Every logical field of the sweep entry state is inherited from the
node entry or the refinement. -/
theorem sweepStart_frames (ctx : Ctx n) (level numcells len : Nat)
    (st : SearchSt n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let start := sweepStart ctx level numcells len st
    start.lab = rs.lab ∧ start.ptn = rs.ptn ∧ start.active = rs.active ∧
    start.fixedpts = st.fixedpts ∧ start.gcaFirst = st.gcaFirst ∧
    start.gcaCanon = st.gcaCanon ∧ start.canonlab = st.canonlab ∧
    start.genTrace = st.genTrace ∧ start.orbits = st.orbits ∧
    start.cosetindex = st.cosetindex ∧ start.firstlab = st.firstlab ∧
    start.needshortprune = st.needshortprune ∧
    (start.noncheaplevel = st.noncheaplevel ∨
      start.noncheaplevel = level + 1) ∧
    (cheapautom rs.ptn level n = false →
      start.noncheaplevel = level + 1) ∧
    (cheapautom rs.ptn level n = true →
      start.noncheaplevel = st.noncheaplevel) := by
  dsimp only
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hlab := otherLeafSt_lab ctx level numcells st
  have hptn := otherLeafSt_ptn ctx level numcells st
  have hact := otherLeafSt_active ctx level numcells st
  unfold sweepStart
  dsimp only
  split
  · rename_i hc
    rw [hptn] at hc
    exact ⟨hlab, hptn, hact, hf5, hf1, hf2, hf3, hf7, hf8, hf4, hf6, hf10,
      Or.inl hf9, fun h => (by rw [hc] at h; cases h), fun _ => hf9⟩
  · rename_i hc
    rw [hptn] at hc
    exact ⟨hlab, hptn, hact, hf5, hf1, hf2, hf3, hf7, hf8, hf4, hf6, hf10,
      Or.inr rfl, fun _ => rfl, fun h => absurd h hc⟩

/-! # A sweep at the node -/

/-- An off-path internal node whose child sweep starts at `sweepStart`
with a loop invariant, given the two state equations of the executable
node and a common incumbent maximum for the loop bound and the node key.
-/
theorem NodeInv.sweepNode {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel sf runFuel level numcells tc len : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {bound : Key n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + (sf + 1) = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b)
    (hlen2 : 2 ≤ len) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := codes ++ [rs.longcode]
    let tcell := worksetOf n rs.lab tc (tc + len - 1)
    let start := sweepStart ctx level numcells len st
    let L := otherChildLoop ctx inf tcLevel runFuel (n + 1) level
      rs.numcells tc ((tcell.nextElem none).getD 0) (tcell.nextElem none)
      tcell start
    LoopInv G ctx tcLevel sf level full bs fs rs.numcells rs.lab rs.ptn tc
      len tcell none start start best trail →
    incMax best bound =
      incMax best (nodeKey ctx tcLevel (sf + 1) level codes st numcells) →
    bound = keysMax
      (sweepKey ctx tcLevel sf level full rs.lab rs.ptn tc rs.numcells 0)
      ((List.range (len - 1)).map fun o =>
        sweepKey ctx tcLevel sf level full rs.lab rs.ptn tc rs.numcells
          (o + 1)) →
    (∀ r out, L = (some r, out) →
      otherNode ctx inf tcLevel (runFuel + 1) level numcells st = (r, out)) →
    (∀ out, L = (none, out) →
      otherNode ctx inf tcLevel (runFuel + 1) level numcells st =
        (Int.ofNat level - 1, out)) →
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel (sf + 1) (runFuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells best outBest trail eventTrail
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2 := by
  intro rs full tcell start L hloop hinc hbound hsome hnone
  have hgsz : ctx.g.size = n := by
    rw [hg]
    exact size_rowsOf G
  have href := hnode.refined hg hn0 (by omega)
  obtain ⟨hsLab, hsPtn, hsActive, hsFixed, hsFirst, hsCanon, hsCanonlab,
    hsGen, hsOrb, hsCoset, hsFirstlab, hsShort, hsNcl, hsPark, hsKeep⟩ :=
    sweepStart_frames ctx level numcells len st
  have hpathFull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstemFull : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hpastFull : codes.length < level := by omega
  have hend : st.ptn[st.ptn.size - 1]! ≤ level :=
    searchOk_end hn0 hnode.run.searchOk (by omega)
  have hrefInv := refine_refInv (ctx := ctx) (level := level)
    (active := st.active) (numcells := numcells)
    (by rw [hnode.run.searchOk.ptnSize]; exact Nat.le_refl n)
    (hnode.run.searchOk.labSize.trans hnode.run.searchOk.ptnSize.symm)
    hend
  have hlive' : OtherLive ctx level start trail := by
    have := hnode.otherLive (len := len) hlive
    exact this
  have hpathStart : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level start := by
    have h1 := hpathOk.refine hn0 (by omega) hgsz hnode.run.searchOk
      hnode.activeStarts
    exact h1.stateEq hsLab hsPtn hsFixed
  have hh : OtherLoopHyp G ctx tcLevel sf level full bs fs rs.numcells
      rs.lab rs.ptn tc len tcell none st.noncheaplevel start start best
      trail := {
    inv := hloop
    live := hlive'
    path := hpathStart
    cursorLt := fun _ h => nomatch h
    sign := Or.inr rfl
    start := fun _ => worksetOf_eq_windowSet rs.lab tc len (by omega)
    guide := GuideRel.refl (by rw [hsFirst, hsCanon]; exact hlive.order)
    baseCanon := by
      rw [hsCanon]
      exact Nat.le_of_lt hnode.canonBelow
    orbits := by
      rw [hsGen, hsOrb]
      exact horb
    coset := by
      rw [hsCoset]
      exact hcoset
    firstDom := by
      rw [hsFirstlab]
      exact hdom
    desc := by
      intro hlt
      rcases hsNcl with hncl | hncl
      · rw [hncl] at hlt
        have hsub := hdesc hlt
        exact (hsub.setActive (a := VSet.empty)).ofFrames
          rfl rfl rfl
      · rw [hncl] at hlt
        exfalso
        omega
    bnd := by
      rcases hsNcl with hncl | hncl <;> rw [hncl] <;> omega
    park := hsPark
    keep := by
      intro hlt
      rcases hsNcl with hncl | hncl
      · exact hncl
      · rw [hncl] at hlt
        omega }
  obtain ⟨outBest, eventTrail, hrunL, hguideL, hkeepL⟩ :=
    otherLoopTotal (tv1 := (tcell.nextElem none).getD 0) (tail := len - 1)
      hg hinf hn0 ih (by omega) (by omega) hpathFull hstemFull hpastFull
      hbound (by omega) (n + 1) none tcell start best trail bs hh
      (by simp only [cursorRank]; omega)
  generalize hLdef : otherChildLoop ctx inf tcLevel runFuel (n + 1) level
    rs.numcells tc ((tcell.nextElem none).getD 0) (tcell.nextElem none) tcell
    start = L' at hrunL hguideL hkeepL
  have hguide : GuideRel level st L'.2 := by
    have hab : GuideRel level st start :=
      ⟨hsFirst, by rw [hsFirst, hsCanon]; exact hlive.order,
        Or.inl ⟨hsCanon, hsCanonlab⟩⟩
    refine GuideRel.transRefine hab hguideL ?_ ?_ ?_ ?_ hend ?_ ?_
    · rw [hsPtn, hnode.run.searchOk.ptnSize, href.1.ok.ptnSize]
    · rw [hsLab, hsPtn, href.1.ok.ptnSize, href.1.ok.labSize]
    · rw [hsPtn, href.1.ok.ptnSize]
      exact hrunL.proof.loop.outcome.event.canonSize
    · rw [hsPtn]
      exact href.1.ok.ptnEnd
    · rw [hsPtn]
      exact hrefInv.grow
    · rw [hsLab]
      exact hrefInv.perm
  have hkeep : OtherKeep ctx level st L'.2 :=
    ⟨hkeepL.firstlab.trans hsFirstlab, hkeepL.orbits, hkeepL.boundary⟩
  rcases L' with ⟨_ | r, out⟩
  · rw [hnone out hLdef]
    exact ⟨outBest, eventTrail,
      hrunL.toNodeNoneInc hinc (by simp only [cursorRank]; omega) hsFixed
        hsCoset hguide, hkeep⟩
  · rw [hsome r out hLdef]
    exact ⟨outBest, eventTrail,
      hrunL.toNodeSomeInc hinc hstemFull hsFixed hsCoset hguide, hkeep⟩

/-! # The specification's target cell -/

/-- An off-path internal node with a nonnegative comparison sweeps the
specification's target cell. -/
theorem NodeInv.plainSweep {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel sf runFuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + (sf + 1) = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (hnonneg : (otherLeafSt ctx level numcells st).compCanon ≥ 0) :
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel (sf + 1) (runFuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells best outBest trail eventTrail
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2 := by
  obtain ⟨tc, len, hmk, hprocess, hchildren, hloop⟩ :=
    LoopInv.NodeInv.otherSweep (specFuel := sf) hg hn0 (by omega) hpath hnode
      (Nat.ne_of_lt hnum) hnonneg (by omega)
  have hlab := otherLeafSt_lab ctx level numcells st
  have hptn := otherLeafSt_ptn ctx level numcells st
  obtain ⟨-, -, -, -, -, -, -, -, -, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hmk' : maketargetcell ctx (otherLeafSt ctx level numcells st).lab
      (otherLeafSt ctx level numcells st).ptn level tcLevel (-1) =
      (tc, worksetOf n (refine ctx level st.lab st.ptn st.active
        numcells).lab tc (tc + len - 1), len) := by
    rw [hlab, hptn]
    exact hmk
  have hmkU := hmk'
  have hprocessU := hprocess
  simp only [otherLeafSt] at hmkU hprocessU
  have hshortBase : ({ otherLeafSt ctx level numcells st with
      tctotal := (otherLeafSt ctx level numcells st).tctotal + len } :
        SearchSt n).needshortprune = false :=
    hf10.trans hnode.shortClear
  have hshortU := hshortBase
  simp only [otherLeafSt] at hshortU
  have hhalf : ¬ (Int.ofNat level < Int.ofNat level) := Int.lt_irrefl _
  rcases hc : cheapautom (otherLeafSt ctx level numcells st).ptn level
      n with _ | _
  · -- the cheap-automorphism test fails: the sweep starts parked
    have hcU := hc
    simp only [otherLeafSt] at hcU
    have hstate := LoopInv.otherNode_park_state ctx inf tcLevel runFuel level numcells
      st hnum hnonneg
      (by
        dsimp only
        rw [hmkU]
        dsimp only
        rw [hprocessU]
        exact hshortU)
      (by
        dsimp only
        rw [hmkU]
        dsimp only
        rw [hprocessU]
        exact hcU)
    dsimp only at hstate
    rw [hmkU] at hstate
    dsimp only at hstate
    rw [hprocessU] at hstate
    dsimp only at hstate
    rw [ite_eq_right hhalf] at hstate
    have hsw : sweepStart ctx level numcells len st =
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len
          noncheaplevel := level + 1 } := by
      unfold sweepStart
      dsimp only
      rw [ite_eq_right (by rw [hc]; exact Bool.false_ne_true)]
    refine hnode.sweepNode hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
      hdesc hlive hpathOk horb hcoset hdom hloop.lenTwo hloop
      (by rw [hchildren]) rfl ?_ ?_
    · intro r out hL
      rw [hstate]
      rw [hsw] at hL
      simp only [otherLeafSt] at hL
      rw [hL]
    · intro out hL
      rw [hstate]
      rw [hsw] at hL
      simp only [otherLeafSt] at hL
      rw [hL]
  · -- the cheap-automorphism test passes
    have hcU := hc
    simp only [otherLeafSt] at hcU
    have hstate := otherNode_plain_state ctx inf tcLevel runFuel level numcells
      st hnum hnonneg
      (by
        dsimp only
        rw [hmkU]
        dsimp only
        rw [hprocessU]
        exact hshortU)
      (by
        dsimp only
        rw [hmkU]
        dsimp only
        rw [hprocessU]
        exact hcU)
    dsimp only at hstate
    rw [hmkU] at hstate
    dsimp only at hstate
    rw [hprocessU] at hstate
    dsimp only at hstate
    rw [ite_eq_right hhalf] at hstate
    have hsw : sweepStart ctx level numcells len st =
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len } := by
      unfold sweepStart
      dsimp only
      rw [ite_eq_left hc]
    refine hnode.sweepNode hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
      hdesc hlive hpathOk horb hcoset hdom hloop.lenTwo hloop
      (by rw [hchildren]) rfl ?_ ?_
    · intro r out hL
      rw [hstate]
      rw [hsw] at hL
      simp only [otherLeafSt] at hL
      rw [hL]
    · intro out hL
      rw [hstate]
      rw [hsw] at hL
      simp only [otherLeafSt] at hL
      rw [hL]

/-! # The first path's hinted target cell -/

/-- A frozen off-path internal node that still agrees with the first path
sweeps the first path's target cell when the stored hint is confirmed.
The sweep bound is not the node key, but both are dominated by the
incumbent. -/
theorem NodeInv.hintSweep {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel sf runFuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + (sf + 1) = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmatch : Int.ofNat (maketargetcell ctx
        (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 =
      (otherLeafSt ctx level numcells st).firsttc[level]!) :
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel (sf + 1) (runFuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells best outBest trail eventTrail
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2 := by
  have href := hnode.refined hg hn0 (by omega)
  have hlab := otherLeafSt_lab ctx level numcells st
  have hptn := otherLeafSt_ptn ctx level numcells st
  obtain ⟨-, -, -, -, -, -, -, -, -, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hnc : ¬ (((refine ctx level st.lab st.ptn st.active
      numcells).numcells == n) = true) := by
    intro h
    exact Nat.ne_of_lt hnum (beq_iff_eq.mp h)
  have hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = false := by
    rw [← Bool.not_eq_true, ← refine_discrete_iff hn0
      hnode.run.searchOk (by omega)]
    exact Nat.ne_of_lt hnum
  obtain ⟨tc, len, hmk, hcell, hlen2, hrange⟩ :=
    maketargetcell_open (ctx := ctx)
      (lab := (refine ctx level st.lab st.ptn st.active numcells).lab)
      (ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn)
      (level := level) (tcLevel := tcLevel)
      (hint := (otherLeafSt ctx level numcells st).firsttc[level]!)
      (by omega) href.1.ok.ptnSize href.1.ok.ptnEnd
      (by rw [href.2.2]; exact hnum)
  have hmk' : maketargetcell ctx (otherLeafSt ctx level numcells st).lab
      (otherLeafSt ctx level numcells st).ptn level tcLevel
      (otherLeafSt ctx level numcells st).firsttc[level]! =
      (tc, worksetOf n (refine ctx level st.lab st.ptn st.active
        numcells).lab tc (tc + len - 1), len) := by
    rw [hlab, hptn]
    exact hmk
  have hprep : RunPrep G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (otherLeafSt ctx level numcells st) best trail :=
    hnode.run.otherLeaf hn0 (by omega) hpath
  have hbase : RunPrep G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal + len }
      best trail :=
    hprep.setTctotal
  have hprocess : processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal + len } =
      (Int.ofNat level,
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len }) := by
    apply processnode_internal
    · intro h
      exact h.1 (beq_iff_eq.mp heq)
    · exact hnc
  obtain ⟨hsLab, hsPtn, -, -, hsFirst, hsCanon, -, -, -, -, -, hsShort, -, -,
    -⟩ := sweepStart_frames ctx level numcells len st
  have hrun : RunInv G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (sweepStart ctx level numcells len st) best trail := by
    unfold sweepStart
    dsimp only
    rcases hc : cheapautom (otherLeafSt ctx level numcells st).ptn level
        n with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      exact hbase.run.park (hbase.cheap.park (by omega) (by omega))
    · simp only [ite_true]
      exact hbase.run
  have hvals : ∀ q : Nat,
      (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! ≤ level ∨
      (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! =
        n + 2 := by
    intro q
    rcases Nat.lt_or_ge q n with hq | hq
    · exact href.1.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [href.1.ok.ptnSize]; omega)]
      exact Nat.zero_le _
  have hloop0 := LoopInv.start (specFuel := sf) hn0 (by omega) hrun
    (by rw [hsFirst]; exact hnode.firstBelow)
    (by rw [hsCanon]; exact hnode.canonBelow)
    (by rw [hsLab, hsPtn]; exact href.2.1)
    (by rw [hsPtn]; exact hcell) hlen2 hrange
    (by rw [hsPtn]; exact hvals)
    (by rw [hsShort]; exact hnode.shortClear) (by omega)
  have hloop : LoopInv G ctx tcLevel sf level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn tc len
      (worksetOf n (refine ctx level st.lab st.ptn st.active numcells).lab tc
        (tc + len - 1))
      none (sweepStart ctx level numcells len st)
      (sweepStart ctx level numcells len st) best trail := by
    rw [worksetOf_eq_windowSet _ tc len (by omega)]
    simpa only [hsLab, hsPtn] using hloop0
  -- both the sweep bound and the node key are dominated by the incumbent
  obtain ⟨tc', len', -, hspec', -, hlen2', -⟩ :=
    hnode.target hg hn0 (by omega) (Nat.ne_of_lt hnum)
  have hlenSpec : (specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn level
      tcLevel).2.2 = (len' - 1) + 1 := by
    rw [hspec']
    dsimp only
    omega
  have hnodeLe : keyLe (nodeKey ctx tcLevel (sf + 1) level codes st numcells)
      (incKey ctx bs st.canonlab) :=
    nodeKey_le_of_frozen hprep.codeInv hneg hdisc hlenSpec
  have hboundLe : keyLe (keysMax
      (sweepKey ctx tcLevel sf level
        (codes ++ [(refine ctx level st.lab st.ptn st.active
          numcells).longcode])
        (refine ctx level st.lab st.ptn st.active numcells).lab
        (refine ctx level st.lab st.ptn st.active numcells).ptn tc
        (refine ctx level st.lab st.ptn st.active numcells).numcells 0)
      ((List.range (len - 1)).map fun o =>
        sweepKey ctx tcLevel sf level
          (codes ++ [(refine ctx level st.lab st.ptn st.active
            numcells).longcode])
          (refine ctx level st.lab st.ptn st.active numcells).lab
          (refine ctx level st.lab st.ptn st.active numcells).ptn tc
          (refine ctx level st.lab st.ptn st.active numcells).numcells
          (o + 1)))
      (incKey ctx bs st.canonlab) := by
    apply keysMax_le
    · exact hprep.codeInv.frozenBound hneg _
    · intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨o, -, rfl⟩ := hy
      exact hprep.codeInv.frozenBound hneg _
  -- the executable node
  have hshort' : SearchSt.needshortprune (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal +
          (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
            (otherLeafSt ctx level numcells st).ptn level tcLevel
            (otherLeafSt ctx level numcells st).firsttc[level]!).2.2 }).2 =
      false := by
    rw [hmk']
    dsimp only
    rw [hprocess]
    exact hf10.trans hnode.shortClear
  have hstate := otherNode_hint_state ctx inf tcLevel runFuel level numcells
    st hnum heq hneg hmatch hshort'
  dsimp only at hstate
  rw [hmk'] at hstate
  dsimp only at hstate
  rw [hprocess] at hstate
  dsimp only at hstate
  rw [ite_eq_right (Int.lt_irrefl _)] at hstate
  have hflip : (if ¬ cheapautom
        ({ otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len } :
            SearchSt n).ptn level n = true then
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len
          noncheaplevel := level + 1 }
      else
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len }) =
      sweepStart ctx level numcells len st := by
    unfold sweepStart
    dsimp only
    rcases hc : cheapautom (otherLeafSt ctx level numcells st).ptn level
        n with _ | _
    · simp only [Bool.false_eq_true, not_false_eq_true, ite_true, ite_false]
    · simp only [not_true_eq_false, ite_false, ite_true]
  rw [hflip] at hstate
  refine hnode.sweepNode hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
    hdesc hlive hpathOk horb hcoset hdom hlen2 hloop
    (by
      rw [hnode.run.incumbent]
      exact (incMax_of_frozen hboundLe).trans (incMax_of_frozen hnodeLe).symm)
    rfl ?_ ?_
  · intro r out hL
    rw [hstate, hL]
  · intro out hL
    rw [hstate, hL]

/-! # Every off-path internal node -/

/-- Totality of an off-path internal node at the next executable fuel,
given totality of every off-path node at the current fuel. -/
theorem NodeInv.internalOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + specFuel = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n) :
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel specFuel (runFuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells best outBest trail eventTrail
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2 := by
  have hle : level ≤ n := hnode.run.searchOk.levelLe
  obtain ⟨sf, rfl⟩ : ∃ sf, specFuel = sf + 1 := ⟨specFuel - 1, by omega⟩
  by_cases hgate : (otherLeafSt ctx level numcells st).eqlevFirst ≠ level ∧
      (otherLeafSt ctx level numcells st).compCanon < 0
  · obtain ⟨hrun, hkeep⟩ := hnode.gateRun (inf := inf) (specFuel := sf)
      (fuel := runFuel) hg hn0 (by omega) hpath hcheap hnum hgate hlive
      horb
    exact ⟨best, trail, hrun, hkeep⟩
  by_cases hnonneg : (otherLeafSt ctx level numcells st).compCanon ≥ 0
  · exact hnode.plainSweep hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
      hdesc hlive hpathOk horb hcoset hdom hnum hnonneg
  have hneg : (otherLeafSt ctx level numcells st).compCanon < 0 := by
    omega
  have heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true := by
    rcases Decidable.em ((otherLeafSt ctx level numcells st).eqlevFirst =
        level) with h | h
    · exact beq_iff_eq.mpr h
    · exact absurd ⟨h, hneg⟩ hgate
  by_cases hmatch : Int.ofNat (maketargetcell ctx
      (otherLeafSt ctx level numcells st).lab
      (otherLeafSt ctx level numcells st).ptn level tcLevel
      (otherLeafSt ctx level numcells st).firsttc[level]!).1 =
      (otherLeafSt ctx level numcells st).firsttc[level]!
  · exact hnode.hintSweep hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
      hdesc hlive hpathOk horb hcoset hdom hnum heq hneg hmatch
  · obtain ⟨hrun, hkeep⟩ := hnode.hintFailRun (inf := inf) (specFuel := sf)
      (fuel := runFuel) hg hn0 (by omega) hpath hcheap hnum heq hneg
      hmatch hlive horb
    exact ⟨best, trail, hrun, hkeep⟩

end Hex.GraphIso.Nauty

/-!
The off-path node step of the totality induction: every off-path node
at executable fuel `runFuel + 1` is total once every node at fuel
`runFuel` is.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- An off-path leaf at any executable fuel is total. -/
theorem NodeInv.leafTotal {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells =
      n)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b) :
    ∃ outBest,
      OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
          numcells best outBest trail trail
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  have hlevel1 : 1 ≤ level := by omega
  rcases heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level)
    with _ | _
  · exact hnode.leafOther hg hn0 hlevel1 hpath hcheap hnum
      (by rw [heq]; decide) hlive hsound hcoset
  · by_cases hadmit :
      (otherLeafSt ctx level numcells st).firstcode[level + 1]! =
          codeSentinel ∧
        isautom ctx (firstScatter n
          (otherLeafSt ctx level numcells st).firstlab
          (otherLeafSt ctx level numcells st).lab) = true
    · exact ⟨best, hnode.leafFirstOther hg hn0 hlevel1 hpath hnum heq
        hadmit.1 hadmit.2 hlive hsound hdom⟩
    · have hfail : (otherLeafSt ctx level numcells st).firstcode[level + 1]! ≠
          codeSentinel ∨
          isautom ctx (firstScatter n
            (otherLeafSt ctx level numcells st).firstlab
            (otherLeafSt ctx level numcells st).lab) = false := by
        by_cases hs : (otherLeafSt ctx level numcells st).firstcode[level + 1]!
            = codeSentinel
        · right
          rcases hp : isautom ctx (firstScatter n
            (otherLeafSt ctx level numcells st).firstlab
            (otherLeafSt ctx level numcells st).lab) with _ | _
          · rfl
          · exact (hadmit ⟨hs, hp⟩).elim
        · exact Or.inl hs
      have hnode' := hnode.setEqlevFirst (e := 0) (Nat.zero_le _)
      have hlive' : Live ctx level { st with eqlevFirst := 0 } trail :=
        hlive.stateEq rfl rfl rfl rfl rfl
      have hef' : ¬(((otherLeafSt ctx level numcells
          { st with eqlevFirst := 0 }).eqlevFirst == level) = true) := by
        rw [otherLeafSt_setEqlev ctx level numcells st hlevel]
        simp only [beq_iff_eq]
        omega
      obtain ⟨outBest, hrun', hkeep'⟩ :=
        NodeInv.leafOther (st := { st with eqlevFirst := 0 }) hg hn0 hlevel1
          hpath hcheap hnum hef' hnode' hlive' hsound hcoset
      exact ⟨outBest, OtherRun.ofGateFail hg hn0 hlevel hpath hcheap hnum
        heq hfail hnode hlive hrun' hkeep'⟩

/-- Every off-path node at the next executable fuel is total once every
node at the current fuel is. -/
theorem OtherTotal.succ (G : Colored n k) (ctx : Ctx n)
    (inf tcLevel runFuel : Nat) (ih : OtherTotal G ctx inf tcLevel runFuel) :
    OtherTotal G ctx inf tcLevel (runFuel + 1) := by
  intro specFuel level numcells codes bs fs st best trail hg hinf hn0
    hlevel hpath hspec hfuel hcheap hdesc hnode hlive hpathOk horb hcoset hdom
  have hle : level ≤ n := hnode.run.searchOk.levelLe
  rcases Nat.lt_or_ge (refine ctx level st.lab st.ptn st.active
    numcells).numcells n with hnum | hnum
  · exact hnode.internalOther hg hinf hn0 ih hlevel hpath hspec hfuel
      hcheap hdesc hlive hpathOk horb hcoset hdom hnum
  · have hnum' : (refine ctx level st.lab st.ptn st.active
        numcells).numcells = n := by
      apply Nat.le_antisymm _ hnum
      rw [← (hnode.refined hg hn0 (by omega)).2.2]
      exact bcount_le _ _ _
    obtain ⟨sf, rfl⟩ : ∃ sf, specFuel = sf + 1 := ⟨specFuel - 1, by omega⟩
    obtain ⟨outBest, hrun, hkeep⟩ := hnode.leafTotal hg hn0 hlevel hpath
      hcheap hnum' hlive horb hcoset hdom
    exact ⟨outBest, trail, hrun, hkeep⟩

end Hex.GraphIso.Nauty
