/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeFirstHyp
import all HexGraphIso.Nauty.Search

public section

/-!
The first-path sibling sweep, part three: the cursor-fuel induction after
the guiding child, the guiding child itself, and the conversion of the
whole sweep back to the enclosing first-path node.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # The sweep induction after the guiding child -/

set_option maxHeartbeats 3200000 in
/-- Totality of the first-path sweep after its guiding child, at every
cursor fuel exceeding the remaining cursor range, given totality of every
off-path child. -/
theorem firstTail {G : Colored n k} {ctx : Ctx n}
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
      (best : Option (Key n)) (trail : FrameTrail) (bs : List Nat) (index : Nat),
      FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells rsLab
        rsPtn tc len tcell cursor e tv1 base st best trail →
      n < cursorRank cursor + loopFuel →
      ∃ outBest eventTrail,
        FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
            fs rsLab rsPtn tc len numcells tcell cursor bound st
            (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell index st).2.2
            best outBest trail eventTrail
            (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell index st).1 ∧
          FirstSweepKeep ctx level e fs st
            (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell index st).2.2
            outBest := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro cursor tcell st best trail bs index hh hfuel
      exfalso
      have := cursorRank_le hh.cursorLt
      omega
  | succ loopFuel ihLoop =>
    intro cursor tcell st best trail bs index hh hfuel
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
    have hguideLe : level ≤ st.gcaFirst := Nat.le_of_eq hh.guide.symm
    rcases hnext : tcell.nextElem cursor with _ | tv
    · -- the sweep is finished
      have hsame : (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
          level numcells tc tv1 none tcell index st).2.2 = st := by
        unfold firstChildLoop
        rfl
      refine ⟨best, trail, ?_, ?_⟩
      · exact FirstSweepRun.done (inf := inf) (runFuel := runFuel)
          (loopFuel := loopFuel) (tv1 := tv1) (index := index) hpath hstem
          hpast hnext hh.sign hbound hlen hh.inv hh.live.toLive hh.firstTrail
          hh.canonTrail hguideLe
      · rw [hsame]
        exact ⟨hh.firstDom, rfl, hh.orbits, hh.coset, hh.keep⟩
    · -- one more vertex
      have htvLt : tv < n := hh.inv.nextLt hnext
      have hafter : tv1 < tv := by
        obtain ⟨v, hv, hle⟩ := hh.after
        have ha := nextElem_after hnext
        rw [hv] at ha
        simp only [After] at ha
        omega
      have hother : (tv == tv1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      obtain ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen, hat⟩ :=
        hh.inv.nextOffsets hnext
      have hfuelRec : n < cursorRank (some tv) + loopFuel :=
        cursorFuel_step (nextElem_after hnext) hfuel
      rcases horb : (st.orbits[tv]! == tv) with _ | _
      · -- an orbit skip
        have hinj : LabInj rsLab rsLab.size := by
          rw [← hh.inv.baseLab, hh.inv.baseOk.labSize]
          exact labInj_of_reach hh.inv.baseOk.labSize hh.inv.nonempty
            hh.inv.baseOk.reach
        have hcover := hh.inv.cover.orbitSkip hnext hoffset hatFrozen hgsz
          (fun γ hγ => hh.inv.run.genTraceOk.check hγ) hh.live.frameStab
          hh.inv.frozenLabSize hinj hh.inv.frozenLabOk hh.inv.frozenPtnSize
          hh.inv.frozenEnd hh.inv.frozenVals hh.inv.cell hh.inv.range
          hh.inv.fuelBound hh.orbits (by
            intro heq
            rw [heq] at horb
            simp at horb)
        have hhSkip : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs
            numcells rsLab rsPtn tc len tcell (some tv) e tv1 base st best
            trail :=
          ⟨{ hh.inv with cover := hcover }, hh.live, hh.path,
            ⟨tv, rfl, Nat.le_of_lt hafter⟩,
            fun v hv => by cases hv; exact htvLt, hh.sign, hh.guide,
            hh.firstTrail, hh.canonTrail, hh.orbits, hh.coset, hh.firstDom,
            hh.desc, hh.bnd, hh.park, hh.keep⟩
        have hstate := firstChildLoop_skip ctx inf tcLevel runFuel loopFuel
          level numcells tc tv1 tv tcell index st horb
        obtain ⟨outBest, eventTrail, hrunTail, hkeepTail⟩ :=
          ihLoop (some tv) tcell st best trail bs
            (if (st.orbits[tv]! == tv1) = true then index + 1 else index)
            hhSkip hfuelRec
        refine ⟨outBest, eventTrail, ?_, ?_⟩
        · rw [hstate]
          exact hrunTail.step (nextElem_after hnext)
        · rw [hstate]
          exact hkeepTail
      · -- an off-path child
        have hcheapOk := hh.cheapOk hg
        obtain ⟨offset', currentOffset', hoffset', hcurrent', hatFrozen',
            hat', hnodeChild⟩ :=
          hh.inv.child (coset := tv) hnext hcheapOk
        rw [hat'] at hnodeChild
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
        let child : SearchSt n :=
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := st.fixedpts.insert tv
            cosetindex := tv }
        let childTrail := trail.push level
          ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset'⟩
        have hdescChild := hh.inv.childDescWeak hg hh.desc hh.bnd hh.park
          hcurrent hat
        have hliveChild : Live ctx (level + 1) child childTrail := by
          have := hh.inv.firstChildLive (coset := tv) hh.live offset'
            currentOffset'
          rw [hat'] at this
          exact this
        have hpathChild : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
            (initialPartition G).1 (level + 1) child := by
          have := hh.path.breakout hh.inv hcurrent
          rw [hat] at this
          exact this.stateEq rfl rfl rfl
        obtain ⟨childBest, eventTrail, hrunChild, hkeepChild⟩ :=
          ih specFuel (level + 1) (numcells + 1) codes bs fs child best
            childTrail hg hinf hn0 (by omega) (by omega) (by omega)
            (by omega) hh.bnd hdescChild hnodeChild hliveChild hpathChild
            hh.orbits htvLt hh.firstDom
        obtain ⟨value, out, hcall⟩ : ∃ value out,
            otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
              child = (value, out) := ⟨_, _, rfl⟩
        have hout : SearchOut G level (level + 1) child out := by
          have := otherNode_ok G ctx inf hinf tcLevel hn0 runFuel
            (level + 1) (numcells + 1) child hnodeChild.run.searchOk
            (by omega) (by omega)
          rw [Nat.add_sub_cancel, hcall] at this
          exact this
        rw [hcall] at hrunChild hkeepChild
        dsimp only at hrunChild hkeepChild
        have heq0 := hh.inv.childKeyAll hoffset' hatFrozen' hat'
        have heq : ∀ o, o < len → rsLab[tc + o]! = tv →
            sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
              numcells o =
            nodeKey ctx tcLevel specFuel (level + 1) codes child
              (numcells + 1) := by
          intro o ho h
          exact (heq0 o ho h).trans (nodeKey_congr rfl rfl rfl).symm
        have hkeyLe : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
            child (numcells + 1)) bound := by
          rw [← heq offset' hoffset' hatFrozen']
          exact LoopInv.keyLeBound hbound hlen hoffset'
        have hsoundChild : NodeSound ctx tcLevel specFuel (level + 1) codes
            child (numcells + 1) best childBest :=
          hrunChild.toProof.outcome.node.receipt.sound hfuelNe
        have hgrows : IncGrows best childBest := hrunChild.grows hfuelNe
        have hfirstlabChild : out.firstlab = st.firstlab :=
          hkeepChild.firstlab
        have hboundaryChild : out.noncheaplevel < level + 1 →
            out.noncheaplevel = st.noncheaplevel :=
          hkeepChild.boundary
        have htrailExt : TrailExt level trail eventTrail :=
          TrailExt.ofPush hrunChild.node.preserved
        have hcosetChild : out.cosetindex = tv := hrunChild.coset
        -- domination of the first leaf by the child's incumbent
        have hdomChild : ∀ b, childBest = some b →
            keyLe (pathLeafKey ctx fs out.firstlab) b := by
          intro b hb
          obtain ⟨b0, hb0⟩ : ∃ b0, best = some b0 :=
            ⟨_, hh.inv.run.incumbent⟩
          obtain ⟨b', hb', hle⟩ := hgrows b0 hb0
          have hbb : b = b' := Option.some.inj (hb.symm.trans hb')
          subst hbb
          rw [hfirstlabChild]
          exact keyLe_trans (hh.firstDom b0 hb0) hle
        by_cases hstay : value < Int.ofNat level
        · -- early exit
          obtain ⟨htrail, hcanon⟩ := hh.childTrails hcurrent hat
            (r := value) hrunChild hfirstlabChild
          have hstate := firstChildLoop_earlyOther ctx inf tcLevel runFuel
            loopFuel level numcells tc tv1 tv tcell index st value out horb
            hother hcall hstay
          have hkeepOut : FirstSweepKeep ctx level e fs st
              (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
                numcells tc tv1 (some tv) tcell index st).2.2 childBest := by
            rw [hstate]
            refine ⟨hdomChild, hfirstlabChild, hkeepChild.orbits, ?_, ?_⟩
            · change out.cosetindex < n
              rw [hcosetChild]
              exact htvLt
            · intro hlt
              change out.noncheaplevel < level at hlt
              change out.noncheaplevel = e
              have hb := hboundaryChild (Nat.lt_succ_of_lt hlt)
              rw [hb] at hlt ⊢
              exact hh.keep hlt
          refine ⟨childBest, eventTrail, ?_, hkeepOut⟩
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
            exact FirstSweepRun.childUnwind hstem hshorter horb hother hcall
              hsoundChild hkeyLe returned hbelowNat payload located control
              hrunChild hfresh htrail hcanon hguideLe
          · exact FirstSweepRun.childFrozen hpath hstem hshorter horb hother
              hcall hrunChild hstay freeze exact hkeyLe hbound hlen
              (hh.inv.cover.advanceKey hnext exact heq) hfresh htrail hcanon
              hguideLe
          · have hbelowNat : boundary ≤ level := by
              rw [returned] at hstay
              simp only [Int.ofNat_eq_natCast] at hstay
              omega
            have hle : st.noncheaplevel ≤ level := by
              have h1 := hboundaryChild (by rw [saved]; omega)
              rw [saved] at h1
              omega
            have hsmall := hh.inv.subtreeAtWeak hh.desc hh.park hle
             
            have hboundEq : bound = nodeKey ctx tcLevel specFuel (level + 1)
                codes child (numcells + 1) := by
              rw [← heq offset' hoffset' hatFrozen']
              exact hh.inv.boundEq hsmall hgsz hsymm hloopless hbound
                hlen hoffset'
            rw [returned] at hcall hrunChild
            exact FirstSweepRun.childCheap hstem hshorter horb hother hcall
              hrunChild positive hbelowNat saved hboundEq exact hfresh htrail
              hcanon hguideLe
          · exact (hfuelNe emptyFuel).elim
        · -- the child stays at the loop level
          let cleaned : SearchSt n :=
            { out with fixedpts := out.fixedpts.erase tv }
          let cleared := clearShortIf out.needshortprune cleaned
          let recSt := recover n inf level cleared
          let tcell' := if out.needshortprune then shortprune tcell cleared
            else tcell
          have hshortRec : cleared.needshortprune = false :=
            clearShortIf_self cleaned
          obtain ⟨bs', hhRec⟩ := hh.next hg hinf hcodesLen hfuelNe hnext
            hoffset' hcurrent' hatFrozen' hat' hrunChild hkeepChild hstay hout
            out.needshortprune hshortRec
          have hinvRec : LoopInv G ctx tcLevel specFuel level codes bs' fs
              numcells rsLab rsPtn tc len tcell' (some tv) base recSt
              childBest eventTrail := by
            rcases hshortC : out.needshortprune with _ | _
            · simpa only [tcell', recSt, cleared, cleaned, hshortC,
                Bool.false_eq_true, ite_false] using hhRec.inv
            · have hlast : ∀ fix mcr : VSet n,
                  cleared.autos.back? = some (fix, mcr) →
                    PairOk ctx.g rsPtn rsLab level fix mcr := by
                intro fix mcr hback
                apply LoopInv.ShortSource.atReceiver hpath hh.inv hh.path
                  hrunChild.node.exit hrunChild.node.event
                  hrunChild.node.preserved (hrunChild.node.short hshortC)
                  hstay
                simpa only [cleared, cleaned, clearShortIf, hshortC, ite_true]
                  using hback
              simpa only [tcell', recSt, cleared, cleaned, hshortC, ite_true]
                using hhRec.inv.shortpruneWith hgsz hlast
          have hhRec' := hhRec.filter hinvRec
          obtain ⟨outBest, eventTrail', hrunTail, hkeepTail⟩ :=
            ihLoop (some tv) tcell' recSt childBest eventTrail bs'
              (if (recSt.orbits[tv]! == tv1) = true then index + 1 else index)
              hhRec' hfuelRec
          have hfixedRec : recSt.fixedpts = st.fixedpts := by
            change (recover n inf level cleared).fixedpts = st.fixedpts
            rw [recover_clearShortIf, (clearShortIf_fields _ _).1,
              recover_fixedpts]
            change out.fixedpts.erase tv = st.fixedpts
            rw [hrunChild.node.fixed, erase_insert_of_miss hfresh]
          have hpre : LoopSound ctx bound best childBest :=
            LoopSound.ofNode hsoundChild hkeyLe
          have hstate := firstChildLoop_stayOther ctx inf tcLevel runFuel
            loopFuel level numcells tc tv1 tv tcell index st value out horb
            hother hcall hstay
          dsimp only at hstate
          refine ⟨outBest, eventTrail', ?_, ?_⟩
          · exact (FirstSweepRun.nextOther hnext horb hother hcall hstay
              hfixedRec hpre hrunTail).retrail htrailExt
          · rw [hstate]
            refine ⟨hkeepTail.dom, ?_, hkeepTail.orbits, hkeepTail.coset,
              hkeepTail.boundary⟩
            rw [hkeepTail.firstlab]
            change (recover n inf level cleared).firstlab = st.firstlab
            rw [recover_firstlab, (clearShortIf_fields _ _).2.2.2.2.2.1]
            exact hfirstlabChild

/-- A node exit depends on its receipt trail only at its unwind target. -/
theorem NodeExit.retrail {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {source dest : FrameTrail} {r : Int}
    (htrail : ∀ target, target < level → source target = dest target)
    (h : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
      best outBest source r) :
    NodeExit ctx tcLevel specFuel runFuel level codes st out numcells best
      outBest dest r := by
  cases h with
  | done returned exact => exact .done returned exact
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below sound payload
        (located.retrail (htrail target below)) control
  | frozen below exact freeze => exact .frozen below exact freeze
  | cheap boundary returned positive atOrAbove saved exact =>
      exact .cheap boundary returned positive atOrAbove saved exact
  | exhausted returned state incumbent emptyFuel =>
      exact .exhausted returned state incumbent emptyFuel

/-! # The whole sweep from its guiding child -/

/-- What the whole first-path sweep establishes for its enclosing node,
relative to the node entry boundary `e`. -/
structure FirstSweepOut (ctx : Ctx n) (level e : Nat) (fs : List Nat)
    (out : SearchSt n) (outBest : Option (Key n)) : Prop where
  dom : ∀ b, outBest = some b → keyLe (pathLeafKey ctx fs out.firstlab) b
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  coset : out.cosetindex < n
  boundary : out.noncheaplevel < level → out.noncheaplevel = e

/-- The sweep bound is every child's key once the frozen frame is a
verified small-cell subtree. -/
theorem boundEq_of_subtree {ctx : Ctx n}
    {tcLevel specFuel level tc len numcells tail offset : Nat} {active : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {bound : Key n}
    (hsmall : SubtreeOk ctx level
      { lab := rsLab, ptn := rsPtn, active := active,
        numcells := numcells, hint := 0, maxpos := 0,
        longcode := numcells })
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcell : IsCell rsPtn level tc len) (hlen2 : 2 ≤ len)
    (hrange : tc + len ≤ n)
    (hfuel : level + 1 + specFuel ≤ n + 1)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1) (hoffset : offset < len) :
    bound = sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells offset := by
  let key := fun o => sweepKey ctx tcLevel specFuel level codes rsLab
    rsPtn tc numcells o
  have hkey : ∀ o, o < len → key o = key offset := by
    intro o ho
    apply congrArg (prefixKey codes)
    exact childKey_eq_of_subtree (tcLevel := tcLevel)
      (fuel := specFuel) (numcells := numcells) (oU := offset) (oV := o)
      hsmall hgsz hsymm hloop hcell hlen2 hrange hoffset ho hfuel
  rw [hbound]
  apply keysMax_eq_of_le
  · rw [show sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells 0 = key 0 by rfl, hkey 0 (by omega)]
    exact keyLe_refl _
  · intro y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hy
    rw [show sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells (o + 1) = key (o + 1) by rfl,
      hkey (o + 1) (by rw [hlen]; have := List.mem_range.mp ho; omega)]
    exact keyLe_refl _
  · rcases offset with _ | offset
    · exact Or.inl rfl
    · right
      exact List.mem_map.mpr ⟨offset, List.mem_range.mpr (by omega), rfl⟩

set_option maxHeartbeats 6400000 in
/-- Totality of the whole first-path sibling sweep of an internal node on
the first descent, from the parked refined state at cursor `none`, given
totality of the guiding child through `FirstTotal` and of every later
sibling through `OtherTotal`. -/
theorem firstLoopTotal {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tail : Nat}
    {cs : List Nat} {st : SearchSt n} {trail : FrameTrail} {bound : Key n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (ihFirst : FirstTotal G ctx inf tcLevel runFuel)
    (hrun : n + 2 < level + 1 + runFuel)
    (hspec : level + 1 + specFuel = n + 1)
    (hlevel : 1 ≤ level) (hpath : level = cs.length + 1) (hlt : level < n)
    (hfirst : FirstInv G ctx level cs numcells st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcell : IsCell (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tc len)
    (hlen2 : 2 ≤ len) (hrange : tc + len ≤ n)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level
        (cs ++ [(refine ctx level st.lab st.ptn st.active numcells).longcode])
        (refine ctx level st.lab st.ptn st.active numcells).lab
        (refine ctx level st.lab st.ptn st.active numcells).ptn tc
        (refine ctx level st.lab st.ptn st.active numcells).numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level
          (cs ++ [(refine ctx level st.lab st.ptn st.active
            numcells).longcode])
          (refine ctx level st.lab st.ptn st.active numcells).lab
          (refine ctx level st.lab st.ptn st.active numcells).ptn tc
          (refine ctx level st.lab st.ptn st.active numcells).numcells
          (o + 1)))
    (hlen : len = tail + 1) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [r.longcode]
    let pre0 : SearchSt n := { st with
      lab := r.lab
      ptn := r.ptn
      active := r.active
      firstcode := st.firstcode.set! level r.longcode
      firsttc := st.firsttc.set! level (Int.ofNat tc)
      numnodes := st.numnodes + 1
      tctotal := st.tctotal + len }
    let pre := if pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level n then
      { pre0 with noncheaplevel := level + 1 }
    else pre0
    let tcell := windowSet n r.lab tc len
    let tv1 := (tcell.nextElem none).getD 0
    ∃ fs outBest eventTrail,
      FirstSweepRun G ctx tcLevel specFuel runFuel (n + 1) level cs full
          fs r.lab r.ptn tc len r.numcells tcell none bound pre
          (firstChildLoop ctx inf tcLevel runFuel (n + 1) level
            r.numcells tc tv1 (tcell.nextElem none) tcell 0 pre).2.2
          none outBest trail eventTrail
          (firstChildLoop ctx inf tcLevel runFuel (n + 1) level
            r.numcells tc tv1 (tcell.nextElem none) tcell 0 pre).1 ∧
        FirstSweepOut ctx level st.noncheaplevel fs
          (firstChildLoop ctx inf tcLevel runFuel (n + 1) level
            r.numcells tc tv1 (tcell.nextElem none) tcell 0 pre).2.2
          outBest := by
  intro r full pre0 pre tcell tv1
  obtain ⟨hit, heqt, hcount⟩ := hfirst.refined hg hn0 hlevel
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
  have hfuelNe : runFuel ≠ 0 := by
    intro h0
    rw [h0] at hrun
    omega
  have hfull : full.length = level := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take cs.length = cs := by
    simp only [full, List.take_left']
  have hpast : cs.length < level := by omega
  have hshorter : cs.length < full.length := by
    rw [hfull]
    exact hpast
  have hfuel : level + 1 + specFuel ≤ n + 1 := by
    omega
  have hls : r.lab.size = n := hit.ok.labSize
  have hlabOk : LabOk r.lab n := hit.ok.labOk
  have hps : r.ptn.size = n := hit.ok.ptnSize
  have hend : r.ptn[r.ptn.size - 1]! ≤ level := hit.ok.ptnEnd
  have hinj : LabInj r.lab n := hit.inj
  have hvals : ∀ q : Nat, r.ptn[q]! ≤ level ∨ r.ptn[q]! = n + 2 := by
    intro q
    rcases Nat.lt_or_ge q n with hq | hq
    · exact hit.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [hps]; omega)]
      exact Nat.zero_le _
  -- the start state
  have hpreLab : pre.lab = r.lab := by
    simp only [pre]
    split <;> rfl
  have hprePtn : pre.ptn = r.ptn := by
    simp only [pre]
    split <;> rfl
  have hpreActive : pre.active = r.active := by
    simp only [pre]
    split <;> rfl
  have hpreFixed : pre.fixedpts = st.fixedpts := by
    simp only [pre]
    split <;> rfl
  have hpreOrbits : pre.orbits = st.orbits := by
    simp only [pre]
    split <;> rfl
  have hpreGen : pre.genTrace = st.genTrace := by
    simp only [pre]
    split <;> rfl
  have hpreFirstlab : pre.firstlab = st.firstlab := by
    simp only [pre]
    split <;> rfl
  have hpreCanonlab : pre.canonlab = st.canonlab := by
    simp only [pre]
    split <;> rfl
  have hpreShort : pre.needshortprune = false := by
    simp only [pre]
    split <;> exact hfirst.shortClear
  have hpreNclEq : pre.noncheaplevel = if st.noncheaplevel ≥ level ∧
      ¬ cheapautom r.ptn level n = true then level + 1
      else st.noncheaplevel := by
    by_cases hc : st.noncheaplevel ≥ level ∧
      ¬ cheapautom r.ptn level n = true
    · simp only [pre, pre0, ite_eq_left hc]
    · simp only [pre, pre0, ite_eq_right hc]
  have hpreNcl : pre.noncheaplevel = st.noncheaplevel ∨
      (pre.noncheaplevel = level + 1 ∧
        cheapautom r.ptn level n = false ∧ st.noncheaplevel ≥ level) := by
    rw [hpreNclEq]
    by_cases hc : st.noncheaplevel ≥ level ∧
      ¬ cheapautom r.ptn level n = true
    · rw [ite_eq_left hc]
      right
      refine ⟨rfl, ?_, hc.1⟩
      rcases hc' : cheapautom r.ptn level n with _ | _
      · rfl
      · exact absurd hc' hc.2
    · rw [ite_eq_right hc]
      left
      rfl
  have hpreParkWeak : cheapautom r.ptn level n = false →
      pre.noncheaplevel ≠ level := by
    intro hc heq
    rw [hpreNclEq] at heq
    by_cases hc' : st.noncheaplevel ≥ level ∧
      ¬ cheapautom r.ptn level n = true
    · rw [ite_eq_left hc'] at heq
      omega
    · rw [ite_eq_right hc'] at heq
      exact hc' ⟨by omega, by simp [hc]⟩
  have hpreBnd : pre.noncheaplevel ≤ level + 1 := by
    rcases hpreNcl with h | h <;> omega
  have hpreKeep : pre.noncheaplevel < level →
      pre.noncheaplevel = st.noncheaplevel := by
    intro hlt'
    rcases hpreNcl with h | h
    · exact h
    · omega
  have hpreOk : SearchOk G level r.numcells pre :=
    refine_searchOk hn0 hfirst.searchOk hlevel hpreLab hprePtn
      (Or.inl hpreCanonlab)
  have hpathPre : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level pre :=
    (hpathOk.refine hn0 hlevel hgsz hfirst.searchOk
      hfirst.activeStarts).stateEq hpreLab hprePtn hpreFixed
  have hcellPre : IsCell pre.ptn level tc len := by
    rw [hprePtn]
    exact hcell
  have horbPre : OrbSound (OrbConn pre.genTrace.toList n) pre.orbits
      n := by
    rw [hpreGen, hpreOrbits]
    exact horb
  -- the guiding vertex
  obtain ⟨v, hv⟩ := nextElem_windowSet_some (lab := r.lab) (tc := tc)
    (len := len) (by omega) (hlabOk _ (by rw [hit.ok.labSize]; omega))
  have hnext : tcell.nextElem none = some tv1 := by
    simp only [tv1, tcell, hv, Option.getD_some]
  have hmem : tv1 ∈ segN r.lab tc len := by
    exact (mem_windowSet.mp (VSet.nextElem_mem hnext)).2
  obtain ⟨o, ho, hato⟩ : ∃ o, o < len ∧ r.lab[tc + o]! = tv1 := by
    simp only [segN, List.mem_map, List.mem_range] at hmem
    obtain ⟨o, ho, h⟩ := hmem
    exact ⟨o, ho, h⟩
  have hat : pre.lab[tc + o]! = tv1 := by
    rw [hpreLab]
    exact hato
  have htvLt : tv1 < n := by
    rw [← hato]
    exact hlabOk _ (by omega)
  have hrep : (pre.orbits[tv1]! == tv1) = true := by
    rw [hpreOrbits, hfirst.orbitId tv1 htvLt]
    simp
  have hfirstTv : (tv1 == tv1) = true := by simp
  have hfresh : pre.fixedpts.mem tv1 = false := by
    rw [← hat]
    apply hpathPre.fixed.fresh
    · rw [hpreLab]; exact hlabOk
    · rw [hpreLab]; exact hinj
    · rw [hpreLab]; exact hls
    · exact hcellPre
    · exact hlen2
    · exact hrange
    · exact ho
  -- the guiding child
  let child : SearchSt n :=
    { pre with
      lab := (breakout n pre.lab pre.ptn (level + 1) tc tv1).1
      ptn := (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.1
      active := (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.2
      fixedpts := pre.fixedpts.insert tv1
      cosetindex := tv1 }
  let childTrail := trail.push level
    ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩
  have hfirstChild : FirstInv G ctx (level + 1) full (r.numcells + 1) child
      childTrail := by
    have h := hfirst.child (specFuel := specFuel) hg hn0 hpath hlt hcell
      hlen2 hrange ho
    dsimp only at h
    rw [show pre.lab[tc + o]! = tv1 from hat] at h
    exact h
  have hpathChild : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 (level + 1) child := by
    have h := hfirst.childPath hg hn0 hpath
      hpathOk hcell hlen2 hrange ho
    dsimp only at h
    rw [show pre.lab[tc + o]! = tv1 from hat] at h
    exact h
  have hchildNcl : child.noncheaplevel = pre.noncheaplevel := rfl
  have hdescChild : CheapDesc ctx (level + 1) child.noncheaplevel
      (refine ctx (level + 1) child.lab child.ptn child.active
        (r.numcells + 1)) := by
    have hlvl : level < n := hlt
    have h := hdesc.child hit heqt hcount hsymm hlvl hcell hlen2 hrange ho
    dsimp only at h
    rw [hato] at h
    change CheapDesc ctx (level + 1) _
      (refine ctx (level + 1) (breakout n r.lab r.ptn (level + 1) tc tv1).1
        (r.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (r.numcells + 1)) at h
    change CheapDesc ctx (level + 1) pre.noncheaplevel
      (refine ctx (level + 1) (breakout n pre.lab pre.ptn (level + 1) tc tv1).1
        (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.1
        (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.2 (r.numcells + 1))
    rw [breakout_ptn, hpreLab, hprePtn, hpreNclEq]
    exact h
  obtain ⟨fs, outBest, eventTrail, hrunG, hkeepG⟩ :=
    ihFirst specFuel (level + 1) (r.numcells + 1) full child childTrail
      hg hinf hn0 (by omega) (by rw [hfull]) (by omega) (by omega)
      (by rw [hchildNcl]; exact hpreBnd) hdescChild horbPre hfirstChild
      hpathChild
  obtain ⟨value, out, hcall⟩ : ∃ value out,
      firstPathNode ctx inf tcLevel runFuel (level + 1) (r.numcells + 1)
        child = (value, out) := ⟨_, _, rfl⟩
  have hout : SearchOut G level (level + 1) child out := by
    have := (firstPathNode_ok G ctx inf hinf tcLevel hn0 runFuel
      (level + 1) (r.numcells + 1) child hfirstChild.searchOk (by omega)
      (by omega)).1
    rw [Nat.add_sub_cancel, hcall] at this
    exact this
  rw [hcall] at hrunG hkeepG
  dsimp only at hrunG hkeepG
  have hgca : level + 1 ≤ out.gcaFirst := hkeepG.guide
  have horderG : level + 1 ≤ out.gcaCanon :=
    Nat.le_trans hgca hrunG.proof.order
  have hsoundG : NodeSound ctx tcLevel specFuel (level + 1) full child
      (r.numcells + 1) none outBest :=
    hrunG.proof.node.outcome.receipt.sound hfuelNe
  -- the guiding child's key is one of the swept keys
  have hkeyEq : ∀ o', o' < len → r.lab[tc + o']! = tv1 →
      sweepKey ctx tcLevel specFuel level full r.lab r.ptn tc r.numcells o' =
        nodeKey ctx tcLevel specFuel (level + 1) full child
          (r.numcells + 1) := by
    intro o' ho' hato'
    have hoo : o' = o := by
      have := hinj.eq_of_getElem! (i := tc + o') (j := tc + o)
        (by omega) (by omega) (hato'.trans hato.symm)
      omega
    subst hoo
    have h := SearchOut.breakoutKey (ctx := ctx) (codes := full) (specFuel := specFuel)
      (tcLevel := tcLevel) (SearchOut.refl G level level hpreOk.reach)
      hpreOk hpreOk hn0 hlevel hcellPre hlen2 hrange ho
      (child := child) (by rw [hat]) (by rw [hat]) (by rw [hat]) rfl
      hfuel
    rw [hpreLab, hprePtn] at h
    exact h
  have hkeyG : keyLe (nodeKey ctx tcLevel specFuel (level + 1) full child
      (r.numcells + 1)) bound := by
    rw [← hkeyEq o ho hato]
    exact LoopInv.keyLeBound hbound hlen ho
  have hpreG : LoopSound ctx bound none outBest :=
    LoopSound.ofNode hsoundG hkeyG
  have hdoneOf : outBest = some (incMax none
      (nodeKey ctx tcLevel specFuel (level + 1) full child
        (r.numcells + 1))) →
      ChildDone ctx tcLevel specFuel level full r.lab r.ptn tc r.numcells
        outBest o := by
    intro hfullKey
    apply ChildDone.ofExact hfullKey
    · rw [hato]
      change (breakout n pre.lab pre.ptn (level + 1) tc tv1).1 = _
      rw [hpreLab, hprePtn]
    · rw [hato]
      change (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.1 = _
      rw [hpreLab, hprePtn]
    · rw [hato]
      change (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.2 = _
      rw [hpreLab, hprePtn]
  have hcoverOf : outBest = some (incMax none
      (nodeKey ctx tcLevel specFuel (level + 1) full child
        (r.numcells + 1))) →
      SweepCover ctx tcLevel specFuel level full r.lab r.ptn tc len
        r.numcells tcell (some tv1) outBest := by
    intro hfullKey
    exact (sweepCover_init ctx tcLevel specFuel level full r.lab r.ptn tc len
      r.numcells none (fun o ho => hlabOk _ (by rw [hit.ok.labSize]; omega))).advanceKey
      hnext hfullKey hkeyEq
  have horbOut : OrbSound (OrbConn out.genTrace.toList n) out.orbits
      n :=
    hkeepG.orbits
  have hcosetOut : out.cosetindex < n := hkeepG.coset htvLt
  have hboundaryG : out.noncheaplevel < level + 1 →
      out.noncheaplevel = pre.noncheaplevel := hkeepG.boundary
  have hext : TrailExt level trail eventTrail :=
    TrailExt.ofPush hrunG.proof.node.outcome.preserved
  have hentry : eventTrail level = some
      ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩ :=
    hrunG.proof.node.outcome.preserved.pushAt
  rw [hnext]
  refine ⟨fs, ?_⟩
  by_cases hstay : value < Int.ofNat level
  · -- the guiding child exits below the loop
    have hstate := firstChildLoop_earlyGuide ctx inf tcLevel runFuel n
      level r.numcells tc tv1 tv1 tcell 0 pre value out hrep hfirstTv hcall
      hstay
    have hkeepOut : FirstSweepOut ctx level st.noncheaplevel fs
        (firstChildLoop ctx inf tcLevel runFuel (n + 1) level r.numcells
          tc tv1 (some tv1) tcell 0 pre).2.2 outBest := by
      rw [hstate]
      refine ⟨hkeepG.dom, horbOut, hcosetOut, ?_⟩
      intro hlt'
      change out.noncheaplevel < level at hlt'
      change out.noncheaplevel = st.noncheaplevel
      have hb := hboundaryG (Nat.lt_succ_of_lt hlt')
      rw [hb] at hlt' ⊢
      exact hpreKeep hlt'
    refine ⟨outBest, eventTrail, ?_, hkeepOut⟩
    rcases hexit : hrunG.exit with
      ⟨returned, exact⟩ |
      ⟨target, returned, below, sound, payload, located, control⟩ |
      ⟨below, exact, freeze⟩ |
      ⟨boundary, returned, positive, atOrAbove, saved, exact⟩ |
      ⟨returned, state, incumbent, emptyFuel⟩
    · exfalso
      rw [returned] at hstay
      simp only [Int.ofNat_eq_natCast] at hstay
      omega
    · exfalso
      have htarget : target < level := by
        rw [returned] at hstay
        exact Int.ofNat_lt.mp hstay
      rcases control with h | h <;> omega
    · exact FirstSweepRun.guideFrozen hfull.symm hstem hshorter hrep hfirstTv
        hcall hrunG hgca hstay freeze exact hkeyG hbound hlen (hcoverOf exact)
        (hdoneOf exact) hfresh hlevel hls hlabOk hps hend hvals hcell hrange
        ho hfuel
    · have hbelowNat : boundary ≤ level := by
        rw [returned] at hstay
        simp only [Int.ofNat_eq_natCast] at hstay
        omega
      have hpreLe : pre.noncheaplevel ≤ level := by
        have h1 := hboundaryG (by rw [saved]; omega)
        rw [saved] at h1
        omega
      have hstLe : st.noncheaplevel ≤ level := by
        rcases hpreNcl with h | h <;> omega
      have hsmall : SubtreeOk ctx level
          { lab := r.lab, ptn := r.ptn, active := pre.active,
            numcells := r.numcells, hint := 0, maxpos := 0,
            longcode := r.numcells } := by
        rw [hpreActive]
        refine SubtreeOk.ofFrames (r := r) ?_ rfl rfl rfl
        apply hdesc.atLevel hit heqt hcount hstLe
        intro heq
        rcases hc : cheapautom r.ptn level n with _ | _
        · exfalso
          have := hpreParkWeak hc
          rcases hpreNcl with h | h <;> omega
        · rfl
      have hboundEq : bound = nodeKey ctx tcLevel specFuel (level + 1) full
          child (r.numcells + 1) := by
        rw [← hkeyEq o ho hato]
        exact boundEq_of_subtree hsmall hgsz hsymm hloopless hcell hlen2
          hrange hfuel hbound hlen ho
      rw [returned] at hcall hrunG
      exact FirstSweepRun.guideCheap hfull.symm hstem hshorter hrep hfirstTv
        hcall hrunG hgca positive hbelowNat saved hboundEq exact
        (hdoneOf exact) hfresh hlevel hls hlabOk hps hend hvals hcell hrange
        ho hfuel
    · exact (hfuelNe emptyFuel).elim
  · -- the guiding child stays at the loop level
    have hreturn : value = Int.ofNat level :=
      hrunG.proof.node.outcome.parentEq hfuelNe hstay
    have hfullKey : outBest = some (incMax none
        (nodeKey ctx tcLevel specFuel (level + 1) full child
          (r.numcells + 1))) := by
      rcases hexit : hrunG.exit with
        ⟨returned, exact⟩ |
        ⟨target, returned, below, sound, payload, located, control⟩ |
        ⟨below, exact, freeze⟩ |
        ⟨boundary, returned, positive, atOrAbove, saved, exact⟩ |
        ⟨returned, state, incumbent, emptyFuel⟩
      · exact exact
      · exfalso
        have htarget : target = level := by
          rw [returned] at hreturn
          exact (Int.ofNat_inj.mp hreturn)
        rcases control with h | h <;> omega
      · exact exact
      · exact exact
      · exact (hfuelNe emptyFuel).elim
    have hdone := hdoneOf hfullKey
    have hcover := hcoverOf hfullKey
    let marked : SearchSt n := { out with gcaFirst := level, stabvertex := tv1 }
    let cleaned : SearchSt n :=
      { out with
        gcaFirst := level
        stabvertex := tv1
        fixedpts := out.fixedpts.erase tv1 }
    let cleared := clearShortIf cleaned.needshortprune cleaned
    let recSt := recover n inf level cleared
    let tcell' := if cleaned.needshortprune then shortprune tcell cleared
      else tcell
    obtain ⟨hfix, hcos, hcomp, hgen, horbC, hfl, hncl, hgf, hgc, hcl, -⟩ :=
      clearShortIf_fields cleaned.needshortprune cleaned
    have hmark : EventOut G ctx tcLevel full fs marked outBest eventTrail
        value :=
      hrunG.proof.setFirstEvent hfull hreturn hdone hlevel hls hlabOk hps
        hend hvals hcell hrange ho hfuel
    have hev : EventOut G ctx tcLevel full fs cleared outBest eventTrail
        value := by
      have h := hmark.setFixed (out.fixedpts.erase tv1)
      rcases hc : cleaned.needshortprune with _ | _
      · simpa only [cleared, hc, clearShortIf, Bool.false_eq_true, ite_false]
          using h
      · simpa only [cleared, hc, clearShortIf, ite_true] using h.clearShort
    have hfirstLe : cleared.gcaFirst ≤ level := by
      rw [hgf]
      exact Nat.le_refl level
    have hinfLevel : level < inf := by
      rw [hinf]
      omega
    have hbaseOut : SearchOut G level level pre out := by
      apply breakout_child_out (stC := child) hn0 hpreOk hlevel hcellPre hlen2
        hrange ho hout
      · rw [hat]
      · exact breakout_ptn (n := n) pre.lab pre.ptn (level + 1) tc tv1
      · rfl
      · rfl
    have hbaseCleared : SearchOut G level level pre cleared := by
      apply hbaseOut.congr
      · exact clearShortIf_lab _ _
      · exact clearShortIf_ptn _ _
      · rw [hfl]
      · rw [hcl]
    have hrecOk := hbaseCleared.recoverOk hinf hlevel hpreOk
    obtain ⟨bs, hrunRec, hstable, hhistory⟩ := hev.recoverRun hreturn hfull
      hlevel hinfLevel hfirstLe hrecOk.2
    have hframes := recover_frames n inf level cleared
    have hgfRec : recSt.gcaFirst = level := by
      rw [show recSt = recover n inf level cleared from rfl,
        hframes.2.2.2.2.2.2.1, hgf]
    have hgcRec : level ≤ recSt.gcaCanon := by
      rw [show recSt = recover n inf level cleared from rfl,
        recover_gcaCanon, hgc]
      change level ≤ if level < out.gcaCanon then level else out.gcaCanon
      split <;> omega
    have hfirstlabRec : recSt.firstlab = out.firstlab := by
      rw [show recSt = recover n inf level cleared from rfl,
        hframes.2.2.2.2.1, hfl]
    have hcanonlabRec : recSt.canonlab = out.canonlab := by
      rw [show recSt = recover n inf level cleared from rfl,
        hframes.1, hcl]
    have hlive : FirstLive ctx level recSt eventTrail r.lab r.ptn := by
      refine ⟨⟨hhistory, ?_, hstable⟩, ?_⟩
      · rw [hgfRec]
        exact hgcRec
      · intro γ hγ
        exact hstable level
          ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩
          (by rw [hgfRec]; exact Int.le_refl _) hentry γ hγ
    obtain ⟨htrailRec, hcanonRec⟩ := hrunG.proof.recoverTrails
      (inf := inf) (fixedpts := out.fixedpts.erase tv1) (tv1 := tv1)
    have hrecEqPlain : recSt = clearShortIf cleaned.needshortprune
        (recover n inf level cleaned) :=
      recover_clearShortIf n inf level cleaned.needshortprune cleaned
    have hfirstTrail : FirstTrail ctx level recSt eventTrail := by
      refine htrailRec.lower.retrail ?_ (TrailExt.refl _ _)
      rw [hfirstlabRec, (recover_frames n inf level _).2.2.2.2.1]
    have hcanonTrail : CanonTrail ctx level recSt eventTrail := by
      refine hcanonRec.retrail ?_ (TrailExt.refl _ _)
      rw [hcanonlabRec, (recover_frames n inf level _).1]
    have hrefs : FrameRefs ctx tcLevel specFuel level full r.lab r.ptn tc len
        r.numcells recSt outBest := by
      have h := hrunG.proof.recoverRefs (inf := inf)
        (fixedpts := out.fixedpts.erase tv1) (tv1 := tv1) hdone ho
      rw [hrecEqPlain]
      rcases hc : cleaned.needshortprune with _ | _
      · simpa only [clearShortIf, Bool.false_eq_true, ite_false] using h
      · simp only [clearShortIf, ite_true]
        exact ⟨h.first, h.canon⟩
    have hshortRec : recSt.needshortprune = false := by
      rw [show recSt = recover n inf level cleared from rfl,
        recover_needshortprune]
      exact clearShortIf_self cleaned
    have hfixedRec : recSt.fixedpts = pre.fixedpts := by
      rw [show recSt = recover n inf level cleared from rfl,
        recover_clearShortIf, (clearShortIf_fields _ _).1, recover_fixedpts]
      change out.fixedpts.erase tv1 = pre.fixedpts
      rw [hrunG.proof.node.fixed]
      exact erase_insert_of_miss hfresh
    have hpathRec : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 level recSt :=
      PathOk.ofSearchOut hn0 hlevel hpathPre hfixedRec hpreOk hrecOk.2
        hrecOk.1
    have hnclRec : recSt.noncheaplevel = if level < out.noncheaplevel
        then level + 1 else out.noncheaplevel := by
      rw [show recSt = recover n inf level cleared from rfl,
        recover_noncheaplevel, hncl]
    have hhRec : FirstSweepHyp G ctx tcLevel specFuel level full bs fs
        r.numcells r.lab r.ptn tc len tcell (some tv1) st.noncheaplevel tv1
        pre recSt outBest eventTrail := by
      refine ⟨?_, hlive, hpathRec, ⟨tv1, rfl, Nat.le_refl _⟩,
        fun v hv => by cases hv; exact htvLt, ?_, hgfRec, hfirstTrail,
        hcanonTrail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact {
          nonempty := hn0
          positive := hlevel
          baseOk := hpreOk
          run := hrunRec
          effect := hrecOk.1
          baseLab := hpreLab
          basePtn := hprePtn
          equitable := heqt
          cell := hcell
          lenTwo := hlen2
          range := hrange
          values := hvals
          members := fun v hv => (mem_windowSet.mp hv).2
          cover := hcover
          refs := hrefs
          shortClear := hshortRec
          fuelBound := hfuel }
      · apply recover_nonpositive
        rw [hcomp]
        exact hmark.nonpositive
      · rw [show recSt = recover n inf level cleared from rfl,
          recover_orbits, recover_genTrace, horbC, hgen]
        exact horbOut
      · rw [show recSt = recover n inf level cleared from rfl,
          recover_coset, hcos]
        exact hcosetOut
      · intro b hb
        rw [hfirstlabRec]
        exact hkeepG.dom b hb
      · intro hlt'
        rw [hnclRec] at hlt'
        rcases Decidable.em (level < out.noncheaplevel) with hc | hc
        · rw [ite_eq_left hc] at hlt'
          exfalso
          omega
        · rw [ite_eq_right hc] at hlt'
          rw [hboundaryG (by omega)] at hlt'
          have hst := hpreKeep hlt'
          rw [hst] at hlt'
          exact SubtreeOk.ofFrames ((hdesc hlt').setActive (a := VSet.empty))
            rfl rfl rfl
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
          rw [hboundaryG (by omega)]
          exact hpreParkWeak hpark
      · intro hlt'
        rw [hnclRec] at hlt' ⊢
        rcases Decidable.em (level < out.noncheaplevel) with hc | hc
        · rw [ite_eq_left hc] at hlt'
          exfalso
          omega
        · rw [ite_eq_right hc] at hlt' ⊢
          rw [hboundaryG (by omega)] at hlt' ⊢
          exact hpreKeep hlt'
    have hinvRec : LoopInv G ctx tcLevel specFuel level full bs fs
        r.numcells r.lab r.ptn tc len tcell' (some tv1) pre recSt outBest
        eventTrail := by
      rcases hc : cleaned.needshortprune with _ | _
      · simpa only [tcell', recSt, cleared, hc, Bool.false_eq_true,
          ite_false] using hhRec.inv
      · have hlast : ∀ fix mcr : VSet n,
            cleared.autos.back? = some (fix, mcr) →
              PairOk ctx.g r.ptn r.lab level fix mcr := by
          intro fix mcr hback
          have hrBelow : value < Int.ofNat (level + 1) :=
            hrunG.exit.below (by omega)
          have hpreserved' : TrailExt (level + 1)
              (eventTrail.push level
                ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩)
              eventTrail := by
            intro target htarget
            rcases Decidable.em (target = level) with rfl | hne
            · rw [FrameTrail.push_self]
              exact hentry
            · rw [FrameTrail.push_of_ne _ _ hne]
          apply shortPairAtReceiver hfull.symm hhRec.inv hpathRec hrBelow
            hrunG.proof.node.outcome.event hpreserved'
            (hrunG.short (by simpa only [cleaned] using hc)) hstay
          simpa only [cleared, clearShortIf, hc, ite_true] using hback
        simpa only [tcell', recSt, cleared, hc, ite_true] using
          hhRec.inv.shortpruneWith hgsz hlast
    have hhRec' := hhRec.filter hinvRec
    have hfuelRec : n < cursorRank (some tv1) + n := by
      simp only [cursorRank]
      omega
    obtain ⟨outBest', eventTrail', hrunTail, hkeepTail⟩ :=
      firstTail hg hinf hn0 ih hrun hspec hfull.symm hstem hpast hbound
        hlen n (some tv1) tcell' recSt outBest eventTrail bs
        (if (recSt.orbits[tv1]! == tv1) = true then 0 + 1 else 0) hhRec'
        hfuelRec
    have hstate := firstChildLoop_stayGuide ctx inf tcLevel runFuel n
      level r.numcells tc tv1 tv1 tcell 0 pre value out hrep hfirstTv hcall
      hstay
    dsimp only at hstate
    refine ⟨outBest', eventTrail', ?_, ?_⟩
    · refine (FirstSweepRun.nextGuide hnext hrep hfirstTv hcall hstay
        ?_ hpreG hrunTail).retrail hext
      exact hfixedRec
    · rw [hstate]
      exact ⟨hkeepTail.dom, hkeepTail.orbits, hkeepTail.coset,
        hkeepTail.boundary⟩

/-! # Back to the enclosing first-path node -/

namespace FirstSweepRun

/-- The escape classification of a sweep result.  Below-loop unwinds are
direct, since the first-path controls keep every orbit pointer at or above
the loop level. -/
theorem escape {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    LoopEscape ctx tcLevel level bound out best outBest receiptTrail r := by
  rcases h.exit with
    ⟨returned, exact⟩ |
    ⟨target, returned, below, sound, payload, located, control⟩ |
    ⟨value, returned, below, exact, freeze⟩ |
    ⟨boundary, returned, positive, below', saved, exact⟩ |
    ⟨returned, finalCursor, progress, bounded⟩
  · exact .full exact
  · cases payload with
    | first anchor carrier =>
        cases located with
        | first _ _ loc => exact .first target returned below anchor carrier loc
    | canon anchor carrier =>
        cases located with
        | canon _ _ loc => exact .canon target returned below anchor carrier loc
    | orbit payload =>
        exfalso
        have := h.guideLevel
        have := h.order
        rcases control with hc | hc <;> omega
  · exact .full exact
  · exact .full exact
  · exact .pending returned

/-- An early integer-valued sweep becomes its enclosing first-path node. -/
theorem toNodeSome {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstSweepRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out none outBest receiptTrail eventTrail (some r)) :
    FirstRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells outBest receiptTrail eventTrail r := by
  have hescape : NodeEscape ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
      out nodeNumcells none outBest receiptTrail r := by
    cases h.escape with
    | full eq => exact .full (by simpa only [hbound] using eq)
    | first target returned below anchor carrier located =>
        exact .first target (Option.some.inj returned) below anchor carrier
          located
    | canon target returned below anchor carrier located =>
        exact .canon target (Option.some.inj returned) below anchor carrier
          located
    | pending returned => cases returned
  refine ⟨⟨⟨h.proof.outcome.toNodeSome hbound, h.proof.fixed.trans hfixed⟩,
    hescape, h.trail, h.canonTrail,
    fun _ => Nat.le_trans (Nat.sub_le level 1) h.guideLevel, h.order⟩,
    h.exit.toNodeSome hbound hprefix, ?_⟩
  intro hshort
  obtain ⟨value, hreturned, hsource⟩ := h.short hshort
  cases Option.some.inj hreturned
  exact hsource

/-- A sufficiently fuelled `none` sweep is genuine completion and becomes
the enclosing first-path node's ordinary return. -/
theorem toNodeNone {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel (specFuel + 1) level nodeCodes
      nodeSt nodeNumcells)
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCodes nodeSt
        nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCodes rsLab rsPtn tc
          loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCodes rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hlen : len = tail + 1)
    (hfuel : n < cursorRank cursor + loopFuel)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out none outBest receiptTrail eventTrail none) :
    FirstRun G ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCodes fs
      nodeSt out nodeNumcells outBest receiptTrail eventTrail
      (Int.ofNat level - 1) := by
  have hfull : outBest = some (incMax none bound) := by
    cases h.proof.outcome.receipt with
    | complete returned sound installed read finalSet finalCursor cover
        empty =>
        rw [hlen] at cover empty
        exact cover.exact_of_read (hbound.trans hchildren) empty sound
          installed read
    | unwind sound target returned below payload located => cases returned
    | pruned target returned below sound installed read full =>
        cases returned
    | exhausted returned sound finalSet finalCursor cover progress
        bounded =>
        exact (LoopResult.exhaustion_false hfuel progress bounded).elim
  have hescape : NodeEscape ctx tcLevel (specFuel + 1) level nodeCodes
      nodeSt out nodeNumcells none outBest receiptTrail
      (Int.ofNat level - 1) := by
    apply NodeEscape.full
    simpa only [hbound] using hfull
  refine ⟨⟨⟨h.proof.outcome.toNodeNone hbound hchildren hlen hfuel,
      h.proof.fixed.trans hfixed⟩,
    hescape, h.trail, h.canonTrail,
    fun _ => Nat.le_trans (Nat.sub_le level 1) h.guideLevel, h.order⟩,
    h.exit.toNodeNone hbound hfuel, ?_⟩
  intro hshort
  obtain ⟨value, hreturned, _⟩ := h.short hshort
  cases hreturned

end FirstSweepRun

end Hex.GraphIso.Nauty
