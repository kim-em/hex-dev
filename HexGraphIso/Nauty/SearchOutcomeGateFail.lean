/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeComplete
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.Domination

public section

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
theorem leafFinish_setEqlev (ctx : Ctx n) (level e : Nat) (st : SearchSt n) :
    leafFinish ctx level { st with eqlevFirst := e } =
      { leafFinish ctx level st with eqlevFirst := e } := by
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
    show (_, leafFinish ctx level
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
        (Int.ofNat level - 1, leafFinish ctx level P.2) := by
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
        show stInc ctx (leafFinish ctx level P.2) = _
        rw [stInc_leafFinish]
        exact hevent.read
      rw [hleaf] at hstable ⊢
      rw [hbest]
      dsimp only at hstable ⊢
      exact EventOut.intro level full bs'
        (hevent.leafFinish (ctx := ctx) (level := level)) hfull hstem
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
