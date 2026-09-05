/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Sweep.Carry
import all HexGraphIso.Nauty.Search.Search

public section

/-!
The internal off-path node: its negative-comparison arms, the
per-child transport its sibling sweep needs, and the fuel-separated
totality statements for the whole node.

The logical fuel in `nodeKey`, the node recursion fuel and a sibling
loop's cursor fuel are kept distinct, and the strict node-fuel bound
makes the executable zero-fuel branch unreachable at every well-formed
node.
-/

/-!
The negative-comparison arms of an internal off-path node.

When the refined code is already below the incumbent's, `othernode`
either prunes at once (the first-path agreement is broken) or descends
through the first path's own target cell looking for automorphisms.  The
subtree is dominated in both cases, so its exact maximum is the unchanged
incumbent; what remains is the executable state bookkeeping.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Frame equations of the frozen-downward arm -/

private theorem pushAuto_genTrace'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_orbits'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).orbits = st.orbits := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_gcaCanon'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).gcaCanon = st.gcaCanon := by
  rw [pushAuto]
  split <;> rfl

/-- The frozen-downward arm records no generator. -/
theorem processnode_fast_genTrace {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.genTrace),
    pushAuto_genTrace'', ite_self]
  rw [ite_eq_left hg]

/-- The frozen-downward arm leaves the orbit array alone. -/
theorem processnode_fast_orbits {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.orbits = st.orbits := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.orbits),
    pushAuto_orbits'', ite_self]
  rw [ite_eq_left hg]

/-- The frozen-downward arm leaves the canonical guide alone. -/
theorem processnode_fast_gcaCanon {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.gcaCanon = st.gcaCanon := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.gcaCanon),
    pushAuto_gcaCanon'', ite_self]
  rw [ite_eq_left hg, ite_eq_right (by decide)]

/-! # State equations of the internal negative branches -/

/-- The prepared state of an off-path node: refinement followed by the
comparison step, before any target selection. -/
theorem otherLeafSt_eq (ctx : Ctx n) (level numcells : Nat) (st : SearchSt n) :
    otherLeafSt ctx level numcells st =
      otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 } := rfl

/-- With the first-path agreement broken under a negative comparison,
an internal node prunes at once and returns the leaf event's result. -/
theorem otherNode_gate_state (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (hgate : (otherLeafSt ctx level numcells st).eqlevFirst ≠ level ∧
      (otherLeafSt ctx level numcells st).compCanon < 0)
    (hearly : (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level) :
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      processnode ctx level
        (refine ctx level st.lab st.ptn st.active numcells).numcells
        (otherLeafSt ctx level numcells st) := by
  dsimp only [otherLeafSt] at hgate hearly ⊢
  rw [otherNode]
  simp only [hnum, true_and]
  rw [ite_eq_right (by
    intro h
    rcases h with h | h
    · exact hgate.1 (beq_iff_eq.mp h)
    · exact absurd hgate.2 (Int.not_lt.mpr h))]
  rw [ite_eq_left hearly]
  rfl

/-- A negative comparison whose hinted target disagrees with the first
path demotes the agreement depth and prunes at once. -/
theorem otherNode_hintFail_state (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmis : Int.ofNat (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 ≠
      (otherLeafSt ctx level numcells st).firsttc[level]!)
    (hearly : (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal +
          (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
            (otherLeafSt ctx level numcells st).ptn level tcLevel
            (otherLeafSt ctx level numcells st).firsttc[level]!).2.2
        eqlevFirst := level - 1 }).1 < Int.ofNat level) :
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      processnode ctx level
        (refine ctx level st.lab st.ptn st.active numcells).numcells
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal +
            (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
              (otherLeafSt ctx level numcells st).ptn level tcLevel
              (otherLeafSt ctx level numcells st).firsttc[level]!).2.2
          eqlevFirst := level - 1 } := by
  dsimp only [otherLeafSt] at heq hneg hmis hearly ⊢
  rw [otherNode]
  simp only [hnum, true_and, heq, true_or, ite_true, hneg, ne_eq,
    not_false_eq_true, ite_true, hmis]
  rw [ite_eq_left hearly]
  rfl

/-- A negative comparison whose hinted target agrees with the first path
enters its child loop over that target cell with the comparison still
frozen. -/
theorem otherNode_hint_state (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmatch : Int.ofNat (maketargetcell ctx
        (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 =
      (otherLeafSt ctx level numcells st).firsttc[level]!)
    (hshort : SearchSt.needshortprune (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal +
          (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
            (otherLeafSt ctx level numcells st).ptn level tcLevel
            (otherLeafSt ctx level numcells st).firsttc[level]!).2.2 }).2 =
      false) :
    let pre := otherLeafSt ctx level numcells st
    let mt := maketargetcell ctx pre.lab pre.ptn level tcLevel
      pre.firsttc[level]!
    let base := { pre with tctotal := pre.tctotal + mt.2.2 }
    let pr := processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells base
    let start := if ¬ cheapautom pr.2.ptn level n then
      { pr.2 with noncheaplevel := level + 1 } else pr.2
    let L := otherChildLoop ctx inf tcLevel fuel (n + 1) level
      (refine ctx level st.lab st.ptn st.active numcells).numcells mt.1
      ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 start
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      if pr.1 < Int.ofNat level then pr
      else match L.1 with
        | some rtn => (rtn, L.2)
        | none => (Int.ofNat level - 1, L.2) := by
  dsimp only
  dsimp only [otherLeafSt] at heq hneg hmatch hshort ⊢
  have hnot : ¬ (Int.ofNat (maketargetcell ctx
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).lab
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).ptn level tcLevel
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).firsttc[level]!).1 ≠
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).firsttc[level]!) :=
    fun h => h hmatch
  simp only [Int.ofNat_eq_natCast] at hnot
  rw [otherNode]
  simp only [hnum, true_and, heq, true_or, ite_true, hneg,
    Int.ofNat_eq_natCast, ite_eq_right hnot, hshort, Bool.false_eq_true,
    ite_false, Int.toNat_natCast]
  generalize hpr : processnode ctx level
    (refine ctx level st.lab st.ptn st.active numcells).numcells _ = pr
  rcases hc : cheapautom pr.2.ptn level n with _ | _ <;>
    simp only [Bool.false_eq_true, not_false_eq_true, ite_true,
      not_true_eq_false, ite_false] <;>
    generalize hL : (otherChildLoop ctx inf tcLevel fuel (n + 1)
      level _ _ _ _ _ _) = L <;>
    rcases L with ⟨r, out⟩ <;>
    cases r <;> simp only [Id.run_pure, apply_ite Id.run] <;> rfl

/-! # Facts an off-path fragment preserves beyond its packaged run -/

/-- Off-path bookkeeping never rewrites the first leaf, keeps the orbit
array sound, and lowers the saved cheap-cell boundary only to a value
it already had on entry. -/
structure OtherKeep (ctx : Ctx n) (level : Nat) (st out : SearchSt n) : Prop where
  firstlab : out.firstlab = st.firstlab
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  boundary : out.noncheaplevel < level → out.noncheaplevel = st.noncheaplevel

/-- Lowering the first-path agreement depth preserves the prepared
state. -/
theorem RunPrep.setEqlevFirst {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells e : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (he : e ≤ st.eqlevFirst) :
    RunPrep G ctx tcLevel level codes bs fs numcells
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

/-- The frozen-downward arm of `processnode`, at any cell count, yields
the packaged event with the incumbent unchanged. -/
theorem RunPrep.fastEvent {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : st.noncheaplevel ≤ level)
    (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    EventOut G ctx tcLevel stem fs (processnode ctx level numcells st).2
      best trail (processnode ctx level numcells st).1 := by
  obtain ⟨hr, hcomp, heqlev, hcode, hcanonlevel, hcanonlab, hcanong,
      hsamerows⟩ :=
    processnode_fast (ctx := ctx) (level := level) (numcells := numcells)
      (st := st) hg
  have hframes := processnode_frames ctx level numcells st
  have hgen := processnode_fast_genTrace (ctx := ctx) (numcells := numcells)
    hg
  have hgcaCanon := processnode_fast_gcaCanon (ctx := ctx)
    (numcells := numcells) hg
  have hef : ¬((st.eqlevFirst == level) = true) :=
    fun h => hg.1 (beq_iff_eq.mp h)
  have hevent : RunEvent G ctx tcLevel level codes bs fs
      (processnode ctx level numcells st).2 best trail := by
    refine ⟨Or.inl ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, hprep.bestCodes, ?_⟩
    · rw [hcomp]
      exact Int.le_of_lt hg.2
    · rw [hcomp, heqlev, hcode, hcanonlevel]
      exact hprep.codeInv
    · rw [hframes.2.2.1, hframes.2.2.2.1]
      exact hprep.firstInv
    · rw [hcanong, hcanonlab, hsamerows]
      exact hprep.canongInv
    · exact hprep.leafRefs.processnodeGen hn0 hsymm hloop
        hprep.searchOk hprep.canongInv hprep.genTraceOk
    · exact hprep.processnodeAutos hn0 hsymm hloop hbound
    · exact hprep.workspace.processOff hprep.codeInv hef
    · exact hprep.cheap.processnode
    · exact hprep.leafRefs.processnode hprep.searchOk
    · exact hprep.guides.stateEq hframes.2.2.2.2.2.2.1 hframes.2.2.2.2.1
        hgcaCanon hcanonlab
    · exact hprep.trailOk.processnode
    · rw [hframes.2.2.2.2.2.2.1]
      exact hprep.firstPositive
    · rw [hgcaCanon]
      exact hprep.canonPositive
    · rw [hframes.2.2.2.2.2.2.1]
      exact hprep.firstBound
    · rw [hgcaCanon]
      exact hprep.canonBound
    · rw [hcanonlab]
      exact hprep.incumbent
  apply EventOut.intro level codes bs hevent hpath hstem hpast
  · rw [hr]
    have hlt := pruneReturn_lt (noncheaplevel := st.noncheaplevel)
      (allsamelevel := st.allsamelevel) (eqlevCanon := st.eqlevCanon)
    have hb : Int.ofNat st.noncheaplevel ≤ Int.ofNat level :=
      Int.ofNat_le.mpr hbound
    omega
  · have hs := hlive.stable.ofGenTraceEq hgen
    rw [hframes.2.2.2.2.2.2.1]
    exact hs.lower (Int.min_le_right _ _)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- The return of the frozen-downward arm lies strictly below the node
whenever the saved boundary does not exceed it. -/
theorem processnode_fast_below {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0)
    (hbound : st.noncheaplevel ≤ level) :
    (processnode ctx level numcells st).1 < Int.ofNat level := by
  rw [(processnode_fast (ctx := ctx) (numcells := numcells) hg).1]
  have hlt := pruneReturn_lt (noncheaplevel := st.noncheaplevel)
    (allsamelevel := st.allsamelevel) (eqlevCanon := st.eqlevCanon)
  have hb : Int.ofNat st.noncheaplevel ≤ Int.ofNat level :=
    Int.ofNat_le.mpr hbound
  omega

/-! # The frozen bound at an internal node -/

/-- With the comparison frozen downward at the refined code, every key
of the node's specification subtree is dominated by the incumbent. -/
theorem nodeKey_le_of_frozen {ctx : Ctx n} {tcLevel specFuel level numcells
    tail : Nat} {codes bs : List Nat} {st : SearchSt n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon compCanon : Int}
    {canonlab : Array Nat}
    (hinv : CodeCmpInv n (codes ++
      [(refine ctx level st.lab st.ptn st.active numcells).longcode]) bs
      canoncode canonlevel eqlevCanon compCanon)
    (hneg : compCanon < 0)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = false)
    (hlen : (specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn level
      tcLevel).2.2 = tail + 1) :
    keyLe (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)
      (incKey ctx bs canonlab) := by
  unfold nodeKey
  rw [specNode_internal codes hdisc hlen]
  apply keysMax_le
  · exact hinv.frozenBound hneg _
  · intro y hy
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hy
    exact hinv.frozenBound hneg _

/-! # The immediately pruning internal node -/

/-- An internal off-path node whose prepared state prunes at once through
the frozen-downward arm: its exact maximum is the unchanged incumbent,
and its return is either a frozen comparison or a cheap-cell jump. -/
theorem NodeInv.fastRun {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st pre : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (hstate : otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      processnode ctx level
        (refine ctx level st.lab st.ptn st.active numcells).numcells pre)
    (hprep : RunPrep G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells pre
      best trail)
    (hlive : Live ctx level pre trail)
    (hgate : pre.eqlevFirst ≠ level ∧ pre.compCanon < 0)
    (hbound : pre.noncheaplevel ≤ level)
    (hclear : pre.needshortprune = false)
    (hfirst : pre.gcaFirst = st.gcaFirst)
    (hcanon : pre.gcaCanon = st.gcaCanon)
    (hcanonlab : pre.canonlab = st.canonlab)
    (hcoset : pre.cosetindex = st.cosetindex)
    (hfixed : pre.fixedpts = st.fixedpts)
    (hfirstlab : pre.firstlab = st.firstlab)
    (hgen : pre.genTrace = st.genTrace)
    (horb : pre.orbits = st.orbits)
    (hncl : pre.noncheaplevel = st.noncheaplevel)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let full := codes ++ [rs.longcode]
  let pr := processnode ctx level rs.numcells pre
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
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
  have hframes := processnode_frames ctx level rs.numcells pre
  have hearly : pr.1 < Int.ofNat level :=
    processnode_fast_below hgate hbound
  have hne : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ n := Nat.ne_of_lt hnum
  have hdisc : discreteAt rs.ptn level n = false := by
    rw [← Bool.not_eq_true, ← refine_discrete_iff hn0
      hnode.run.searchOk hlevel]
    exact hne
  obtain ⟨tc, len, -, hspec, -, hlen, -⟩ :=
    hnode.target hg hn0 hlevel hne
  have hkeyLe : keyLe (nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells) (incKey ctx bs pre.canonlab) := by
    apply nodeKey_le_of_frozen (tail := len - 1) hprep.codeInv hgate.2
      hdisc
    rw [hspec]
    simp only
    omega
  have hexact : best = some (incMax best
      (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
    rw [hprep.incumbent, incMax, keyMax_eq_left hkeyLe]
  have hevent : EventOut G ctx tcLevel codes fs pr.2 best trail pr.1 :=
    hprep.fastEvent hn0 hsymm hloop hfull hstem (by omega) hbound
      hgate hlive
  have hgenOut : pr.2.genTrace = pre.genTrace :=
    processnode_fast_genTrace hgate
  have horbOut : pr.2.orbits = pre.orbits :=
    processnode_fast_orbits hgate
  have hcanonOut : pr.2.gcaCanon = pre.gcaCanon :=
    processnode_fast_gcaCanon hgate
  have hcanonlabOut : pr.2.canonlab = pre.canonlab :=
    (processnode_fast (ctx := ctx) (numcells := rs.numcells) hgate).2.2.2.2.2.1
  have hexit : NodeExit ctx tcLevel (specFuel + 1) (fuel + 1) level codes st
      pr.2 numcells best best trail pr.1 := by
    have hfirstNe : pre.eqlevFirst ≠ level := hgate.1
    rcases hprep.pruneMode hfull hstem hfirstNe hgate.2 with
      hfreeze | hjump
    · exact NodeExit.frozen hearly hexact hfreeze
    · apply NodeExit.cheap pre.noncheaplevel hjump hprep.cheap.positive
        hbound
      · exact hframes.2.2.2.2.2.2.2.1
      · exact hexact
  rw [hstate]
  refine ⟨⟨⟨hexit, hevent, TrailExt.refl level trail, ?_, ?_⟩, ?_, ?_, ?_,
    ?_⟩, ?_, ?_, ?_⟩
  · rw [processnode_fixedpts, hfixed]
  · intro hshort
    exact hprep.fastSource hbound hgate hclear hshort
  · rw [hframes.2.2.2.2.2.2.1, hfirst]
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).2
  · left
    exact ⟨hcanonOut.trans hcanon, hcanonlabOut.trans hcanonlab⟩
  · rw [processnode_coset, hcoset]
  · rw [hframes.2.2.2.2.1, hfirstlab]
  · rw [hgenOut, horbOut, hgen, horb]
    exact hsound
  · intro _
    rw [hframes.2.2.2.2.2.2.2.1, hncl]

/-- The prepared state of an off-path node keeps every field the
immediate-prune packaging reads. -/
theorem otherLeafSt_frames (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).gcaFirst = st.gcaFirst ∧
    (otherLeafSt ctx level numcells st).gcaCanon = st.gcaCanon ∧
    (otherLeafSt ctx level numcells st).canonlab = st.canonlab ∧
    (otherLeafSt ctx level numcells st).cosetindex = st.cosetindex ∧
    (otherLeafSt ctx level numcells st).fixedpts = st.fixedpts ∧
    (otherLeafSt ctx level numcells st).firstlab = st.firstlab ∧
    (otherLeafSt ctx level numcells st).genTrace = st.genTrace ∧
    (otherLeafSt ctx level numcells st).orbits = st.orbits ∧
    (otherLeafSt ctx level numcells st).noncheaplevel = st.noncheaplevel ∧
    (otherLeafSt ctx level numcells st).needshortprune =
      st.needshortprune := by
  refine ⟨RefTrail.otherLeaf_gcaFirst ctx level numcells st,
    RefTrail.otherLeaf_gcaCanon ctx level numcells st, ?_, ?_,
    otherLeafSt_fixedpts ctx level numcells st, ?_, ?_, ?_,
    RefTrail.otherLeaf_noncheaplevel ctx level numcells st,
    otherLeafSt_short ctx level numcells st⟩
  · rw [otherLeafSt_eq, (otherNodePrep_frames _ _ _).1]
  · rw [otherLeafSt_eq, otherNodePrep_coset]
  · rw [otherLeafSt_eq, otherNodePrep_firstlab']
  · rw [otherLeafSt_eq, otherNodePrep_genTrace']
  · rw [otherLeafSt_eq, otherNodePrep_orbits']

/-- The broken-agreement negative branch of an internal node. -/
theorem NodeInv.gateRun {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (hgate : (otherLeafSt ctx level numcells st).eqlevFirst ≠ level ∧
      (otherLeafSt ctx level numcells st).compCanon < 0)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hprep := hnode.run.otherLeaf hn0 hlevel hpath
  have hbound : (otherLeafSt ctx level numcells st).noncheaplevel ≤ level := by
    rw [hf9]
    exact hcheap
  have hstate := otherNode_gate_state ctx inf tcLevel fuel level numcells st
    hnum hgate (processnode_fast_below hgate hbound)
  exact hnode.fastRun hg hn0 hlevel hpath hnum hstate hprep
    (hlive.otherLeaf (numcells := numcells)) hgate hbound
    (by rw [hf10, hnode.shortClear]) hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9
    hsound

/-- The mismatched-hint negative branch of an internal node. -/
theorem NodeInv.hintFailRun {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmis : Int.ofNat (maketargetcell ctx
        (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 ≠
      (otherLeafSt ctx level numcells st).firsttc[level]!)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  let pre0 := otherLeafSt ctx level numcells st
  let pre : SearchSt n :=
    { pre0 with
      tctotal := pre0.tctotal +
        (maketargetcell ctx pre0.lab pre0.ptn level tcLevel
          pre0.firsttc[level]!).2.2
      eqlevFirst := level - 1 }
  have hprep0 := hnode.run.otherLeaf hn0 hlevel hpath
  have hprep : RunPrep G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells pre
      best trail := by
    have h1 := hprep0.setTctotal (value := pre0.tctotal +
      (maketargetcell ctx pre0.lab pre0.ptn level tcLevel
        pre0.firsttc[level]!).2.2)
    have h2 := h1.setEqlevFirst (e := level - 1) (by
      change level - 1 ≤ pre0.eqlevFirst
      rw [beq_iff_eq.mp heq]
      omega)
    exact h2
  have hgate : pre.eqlevFirst ≠ level ∧ pre.compCanon < 0 := by
    refine ⟨?_, hneg⟩
    change level - 1 ≠ level
    omega
  have hbound : pre.noncheaplevel ≤ level := by
    change pre0.noncheaplevel ≤ level
    rw [hf9]
    exact hcheap
  have hlive' : Live ctx level pre trail :=
    (hlive.otherLeaf (numcells := numcells)).stateEq rfl rfl rfl rfl rfl
  have hstate := otherNode_hintFail_state ctx inf tcLevel fuel level numcells
    st hnum heq hneg hmis (processnode_fast_below hgate hbound)
  exact hnode.fastRun hg hn0 hlevel hpath hnum hstate hprep hlive' hgate
    hbound (by change pre0.needshortprune = false; rw [hf10, hnode.shortClear])
    hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hsound

end Hex.GraphIso.Nauty

/-!
Per-child transport for the off-path sibling sweep: the guide relation to
the frozen loop entry, the small-cell descent invariant into each
individualized child, and the key identification used by every early
exit.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Key n identification -/

/-- The node key reads only the labelling, partition, and active set. -/
theorem nodeKey_congr {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {cs : List Nat} {st st' : SearchSt n}
    (hlab : st'.lab = st.lab) (hptn : st'.ptn = st.ptn)
    (hactive : st'.active = st.active) :
    nodeKey ctx tcLevel fuel level cs st' numcells =
      nodeKey ctx tcLevel fuel level cs st numcells := by
  unfold nodeKey
  rw [hlab, hptn, hactive]

/-- Every frozen offset carrying the selected vertex has the key of the
executable child built from it. -/
theorem LoopInv.childKeyAll {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv offset currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hoffset : offset < len)
    (hfrozen : rsLab[tc + offset]! = tv)
    (hcurrentAt : st.lab[tc + currentOffset]! = tv) :
    ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := st.fixedpts.insert tv }
          (numcells + 1) := by
  intro o ho hotv
  have hinj : LabInj rsLab n := by
    rw [← h.baseLab]
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
    (hlen : 1 ≤ len) (hlt : lab[tc]! < n) :
    ∃ v, (windowSet n lab tc len).nextElem none = some v := by
  rcases hnext : (windowSet n lab tc len).nextElem none with _ | v
  · exfalso
    have hmem : (windowSet n lab tc len).mem lab[tc]! = true := by
      refine mem_windowSet.mpr ⟨hlt, ?_⟩
      rw [segN]
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), by simp⟩
    exact no_child_after hnext lab[tc]! hmem trivial
  · exact ⟨v, rfl⟩

/-! # Guide relation across one child -/

namespace GuideRel

/-- The guide relation depends only on the guide controls and the two
reference labellings. -/
theorem stateEq {level : Nat} {base st st' : SearchSt n}
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
theorem ofChild {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hguide : GuideRel level base st)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      out (numcells + 1) best outBest receiptTrail eventTrail r) :
    GuideRel level base out := by
  let child : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv }
  have hfirst : out.gcaFirst = st.gcaFirst := hchild.firstGuide
  refine ⟨hfirst.trans hguide.first, hchild.order, ?_⟩
  rcases hchild.canonGuide with hold | hnew
  · rw [hold.1, hold.2]
    exact hguide.canon
  · right
    refine ⟨Nat.le_trans (Nat.le_succ level) hnew.1, ?_⟩
    have hok := hinv.run.searchOk
    have hstSize : st.lab.size = n := hok.labSize
    have hstPtnSize : st.ptn.size = n := hok.ptnSize
    have htcPtn : tc < st.ptn.size := by
      rw [hstPtnSize]
      exact Nat.lt_of_lt_of_le (by omega : tc < tc + len) hinv.range
    have hrangePtn : tc + len ≤ st.ptn.size := by
      rw [hstPtnSize]
      exact hinv.range
    have hchildPtn : child.ptn = st.ptn.set! tc (level + 1) :=
      breakout_ptn (n := n) st.lab st.ptn (level + 1) tc tv
    have hchildOk : SearchOk G (level + 1) (numcells + 1) child := by
      apply breakout_searchOk hinv.nonempty hok hinv.positive
        hinv.currentCell hinv.lenTwo hinv.range hcurrent
      · change (breakout n st.lab st.ptn (level + 1) tc tv).1 = _
        rw [hat]
      · exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc tv
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
        (breakout n st.lab st.ptn (level + 1) tc tv).1
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
theorem recover {level inf : Nat} {base out : SearchSt n}
    (h : GuideRel level base out) (hbase : base.gcaCanon ≤ level)
    (horder : (Nauty.recover n inf level out).gcaFirst ≤
      (Nauty.recover n inf level out).gcaCanon) :
    GuideRel level base (Nauty.recover n inf level out) := by
  have hframes := recover_frames n inf level out
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
theorem SubtreeOk.setActive {ctx : Ctx n} {level : Nat} {r : RefineSt n}
    {a : VSet n} (h : SubtreeOk ctx level r) :
    SubtreeOk ctx level { r with active := a } :=
  ⟨⟨⟨h.it.ok.labSize, h.it.ok.labOk, h.it.ok.ptnSize,
    h.it.ok.ptnEnd⟩, h.it.inj, h.it.vals, h.it.lvl⟩, h.eqt, h.acc,
    h.shape⟩

/-- The frozen frame of a sweep, as a refinement state. -/
@[expose] def LoopInv.frame (rsLab rsPtn : Array Nat) (numcells : Nat) :
    RefineSt n :=
  { lab := rsLab, ptn := rsPtn, active := VSet.empty, numcells := numcells,
    hint := 0, maxpos := 0, longcode := numcells }

/-- A sweep frame with a live target cell has an open position. -/
theorem LoopInv.levelLt {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    level < n := by
  have hbc := h.run.searchOk.bc
  rw [h.ptnEq] at hbc
  have hopen : rsPtn[tc]! > level := by
    have := h.cell.2.2.1 tc (Nat.le_refl tc) (by have := h.lenTwo; omega)
    omega
  have htc : tc < n := by
    have := h.range
    have := h.lenTwo
    omega
  have hne : bcount rsPtn level n ≠ n := by
    intro heq
    rw [bcount] at heq
    have hall := List.countP_eq_length.mp (by
      rw [heq, List.length_range])
    have := of_decide_eq_true (hall tc (List.mem_range.mpr htc))
    omega
  have hle := bcount_le rsPtn level n
  omega

/-- The small-cell descent invariant at the frozen frame transports to
the individualized child of the current recovered state. -/
theorem LoopInv.childDesc {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hpark : cheapautom rsPtn level n = false →
      st.noncheaplevel = level + 1)
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
    · rw [hpark hc]
      simp
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

/-- A small-cell subtree fact at the frozen frame, in the form the
sibling-sweep bound identification consumes. -/
theorem LoopInv.subtreeAt {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hpark : cheapautom rsPtn level n = false →
      st.noncheaplevel = level + 1)
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
      · have := hpark hc
        omega
      · exact hc
  exact hsub.setActive

end Hex.GraphIso.Nauty

/-!
Fuel-separated totality statements for the transcribed search.

The logical fuel in `nodeKey`, the node recursion fuel, and a sibling
loop's cursor fuel are deliberately kept distinct.  The strict node-fuel
bound is preserved by descent and makes the executable zero-fuel branch
unreachable at every well-formed node.

Beyond the packaged run, each node statement carries the facts the
enclosing loops thread through it: the saved cheap-cell boundary, the
small-cell descent invariant at the refined frame, orbit soundness, the
coset cursor, and domination of the first leaf by the incumbent.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Facts a first-path node preserves or establishes beyond its packaged
run. -/
structure FirstKeep (ctx : Ctx n) (level : Nat) (st out : SearchSt n)
    (fs : List Nat) (outBest : Option (Key n)) : Prop where
  dom : ∀ b, outBest = some b → keyLe (pathLeafKey ctx fs out.firstlab) b
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  coset : st.cosetindex < n → out.cosetindex < n
  boundary : out.noncheaplevel < level → out.noncheaplevel = st.noncheaplevel
  guide : level ≤ out.gcaFirst

/-- Totality of one off-path node at a fixed executable recursion fuel.
Off-path nodes are never the root, so the level is at least two. -/
@[expose] def OtherTotal (G : Colored n k) (ctx : Ctx n)
    (inf tcLevel runFuel : Nat) : Prop :=
  ∀ (specFuel level numcells : Nat) (codes bs fs : List Nat)
    (st : SearchSt n) (best : Option (Key n)) (trail : FrameTrail),
    ctx.g = rowsOf G → inf = n + 2 → 0 < n →
    2 ≤ level → level = codes.length + 1 →
    level + specFuel = n + 1 → n + 2 < level + runFuel →
    st.noncheaplevel ≤ level →
    CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells) →
    NodeInv G ctx tcLevel level codes bs fs numcells st best trail →
    Live ctx level st trail →
    PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st →
    OrbSound (OrbConn st.genTrace.toList n) st.orbits n →
    st.cosetindex < n →
    (∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b) →
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel specFuel runFuel level codes fs st
          (otherNode ctx inf tcLevel runFuel level numcells st).2 numcells
          best outBest trail eventTrail
          (otherNode ctx inf tcLevel runFuel level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel runFuel level numcells st).2

/-- Totality of one node on the unique descent preceding the first leaf. -/
@[expose] def FirstTotal (G : Colored n k) (ctx : Ctx n)
    (inf tcLevel runFuel : Nat) : Prop :=
  ∀ (specFuel level numcells : Nat) (codes : List Nat)
    (st : SearchSt n) (trail : FrameTrail),
    ctx.g = rowsOf G → inf = n + 2 → 0 < n →
    1 ≤ level → level = codes.length + 1 →
    level + specFuel = n + 1 → n + 2 < level + runFuel →
    st.noncheaplevel ≤ level →
    CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells) →
    OrbSound (OrbConn st.genTrace.toList n) st.orbits n →
    FirstInv G ctx level codes numcells st trail →
    PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st →
    ∃ fs outBest eventTrail,
      FirstRun G ctx tcLevel specFuel runFuel level codes fs st
          (firstPathNode ctx inf tcLevel runFuel level numcells st).2
          numcells outBest trail eventTrail
          (firstPathNode ctx inf tcLevel runFuel level numcells st).1 ∧
        FirstKeep ctx level st
          (firstPathNode ctx inf tcLevel runFuel level numcells st).2 fs
          outBest

/-- A well-formed search node cannot occur deeper than the graph. -/
theorem SearchOk.levelLe {G : Colored n k} {level numcells : Nat}
    {st : SearchSt n} (h : SearchOk G level numcells st) : level ≤ n :=
  Nat.le_trans h.bc (bcount_le st.ptn level n)

/-- The strict node-fuel invariant rules out the zero-fuel off-path
branch before any operational case analysis is needed. -/
theorem OtherTotal.zero (G : Colored n k) (ctx : Ctx n) (inf tcLevel : Nat) :
    OtherTotal G ctx inf tcLevel 0 := by
  intro specFuel level numcells codes bs fs st best trail _ _ _ _ _ _
    hfuel _ _ hnode _ _ _ _ _
  have hle : level ≤ n := hnode.run.searchOk.levelLe
  omega

/-- The same strict bound rules out zero executable fuel on the initial
descent. -/
theorem FirstTotal.zero (G : Colored n k) (ctx : Ctx n) (inf tcLevel : Nat) :
    FirstTotal G ctx inf tcLevel 0 := by
  intro specFuel level numcells codes st trail _ _ _ _ _ _ hfuel _ _ _
    hfirst _
  have hle : level ≤ n := hfirst.searchOk.levelLe
  omega

end Hex.GraphIso.Nauty
