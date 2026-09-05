/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeCarry
import all HexGraphIso.Nauty.Search

public section

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

private theorem pushAuto_genTrace'' (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_orbits'' (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).orbits = st.orbits := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_gcaCanon'' (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).gcaCanon = st.gcaCanon := by
  rw [pushAuto]
  split <;> rfl

/-- The frozen-downward arm records no generator. -/
theorem processnode_fast_genTrace {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.genTrace),
    pushAuto_genTrace'', ite_self]
  rw [ite_eq_left hg]

/-- The frozen-downward arm leaves the orbit array alone. -/
theorem processnode_fast_orbits {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.orbits = st.orbits := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.orbits),
    pushAuto_orbits'', ite_self]
  rw [ite_eq_left hg]

/-- The frozen-downward arm leaves the canonical guide alone. -/
theorem processnode_fast_gcaCanon {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.gcaCanon = st.gcaCanon := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.gcaCanon),
    pushAuto_gcaCanon'', ite_self]
  rw [ite_eq_left hg, ite_eq_right (by decide)]

/-! # State equations of the internal negative branches -/

/-- The prepared state of an off-path node: refinement followed by the
comparison step, before any target selection. -/
theorem otherLeafSt_eq (ctx : Ctx) (level numcells : Nat) (st : SearchSt) :
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
theorem otherNode_gate_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
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
theorem otherNode_hintFail_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
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
theorem otherNode_hint_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
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
    let start := if ¬ cheapautom pr.2.ptn level ctx.n then
      { pr.2 with noncheaplevel := level + 1 } else pr.2
    let L := otherChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
      (refine ctx level st.lab st.ptn st.active numcells).numcells mt.1
      ((nextElem mt.2.1 none).getD 0) (nextElem mt.2.1 none) mt.2.1 start
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
  rcases hc : cheapautom pr.2.ptn level ctx.n with _ | _ <;>
    simp only [hc, Bool.false_eq_true, not_false_eq_true, ite_true,
      not_true_eq_false, ite_false] <;>
    generalize hL : (otherChildLoop ctx inf tcLevel fuel (ctx.n + 1)
      level _ _ _ _ _ _) = L <;>
    rcases L with ⟨r, out⟩ <;>
    cases r <;> simp only [Id.run_pure, apply_ite Id.run] <;> rfl

/-! # Facts an off-path fragment preserves beyond its packaged run -/

/-- Off-path bookkeeping never rewrites the first leaf, keeps the orbit
array sound, and lowers the saved cheap-cell boundary only to a value
it already had on entry. -/
structure OtherKeep (ctx : Ctx) (level : Nat) (st out : SearchSt) : Prop where
  firstlab : out.firstlab = st.firstlab
  orbits : OrbSound (OrbConn out.genTrace.toList ctx.n) out.orbits ctx.n
  boundary : out.noncheaplevel < level → out.noncheaplevel = st.noncheaplevel

/-- Lowering the first-path agreement depth preserves the prepared
state. -/
theorem RunPrep.setEqlevFirst {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells e : Nat} {codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (h : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (he : e ≤ st.eqlevFirst) :
    RunPrep G ctx tcLevel level codes bs fs numcells
      { st with eqlevFirst := e } best trail := by
  let st' : SearchSt := { st with eqlevFirst := e }
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
theorem RunPrep.fastEvent {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
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
    · exact hprep.leafRefs.processnodeGen hn hn0 hgb hsymm hloop
        hprep.searchOk hprep.canongInv hprep.genTraceOk
    · exact hprep.processnodeAutos hn hn0 hgb hsymm hloop hbound
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
theorem processnode_fast_below {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0)
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
theorem nodeKey_le_of_frozen {ctx : Ctx} {tcLevel specFuel level numcells
    tail : Nat} {codes bs : List Nat} {st : SearchSt}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon compCanon : Int}
    {canonlab : Array Nat}
    (hinv : CodeCmpInv n (codes ++
      [(refine ctx level st.lab st.ptn st.active numcells).longcode]) bs
      canoncode canonlevel eqlevCanon compCanon)
    (hneg : compCanon < 0)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = false)
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
theorem NodeInv.fastRun {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st pre : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
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
    (hsound : OrbSound (OrbConn st.genTrace.toList ctx.n) st.orbits ctx.n) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  subst n
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let full := codes ++ [rs.longcode]
  let pr := processnode ctx level rs.numcells pre
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hgsz : ctx.g.size = ctx.n := by
    rw [hg]
    exact size_rowsOf G
  have hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n := by
    rw [hg]
    exact rowsOf_bounded G
  have hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u := by
    rw [hg]
    exact rowsOf_symm G
  have hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false := by
    rw [hg]
    exact rowsOf_loopless G
  have hframes := processnode_frames ctx level rs.numcells pre
  have hearly : pr.1 < Int.ofNat level :=
    processnode_fast_below hgate hbound
  have hne : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ ctx.n := Nat.ne_of_lt hnum
  have hdisc : discreteAt rs.ptn level ctx.n = false := by
    rw [← Bool.not_eq_true, ← refine_discrete_iff rfl hn0
      hnode.run.searchOk hlevel]
    exact hne
  obtain ⟨tc, len, -, hspec, -, hlen, -⟩ :=
    hnode.target rfl hg hn0 hlevel hne
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
    hprep.fastEvent rfl hn0 hgb hsymm hloop hfull hstem (by omega) hbound
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
    rcases hprep.pruneMode rfl hfull hstem hfirstNe hgate.2 with
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
theorem otherLeafSt_frames (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
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
theorem NodeInv.gateRun {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
    (hgate : (otherLeafSt ctx level numcells st).eqlevFirst ≠ level ∧
      (otherLeafSt ctx level numcells st).compCanon < 0)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList ctx.n) st.orbits ctx.n) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hprep := hnode.run.otherLeaf hn hn0 hlevel hpath
  have hbound : (otherLeafSt ctx level numcells st).noncheaplevel ≤ level := by
    rw [hf9]
    exact hcheap
  have hstate := otherNode_gate_state ctx inf tcLevel fuel level numcells st
    hnum hgate (processnode_fast_below hgate hbound)
  exact hnode.fastRun hn hg hn0 hlevel hpath hnum hstate hprep
    (hlive.otherLeaf (numcells := numcells)) hgate hbound
    (by rw [hf10, hnode.shortClear]) hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9
    hsound

/-- The mismatched-hint negative branch of an internal node. -/
theorem NodeInv.hintFailRun {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmis : Int.ofNat (maketargetcell ctx
        (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 ≠
      (otherLeafSt ctx level numcells st).firsttc[level]!)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList ctx.n) st.orbits ctx.n) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  let pre0 := otherLeafSt ctx level numcells st
  let pre : SearchSt :=
    { pre0 with
      tctotal := pre0.tctotal +
        (maketargetcell ctx pre0.lab pre0.ptn level tcLevel
          pre0.firsttc[level]!).2.2
      eqlevFirst := level - 1 }
  have hprep0 := hnode.run.otherLeaf hn hn0 hlevel hpath
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
  exact hnode.fastRun hn hg hn0 hlevel hpath hnum hstate hprep hlive' hgate
    hbound (by change pre0.needshortprune = false; rw [hf10, hnode.shortClear])
    hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hsound

end Hex.GraphIso.Nauty
