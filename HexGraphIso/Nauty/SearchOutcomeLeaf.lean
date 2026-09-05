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
