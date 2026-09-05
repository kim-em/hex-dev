/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.State.Ledger
public import HexGraphIso.Nauty.Correct.Unwind.Located
public import HexGraphIso.Nauty.Equitable.Root

public section

/-!
The two frame invariants of the search induction.

`FirstInv` records the pre-incumbent descent, before `firstterminal`
installs the first leaf and the comparison, leaf and guide ledgers exist.
`LoopInv` freezes the refined frame used by the specification and relates
every later state of a mutable child sweep to it by vertex membership.

This module builds on `Correct.State.Ledger` and the located guides of
`Correct.Unwind.Located`.  `Correct.RunInv.History` and every node module
after it carry one of these two frame invariants.
-/

/-!
The pre-incumbent phase of the outcome-indexed search induction.

Before `firstterminal` installs the first leaf, the comparison, leaf, and
guide ledgers do not yet exist.  `FirstInv` records exactly the state that
the unique first descent must preserve.  The ordinary `RunInv` takes over
at the discrete leaf.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- State carried by the unique descent before the first leaf exists. -/
structure FirstInv (G : Colored n k) (ctx : Ctx n) (level : Nat)
    (cs : List Nat) (numcells : Nat) (st : SearchSt n)
    (trail : FrameTrail) : Prop where
  searchOk : SearchOk G level numcells st
  codes : DescentCodes n cs st
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) level st
  cert : CertInv ctx level
    { lab := st.lab, ptn := st.ptn, active := st.active,
      numcells := numcells, hint := 0, maxpos := 0,
      longcode := numcells }
  activeStarts : ∀ v : Nat, st.active.mem v = true →
    v = 0 ∨ st.ptn[v - 1]! ≤ level
  trailOk : TrailOk ctx level st trail
  frameSize : ∀ target entry, target < level →
    trail target = some entry → entry.frame.rsLab.size = n
  genEmpty : st.genTrace = #[]
  autosEmpty : st.autos = #[]
  workspace : WorkspaceOk st
  canongSize : st.canong.size = n
  orbitId : ∀ v, v < n → st.orbits[v]! = v
  shortClear : st.needshortprune = false

/-- A nonempty root starts the first descent with empty stores, identity
orbits, and no active ancestor frame. -/
theorem FirstInv.root {G : Colored n k} (hn0 : 0 < n) :
    FirstInv G { g := rowsOf G } 1 []
      (initialPartition G).2.length
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      FrameTrail.empty := by
  have hok := root_searchOk G hn0
  refine ⟨hok, DescentCodes.root _ _ hn0, ?_, ?_, ?_,
    TrailOk.empty _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CheapOk.root hn0 hok (by simp [rootSt])
  · simpa only [rootSt] using certInv_initial G hn0
  · simpa only [rootSt] using (initial_nodeOk G hn0).starts
  · intro target entry _ hentry
    simp [FrameTrail.empty] at hentry
  · simp [rootSt]
  · simp [rootSt]
  · simp [WorkspaceOk, rootSt]
  · simp [rootSt]
  · intro v hv
    change (Array.ofFn (n := n) fun i : Fin n => i.val)[v]! = v
    rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_ofFn]
  · simp [rootSt]

/-- Refining a first-descent node produces the well-formed equitable
state from which either the first leaf or the next child is selected. -/
theorem FirstInv.refined {G : Colored n k} {ctx : Ctx n}
    {level numcells : Nat} {cs : List Nat} {st : SearchSt n}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level)
    (h : FirstInv G ctx level cs numcells st trail) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    IterOk ctx level r ∧ Equitable ctx level r.lab r.ptn ∧
      bcount r.ptn level n = r.numcells := by
  dsimp only
  let r := refine ctx level st.lab st.ptn st.active numcells
  have hend := searchOk_end hn0 h.searchOk hlevel
  have hls : st.lab.size = n := h.searchOk.labSize
  have hps : st.ptn.size = n := h.searchOk.ptnSize
  have hlab : LabOk st.lab n := by
    exact labOk_of_reach h.searchOk.labSize h.searchOk.reach
  have hinj : LabInj st.lab n := by
    exact labInj_of_reach h.searchOk.labSize hn0 h.searchOk.reach
  have hrst : StOk n level r := by
    apply refine_stOk (ctx := ctx) hls hlab hps hend
  have hrreach : CellsReach G r.lab := by
    apply refine_cellsReach hn0 h.searchOk.reach h.searchOk.labSize
      h.searchOk.ptnSize hend
    intro q hq
    exact Nat.le_trans (h.searchOk.init1 q hq) hlevel
  have hrit : IterOk ctx level r := by
    refine ⟨hrst, ?_, ?_, ?_⟩
    · exact labInj_of_reach hrst.labSize hn0 hrreach
    · intro q hq
      rcases ptn_refine_vals ctx level st.lab st.ptn st.active
        numcells q with he | he
      · rw [he]
        rcases h.searchOk.vals q hq with hq | hq
        · exact Or.inl hq
        · exact Or.inr hq
      · rw [he]
        exact Or.inl (Nat.le_refl level)
    · have hb := h.searchOk.bc
      have hbn := bcount_le st.ptn level n
      omega
  have heqt : Equitable ctx level r.lab r.ptn := by
    apply refine_equitable hls hlab hps hend hinj h.activeStarts
    · intro u v hu hv
      rw [hg]
      apply rowsOf_symm G
      · exact hu
      · exact hv
    · have hcount := h.searchOk.count
      exact hcount.symm
    · exact h.cert
  have hacc : bcount r.ptn level n = r.numcells := by
    have hc := refine_bcount (ctx := ctx) (level := level)
      (lab := st.lab) (ptn := st.ptn) (active := st.active)
      (numcells := numcells) hps.symm (by rw [hls, hps]) hend
    have hold := h.searchOk.count
    change bcount r.ptn level n = r.numcells
    change r.numcells + bcount st.ptn level n =
      numcells + bcount r.ptn level n at hc
    omega
  exact ⟨hrit, heqt, hacc⟩

/-- The selected target-cell child preserves the pre-incumbent invariant
and records its exact parent sweep position in the active trail. -/
theorem FirstInv.child {G : Colored n k} {ctx : Ctx n}
    {specFuel level numcells tc len o : Nat} {cs : List Nat}
    {st : SearchSt n} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hpath : level = cs.length + 1) (hlt : level < n)
    (h : FirstInv G ctx level cs numcells st trail)
    (hcell : IsCell
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tc len)
    (hlen : 2 ≤ len) (hrange : tc + len ≤ n) (ho : o < len) :
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
    let child : SearchSt n := { pre with
      lab := (breakout n pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).1
      ptn := (breakout n pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.1
      active := (breakout n pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.2
      fixedpts := pre.fixedpts.insert pre.lab[tc + o]!
      cosetindex := pre.lab[tc + o]! }
    FirstInv G ctx (level + 1) full (r.numcells + 1) child
      (trail.push level
        ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩) := by
  dsimp only
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
  let child : SearchSt n := { pre with
    lab := (breakout n pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).1
    ptn := (breakout n pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).2.1
    active := (breakout n pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).2.2
    fixedpts := pre.fixedpts.insert pre.lab[tc + o]!
    cosetindex := pre.lab[tc + o]! }
  have hlevel : 1 ≤ level := by omega
  have href := h.refined hg hn0 hlevel
  have hend := searchOk_end hn0 h.searchOk hlevel
  have hpreLab : pre.lab = r.lab := by unfold pre; split <;> rfl
  have hprePtn : pre.ptn = r.ptn := by unfold pre; split <;> rfl
  have hpreFirst : pre.firstcode = st.firstcode.set! level r.longcode := by
    unfold pre
    split <;> rfl
  have hpreCanon : pre.canoncode = st.canoncode := by
    unfold pre
    split <;> rfl
  have hpreGen : pre.genTrace = st.genTrace := by
    unfold pre
    split <;> rfl
  have hpreAutos : pre.autos = st.autos := by
    unfold pre
    split <;> rfl
  have hpreCap : pre.wsCap = st.wsCap := by
    unfold pre
    split <;> rfl
  have hpreCanong : pre.canong = st.canong := by
    unfold pre
    split <;> rfl
  have hpreOrbits : pre.orbits = st.orbits := by
    unfold pre
    split <;> rfl
  have hokPre : SearchOk G level r.numcells pre := by
    apply refine_searchOk hn0 h.searchOk hlevel
    · simp only [pre, pre0]
      split <;> rfl
    · simp only [pre, pre0]
      split <;> rfl
    · exact Or.inl (by simp only [pre, pre0]; split <;> rfl)
  have hcellPre : IsCell pre.ptn level tc len := by
    rw [hprePtn]
    exact hcell
  have hokChild : SearchOk G (level + 1) (r.numcells + 1) child := by
    apply breakout_searchOk hn0 hokPre hlevel hcellPre hlen hrange ho
    · rfl
    · exact breakout_ptn (n := n) pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!
    · rfl
  have hcheap0 : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) level pre0 := by
    apply h.cheap.refine hlevel <;> rfl
  have hcheapPre : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (level + 1) pre := by
    rcases Decidable.em (pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level n) with hguard | hguard
    · have hpre : pre = { pre0 with noncheaplevel := level + 1 } := by
        unfold pre
        rw [ite_eq_left hguard]
      rw [hpre]
      exact hcheap0.park (by omega) (by omega)
    · have hnext : CheapOk ctx (initialPartition G).1
          (initPtn n (n + 2) (initialPartition G).2)
          (level + 1) pre0 := by
        apply hcheap0.next
        intro heq
        have heq' : st.noncheaplevel = level := by simpa [pre0] using heq
        have hguard' : ¬(st.noncheaplevel ≥ level ∧
            ¬ cheapautom r.ptn level n) := by
          simpa [pre0] using hguard
        have hca : cheapautom r.ptn level n = true := by
          rcases hca0 : cheapautom r.ptn level n with _ | _
          · exfalso
            exact hguard' ⟨by omega, by simp [hca0]⟩
          · rfl
        have hS : SubtreeOk ctx level r :=
          subtreeOk_of_cheapautom href.1 href.2.1 href.2.2 hca
        have hpair : PairOk ctx.g
            (initPtn n (n + 2) (initialPartition G).2)
            (initialPartition G).1 1
            (fmptn r.lab r.ptn level n).1
            (fmptn r.lab r.ptn level n).2 := by
          apply pairOk_fmptn_of_subtree (ctx := ctx) (G := G)
            (r := r) hn0 hlevel
          · rw [hg]
            exact size_rowsOf G
          · rw [hg]
            exact rowsOf_symm G
          · rw [hg]
            exact rowsOf_loopless G
          · exact hS
          · rw [← hpreLab]
            exact hokPre.reach
          · intro q hq
            rw [← hprePtn]
            exact hokPre.init1 q hq
        simpa [pre0, heq'] using hpair
      have hpre : pre = pre0 := by
        unfold pre
        rw [ite_eq_right hguard]
      rw [hpre]
      exact hnext
  have hcheapChild : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (level + 1) child := by
    apply hcheapPre.breakout hlevel hcellPre hlen hrange ho <;> rfl
  have htrail : TrailOk ctx (level + 1) child
      (trail.push level
        ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩) := by
    have htrailPre : TrailOk ctx level pre trail := by
      apply h.trailOk.refine
          (by rw [h.searchOk.labSize]) (by rw [h.searchOk.ptnSize]) hend
          (out := pre)
      · exact hpreLab
      · exact hprePtn
    have hpush : TrailOk ctx (level + 1) child
        (trail.push level
          ⟨sweepFrame specFuel full pre.lab pre.ptn tc r.numcells, o⟩) := by
      apply htrailPre.push (specFuel := specFuel) (codes := full)
          (numcells := r.numcells) (tc := tc) (len := len) (o := o)
          (st := pre) (out := child)
      · exact hokPre.labSize
      · exact hokPre.ptnSize
      · rw [hokPre.labSize]
        exact labInj_of_reach hokPre.labSize hn0 hokPre.reach
      · exact searchOk_end hn0 hokPre hlevel
      · exact hcellPre
      · exact hlen
      · exact hrange
      · exact ho
      · rfl
      · exact breakout_ptn (n := n) pre.lab pre.ptn (level + 1) tc
          pre.lab[tc + o]!
    simpa only [hpreLab, hprePtn] using hpush
  refine ⟨hokChild, ?_, hcheapChild, ?_, ?_, htrail, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · apply h.codes.next
    · change child.firstcode =
        st.firstcode.set! (cs.length + 1) r.longcode
      calc
        child.firstcode = pre.firstcode := rfl
        _ = st.firstcode.set! level r.longcode := hpreFirst
        _ = st.firstcode.set! (cs.length + 1) r.longcode := by rw [hpath]
    · rw [show child.canoncode = pre.canoncode by rfl, hpreCanon]
    · omega
    · exact refine_longcode_lt ctx level st.lab st.ptn st.active numcells
  · have hmem : (tc, tc + len - 1) ∈ cells r.ptn level n := by
      apply isCell_mem_cells hcell
      · exact Nat.le_of_eq href.1.ok.ptnSize.symm
      · exact href.1.ok.ptnEnd
      · omega
    have hcert := certInv_breakout (ctx := ctx) (level := level)
      (lab := r.lab) (ptn := r.ptn) (tc := tc)
      (e := tc + len - 1) (o := o) (numcells := r.numcells)
      href.1.ok.labSize href.1.ok.ptnSize href.1.ok.ptnEnd
      href.1.valsWeak href.1.inj hmem (by omega) (by omega) href.2.1
    change CertInv ctx (level + 1)
      { lab := (breakout n pre.lab pre.ptn (level + 1) tc
          pre.lab[tc + o]!).1,
        ptn := (breakout n pre.lab pre.ptn (level + 1) tc
          pre.lab[tc + o]!).2.1,
        active := (breakout n pre.lab pre.ptn (level + 1) tc
          pre.lab[tc + o]!).2.2,
        numcells := r.numcells + 1, hint := 0, maxpos := 0,
        longcode := r.numcells + 1 }
    rw [hpreLab, hprePtn, breakout_ptn]
    exact hcert
  · change ∀ v : Nat,
      (breakout n pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.2.mem v = true →
      v = 0 ∨ (breakout n pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.1[v - 1]! ≤ level + 1
    rw [breakout_ptn]
    exact split_starts hcellPre (by omega)
  · intro target entry hlt hentry
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | rfl
    · rw [FrameTrail.push_of_ne _ _ (Nat.ne_of_lt hold)] at hentry
      exact h.frameSize target entry hold hentry
    · rw [FrameTrail.push_self] at hentry
      have heq : entry =
          ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩ :=
        Option.some.inj hentry.symm
      subst entry
      simpa only [sweepFrame] using href.1.ok.labSize
  · rw [show child.genTrace = pre.genTrace by rfl, hpreGen]
    exact h.genEmpty
  · rw [show child.autos = pre.autos by rfl, hpreAutos]
    exact h.autosEmpty
  · apply h.workspace.ofFields
    · exact (show child.wsCap = pre.wsCap from rfl).trans hpreCap
    · exact (show child.autos = pre.autos from rfl).trans hpreAutos
  · rw [show child.canong = pre.canong by rfl, hpreCanong]
    exact h.canongSize
  · intro v hv
    rw [show child.orbits = pre.orbits by rfl, hpreOrbits]
    exact h.orbitId v hv
  · change pre.needshortprune = false
    unfold pre pre0
    split <;> exact h.shortClear

/-- Reaching a discrete node installs the first leaf and enters the stable
post-incumbent invariant. -/
theorem FirstInv.terminal {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {cs : List Nat} {st : SearchSt n}
    {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [rs.longcode]
    RunInv G ctx tcLevel level full full full rs.numcells
      (firstterminal level (firstLeafSt ctx level numcells st))
      (some (pathLeafKey ctx full rs.lab)) trail := by
  dsimp only
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let leaf := firstLeafSt ctx level numcells st
  let full := cs ++ [rs.longcode]
  have hlevelOne : 1 ≤ level := by omega
  have hok : SearchOk G level rs.numcells leaf := by
    apply refine_searchOk hn0 h.searchOk hlevelOne
    · rfl
    · rfl
    · exact Or.inl rfl
  have hfullLen : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hfullBound : full.length ≤ n := by
    rw [← hfullLen]
    rw [hlevel]
    exact h.codes.bound
  have hfullCodes : ∀ i, 1 ≤ i → i ≤ full.length →
      leaf.firstcode[i]! = full[i - 1]! := by
    simpa only [leaf, full, rs] using
      (firstLeafSt_codes (ctx := ctx) (nn := n) (level := level)
        (numcells := numcells) (cs := cs) (st := st) hlevel
        h.codes.firstSize (by omega) h.codes.content)
  have hfullLt : ∀ c ∈ full, c < codeSentinel := by
    intro c hc
    change c ∈ cs ++ [rs.longcode] at hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact h.codes.lt c hc
    · rw [List.mem_singleton.mp hc]
      exact refine_longcode_lt ctx level st.lab st.ptn st.active numcells
  have hcheap : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) level leaf := by
    apply h.cheap.refine hlevelOne <;> rfl
  have htrail : TrailOk ctx level leaf trail := by
    apply h.trailOk.refine
    · rw [h.searchOk.labSize]
    · rw [h.searchOk.ptnSize]
    · exact searchOk_end hn0 h.searchOk hlevelOne
    · rfl
    · rfl
  have hcheap' : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) full.length leaf := by
    rw [← hfullLen]
    exact hcheap
  apply RunInv.firstterminal (hpath := hfullLen)
      (hok := hok) (hbound := hfullBound) (hcodes := hfullCodes)
      (hlt := hfullLt) (hcheap := hcheap') (htrail := htrail)
  · simp [leaf, firstLeafSt, h.codes.firstSize]
  · simp [leaf, firstLeafSt, h.codes.canonSize]
  · simpa [leaf, firstLeafSt] using h.canongSize
  · simpa [leaf, firstLeafSt] using h.genEmpty
  · simpa [leaf, firstLeafSt] using h.autosEmpty
  · exact h.workspace.ofFields rfl rfl
  · intro he
    have := congrArg List.length he
    simp [full] at this

/-- A discrete node on the first descent returns an exact located receipt
and the stable state installed by that leaf. -/
theorem FirstInv.terminalReceipt {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt n} {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [rs.longcode]
    let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
    NodeReceipt trail ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
        out.2 numcells none (some (pathLeafKey ctx full rs.lab)) out.1 ∧
      RunInv G ctx tcLevel level full full full rs.numcells out.2
        (some (pathLeafKey ctx full rs.lab)) trail := by
  dsimp only
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let full := cs ++ [rs.longcode]
  let leaf := firstLeafSt ctx level numcells st
  have hstate := firstPath_discrete_state ctx inf tcLevel fuel level
    numcells st hnum
  have hrun : RunInv G ctx tcLevel level full full full rs.numcells
      (firstterminal level leaf) (some (pathLeafKey ctx full rs.lab))
      trail := by
    simpa only [rs, full, leaf] using h.terminal hn0 hlevel
  have hdisc : discreteAt rs.ptn level n = true := by
    rw [← refine_discrete_iff hn0 h.searchOk (by omega)]
    exact hnum
  have hnode : nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      pathLeafKey ctx full rs.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey]
  have hread : stInc ctx (firstterminal level leaf) =
      some (pathLeafKey ctx full rs.lab) := by
    apply hrun.read
    rw [(firstterminal_state level leaf).2.2.2.2]
    omega
  constructor
  · rw [hstate]
    apply NodeReceipt.complete
    · apply NodeSound.ofExact
      simp only [incMax, hnode, rs, full]
    · rfl
    · apply canonlevel_ne_zero_of_stInc
      simpa only [leaf] using hread
    · simpa only [leaf] using hread
    · simp only [incMax, hnode, rs, full]
  · rw [hstate]
    exact hrun

end Hex.GraphIso.Nauty

/-!
The stable frame carried by a mutable child sweep.

The executable recovers the parent after every recursive child and may
permute its target cell.  Consequently the loop cannot identify a child
by the current array offset.  `LoopInv` freezes the refined frame used by
the specification and relates every later loop state to it by vertex
membership.  Coverage and generator anchors are likewise stated over
the frozen offsets.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The target-cell representation used by `maketargetcell` is the same
bitset as the length-indexed window representation used by sweep
coverage. -/
theorem worksetOf_eq_windowSet (lab : Array Nat) (tc len : Nat)
    (hlen : 1 ≤ len) :
    worksetOf n lab tc (tc + len - 1) = windowSet n lab tc len := by
  unfold worksetOf windowSet segN
  rw [show tc + len - 1 + 1 - tc = len by omega]
  rw [List.foldl_map]

/-- Charging target-cell statistics changes no logical search field. -/
theorem RunPrep.setTctotal {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells value : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunPrep G ctx tcLevel level codes bs fs numcells st best trail) :
    RunPrep G ctx tcLevel level codes bs fs numcells
      { st with tctotal := value } best trail := by
  let st' : SearchSt n := { st with tctotal := value }
  have hok : SearchOk G level numcells st' := by
    refine ⟨h.searchOk.labSize, h.searchOk.ptnSize, h.searchOk.reach,
      h.searchOk.init1, h.searchOk.vals, h.searchOk.count, h.searchOk.bc,
      h.searchOk.canon⟩
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  refine ⟨hok, h.codeInv, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- Parking the cheap-automorphism boundary changes only the `CheapOk`
component of the stable invariant. -/
theorem RunInv.park {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hcheap : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) level
      { st with noncheaplevel := level + 1 }) :
    RunInv G ctx tcLevel level codes bs fs numcells
      { st with noncheaplevel := level + 1 } best trail := by
  let st' : SearchSt n := { st with noncheaplevel := level + 1 }
  have hok : SearchOk G level numcells st' := by
    refine ⟨h.searchOk.labSize, h.searchOk.ptnSize, h.searchOk.reach,
      h.searchOk.init1, h.searchOk.vals, h.searchOk.count, h.searchOk.bc,
      h.searchOk.canon⟩
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  refine ⟨hok, h.codeInv, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, hcheap, hrefs,
    h.guides.stateEq rfl rfl rfl rfl,
    h.trailOk.stateEq rfl rfl, h.firstPositive, h.canonPositive,
    h.firstBound, h.canonBound, h.bestCodes, h.incumbent⟩

/-- First and canonical controls that point at the current loop level are
backed by children already absorbed into the semantic incumbent. -/
structure FrameRefs (ctx : Ctx n) (tcLevel specFuel level : Nat)
    (codes : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (st : SearchSt n) (best : Option (Key n)) : Prop where
  first : st.gcaFirst = level →
    ∃ o, o < len ∧
      ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells best o ∧
      st.firstlab[tc]! = rsLab[tc + o]! ∧
      cellsPerm rsPtn level rsLab st.firstlab
  canon : st.gcaCanon = level →
    ∃ o, o < len ∧
      ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells best o ∧
      st.canonlab[tc]! = rsLab[tc + o]! ∧
      cellsPerm rsPtn level rsLab st.canonlab

/-- Frame references survive an incumbent increase. -/
theorem FrameRefs.grow {ctx : Ctx n} {tcLevel specFuel level : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {st : SearchSt n} {best best' : Option (Key n)}
    (h : FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells st best)
    (hinc : IncGrows best best') :
    FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells st best' := by
  constructor
  · intro heq
    obtain ⟨o, ho, hdone, hat, hperm⟩ := h.first heq
    exact ⟨o, ho, hdone.mono hinc, hat, hperm⟩
  · intro heq
    obtain ⟨o, ho, hdone, hat, hperm⟩ := h.canon heq
    exact ⟨o, ho, hdone.mono hinc, hat, hperm⟩

/-- Recovering a state related to a valid loop entry restores the full
parent invariant as well as the composable parent-level effect. -/
theorem SearchOut.recoverOk {G : Colored n k}
    {level numcells inf : Nat} {base out : SearchSt n}
    (hinf : inf = n + 2)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells base)
    (hout : SearchOut G level level base out) :
    SearchOut G level level base (Nauty.recover n inf level out) ∧
      SearchOk G level numcells (Nauty.recover n inf level out) := by
  subst inf
  have hrec : SearchOut G level level out
      (Nauty.recover n (n + 2) level out) := by
    have hle : level ≤ n := Nat.le_trans hok.bc
      (bcount_le base.ptn level n)
    exact recover_out (by omega) hout.reach
  have heffect := hout.trans hrec
  refine ⟨heffect, searchOk_of_out hok hlevel heffect ?_⟩
  intro q hq
  rw [recover_ptn]
  rcases Decidable.em (q < n ∧ out.ptn[q]! > level) with hc | hc
  · rw [ite_eq_left hc]
    exact Or.inr rfl
  · rw [ite_eq_right hc]
    left
    rcases Nat.lt_or_ge level out.ptn[q]! with hgt | hle
    · exact absurd ⟨hq, hgt⟩ hc
    · exact hle

/-- Invariant of one imperative child loop.  `base` is the refined state
whose labelling and partition were frozen for `specNode`.  `st` is the
current recovered state after zero or more children and pruning steps. -/
structure LoopInv (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel level : Nat) (codes bs fs : List Nat)
    (numcells : Nat) (rsLab rsPtn : Array Nat) (tc len : Nat) (tcell : VSet n)
    (cursor : Option Nat) (base st : SearchSt n) (best : Option (Key n))
    (trail : FrameTrail) : Prop where
  nonempty : 0 < n
  positive : 1 ≤ level
  baseOk : SearchOk G level numcells base
  run : RunInv G ctx tcLevel level codes bs fs numcells st best trail
  effect : SearchOut G level level base st
  baseLab : base.lab = rsLab
  basePtn : base.ptn = rsPtn
  equitable : Equitable ctx level rsLab rsPtn
  cell : IsCell rsPtn level tc len
  lenTwo : 2 ≤ len
  range : tc + len ≤ n
  values : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2
  members : ∀ v, tcell.mem v = true → v ∈ segN rsLab tc len
  cover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
    numcells tcell cursor best
  refs : FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
    numcells st best
  shortClear : st.needshortprune = false
  fuelBound : level + 1 + specFuel ≤ n + 1

namespace LoopInv

/-- A fresh sweep freezes the current equitable target-cell frame.  The
strict guide bounds make current-level frame references vacuous before
the first child is explored. -/
theorem start {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (h : RunInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hfirst : st.gcaFirst < level) (hcanon : st.gcaCanon < level)
    (heq : Equitable ctx level st.lab st.ptn)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n)
    (hvals : ∀ q : Nat, st.ptn[q]! ≤ level ∨
      st.ptn[q]! = n + 2)
    (hshort : st.needshortprune = false)
    (hfuel : level + 1 + specFuel ≤ n + 1) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      st.lab st.ptn tc len (windowSet n st.lab tc len) none st st best
      trail := by
  refine ⟨hn0, hlevel, h.searchOk, h,
    SearchOut.refl G level level h.searchOk.reach, rfl, rfl, heq, hcell,
    hlen, hrange, hvals, ?_, sweepCover_init ctx tcLevel specFuel level
      codes st.lab st.ptn tc len numcells best (fun o ho =>
        labOk_of_reach h.searchOk.labSize h.searchOk.reach _
          (by rw [h.searchOk.labSize]; omega)), ?_, hshort, hfuel⟩
  · intro v hv
    exact (mem_windowSet.mp hv).2
  · constructor
    · intro he
      exact (Nat.ne_of_lt hfirst he).elim
    · intro he
      exact (Nat.ne_of_lt hcanon he).elim

theorem frozenLabSize {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    rsLab.size = n := by
  rw [← h.baseLab, h.baseOk.labSize]

theorem frozenPtnSize {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    rsPtn.size = n := by
  rw [← h.basePtn, h.baseOk.ptnSize]

theorem frozenLabOk {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    LabOk rsLab n := by
  rw [← h.baseLab]
  exact labOk_of_reach h.baseOk.labSize h.baseOk.reach

theorem frozenEnd {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    rsPtn[rsPtn.size - 1]! ≤ level := by
  rw [← h.basePtn]
  exact searchOk_end h.nonempty h.baseOk h.positive

theorem frozenVals {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2 := by
  exact h.values

/-- The current recovered partition is exactly the frozen partition. -/
theorem ptnEq {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    st.ptn = rsPtn := by
  rw [← h.basePtn]
  exact h.effect.ptnEq h.baseOk h.run.searchOk

/-- Recovery may reorder a cell, but cannot change its vertex set. -/
theorem labPerm {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    cellsPerm rsPtn level rsLab st.lab := by
  rw [← h.basePtn, ← h.baseLab]
  exact h.effect.perm

theorem currentEquitable {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    Equitable ctx level st.lab st.ptn := by
  rw [h.ptnEq]
  exact h.equitable.ofCellsPerm h.labPerm h.frozenPtnSize h.frozenEnd

theorem currentCell {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    IsCell st.ptn level tc len := by
  rw [h.ptnEq]
  exact h.cell

/-- A recursive child effect, followed by temporary fixed-point cleanup
and `recover`, composes back into the frozen parent frame. -/
theorem recoverChild {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {currentOffset inf : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hinf : inf = n + 2) (hcurrent : currentOffset < len)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      out) :
    let cleaned : SearchSt n :=
      { out with fixedpts := out.fixedpts.erase st.lab[tc + currentOffset]! }
    let recovered := Nauty.recover n inf level cleaned
    SearchOut G level level base recovered ∧
      SearchOk G level numcells recovered := by
  dsimp only
  let cleaned : SearchSt n :=
    { out with fixedpts := out.fixedpts.erase st.lab[tc + currentOffset]! }
  have hchild : SearchOut G level level st out := by
    apply breakout_child_out hinv.nonempty hinv.run.searchOk hinv.positive
      hinv.currentCell hinv.lenTwo
      hinv.range hcurrent
    · exact hout
    · rfl
    · exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!
    · rfl
    · rfl
  have hclean : SearchOut G level level st cleaned := by
    exact hchild.congr rfl rfl rfl rfl
  have hbase : SearchOut G level level base cleaned :=
    hinv.effect.trans hclean
  simpa only [cleaned] using hbase.recoverOk hinf
    hinv.positive hinv.baseOk

/-- A vertex selected from the mutable bitset has both its frozen
specification offset and its current executable offset. -/
theorem nextOffsets {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hnext : tcell.nextElem cursor = some tv) :
    ∃ offset currentOffset, offset < len ∧ currentOffset < len ∧
      rsLab[tc + offset]! = tv ∧ st.lab[tc + currentOffset]! = tv := by
  have hmemBit : tcell.mem tv = true := VSet.nextElem_mem hnext
  have hmemFrozen := h.members tv hmemBit
  obtain ⟨offset, hoffset, hatFrozen⟩ := mem_segN_iff.mp hmemFrozen
  have hmemCurrent : tv ∈ segN st.lab tc len :=
    (h.labPerm tc len h.cell).mem_iff.mp hmemFrozen
  obtain ⟨currentOffset, hcurrent, hatCurrent⟩ :=
    mem_segN_iff.mp hmemCurrent
  exact ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen,
    hatCurrent⟩

/-- Every vertex returned by a verified sibling sweep lies in the graph
vertex range.  This is the cursor bound used by the fuel induction, and
it is derived from the frozen target-cell membership rather than from the
mutable bitset alone. -/
theorem nextLt {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hnext : tcell.nextElem cursor = some tv) :
    tv < n := by
  obtain ⟨offset, _, hoffset, _, hatFrozen, _⟩ := h.nextOffsets hnext
  rw [← hatFrozen]
  apply h.frozenLabOk (tc + offset)
  rw [h.frozenLabSize]
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoffset tc) h.range

/-- The next mutable-loop selection enters a valid recursive node while
recording the corresponding frozen specification offset in the trail. -/
theorem child {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hnext : tcell.nextElem cursor = some tv)
    (hcheap : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) (level + 1) st) :
    ∃ offset currentOffset, offset < len ∧ currentOffset < len ∧
      rsLab[tc + offset]! = tv ∧ st.lab[tc + currentOffset]! = tv ∧
      NodeInv G ctx tcLevel (level + 1) codes bs fs (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).2.2
          fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]!
          cosetindex := coset }
        best
        (trail.push level
          ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) := by
  obtain ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen,
      hatCurrent⟩ := h.nextOffsets hnext
  let child : SearchSt n := { st with
    lab := (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + currentOffset]!).1
    ptn := (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + currentOffset]!).2.1
    active := (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + currentOffset]!).2.2
    fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]!
    cosetindex := coset }
  let childTrail := trail.push level
    ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
  have hfirstSize : st.firstlab.size = n := by
    exact h.run.leafRefs.firstSize
  have hcanonSize : st.canonlab.size = n := by
    exact h.run.leafRefs.canonSize
  have hguides : GuideStore ctx tcLevel (level + 1) child best
      childTrail := by
    apply GuideStore.stateEq
      (h.run.guides.pushSweep h.positive h.frozenLabSize h.frozenLabOk
        h.frozenPtnSize h.frozenEnd h.frozenVals h.cell h.range
        h.fuelBound hfirstSize hcanonSize
        h.refs.first h.refs.canon)
    all_goals rfl
  have hls : st.lab.size = n := by
    exact h.run.searchOk.labSize
  have hps : st.ptn.size = n := by
    exact h.run.searchOk.ptnSize
  have hinj : LabInj st.lab st.lab.size := by
    rw [h.run.searchOk.labSize]
    exact labInj_of_reach h.run.searchOk.labSize h.nonempty
      h.run.searchOk.reach
  have htrail : TrailOk ctx (level + 1) child childTrail := by
    apply h.run.trailOk.pushFrame hls hps hinj
      (searchOk_end h.nonempty h.run.searchOk h.positive)
      h.frozenLabSize h.frozenPtnSize h.frozenEnd h.labPerm h.ptnEq
      h.cell h.currentCell h.lenTwo h.range hoffset hcurrent
    · exact hatCurrent.trans hatFrozen.symm
    · rfl
    · exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!
  have hnode : NodeInv G ctx tcLevel (level + 1) codes bs fs
      (numcells + 1) child best childTrail := by
    apply h.run.child h.nonempty h.positive h.currentEquitable
      h.currentCell h.lenTwo h.range hcurrent h.shortClear hcheap hguides
      htrail
  exact ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen, hatCurrent,
    hnode⟩

/-- An internal off-path node reaches a fresh verified child sweep after
the executable refinement, comparison, target-accounting, and cheap-rule
bookkeeping.  The returned target is simultaneously the executable and
specification target, so the accompanying equality exposes the whole
node key as this sweep's bound. -/
theorem NodeInv.otherSweep {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (h : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ n)
    (hnonneg : (otherLeafSt ctx level numcells st).compCanon ≥ 0)
    (hfuel : level + 1 + specFuel ≤ n + 1) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    let full := codes ++ [r.longcode]
    let pre := otherLeafSt ctx level numcells st
    ∃ tc len,
      let tcell := worksetOf n r.lab tc (tc + len - 1)
      let base : SearchSt n := { pre with tctotal := pre.tctotal + len }
      let start := if cheapautom base.ptn level n then base
        else { base with noncheaplevel := level + 1 }
      maketargetcell ctx r.lab r.ptn level tcLevel (-1) =
          (tc, tcell, len) ∧
        processnode ctx level r.numcells base = (Int.ofNat level, base) ∧
        nodeKey ctx tcLevel (specFuel + 1) level codes st numcells =
          keysMax
            (sweepKey ctx tcLevel specFuel level full r.lab r.ptn tc
              r.numcells 0)
            ((List.range (len - 1)).map fun o =>
              sweepKey ctx tcLevel specFuel level full r.lab r.ptn tc
                r.numcells (o + 1)) ∧
        LoopInv G ctx tcLevel specFuel level full bs fs r.numcells
          r.lab r.ptn tc len tcell none start start best trail := by
  dsimp only
  let r := refine ctx level st.lab st.ptn st.active numcells
  let full := codes ++ [r.longcode]
  let pre := otherLeafSt ctx level numcells st
  have href := h.refined hg hn0 hlevel
  obtain ⟨tc, len, hmk, hspec, hcell, hlen, hrange⟩ :=
    h.target hg hn0 hlevel hnum
  refine ⟨tc, len, ?_⟩
  let tcell := worksetOf n r.lab tc (tc + len - 1)
  let base : SearchSt n := { pre with tctotal := pre.tctotal + len }
  let start := if cheapautom base.ptn level n then base
    else { base with noncheaplevel := level + 1 }
  have hdisc : discreteAt r.ptn level n = false := by
    rw [← Bool.not_eq_true, ← refine_discrete_iff hn0
      h.run.searchOk hlevel]
    exact hnum
  have hchildren := h.children (specFuel := specFuel) hdisc hspec hlen
  have hprep : RunPrep G ctx tcLevel level full bs fs r.numcells pre
      best trail := by
    simpa only [r, full, pre] using
      h.run.otherLeaf hn0 hlevel hpath
  have hbase : RunPrep G ctx tcLevel level full bs fs r.numcells base
      best trail := by
    exact hprep.setTctotal
  have hpreNonneg : pre.compCanon ≥ 0 := by
    simpa only [pre] using hnonneg
  have hprocess : processnode ctx level r.numcells base =
      (Int.ofNat level, base) := by
    apply processnode_internal
    · intro hgate
      have hcomp : base.compCanon = pre.compCanon := rfl
      rw [hcomp] at hgate
      omega
    · intro heq
      exact hnum (beq_iff_eq.mp heq)
  have hrun : RunInv G ctx tcLevel level full bs fs r.numcells start
      best trail := by
    rcases hc : cheapautom base.ptn level n with _ | _
    · have hp : CheapOk ctx (initialPartition G).1
          (initPtn n (n + 2) (initialPartition G).2) level
          { base with noncheaplevel := level + 1 } :=
        hbase.cheap.park (by omega) (by omega)
      simpa only [start, hc, Bool.false_eq_true, ite_false] using
        hbase.run.park hp
    · simpa only [start, hc, ite_true] using hbase.run
  have hpreFirst : pre.gcaFirst = st.gcaFirst := by
    dsimp only [pre, otherLeafSt, r]
    exact (otherNodePrep_frames level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
        active := (refine ctx level st.lab st.ptn st.active numcells).active
        numnodes := st.numnodes + 1 }).2.2.2.2.2.2.1
  have hpreCanon : pre.gcaCanon = st.gcaCanon := by
    dsimp only [pre, otherLeafSt, r]
    exact (otherNodePrep_frames level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
        active := (refine ctx level st.lab st.ptn st.active numcells).active
        numnodes := st.numnodes + 1 }).2.2.2.2.2.2.2.1
  have hpreShort : pre.needshortprune = st.needshortprune := by
    dsimp only [pre, otherLeafSt, r]
    rw [otherNodePrep]
    simp only [Id.run_pure, apply_ite Id.run,
      apply_ite SearchSt.needshortprune, ite_self]
  have hstartFirst : start.gcaFirst = st.gcaFirst := by
    unfold start base
    split <;> exact hpreFirst
  have hstartCanon : start.gcaCanon = st.gcaCanon := by
    unfold start base
    split <;> exact hpreCanon
  have hstartShort : start.needshortprune = false := by
    unfold start base
    split <;> simpa only [hpreShort] using h.shortClear
  have hstartLab : start.lab = r.lab := by
    unfold start base pre otherLeafSt
    split <;>
      simpa only [r] using
        (otherNodePrep_frames level r.longcode
          { st with
            lab := r.lab
            ptn := r.ptn
            active := r.active
            numnodes := st.numnodes + 1 }).2.2.2.2.2.2.2.2.2.2.2.1
  have hstartPtn : start.ptn = r.ptn := by
    unfold start base pre otherLeafSt
    split <;>
      simpa only [r] using
        (otherNodePrep_frames level r.longcode
          { st with
            lab := r.lab
            ptn := r.ptn
            active := r.active
            numnodes := st.numnodes + 1 }).2.2.2.2.2.2.2.2.2.2.2.2
  have hvals : ∀ q : Nat, r.ptn[q]! ≤ level ∨
      r.ptn[q]! = n + 2 := by
    intro q
    rcases Nat.lt_or_ge q n with hq | hq
    · exact href.1.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [href.1.ok.ptnSize]; omega)]
      exact Nat.zero_le _
  have hloop := LoopInv.start hn0 hlevel hrun
    (by rw [hstartFirst]; exact h.firstBelow)
    (by rw [hstartCanon]; exact h.canonBelow)
    (by rw [hstartLab, hstartPtn]; exact href.2.1)
    (by rw [hstartPtn]; exact hcell) hlen hrange
    (by rw [hstartPtn]; exact hvals) hstartShort hfuel
  refine ⟨?_, hprocess, hchildren, ?_⟩
  · simpa only [r, tcell] using hmk
  · rw [worksetOf_eq_windowSet r.lab tc len (by omega)]
    simpa only [hstartLab, hstartPtn] using hloop

set_option maxHeartbeats 800000 in
/-- The nonnegative internal branch with a failed cheap-automorphism test
parks the boundary before entering its child loop. -/
theorem otherNode_park_state (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (hnonneg : let r := refine ctx level st.lab st.ptn st.active numcells
      let pre := otherNodePrep level r.longcode { st with
        lab := r.lab, ptn := r.ptn, active := r.active
        numnodes := st.numnodes + 1 }
      pre.compCanon ≥ 0)
    (hshort : let r := refine ctx level st.lab st.ptn st.active numcells
      let pre := otherNodePrep level r.longcode { st with
        lab := r.lab, ptn := r.ptn, active := r.active
        numnodes := st.numnodes + 1 }
      let mt := maketargetcell ctx pre.lab pre.ptn level tcLevel (-1)
      let base := { pre with tctotal := pre.tctotal + mt.2.2 }
      (processnode ctx level r.numcells base).2.needshortprune = false)
    (hcheap : let r := refine ctx level st.lab st.ptn st.active numcells
      let pre := otherNodePrep level r.longcode { st with
        lab := r.lab, ptn := r.ptn, active := r.active
        numnodes := st.numnodes + 1 }
      let mt := maketargetcell ctx pre.lab pre.ptn level tcLevel (-1)
      let base := { pre with tctotal := pre.tctotal + mt.2.2 }
      cheapautom (processnode ctx level r.numcells base).2.ptn
        level n = false) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    let pre := otherNodePrep level r.longcode { st with
      lab := r.lab, ptn := r.ptn, active := r.active
      numnodes := st.numnodes + 1 }
    let mt := maketargetcell ctx pre.lab pre.ptn level tcLevel (-1)
    let base := { pre with tctotal := pre.tctotal + mt.2.2 }
    let pr := processnode ctx level r.numcells base
    let parked := { pr.2 with noncheaplevel := level + 1 }
    let L := otherChildLoop ctx inf tcLevel fuel (n + 1) level
      r.numcells mt.1 ((mt.2.1.nextElem none).getD 0)
      (mt.2.1.nextElem none) mt.2.1 parked
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      if pr.1 < Int.ofNat level then pr
      else match L.1 with
        | some rtn => (rtn, L.2)
        | none => (Int.ofNat level - 1, L.2) := by
  dsimp only at hnonneg hshort hcheap ⊢
  rw [otherNode]
  simp only [hnum, true_and, ne_eq, ite_eq_left (Or.inr hnonneg),
    ite_eq_right (by omega : ¬((otherNodePrep level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
        active := (refine ctx level st.lab st.ptn st.active numcells).active
        numnodes := st.numnodes + 1 }).compCanon < 0)),
    hshort, Bool.false_eq_true, ite_false, hcheap, 
    Int.ofNat_eq_natCast, Int.toNat_natCast]
  generalize hL : (otherChildLoop ctx inf tcLevel fuel (n + 1)
    level _ _ _ _ _ _) = L
  rcases L with ⟨r, out⟩
  cases r <;> simp only [Id.run_pure, apply_ite Id.run] <;> rfl

end LoopInv

end Hex.GraphIso.Nauty
