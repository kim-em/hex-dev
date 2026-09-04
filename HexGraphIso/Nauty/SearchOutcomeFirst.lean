/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeLedger
public import HexGraphIso.Nauty.RootEquitable

public section

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
structure FirstInv (G : Colored n k) (ctx : Ctx) (level : Nat)
    (cs : List Nat) (numcells : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop where
  searchOk : SearchOk G level numcells st
  codes : DescentCodes n cs st
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) level st
  cert : CertInv ctx level
    { lab := st.lab, ptn := st.ptn, active := st.active,
      numcells := numcells, hint := 0, maxpos := 0,
      longcode := numcells }
  activeLt : st.active < 2 ^ ctx.n
  activeStarts : ∀ v : Nat, elem st.active v = true →
    v = 0 ∨ st.ptn[v - 1]! ≤ level
  trailOk : TrailOk ctx level st trail
  frameSize : ∀ target entry, target < level →
    trail target = some entry → entry.frame.rsLab.size = ctx.n
  genEmpty : st.genTrace = #[]
  autosEmpty : st.autos = #[]
  workspace : WorkspaceOk st
  canongSize : st.canong.size = ctx.n
  orbitId : ∀ v, v < ctx.n → st.orbits[v]! = v
  shortClear : st.needshortprune = false

/-- A nonempty root starts the first descent with empty stores, identity
orbits, and no active ancestor frame. -/
theorem FirstInv.root {G : Colored n k} (hn0 : 0 < n) :
    FirstInv G { n := n, g := rowsOf G } 1 []
      (initialPartition G).2.length
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      FrameTrail.empty := by
  have hok := root_searchOk G hn0
  refine ⟨hok, DescentCodes.root _ _ hn0, ?_, ?_, ?_, ?_,
    TrailOk.empty _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CheapOk.root rfl hn0 hok (by simp [rootSt])
  · simpa only [rootSt] using certInv_initial G hn0
  · simpa only [rootSt] using (initial_nodeOk G hn0).act
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
theorem FirstInv.refined {G : Colored n k} {ctx : Ctx}
    {level numcells : Nat} {cs : List Nat} {st : SearchSt}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level)
    (h : FirstInv G ctx level cs numcells st trail) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    IterOk ctx level r ∧ Equitable ctx level r.lab r.ptn ∧
      bcount r.ptn level ctx.n = r.numcells := by
  subst n
  dsimp only
  let r := refine ctx level st.lab st.ptn st.active numcells
  have hend := searchOk_end hn0 h.searchOk hlevel
  have hls : st.lab.size = ctx.n := h.searchOk.labSize
  have hps : st.ptn.size = ctx.n := h.searchOk.ptnSize
  have hlab : LabOk st.lab ctx.n := by
    exact labOk_of_reach h.searchOk.labSize h.searchOk.reach
  have hinj : LabInj st.lab ctx.n := by
    exact labInj_of_reach h.searchOk.labSize hn0 h.searchOk.reach
  have hrst : StOk ctx.n level r := by
    apply refine_stOk (ctx := ctx) rfl hls hlab hps h.activeLt hend
  have hrreach : CellsReach G r.lab := by
    apply refine_cellsReach rfl hn0 h.searchOk.reach h.searchOk.labSize
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
      have hbn := bcount_le st.ptn level ctx.n
      omega
  have heqt : Equitable ctx level r.lab r.ptn := by
    apply refine_equitable hls hlab hps h.activeLt hend hinj h.activeStarts
    · intro u v hu hv
      rw [hg]
      apply rowsOf_symm G
      · exact hu
      · exact hv
    · have hcount := h.searchOk.count
      exact hcount.symm
    · exact h.cert
  have hacc : bcount r.ptn level ctx.n = r.numcells := by
    have hc := refine_bcount (ctx := ctx) (level := level)
      (lab := st.lab) (ptn := st.ptn) (active := st.active)
      (numcells := numcells) hps.symm (by rw [hls, hps]) hend
    have hold := h.searchOk.count
    change bcount r.ptn level ctx.n = r.numcells
    change r.numcells + bcount st.ptn level ctx.n =
      numcells + bcount r.ptn level ctx.n at hc
    omega
  exact ⟨hrit, heqt, hacc⟩

/-- The selected target-cell child preserves the pre-incumbent invariant
and records its exact parent sweep position in the active trail. -/
theorem FirstInv.child {G : Colored n k} {ctx : Ctx}
    {specFuel level numcells tc len o : Nat} {cs : List Nat}
    {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hpath : level = cs.length + 1) (hlt : level < n)
    (h : FirstInv G ctx level cs numcells st trail)
    (hcell : IsCell
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tc len)
    (hlen : 2 ≤ len) (hrange : tc + len ≤ ctx.n) (ho : o < len) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [r.longcode]
    let pre0 : SearchSt := { st with
      lab := r.lab
      ptn := r.ptn
      active := r.active
      firstcode := st.firstcode.set! level r.longcode
      firsttc := st.firsttc.set! level (Int.ofNat tc)
      numnodes := st.numnodes + 1
      tctotal := st.tctotal + len }
    let pre := if pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level ctx.n then
      { pre0 with noncheaplevel := level + 1 }
    else pre0
    let child : SearchSt := { pre with
      lab := (breakout pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).1
      ptn := (breakout pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.1
      active := (breakout pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.2
      fixedpts := insert pre.fixedpts pre.lab[tc + o]!
      cosetindex := pre.lab[tc + o]! }
    FirstInv G ctx (level + 1) full (r.numcells + 1) child
      (trail.push level
        ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩) := by
  subst n
  dsimp only
  let r := refine ctx level st.lab st.ptn st.active numcells
  let full := cs ++ [r.longcode]
  let pre0 : SearchSt := { st with
    lab := r.lab
    ptn := r.ptn
    active := r.active
    firstcode := st.firstcode.set! level r.longcode
    firsttc := st.firsttc.set! level (Int.ofNat tc)
    numnodes := st.numnodes + 1
    tctotal := st.tctotal + len }
  let pre := if pre0.noncheaplevel ≥ level ∧
      ¬ cheapautom pre0.ptn level ctx.n then
    { pre0 with noncheaplevel := level + 1 }
  else pre0
  let child : SearchSt := { pre with
    lab := (breakout pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).1
    ptn := (breakout pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).2.1
    active := (breakout pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).2.2
    fixedpts := insert pre.fixedpts pre.lab[tc + o]!
    cosetindex := pre.lab[tc + o]! }
  have hlevel : 1 ≤ level := by omega
  have href := h.refined rfl hg hn0 hlevel
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
    apply refine_searchOk rfl hn0 h.searchOk hlevel
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
    · exact breakout_ptn pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!
    · rfl
  have hcheap0 : CheapOk ctx (initialPartition G).1
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2) level pre0 := by
    apply h.cheap.refine hlevel <;> rfl
  have hcheapPre : CheapOk ctx (initialPartition G).1
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (level + 1) pre := by
    rcases Decidable.em (pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level ctx.n) with hguard | hguard
    · have hpre : pre = { pre0 with noncheaplevel := level + 1 } := by
        unfold pre
        rw [ite_eq_left hguard]
      rw [hpre]
      exact hcheap0.park (by omega) (by omega)
    · have hnext : CheapOk ctx (initialPartition G).1
          (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
          (level + 1) pre0 := by
        apply hcheap0.next
        intro heq
        have heq' : st.noncheaplevel = level := by simpa [pre0] using heq
        have hguard' : ¬(st.noncheaplevel ≥ level ∧
            ¬ cheapautom r.ptn level ctx.n) := by
          simpa [pre0] using hguard
        have hca : cheapautom r.ptn level ctx.n = true := by
          rcases hca0 : cheapautom r.ptn level ctx.n with _ | _
          · exfalso
            exact hguard' ⟨by omega, by simp [hca0]⟩
          · rfl
        have hS : SubtreeOk ctx level r :=
          subtreeOk_of_cheapautom href.1 href.2.1 href.2.2 hca
        have hpair : PairOk ctx.g
            (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
            (initialPartition G).1 1 ctx.n
            (fmptn r.lab r.ptn level ctx.n).1
            (fmptn r.lab r.ptn level ctx.n).2 := by
          apply pairOk_fmptn_of_subtree (ctx := ctx) (G := G)
            (r := r) hn0 hlevel
          · rw [hg]
            exact size_rowsOf G
          · rw [hg]
            exact rowsOf_bounded G
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
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
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
      · exact breakout_ptn pre.lab pre.ptn (level + 1) tc
          pre.lab[tc + o]!
    simpa only [hpreLab, hprePtn] using hpush
  refine ⟨hokChild, ?_, hcheapChild, ?_, ?_, ?_, htrail, ?_, ?_, ?_,
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
  · have hmem : (tc, tc + len - 1) ∈ cells r.ptn level ctx.n := by
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
      { lab := (breakout pre.lab pre.ptn (level + 1) tc
          pre.lab[tc + o]!).1,
        ptn := (breakout pre.lab pre.ptn (level + 1) tc
          pre.lab[tc + o]!).2.1,
        active := (breakout pre.lab pre.ptn (level + 1) tc
          pre.lab[tc + o]!).2.2,
        numcells := r.numcells + 1, hint := 0, maxpos := 0,
        longcode := r.numcells + 1 }
    rw [hpreLab, hprePtn, breakout_ptn]
    exact hcert
  · change (breakout pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).2.2 < 2 ^ ctx.n
    exact singleActive_lt (by omega)
  · change ∀ v : Nat,
      elem (breakout pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.2 v = true →
      v = 0 ∨ (breakout pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.1[v - 1]! ≤ level + 1
    rw [breakout_ptn]
    exact split_starts hokPre.ptnSize hcellPre
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
theorem FirstInv.terminal {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {cs : List Nat} {st : SearchSt}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : level = cs.length + 1)
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
    apply refine_searchOk hn hn0 h.searchOk hlevelOne
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
    · rw [h.searchOk.labSize, ← hn]
    · rw [h.searchOk.ptnSize, ← hn]
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
theorem FirstInv.terminalReceipt {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
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
    simpa only [rs, full, leaf] using h.terminal hn hn0 hlevel
  have hdisc : discreteAt rs.ptn level ctx.n = true := by
    rw [← refine_discrete_iff hn hn0 h.searchOk (by omega)]
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
