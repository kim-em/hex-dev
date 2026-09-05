/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeLocated
public import HexGraphIso.Nauty.SearchOutcomeProof

public section

/-!
Operational composition lemmas for frame-aware search receipts.
-/

namespace Hex.GraphIso.Nauty

/-- Once both ends of a loop frame are recovered at the same level, the
`SearchOut` low-boundary contract identifies their partitions exactly.
The labelling may still differ by a within-cell permutation. -/
theorem SearchOut.ptnEq {G : Colored n k} {level numcells : Nat}
    {st out : SearchSt} (h : SearchOut G level level st out)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out) : out.ptn = st.ptn := by
  apply Array.ext h.ptnSize
  intro i hi hi'
  have hin : i < n := by rw [hout.ptnSize] at hi; exact hi
  have heq : out.ptn[i]! = st.ptn[i]! := by
    rcases hok.vals i hin with hold | hold
    · exact h.low i (Or.inl hold)
    · rcases hout.vals i hin with hnew | hnew
      · exact h.low i (Or.inr hnew)
      · rw [hold, hnew]
  simpa only [getElem!_pos out.ptn i hi, getElem!_pos st.ptn i hi']
    using heq

/-- A recovered loop state individualizes the same vertex as its frozen
entry frame, possibly at a different offset within the target cell.  The
two resulting child labellings remain cell-equivalent. -/
theorem SearchOut.breakoutPerm {G : Colored n k} {level numcells tc len o : Nat}
    {st out : SearchSt} (h : SearchOut G level level st out)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    ∃ oCur, oCur < len ∧ out.lab[tc + oCur]! = st.lab[tc + o]! ∧
      cellsPerm (st.ptn.set! tc (level + 1)) (level + 1)
        (breakout st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (breakout out.lab out.ptn (level + 1) tc st.lab[tc + o]!).1 := by
  have hend := searchOk_end hn0 hok hlevel
  have hmem : st.lab[tc + o]! ∈ segN st.lab tc len :=
    mem_segN_iff.mpr ⟨o, ho, rfl⟩
  have hmem' : st.lab[tc + o]! ∈ segN out.lab tc len :=
    (h.perm tc len hcell).mem_iff.mp hmem
  obtain ⟨oCur, hoCur, hat⟩ := mem_segN_iff.mp hmem'
  refine ⟨oCur, hoCur, hat, ?_⟩
  have hptn := h.ptnEq hok hout
  let σ : Renaming n := {
    toFun := id
    inj := fun _ _ heq => heq
    maps := fun _ => Iff.rfl }
  have hmap : out.lab.map σ.toFun = out.lab := by
    apply Array.ext (by simp)
    intro i hi hi'
    simp [σ]
  have hcp : cellsPerm st.ptn level st.lab (out.lab.map σ.toFun) := by
    rw [hmap]
    exact h.perm
  have hvals : ∀ q, q < n →
      st.ptn[q]! ≤ level ∨ level + 1 < st.ptn[q]! := by
    have hleveln : level ≤ n :=
      Nat.le_trans hok.bc (bcount_le st.ptn level n)
    intro q hq
    rcases hok.vals q hq with hq' | hq'
    · exact Or.inl hq'
    · exact Or.inr (by rw [hq']; omega)
  have hcell' : (tc, tc + len - 1) ∈ cells st.ptn level n :=
    isCell_mem_cells hcell (by rw [hok.ptnSize]; exact Nat.le_refl n)
      hend (by omega)
  have hb := breakout_cellsPerm_map (ctx := { n := n, g := #[] })
    (σ := σ) (labV := st.lab) (labU := out.lab) (ptn := st.ptn)
    (level := level) (tc := tc) (e := tc + len - 1)
    (oV := o) (oU := oCur) hok.ptnSize hok.labSize hout.labSize hend
    hvals hcp hcell' (by omega) (by omega) (by omega) (by
      dsimp only [σ, id]
      exact hat.symm)
  have map_id (a : Array Nat) : a.map σ.toFun = a := by
    apply Array.ext (by simp)
    intro i hi hi'
    simp [σ]
  rw [map_id, hat] at hb
  rw [hptn]
  exact hb

/-- Splitting a nonempty cell start keeps the final partition position
closed one level later. -/
theorem split_end {ptn : Array Nat} {level tc : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level) (htc : tc < ptn.size) :
    (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
  rw [Array.size_set!]
  rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
  · rw [Array.getElem!_set!_self _ _ _ (by omega)]
    omega
  · rw [Array.getElem!_set!_ne _ _ _ _ hx]
    omega

/-- The active singleton created by individualization is bounded by the
vertex universe. -/
theorem singleActive_lt {n tc : Nat} (htc : tc < n) :
    insert 0 tc < 2 ^ n := by
  rw [insert, Nat.zero_or, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.pow_lt_pow_right (by omega) htc

/-- The active singleton created by individualization marks a cell start
of the split partition. -/
theorem split_starts {ptn : Array Nat} {level tc len : Nat}
    (_hpsz : ptn.size = n) (hcell : IsCell ptn level tc len) :
    ∀ v : Nat, elem (insert 0 tc) v = true →
      v = 0 ∨ (ptn.set! tc (level + 1))[v - 1]! ≤ level + 1 := by
  intro v hv
  rw [elem_single] at hv
  have hvtc : v = tc := of_decide_eq_true hv
  subst v
  rcases Decidable.em (tc = 0) with h0 | h0
  · exact Or.inl h0
  · rcases hcell.2.1 with hstart | hstart
    · exact Or.inl hstart
    · right
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      omega

/-- Individualizing the same frozen vertex after a recovered within-cell
permutation produces the same specification child key. This is the bridge
from `SearchOut.breakoutPerm` to the exact key premise consumed by
`SweepCover.receipt`. -/
theorem SearchOut.breakoutKey {G : Colored n k} {ctx : Ctx}
    (hn : ctx.n = n) {level numcells tc len o specFuel tcLevel : Nat}
    {st out child : SearchSt}
    (h : SearchOut G level level st out)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len)
    (hclab : child.lab = (breakout out.lab out.ptn (level + 1) tc
      st.lab[tc + o]!).1)
    (hcptn : child.ptn = (breakout out.lab out.ptn (level + 1) tc
      st.lab[tc + o]!).2.1)
    (hcactive : child.active = (breakout out.lab out.ptn (level + 1) tc
      st.lab[tc + o]!).2.2)
    (hcanon : child.canonlab = out.canonlab)
    (hfuel : level + 1 + specFuel ≤ n + 1) :
    sweepKey ctx tcLevel specFuel level codes st.lab st.ptn tc numcells o =
      nodeKey ctx tcLevel specFuel (level + 1) codes child
        (numcells + 1) := by
  obtain ⟨oCur, hoCur, hat, hperm⟩ :=
    h.breakoutPerm hok hout hn0 hlevel hcell hlen hrange ho
  have hptn := h.ptnEq hok hout
  have hcellOut : IsCell out.ptn level tc len := by
    rw [hptn]
    exact hcell
  have hclab' : child.lab = (breakout out.lab out.ptn (level + 1) tc
      out.lab[tc + oCur]!).1 := by
    rw [hat]
    exact hclab
  have hcptn' : child.ptn = out.ptn.set! tc (level + 1) := by
    rw [hcptn, breakout_ptn]
  have hchildOk := breakout_searchOk (st' := child) hn0 hout hlevel
    hcellOut hlen hrange hoCur hclab' hcptn' hcanon
  let refChild : SearchSt :=
    { st with
      lab := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1
      ptn := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.1
      active := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.2 }
  have hrefOk : SearchOk G (level + 1) (numcells + 1) refChild := by
    apply breakout_searchOk hn0 hok hlevel hcell hlen hrange ho
    · rfl
    · exact breakout_ptn st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!
    · rfl
  change nodeKey ctx tcLevel specFuel (level + 1) codes refChild
      (numcells + 1) =
    nodeKey ctx tcLevel specFuel (level + 1) codes child
      (numcells + 1)
  apply nodeKey_perm hn tcLevel specFuel (level + 1) codes refChild child
    (numcells + 1)
  · change cellsPerm
      (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.1 (level + 1)
      (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1 child.lab
    rw [breakout_ptn, hclab]
    exact hperm
  · rw [hchildOk.labSize, hrefOk.labSize]
  · exact hrefOk.labSize
  · exact labOk_of_reach hrefOk.labSize hrefOk.reach
  · exact labOk_of_reach hchildOk.labSize hchildOk.reach
  · rw [hcptn', hptn]
    rfl
  · rw [hcactive]
    rfl
  · exact hrefOk.ptnSize
  · apply singleActive_lt
    omega
  · exact split_end (searchOk_end hn0 hok hlevel) (by
      rw [hok.ptnSize]
      omega)
  · exact split_starts hok.ptnSize hcell
  · intro q
    rcases Nat.lt_or_ge q n with hq | hq
    · exact hrefOk.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [hrefOk.ptnSize]; omega)]
      exact Nat.zero_le _
  · exact hfuel

/-- First-path exit bookkeeping preserves the location of a transported
generator unwind. -/
theorem Unwind.Located.firstFinish {ctx : Ctx}
    {tcLevel target level size index : Nat} {st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    {payload : Unwind ctx tcLevel target st best}
    (h : payload.Located trail) :
    (payload.firstFinish (level := level) (size := size)
      (index := index)).Located trail := by
  cases h with
  | first anchor carrier located =>
      exact Unwind.Located.first anchor (by
        rw [Nauty.firstFinish]
        split <;> exact carrier) located
  | canon anchor carrier located =>
      exact Unwind.Located.canon anchor (by
        rw [Nauty.firstFinish]
        split <;> exact carrier) located
  | orbit orbitPayload =>
      exact .orbit {
        positive := orbitPayload.positive
        bound := by
          unfold Nauty.firstFinish
          split <;> exact orbitPayload.bound
        currentLt := by
          unfold Nauty.firstFinish
          split <;> exact orbitPayload.currentLt
        smaller := by
          unfold Nauty.firstFinish
          split <;> exact orbitPayload.smaller
        sound := by
          unfold Nauty.firstFinish
          split <;> exact orbitPayload.sound }

/-- Every located node receipt crosses the first-path exit-counter
update. -/
theorem NodeReceipt.firstFinish {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs : List Nat} {st out : SearchSt} {best outBest : Option Key}
    {r : Int} (hfuel : runFuel ≠ 0)
    (h : NodeReceipt trail ctx tcLevel specFuel runFuel level cs st out
      numcells best outBest r) :
    NodeReceipt trail ctx tcLevel specFuel runFuel level cs st
      (Nauty.firstFinish level size index out) numcells best outBest r := by
  cases h with
  | complete sound returned installed read full =>
      exact .complete sound returned
        (by rw [canonlevel_firstFinish]; exact installed)
        ((stInc_firstFinish ctx level size index out).trans read) full
  | unwind sound target returned below payload located =>
      exact .unwind sound target returned below payload.firstFinish
        located.firstFinish
  | pruned sound target returned below installed read full =>
      exact .pruned sound target returned below
        (by rw [canonlevel_firstFinish]; exact installed)
        ((stInc_firstFinish ctx level size index out).trans read) full
  | exhausted empty returned unchanged bestUnchanged =>
      exact (hfuel empty).elim

set_option maxHeartbeats 800000 in
/-- A located child-loop receipt supplies the complete outcome of a
non-discrete first-path node. -/
theorem firstPath_internal_receipt (ctx : Ctx)
    (inf tcLevel specFuel fuel level numcells tail : Nat)
    (cs : List Nat) (st : SearchSt) (best outBest : Option Key)
    (trail : FrameTrail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ ctx.n)
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      let rs := refine ctx level st.lab st.ptn st.active numcells
      let mt := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
      keysMax
        (sweepKey ctx tcLevel specFuel level (cs ++ [rs.longcode])
          rs.lab rs.ptn mt.1 rs.numcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level (cs ++ [rs.longcode])
            rs.lab rs.ptn mt.1 rs.numcells (o + 1)))
    (hlen : (maketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn level
      tcLevel (-1)).2.2 = tail + 1) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let mt := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
    let pre0 : SearchSt := { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      firstcode := st.firstcode.set! level rs.longcode
      firsttc := st.firsttc.set! level (Int.ofNat mt.1)
      numnodes := st.numnodes + 1
      tctotal := st.tctotal + mt.2.2 }
    let pre := if pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level ctx.n then
      { pre0 with noncheaplevel := level + 1 }
    else pre0
    let L := firstChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
      rs.numcells mt.1 ((nextElem mt.2.1 none).getD 0)
      (nextElem mt.2.1 none) mt.2.1 0 pre
    LoopReceipt trail ctx tcLevel specFuel fuel (ctx.n + 1) level
      (cs ++ [rs.longcode]) rs.lab rs.ptn mt.1 mt.2.2 rs.numcells
      mt.2.1 none
      (nodeKey ctx tcLevel (specFuel + 1) level cs st numcells)
      pre L.2.2 best outBest L.1 →
    NodeReceipt trail ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  dsimp only
  intro hloop
  rw [firstPath_internal_state ctx inf tcLevel fuel level numcells st hnum]
  generalize hL : firstChildLoop ctx inf tcLevel fuel (ctx.n + 1)
      level _ _ _ _ _ _ _ = L at hloop ⊢
  rcases L with ⟨r, index, out⟩
  cases r with
  | none =>
      have hnode := NodeReceipt.ofLoopNone (ctx := ctx)
        (nodeRunFuel := fuel + 1) (cursor := none)
        (loopFuel := ctx.n + 1) rfl hchildren hlen
        (by simp only [cursorRank]; omega) hloop
      exact hnode.firstFinish (by omega)
  | some r =>
      exact NodeReceipt.ofLoopSome (ctx := ctx)
        (nodeRunFuel := fuel + 1) rfl hloop

/-- Once the imperative prefix exposes an off-path child loop, its
located receipt constructs the corresponding located node receipt. -/
theorem otherNode_receipt {ctx : Ctx}
    {inf tcLevel specFuel fuel level nodeNumcells loopNumcells tail : Nat}
    {nodeCs loopCs : List Nat} {nodeSt loopSt : SearchSt}
    {rsLab rsPtn : Array Nat} {tc len tcell : Nat}
    {best outBest : Option Key} {trail : FrameTrail}
    {L : Option Int × SearchSt}
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
          loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hlen : len = tail + 1)
    (hstate : otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells
        nodeSt =
      match L.1 with
      | some r => (r, L.2)
      | none => (Int.ofNat level - 1, L.2))
    (hloop : LoopReceipt trail ctx tcLevel specFuel fuel (ctx.n + 1) level
      loopCs rsLab rsPtn tc len loopNumcells tcell none
      (nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells)
      loopSt L.2 best outBest L.1) :
    NodeReceipt trail ctx tcLevel (specFuel + 1) (fuel + 1) level nodeCs
      nodeSt (otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells
        nodeSt).2
      nodeNumcells best outBest
      (otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells nodeSt).1 := by
  rw [hstate]
  rcases L with ⟨r, out⟩
  cases r with
  | none =>
      exact NodeReceipt.ofLoopNone (ctx := ctx)
        (nodeRunFuel := fuel + 1) (cursor := none)
        (loopFuel := ctx.n + 1) rfl hchildren hlen
        (by simp only [cursorRank]; omega) hloop
  | some r =>
      exact NodeReceipt.ofLoopSome (ctx := ctx)
        (nodeRunFuel := fuel + 1) rfl hloop

/-- An off-path child generator unwind strictly past this loop returns
with its frame location intact after fixed-vertex cleanup. -/
theorem otherLoop_childReceipt (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (best outBest : Option Key) (target : Nat) (trail : FrameTrail)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }
      (numcells + 1)) bound)
    (hreturn : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }).1 = Int.ofNat target)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := insert st.fixedpts tv }).2 outBest)
    (hloc : payload.Located trail) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hreturn]
  split
  · exact LoopReceipt.ofChildUnwind hsound hkey hbelow payload hloc
  · rename_i hnot
    exact (hnot (Int.ofNat_lt.mpr hbelow)).elim

/-- First-path loop fuel exhaustion is retained as a distinct located
receipt. -/
theorem firstLoop_zeroReceipt (ctx : Ctx)
    (inf tcLevel specFuel runFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tv? cursor : Option Nat) (tcell index : Nat) (bound : Key)
    (st : SearchSt) (best : Option Key) (trail : FrameTrail)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hcursor : ∀ v, cursor = some v → v < ctx.n) :
    LoopReceipt trail ctx tcLevel specFuel runFuel 0 level cs rsLab rsPtn
      tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).2.2
      best best
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).1 := by
  unfold firstChildLoop
  exact .exhausted rfl (.refl ctx bound best) tcell cursor hcover
    (by omega) hcursor

/-- Off-path loop fuel exhaustion is retained as a distinct located
receipt. -/
theorem otherLoop_zeroReceipt (ctx : Ctx)
    (inf tcLevel specFuel runFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tv? cursor : Option Nat) (tcell : Nat) (bound : Key) (st : SearchSt)
    (best : Option Key) (trail : FrameTrail)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hcursor : ∀ v, cursor = some v → v < ctx.n) :
    LoopReceipt trail ctx tcLevel specFuel runFuel 0 level cs rsLab rsPtn
      tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).2
      best best
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).1 := by
  unfold otherChildLoop
  exact .exhausted rfl (.refl ctx bound best) tcell cursor hcover
    (by omega) hcursor

/-- An absent next child completes a positive-fuel first-path loop. -/
theorem firstLoop_doneReceipt (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tcell index : Nat) (cursor : Option Nat) (bound : Key)
    (st : SearchSt) (best : Option Key) (trail : FrameTrail)
    (hinstalled : st.canonlevel ≠ 0) (hread : stInc ctx st = best)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = none) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).2.2
      best best
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).1 := by
  unfold firstChildLoop
  exact .complete rfl (.refl ctx bound best) hinstalled hread tcell cursor
    hcover fun o ho => no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- An absent next child completes a positive-fuel off-path loop. -/
theorem otherLoop_doneReceipt (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (best : Option Key) (trail : FrameTrail)
    (hinstalled : st.canonlevel ≠ 0) (hread : stInc ctx st = best)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = none) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).2
      best best
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).1 := by
  unfold otherChildLoop
  exact .complete rfl (.refl ctx bound best) hinstalled hread tcell cursor
    hcover fun o ho => no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- A non-root orbit pointer skips the current first-path child while
retaining located outcomes from the recursive tail. -/
theorem firstLoop_orbitReceipt (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell index o : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (best : Option Key) (trail : FrameTrail)
    (gens : List (Array Nat))
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = some tv) (ho : o < len)
    (htv : rsLab[tc + o]! = tv)
    (hgsz : ctx.g.size = ctx.n)
    (hbg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ ctx.n = true)
    (hstab : ∀ γ ∈ gens, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = ctx.n) (hinj : LabInj rsLab rsLab.size)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1)
    (hsound : OrbSound (OrbConn gens ctx.n) st.orbits ctx.n)
    (horbit : (st.orbits[tv]! == tv) = false)
    (hrec : ∀ index',
      SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
        tcell (some tv) best →
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells tcell (some tv) bound st
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell index' st).2.2
        best best
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell index' st).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best best
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  have hne : st.orbits[tv]! ≠ tv := by
    simpa only [beq_eq_false_iff_ne] using horbit
  have hcover' := hcover.orbitSkip hnext ho htv hgsz hbg hv hstab hs hinj
    hok hsp hend hvals hic hrange hlf hsound hne
  unfold firstChildLoop
  simp only [horbit, Bool.false_eq_true, ite_false, Id.run_pure,
    apply_ite Id.run]
  rcases hidx : (st.orbits[tv]! == tv1) with _ | _ <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    exact (hrec _ hcover').step (nextElem_after hnext)

/-- An off-path child of the first-path loop transports a located unwind
strictly past the loop. -/
theorem firstLoop_otherReceipt (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell index : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (best outBest : Option Key) (target : Nat) (trail : FrameTrail)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hother : (tv == tv1) = false)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      (numcells + 1)) bound)
    (hreturn : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }).1 = Int.ofNat target)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := insert st.fixedpts tv
          cosetindex := tv }).2 outBest)
    (hloc : payload.Located trail) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  unfold firstChildLoop
  simp only [hrep, ite_true, hother, Bool.false_eq_true, ite_false,
    Id.run_pure, apply_ite Id.run]
  rw [hreturn]
  split
  · exact LoopReceipt.ofChildUnwind hsound hkey hbelow payload hloc
  · rename_i hnot
    exact (hnot (Int.ofNat_lt.mpr hbelow)).elim

/-- The guiding child transports a located unwind strictly past the loop
after installing its first-path return controls. -/
theorem firstLoop_guideReceipt (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell index : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (best outBest : Option Key) (target : Nat) (trail : FrameTrail)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hfirst : (tv == tv1) = true)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      (numcells + 1)) bound)
    (hreturn : (firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }).1 = Int.ofNat target)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target
      (firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := insert st.fixedpts tv
          cosetindex := tv }).2 outBest)
    (hloc : payload.Located trail) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  obtain ⟨payload', hloc'⟩ :=
    hloc.setFirst level tv1 (Nat.le_of_lt hbelow)
  unfold firstChildLoop
  simp only [hrep, ite_true, hfirst, Id.run_pure, apply_ite Id.run]
  rw [hreturn]
  split
  · exact LoopReceipt.ofChildUnwind hsound hkey hbelow payload' hloc'
  · rename_i hnot
    exact (hnot (Int.ofNat_lt.mpr hbelow)).elim

/-- After an ordinary child completes without either filter, an off-path
loop continues while retaining every located recursive outcome. -/
theorem otherLoop_nextReceipt (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (best mid outBest : Option Key) (r : Int) (trail : FrameTrail)
    (hnext : nextElem tcell cursor = some tv)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }
      (numcells + 1) best mid)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }
      (numcells + 1)) bound)
    (hreturn : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }).1 = r)
    (hstay : ¬ r < Int.ofNat level)
    (hshort : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }).2.needshortprune = false)
    (hother : (tv == tv1) = false)
    (hrec : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level
      cs rsLab rsPtn tc len numcells tcell (some tv) bound
      (recover ctx.n inf level
        { (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
          { st with
            lab := (breakout st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := insert st.fixedpts tv }).2 with
          fixedpts := erase (otherNode ctx inf tcLevel runFuel (level + 1)
            (numcells + 1)
            { st with
              lab := (breakout st.lab st.ptn (level + 1) tc tv).1
              ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
              active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
              fixedpts := insert st.fixedpts tv }).2.fixedpts tv })
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem tcell (some tv)) tcell
        (recover ctx.n inf level
          { (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
            { st with
              lab := (breakout st.lab st.ptn (level + 1) tc tv).1
              ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
              active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
              fixedpts := insert st.fixedpts tv }).2 with
            fixedpts := erase (otherNode ctx inf tcLevel runFuel (level + 1)
              (numcells + 1)
              { st with
                lab := (breakout st.lab st.ptn (level + 1) tc tv).1
                ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
                active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
                fixedpts := insert st.fixedpts tv }).2.fixedpts tv })).2
      mid outBest
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem tcell (some tv)) tcell
        (recover ctx.n inf level
          { (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
            { st with
              lab := (breakout st.lab st.ptn (level + 1) tc tv).1
              ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
              active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
              fixedpts := insert st.fixedpts tv }).2 with
            fixedpts := erase (otherNode ctx inf tcLevel runFuel (level + 1)
              (numcells + 1)
              { st with
                lab := (breakout st.lab st.ptn (level + 1) tc tv).1
                ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
                active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
                fixedpts := insert st.fixedpts tv }).2.fixedpts tv })).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hreturn, ite_eq_right hstay]
  split
  · rename_i hyes
    rw [hshort] at hyes
    cases hyes
  · simp only [hother, Bool.false_eq_true, ite_false]
    exact (hrec.prefix (st := st) (LoopSound.ofNode hsound hkey)).step
      (nextElem_after hnext)

/-- After an ordinary non-guiding child completes without requesting a
short prune, the first-path loop recovers its parent frame and continues.
The child call is exposed as one equation so the mutual induction need not
duplicate its output expression in every premise. -/
theorem firstLoop_otherNext (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell index : Nat)
    (cursor : Option Nat) (bound : Key) (st child recSt : SearchSt)
    (best mid outBest : Option Key) (r : Int) (trail : FrameTrail)
    (hnext : nextElem tcell cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = false)
    (hrecover : recSt = recover ctx.n inf level
      { child with fixedpts := erase child.fixedpts tv })
    (hpre : LoopSound ctx bound best mid)
    (hrec : ∀ index',
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells tcell (some tv) bound recSt
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell index' recSt).2.2
        mid outBest
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell index' recSt).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  subst recSt
  simp only [hshort] at hrec
  unfold firstChildLoop
  simp only [hrep, ite_true, hother, Bool.false_eq_true, ite_false,
    Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, Bool.false_eq_true, ite_false]
  split <;>
    exact ((hrec _).prefix hpre).step (nextElem_after hnext)

/-- After the guiding child completes without requesting a short prune,
the first-path loop installs its return controls, recovers the parent
frame, and continues with every recursive location intact. -/
theorem firstLoop_guideNext (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell index : Nat)
    (cursor : Option Nat) (bound : Key) (st child recSt : SearchSt)
    (best mid outBest : Option Key) (r : Int) (trail : FrameTrail)
    (hnext : nextElem tcell cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = false)
    (hrecover : recSt = recover ctx.n inf level
      { child with
        fixedpts := erase child.fixedpts tv
        gcaFirst := level
        stabvertex := tv1 })
    (hpre : LoopSound ctx bound best mid)
    (hrec : ∀ index',
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells tcell (some tv) bound recSt
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell index' recSt).2.2
        mid outBest
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell index' recSt).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  subst recSt
  simp only [hshort] at hrec
  unfold firstChildLoop
  simp only [hrep, ite_true, hfirst, Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, Bool.false_eq_true, ite_false]
  split <;>
    exact ((hrec _).prefix hpre).step (nextElem_after hnext)

/-- When the guiding child of an off-path loop completes without a short
prune, the long-pruned recursive sweep reindexes to the loop's original
entry set while retaining located outcomes. -/
theorem otherLoop_longNext (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell filtered : Nat)
    (cursor : Option Nat) (bound : Key) (st child recSt : SearchSt)
    (best mid outBest : Option Key) (r : Int) (trail : FrameTrail)
    (hnext : nextElem tcell cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = false)
    (hfirst : (tv == tv1) = true)
    (hfiltered : filtered = longprune tcell
      (erase child.fixedpts tv) child.autos)
    (hrecover : recSt = recover ctx.n inf level
      { child with fixedpts := erase child.fixedpts tv })
    (hpre : LoopSound ctx bound best mid)
    (hrec : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level
      cs rsLab rsPtn tc len numcells filtered (some tv) bound recSt
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem filtered (some tv)) filtered recSt).2
      mid outBest
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem filtered (some tv)) filtered recSt).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  subst filtered
  subst recSt
  simp only [hshort] at hrec
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, Bool.false_eq_true, ite_false, hfirst, ite_true]
  exact ((hrec.prefix hpre).reindexSet).step (nextElem_after hnext)

/-- A short-pruned off-path sweep whose current child is not the guiding
vertex reindexes its recursive receipt to the original entry set. -/
theorem otherLoop_shortNext (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell filtered : Nat)
    (cursor : Option Nat) (bound : Key) (st child recSt : SearchSt)
    (best mid outBest : Option Key) (r : Int) (trail : FrameTrail)
    (hnext : nextElem tcell cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = true)
    (hother : (tv == tv1) = false)
    (hfiltered : filtered = shortprune tcell
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hrecover : recSt = recover ctx.n inf level
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hpre : LoopSound ctx bound best mid)
    (hrec : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level
      cs rsLab rsPtn tc len numcells filtered (some tv) bound recSt
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem filtered (some tv)) filtered recSt).2
      mid outBest
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem filtered (some tv)) filtered recSt).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  subst filtered
  subst recSt
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, ite_true, hother, Bool.false_eq_true, ite_false]
  exact ((hrec.prefix hpre).reindexSet).step (nextElem_after hnext)

/-- When both executable filters fire, their composed target set still
reindexes to the original off-path loop entry while locations are retained.
-/
theorem otherLoop_bothNext (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat)
    (len tcell shortSet filtered : Nat)
    (cursor : Option Nat) (bound : Key) (st child recSt : SearchSt)
    (best mid outBest : Option Key) (r : Int) (trail : FrameTrail)
    (hnext : nextElem tcell cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = true)
    (hfirst : (tv == tv1) = true)
    (hshortSet : shortSet = shortprune tcell
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hfiltered : filtered = longprune shortSet
      (erase child.fixedpts tv) child.autos)
    (hrecover : recSt = recover ctx.n inf level
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hpre : LoopSound ctx bound best mid)
    (hrec : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level
      cs rsLab rsPtn tc len numcells filtered (some tv) bound recSt
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem filtered (some tv)) filtered recSt).2
      mid outBest
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem filtered (some tv)) filtered recSt).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  subst filtered
  subst shortSet
  subst recSt
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, hfirst, ite_true]
  exact ((hrec.prefix hpre).reindexSet).step (nextElem_after hnext)

/-- A short-pruned non-guiding first-path child reindexes the recursive
sweep to the original loop entry while retaining located outcomes. -/
theorem firstLoop_otherShort (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat)
    (len tcell filtered index : Nat)
    (cursor : Option Nat) (bound : Key) (st child recSt : SearchSt)
    (best mid outBest : Option Key) (r : Int) (trail : FrameTrail)
    (hnext : nextElem tcell cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = true)
    (hfiltered : filtered = shortprune tcell
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hrecover : recSt = recover ctx.n inf level
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hpre : LoopSound ctx bound best mid)
    (hrec : ∀ index',
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells filtered (some tv) bound recSt
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem filtered (some tv)) filtered index' recSt).2.2
        mid outBest
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem filtered (some tv)) filtered index' recSt).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  subst filtered
  subst recSt
  unfold firstChildLoop
  simp only [hrep, ite_true, hother, Bool.false_eq_true, ite_false,
    Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, ite_true]
  split <;>
    exact (((hrec _).prefix hpre).reindexSet).step (nextElem_after hnext)

/-- A short-pruned guiding first-path child installs the guide controls
before reindexing the recursive sweep to its original entry set. -/
theorem firstLoop_guideShort (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat)
    (len tcell filtered index : Nat)
    (cursor : Option Nat) (bound : Key) (st child recSt : SearchSt)
    (best mid outBest : Option Key) (r : Int) (trail : FrameTrail)
    (hnext : nextElem tcell cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = true)
    (hfiltered : filtered = shortprune tcell
      { child with
        fixedpts := erase child.fixedpts tv
        gcaFirst := level
        stabvertex := tv1
        needshortprune := false })
    (hrecover : recSt = recover ctx.n inf level
      { child with
        fixedpts := erase child.fixedpts tv
        gcaFirst := level
        stabvertex := tv1
        needshortprune := false })
    (hpre : LoopSound ctx bound best mid)
    (hrec : ∀ index',
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells filtered (some tv) bound recSt
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem filtered (some tv)) filtered index' recSt).2.2
        mid outBest
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem filtered (some tv)) filtered index' recSt).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  subst filtered
  subst recSt
  unfold firstChildLoop
  simp only [hrep, ite_true, hfirst, Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, ite_true]
  split <;>
    exact (((hrec _).prefix hpre).reindexSet).step (nextElem_after hnext)

end Hex.GraphIso.Nauty
