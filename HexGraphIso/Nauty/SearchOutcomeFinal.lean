/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeMutual
import all HexGraphIso.Nauty.Search

public section

/-!
The final corrected mutual induction for the transcribed search.

The semantic outcomes distinguish completed subtrees, located unwinds,
comparison prunes, and exhausted runtime fuel.  This file couples those
outcomes to the one extra executable frame fact needed by the induction:
every recursive node call restores the fixed-point bitset with which it
was entered.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- At a loop boundary, an implicit small-cell pair is available even
when `noncheaplevel` is exactly the loop level.  `CheapOk` deliberately
omits this equality case at general node entries; the loop guards restore
it before beginning a sibling sweep. -/
@[expose] def BoundaryOk (G : Colored n k) (ctx : Ctx)
    (level : Nat) (st : SearchSt) : Prop :=
  st.noncheaplevel = level →
    PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (fmptn st.lab st.ptn level ctx.n).1
      (fmptn st.lab st.ptn level ctx.n).2

namespace BoundaryOk

/-- Parking strictly past a loop makes its equality obligation vacuous. -/
theorem parked {G : Colored n k} {ctx : Ctx} {level : Nat}
    {st : SearchSt} :
    BoundaryOk G ctx level { st with noncheaplevel := level + 1 } := by
  intro heq
  simp only at heq
  omega

/-- A successful cheap-cell test supplies the implicit pair required at
the loop boundary. -/
theorem ofCheap {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hcheap : cheapautom st.ptn level ctx.n = true) :
    BoundaryOk G ctx level st := by
  have hn := hinv.nodeCount
  subst n
  intro hboundary
  let r : RefineSt :=
    { lab := st.lab, ptn := st.ptn, active := 0, numcells := numcells,
      hint := 0, maxpos := 0, longcode := numcells }
  have hlab : LabOk st.lab ctx.n :=
    labOk_of_reach hinv.run.searchOk.labSize hinv.run.searchOk.reach
  have hinj : LabInj st.lab ctx.n :=
    labInj_of_reach hinv.run.searchOk.labSize hinv.nonempty
      hinv.run.searchOk.reach
  have hend := searchOk_end hinv.nonempty hinv.run.searchOk hinv.positive
  have hit : IterOk ctx level r := by
    constructor
    · exact ⟨hinv.run.searchOk.labSize, hlab,
        hinv.run.searchOk.ptnSize, Nat.two_pow_pos ctx.n, hend⟩
    · exact hinj
    · intro q hq
      exact hinv.run.searchOk.vals q hq
    · exact Nat.le_trans hinv.run.searchOk.bc
        (bcount_le st.ptn level ctx.n)
  have heq : Equitable ctx level r.lab r.ptn := by
    simpa only [r] using hinv.currentEquitable
  have hcount : bcount r.ptn level ctx.n = r.numcells := by
    simpa only [r] using hinv.run.searchOk.count.symm
  have hsub : SubtreeOk ctx level r :=
    subtreeOk_of_cheapautom hit heq hcount (by simpa only [r] using hcheap)
  have hpair : PairOk ctx.g
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (fmptn r.lab r.ptn level ctx.n).1
      (fmptn r.lab r.ptn level ctx.n).2 := by
    apply pairOk_fmptn_of_subtree (ctx := ctx) (G := G)
      (r := r) hinv.nonempty hinv.positive
    · rw [hg]
      exact size_rowsOf G
    · rw [hg]
      exact rowsOf_bounded G
    · rw [hg]
      exact rowsOf_symm G
    · rw [hg]
      exact rowsOf_loopless G
    · exact hsub
    · exact hinv.run.searchOk.reach
    · exact hinv.run.searchOk.init1
  simpa only [r, hboundary] using hpair

/-- The boundary pair advances the strict `CheapOk` ledger through the
next child level. -/
theorem nextCheap {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (h : BoundaryOk G ctx level st)
    (hrun : RunInv G ctx tcLevel level codes bs fs numcells st best trail) :
    CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) (level + 1) st := by
  apply hrun.cheap.next
  intro heq
  simpa only [heq] using h heq

end BoundaryOk

namespace EventOut

/-- Recovering a child event to its parent supplies the equality-boundary
pair needed by the next sibling, even though ordinary `CheapOk` makes
that equality case dormant. -/
theorem recoverBoundary {G : Colored n k} {ctx : Ctx}
    {tcLevel level inf fixedpts : Nat} {stem fs : List Nat}
    {out : SearchSt} {best : Option Key} {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (hstem : stem.length = level) (hlevel : 1 ≤ level)
    (hinf : level < inf) :
    BoundaryOk G ctx level
      (Nauty.recover ctx.n inf level { out with fixedpts := fixedpts }) := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
    intro hboundary
    let cleaned : SearchSt := { out with fixedpts := fixedpts }
    have hevent : RunEvent G ctx tcLevel current codes bestCodes fs cleaned
        best trail := event.setFixed fixedpts
    have hcurrent : level < current := by
      rw [← hstem]
      exact past
    have hncl : (Nauty.recover ctx.n inf level cleaned).noncheaplevel =
        if level < cleaned.noncheaplevel then level + 1
        else cleaned.noncheaplevel := by
      unfold _root_.Hex.GraphIso.Nauty.recover
      simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
        apply_ite SearchSt.noncheaplevel, ite_self]
    have hsaved : cleaned.noncheaplevel = level := by
      rw [hncl] at hboundary
      rcases Decidable.em (level < cleaned.noncheaplevel) with hc | hc
      · rw [ite_eq_left hc] at hboundary
        omega
      · rw [ite_eq_right hc] at hboundary
        exact hboundary
    have hpair := hevent.cheap.pair (by omega)
    rw [hsaved] at hpair
    have hfm := recover_fmptn (st := cleaned)
      (n := ctx.n) (inf := inf) (level := level) (saved := level)
      (Nat.le_of_eq hevent.cheap.ptnSize.symm)
      (Nat.le_trans hevent.cheap.rootEnd hlevel)
      (Nat.le_refl level) hinf
    change PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (fmptn (Nauty.recover ctx.n inf level cleaned).lab
        (Nauty.recover ctx.n inf level cleaned).ptn level ctx.n).1
      (fmptn (Nauty.recover ctx.n inf level cleaned).lab
        (Nauty.recover ctx.n inf level cleaned).ptn level ctx.n).2
    rw [hfm]
    exact hpair

end EventOut

/-! # Fixed-point equations for node prefixes -/

theorem firstLeafSt_fixedpts (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (firstLeafSt ctx level numcells st).fixedpts = st.fixedpts := by
  rfl

theorem otherLeafSt_fixedpts (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (otherLeafSt ctx level numcells st).fixedpts = st.fixedpts := by
  unfold otherLeafSt
  exact otherNodePrep_fixedpts _ _ _

theorem leafFinish_fixedpts (ctx : Ctx) (level : Nat) (st : SearchSt) :
    (leafFinish ctx level st).fixedpts = st.fixedpts := by
  rw [leafFinish]
  split <;> split <;> rfl

/-- Clearing a freshly inserted bit restores the original set. -/
theorem erase_insert_of_miss {s v : Nat} (h : elem s v = false) :
    erase (insert s v) v = s := by
  apply Nat.eq_of_testBit_eq
  intro u
  rw [testBit_erase, testBit_insert]
  rcases Decidable.em (v = u) with rfl | hne
  · simp only [beq_self_eq_true, Bool.not_true, Bool.or_true,
      Bool.and_false]
    exact h.symm
  · have hb : (v == u) = false := by simp [hne]
    rw [hb]
    simp

/-- The discrete first-path arm restores its entry fixed-point set. -/
theorem firstPath_discrete_fixedpts (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2.fixedpts =
      st.fixedpts := by
  rw [firstPath_discrete_state ctx inf tcLevel fuel level numcells st hnum]
  exact (firstterminal_fixedpts level _).trans
    (firstLeafSt_fixedpts ctx level numcells st)

/-- Every early off-path leaf return restores its entry fixed-point set. -/
theorem otherNode_leaf_early_fixedpts (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hearly : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level) :
    (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2.fixedpts =
      st.fixedpts := by
  rw [otherNode_leaf_early ctx inf tcLevel fuel level numcells st hnum
    hearly]
  exact (processnode_fixedpts ctx level ctx.n _).trans
    (otherLeafSt_fixedpts ctx level numcells st)

/-- Every completed off-path leaf restores its entry fixed-point set. -/
theorem otherNode_leaf_done_fixedpts (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdone : ¬((processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)) :
    (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2.fixedpts =
      st.fixedpts := by
  rw [otherNode_leaf_done_state ctx inf tcLevel fuel level numcells st
    hnum hdone]
  exact (leafFinish_fixedpts ctx level _).trans
    ((processnode_fixedpts ctx level ctx.n _).trans
      (otherLeafSt_fixedpts ctx level numcells st))

/-- A semantic node outcome together with restoration of its entry
fixed-point set. -/
structure NodeProof (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  outcome : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
    numcells best outBest receiptTrail eventTrail r
  fixed : out.fixedpts = st.fixedpts

/-- The stronger off-path result retains the guide facts required by an
ordinary sibling loop. -/
structure OtherProof (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  outcome : OtherOutcome G ctx tcLevel specFuel runFuel level cs fs st out
    numcells best outBest receiptTrail eventTrail r
  fixed : out.fixedpts = st.fixedpts

/-- A semantic loop outcome together with restoration of the loop entry's
fixed-point set. -/
structure LoopProof (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells tcell : Nat) (cursor : Option Nat) (bound : Key)
    (st out : SearchSt) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  outcome : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
    codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
    outBest receiptTrail eventTrail r
  fixed : out.fixedpts = st.fixedpts

/-- The first leaf remembers every child selected on the unique initial
descent.  Unlike `RefTrail.first`, this history is deliberately independent
of the mutable `gcaFirst` return control: outer first-path loops reset that
control while the leaf remains a descendant of all their frozen frames. -/
structure FirstTrail (ctx : Ctx) (current : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop where
  reach : ∀ target entry, target < current →
    trail target = some entry →
    cellsPerm entry.frame.rsPtn target entry.frame.rsLab st.firstlab
  picked : ∀ target entry, target < current →
    trail target = some entry →
    ∃ len, IsCell entry.frame.rsPtn target entry.frame.tc len ∧
      entry.offset < len ∧
      st.firstlab[entry.frame.tc]! =
        entry.frame.rsLab[entry.frame.tc + entry.offset]!

/-- A first-path node proof additionally retains the unconditional history
of the first leaf through every active ancestor frame. -/
structure FirstProof (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  node : NodeProof G ctx tcLevel specFuel runFuel level cs fs st out
    numcells none outBest receiptTrail eventTrail r
  trail : FirstTrail ctx level out eventTrail

/-- A first-path loop keeps the current frozen frame in the first leaf's
history until the loop is converted back to its parent node result. -/
structure FirstLoopProof (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells tcell : Nat) (cursor : Option Nat) (bound : Key)
    (st out : SearchSt) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  loop : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
    fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail eventTrail r
  trail : FirstTrail ctx (level + 1) out eventTrail

namespace FirstTrail

/-- Reindex first-leaf history along an output trail extension and a state
update that leaves the stored first leaf unchanged. -/
theorem retrail {ctx : Ctx} {current : Nat} {st out : SearchSt}
    {source dest : FrameTrail}
    (h : FirstTrail ctx current st source)
    (hfirst : out.firstlab = st.firstlab)
    (hext : TrailExt current source dest) :
    FirstTrail ctx current out dest := by
  constructor
  · intro target entry htarget hentry
    rw [hext target htarget] at hentry
    rw [hfirst]
    exact h.reach target entry htarget hentry
  · intro target entry htarget hentry
    rw [hext target htarget] at hentry
    obtain ⟨len, hcell, hoff, hat⟩ :=
      h.picked target entry htarget hentry
    exact ⟨len, hcell, hoff, by simpa only [hfirst] using hat⟩

/-- Forgetting the newest active frame gives the history expected by its
parent node. -/
theorem lower {ctx : Ctx} {current : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : FirstTrail ctx (current + 1) st trail) :
    FirstTrail ctx current st trail := by
  constructor
  · intro target entry htarget hentry
    exact h.reach target entry (by omega) hentry
  · intro target entry htarget hentry
    exact h.picked target entry (by omega) hentry

end FirstTrail

/-- First-path sweep cleanup changes only `allsamelevel`. -/
theorem firstFinish_firstlab (level size index : Nat) (st : SearchSt) :
    (firstFinish level size index st).firstlab = st.firstlab := by
  rw [firstFinish]
  split <;> rfl

/-- A completed child, cleanup, and recovery restore both parent path
facts.  The selected vertex is fresh because it lies in a non-singleton
target cell while all older fixed vertices occupy singleton cells. -/
theorem LoopInv.recoverPath {G : Colored n k} {ctx : Ctx}
    {rootPtn rootLab rsLab rsPtn : Array Nat}
    {tcLevel specFuel level numcells tc len tcell currentOffset inf : Nat}
    {codes bs fs : List Nat} {cursor : Option Nat}
    {base st out : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx rootPtn rootLab level st)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
      out)
    (hfixed : out.fixedpts =
      insert st.fixedpts st.lab[tc + currentOffset]!)
    (hinf : inf = n + 2) (hcurrent : currentOffset < len) :
    let cleaned : SearchSt :=
      { out with
        fixedpts := erase out.fixedpts st.lab[tc + currentOffset]! }
    let recovered := Nauty.recover ctx.n inf level cleaned
    PathOk ctx rootPtn rootLab level recovered ∧
      recovered.fixedpts = st.fixedpts := by
  dsimp only
  let cleaned : SearchSt :=
    { out with
      fixedpts := erase out.fixedpts st.lab[tc + currentOffset]! }
  let recovered := Nauty.recover ctx.n inf level cleaned
  have hn := hinv.nodeCount
  subst n
  have hok := hinv.run.searchOk
  have hlab : LabOk st.lab ctx.n :=
    labOk_of_reach hok.labSize hok.reach
  have hinj : LabInj st.lab ctx.n :=
    labInj_of_reach hok.labSize hinv.nonempty hok.reach
  have hfresh : elem st.fixedpts st.lab[tc + currentOffset]! = false :=
    hpath.fixed.fresh hlab hinj hok.labSize hinv.currentCell
      hinv.lenTwo hinv.range hcurrent
  have hcleaned : cleaned.fixedpts = st.fixedpts := by
    change erase out.fixedpts st.lab[tc + currentOffset]! = st.fixedpts
    rw [hfixed, erase_insert_of_miss hfresh]
  have hparent : SearchOut G level level st out := by
    apply breakout_child_out hinv.nonempty hok hinv.positive
      hinv.currentCell hinv.lenTwo hinv.range hcurrent hout
    · rfl
    · exact breakout_ptn st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!
    · rfl
    · rfl
  have hclean : SearchOut G level level st cleaned :=
    hparent.congr rfl rfl rfl rfl
  have hrec := hclean.recoverOk rfl hinf hinv.positive hok
  have hrecovered : recovered.fixedpts = st.fixedpts := by
    exact (recover_fixedpts ctx.n inf level cleaned).trans hcleaned
  exact ⟨hpath.ofSearchOut rfl hinv.nonempty hinv.positive hrecovered
    hok hrec.2 hrec.1, hrecovered⟩

namespace NodeProof

theorem firstFinish {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs fs : List Nat} {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : NodeProof G ctx tcLevel specFuel runFuel level cs fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeProof G ctx tcLevel specFuel runFuel level cs fs st
      (Nauty.firstFinish level size index out) numcells best outBest
      receiptTrail eventTrail r :=
  ⟨h.outcome.firstFinish hfuel,
    (firstFinish_fixedpts level size index out).trans h.fixed⟩

end NodeProof

namespace PathOk

/-- Reindex path facts across a state update that changes none of the
fields they mention. -/
theorem stateEq {ctx : Ctx} {rootPtn rootLab : Array Nat}
    {level : Nat} {st out : SearchSt}
    (h : PathOk ctx rootPtn rootLab level st)
    (hlab : out.lab = st.lab) (hptn : out.ptn = st.ptn)
    (hfixed : out.fixedpts = st.fixedpts) :
    PathOk ctx rootPtn rootLab level out := by
  constructor
  · intro v hv hm
    rw [hfixed] at hm
    obtain ⟨q, hq, hqv, hc⟩ := h.fixed v hv hm
    exact ⟨q, hq, by simpa only [hlab] using hqv,
      by simpa only [hptn] using hc⟩
  · intro gamma hcheck hroot hfix
    rw [hfixed] at hfix
    simpa only [hlab, hptn] using h.stab gamma hcheck hroot hfix

/-- Individualization extends path facts from any well-formed equitable
parent frame.  This is the pre-incumbent analogue of `PathOk.breakout`,
which obtains the same premises from a `LoopInv`. -/
theorem individualize {ctx : Ctx} {rootPtn rootLab : Array Nat}
    {level tc len o : Nat} {st : SearchSt}
    (h : PathOk ctx rootPtn rootLab level st)
    (hinj : LabInj st.lab ctx.n) (hlab : LabOk st.lab ctx.n)
    (hsize : st.lab.size = ctx.n) (hpsize : st.ptn.size = ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ ctx.n) (ho : o < len)
    (hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1) :
    PathOk ctx rootPtn rootLab (level + 1)
      { st with
        lab := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + o]! } := by
  constructor
  · exact h.fixed.breakout hinj hsize hpsize hcell hlen hrange ho
  · exact h.stab.breakout hcell (by rw [hpsize]; exact hrange)
      (hsize.trans hpsize.symm) hlab ho hlen hend hvals

end PathOk

namespace FirstInv

/-- A discrete first-path leaf supplies the coupled node result and
restores the fixed-point frame with which the node was entered. -/
theorem terminalProof {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [rs.longcode]
    let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
    NodeProof G ctx tcLevel (specFuel + 1) (fuel + 1) level cs full st
      out.2 numcells none (some (pathLeafKey ctx full rs.lab)) trail trail
      out.1 := by
  dsimp only
  exact ⟨h.terminalOutcome hn hn0 hlevel hnum,
    firstPath_discrete_fixedpts ctx inf tcLevel fuel level numcells st hnum⟩

/-- The first leaf also turns the accumulated active descent into an
unconditional history of the selected child at every ancestor frame. -/
theorem terminalFirstProof {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [rs.longcode]
    let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
    FirstProof G ctx tcLevel (specFuel + 1) (fuel + 1) level cs full st
      out.2 numcells (some (pathLeafKey ctx full rs.lab)) trail trail
      out.1 := by
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
  constructor
  · exact h.terminalProof hn hn0 hlevel hnum
  · rw [hstate]
    constructor
    · intro target entry htarget hentry
      rw [firstterminal_firstlab]
      exact hrun.trailOk.reach target entry htarget hentry
    · intro target entry htarget hentry
      obtain ⟨len, hcell, hoff, -, -, hat⟩ :=
        hrun.trailOk.picked target entry htarget hentry
      refine ⟨len, hcell, hoff, ?_⟩
      rw [firstterminal_firstlab]
      exact hat

/-- The executable first-child prefix preserves and extends the root path
facts before the first incumbent exists. -/
theorem childPath {G : Colored n k} {ctx : Ctx}
    {rootPtn rootLab : Array Nat}
    {specFuel level numcells tc len o : Nat} {cs : List Nat}
    {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hpath : level = cs.length + 1) (hlt : level < n)
    (h : FirstInv G ctx level cs numcells st trail)
    (hp : PathOk ctx rootPtn rootLab level st)
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
      lab := (Nauty.breakout pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).1
      ptn := (Nauty.breakout pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.1
      active := (Nauty.breakout pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.2
      fixedpts := insert pre.fixedpts pre.lab[tc + o]!
      cosetindex := pre.lab[tc + o]! }
    PathOk ctx rootPtn rootLab (level + 1) child := by
  subst n
  dsimp only
  let r := refine ctx level st.lab st.ptn st.active numcells
  let refined : SearchSt := { st with
    lab := r.lab, ptn := r.ptn, active := r.active }
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
    lab := (Nauty.breakout pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).1
    ptn := (Nauty.breakout pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).2.1
    active := (Nauty.breakout pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).2.2
    fixedpts := insert pre.fixedpts pre.lab[tc + o]!
    cosetindex := pre.lab[tc + o]! }
  have hlevel : 1 ≤ level := by omega
  have href := h.refined rfl hg hn0 hlevel
  have hpRefined : PathOk ctx rootPtn rootLab level refined := by
    exact hp.refine rfl hn0 hlevel (by rw [hg]; exact size_rowsOf G)
      h.searchOk h.activeLt h.activeStarts
  have hpreLab : pre.lab = r.lab := by unfold pre pre0; split <;> rfl
  have hprePtn : pre.ptn = r.ptn := by unfold pre pre0; split <;> rfl
  have hpreFixed : pre.fixedpts = st.fixedpts := by
    unfold pre pre0
    split <;> rfl
  have hpPre : PathOk ctx rootPtn rootLab level pre := by
    apply hpRefined.stateEq
    · simpa only [refined] using hpreLab
    · simpa only [refined] using hprePtn
    · simpa only [refined] using hpreFixed
  have hpreSize : pre.lab.size = ctx.n := by
    rw [hpreLab]
    exact href.1.ok.labSize
  have hprePsize : pre.ptn.size = ctx.n := by
    rw [hprePtn]
    exact href.1.ok.ptnSize
  have hpreLabOk : LabOk pre.lab ctx.n := by
    rw [hpreLab]
    exact href.1.ok.labOk
  have hpreInj : LabInj pre.lab ctx.n := by
    rw [hpreLab]
    exact href.1.inj
  have hpreEnd : pre.ptn[pre.ptn.size - 1]! ≤ level := by
    rw [hprePtn]
    exact href.1.ok.ptnEnd
  have hpreCell : IsCell pre.ptn level tc len := by
    rw [hprePtn]
    exact hcell
  have hvals : ∀ q : Nat, pre.ptn[q]! ≠ level + 1 := by
    intro q heq
    rw [hprePtn] at heq
    change (refine ctx level st.lab st.ptn st.active
      numcells).ptn[q]! = level + 1 at heq
    rcases Decidable.em (q < ctx.n) with hq | hq
    · rcases href.1.valsWeak q hq with hle | hgt <;> omega
    · have hqsize : ¬q < (refine ctx level st.lab st.ptn st.active
          numcells).ptn.size := by
        rw [href.1.ok.ptnSize]
        exact hq
      rw [getElem!_neg
        (refine ctx level st.lab st.ptn st.active numcells).ptn q hqsize]
        at heq
      simp at heq
  have hpChild := hpPre.individualize hpreInj hpreLabOk hpreSize
    hprePsize hpreEnd hpreCell hlen hrange ho hvals
  apply hpChild.stateEq
  · rfl
  · rfl
  · rfl

end FirstInv

namespace OtherProof

/-- Package any early off-path leaf outcome with its fixed-frame
equation. -/
theorem ofLeafEarly {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes fs : List Nat} {st : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail}
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hearly : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hout : OtherOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes fs st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest receiptTrail eventTrail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1) :
    OtherProof G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 numcells
      best outBest receiptTrail eventTrail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 :=
  ⟨hout, otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
    numcells st hnum hearly⟩

/-- Package any completed off-path leaf outcome with its fixed-frame
equation. -/
theorem ofLeafDone {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes fs : List Nat} {st : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail}
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdone : ¬((processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level))
    (hout : OtherOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes fs st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest receiptTrail eventTrail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1) :
    OtherProof G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 numcells
      best outBest receiptTrail eventTrail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 :=
  ⟨hout, otherNode_leaf_done_fixedpts ctx inf tcLevel fuel level numcells
    st hnum hdone⟩

theorem node {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {cs fs : List Nat}
    {st out : SearchSt} {best outBest : Option Key} {r : Int}
    {receiptTrail eventTrail : FrameTrail}
    (h : OtherProof G ctx tcLevel specFuel runFuel level cs fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeProof G ctx tcLevel specFuel runFuel level cs fs st out numcells
      best outBest receiptTrail eventTrail r :=
  ⟨h.outcome.node, h.fixed⟩

end OtherProof

namespace LoopProof

theorem reindexSet {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell tcell' : Nat} {cursor : Option Nat}
    {bound : Key} {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r) :
    LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.outcome.reindexSet, h.fixed⟩

theorem step {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell (some tv) bound st out best
      outBest receiptTrail eventTrail r) :
    LoopProof G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.outcome.step ha, h.fixed⟩

theorem retrail {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st out : SearchSt} {best outBest : Option Key}
    {source dest eventTrail : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      source eventTrail r) :
    LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      dest eventTrail r :=
  ⟨h.outcome.retrail htrail, h.fixed⟩

theorem prepend {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st recSt out : SearchSt} {best mid outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (h : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound recSt out mid
      outBest receiptTrail eventTrail r) :
    LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.outcome.prefix hpre, h.fixed.trans hfixed⟩

end LoopProof

namespace FirstLoopProof

/-- An early-returning first-path loop supplies its enclosing first-path
node while dropping the loop's own frozen frame from the active history. -/
theorem toNodeSome {G : Colored n k} {ctx : Ctx}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level : Nat}
    {nodeCs loopCs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {outBest : Option Key} {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCs nodeSt
      nodeNumcells)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstLoopProof G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCs loopCs fs rsLab rsPtn tc len loopNumcells tcell cursor bound
      loopSt out none outBest receiptTrail eventTrail (some r)) :
    FirstProof G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCs fs nodeSt
      out nodeNumcells outBest receiptTrail eventTrail r :=
  ⟨⟨h.loop.outcome.toNodeSome hbound, h.loop.fixed.trans hfixed⟩,
    h.trail.lower⟩

/-- A fully exhausted first-path loop supplies its enclosing node once
cursor fuel proves that exhaustion means complete child coverage. -/
theorem toNodeNone {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCs loopCs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {outBest : Option Key} {receiptTrail eventTrail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel (specFuel + 1) level nodeCs
      nodeSt nodeNumcells)
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
          loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hlen : len = tail + 1)
    (hfuel : ctx.n < cursorRank cursor + loopFuel)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level
      nodeCs loopCs fs rsLab rsPtn tc len loopNumcells tcell cursor bound
      loopSt out none outBest receiptTrail eventTrail none) :
    FirstProof G ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCs fs
      nodeSt out nodeNumcells outBest receiptTrail eventTrail
      (Int.ofNat level - 1) :=
  ⟨⟨h.loop.outcome.toNodeNone hbound hchildren hlen hfuel,
      h.loop.fixed.trans hfixed⟩,
    h.trail.lower⟩

theorem reindexSet {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell tcell' : Nat} {cursor : Option Nat}
    {bound : Key} {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.loop.reindexSet, h.trail⟩

theorem step {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound st out
      best outBest receiptTrail eventTrail r) :
    FirstLoopProof G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r :=
  ⟨h.loop.step ha, h.trail⟩

theorem retrail {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st out : SearchSt} {best outBest : Option Key}
    {source dest eventTrail : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest source eventTrail r) :
    FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      dest eventTrail r :=
  ⟨h.loop.retrail htrail, h.trail⟩

theorem prepend {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st recSt out : SearchSt} {best mid outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound recSt out mid
      outBest receiptTrail eventTrail r) :
    FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.loop.prepend hfixed hpre, h.trail⟩

end FirstLoopProof

namespace FirstProof

/-- The final first-path `allsamelevel` adjustment preserves both the
semantic result and the stored first-leaf history. -/
theorem firstFinish {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs fs : List Nat} {st out : SearchSt} {outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : FirstProof G ctx tcLevel specFuel runFuel level cs fs st out
      numcells outBest receiptTrail eventTrail r) :
    FirstProof G ctx tcLevel specFuel runFuel level cs fs st
      (Nauty.firstFinish level size index out) numcells outBest
      receiptTrail eventTrail r :=
  ⟨h.node.firstFinish hfuel,
    h.trail.retrail (firstFinish_firstlab level size index out)
      (TrailExt.refl level eventTrail)⟩

end FirstProof

namespace LoopInv

/-- Exhausting first-path loop fuel retains both the semantic event and
the unchanged fixed-point frame.  The outer node later rules this case
out from the cursor-progress bound. -/
theorem firstZero {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel level numcells tc len tcell tv1 index : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tv? cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hcursor : ∀ v, cursor = some v → v < ctx.n) :
    LoopProof G ctx tcLevel specFuel runFuel 0 level stem codes fs rsLab
      rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).1 := by
  constructor
  · constructor
    · exact firstLoop_zeroReceipt ctx inf tcLevel specFuel runFuel level
        numcells tc tv1 codes rsLab rsPtn len tv? cursor tcell index bound
        st best trail hinv.cover hcursor
    · simpa only [firstChildLoop, loopReturn] using
        (EventOut.ofRun hinv.run hpath hstem hpast (by omega) hnp
          (hlive.stable.lower (by omega)) hlive.history)
    · exact TrailExt.refl level trail
  · rw [firstChildLoop]

/-- Exhausting off-path loop fuel retains both the semantic event and the
unchanged fixed-point frame. -/
theorem otherZero {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel level numcells tc len tcell tv1 : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tv? cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hcursor : ∀ v, cursor = some v → v < ctx.n) :
    LoopProof G ctx tcLevel specFuel runFuel 0 level stem codes fs rsLab
      rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).1 := by
  constructor
  · constructor
    · exact otherLoop_zeroReceipt ctx inf tcLevel specFuel runFuel level
        numcells tc tv1 codes rsLab rsPtn len tv? cursor tcell bound st best
        trail hinv.cover hcursor
    · simpa only [otherChildLoop, loopReturn] using
        (EventOut.ofRun hinv.run hpath hstem hpast (by omega) hnp
          (hlive.stable.lower (by omega)) hlive.history)
    · exact TrailExt.refl level trail
  · rw [otherChildLoop]

/-- Completing a positive-fuel first-path sweep leaves its fixed-point
frame unchanged. -/
theorem firstDoneProof {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 index : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : nextElem tcell cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    LoopProof G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).1 := by
  refine ⟨hinv.firstDone hpath hstem hpast hnext hnp hlive, ?_⟩
  rw [firstChildLoop]
  case x_1 => omega

/-- Completing a positive-fuel off-path sweep leaves its fixed-point
frame unchanged. -/
theorem otherDoneProof {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : nextElem tcell cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    LoopProof G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).1 := by
  refine ⟨hinv.otherDone hpath hstem hpast hnext hnp hlive, ?_⟩
  rw [otherChildLoop]
  case x_1 => omega

end LoopInv

end Hex.GraphIso.Nauty
