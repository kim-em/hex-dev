/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.RunInv.Coset
import all HexGraphIso.Nauty.Search.Search

public section

/-!
The mutual induction for the transcribed search, coupled to its frame
equations.

The semantic outcomes distinguish completed subtrees, located unwinds,
comparison prunes, and exhausted runtime fuel.  This module couples those
outcomes to the one extra executable frame fact needed by the induction:
every recursive node call restores the fixed-point bitset with which it
was entered.  It also records the two unconditional leaf histories
`FirstTrail` and `CanonTrail` and the frozen comparison verdict
`FrozenOut`.

This module builds on `Correct.RunInv.Coset`.  `Correct.Exit.Classify`
classifies the exits of the node and loop proofs defined here.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- At a loop boundary, an implicit small-cell pair is available even
when `noncheaplevel` is exactly the loop level.  `CheapOk` omits this
equality case at general node entries.  The loop guards restore it before
beginning a sibling sweep. -/
@[expose] def BoundaryOk (G : Colored n k) (ctx : Ctx n)
    (level : Nat) (st : SearchSt n) : Prop :=
  st.noncheaplevel = level →
    PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (fmptn st.lab st.ptn level n).1
      (fmptn st.lab st.ptn level n).2

namespace BoundaryOk

/-- Parking strictly past a loop makes its equality case vacuous. -/
theorem parked {G : Colored n k} {ctx : Ctx n} {level : Nat}
    {st : SearchSt n} :
    BoundaryOk G ctx level { st with noncheaplevel := level + 1 } := by
  intro heq
  simp only at heq
  omega

/-- A successful cheap-cell test supplies the implicit pair required at
the loop boundary. -/
theorem ofCheap {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hcheap : cheapautom st.ptn level n = true) :
    BoundaryOk G ctx level st := by
  intro hboundary
  let r : RefineSt n :=
    { lab := st.lab, ptn := st.ptn, active := VSet.empty, numcells := numcells,
      hint := 0, maxpos := 0, longcode := numcells }
  have hlab : LabOk st.lab n :=
    labOk_of_reach hinv.run.searchOk.labSize hinv.run.searchOk.reach
  have hinj : LabInj st.lab n :=
    labInj_of_reach hinv.run.searchOk.labSize hinv.nonempty
      hinv.run.searchOk.reach
  have hend := searchOk_end hinv.nonempty hinv.run.searchOk hinv.positive
  have hit : IterOk ctx level r := by
    constructor
    · exact ⟨hinv.run.searchOk.labSize, hlab,
        hinv.run.searchOk.ptnSize, hend⟩
    · exact hinj
    · intro q hq
      exact hinv.run.searchOk.vals q hq
    · exact Nat.le_trans hinv.run.searchOk.bc
        (bcount_le st.ptn level n)
  have heq : Equitable ctx level r.lab r.ptn := by
    simpa only [r] using hinv.currentEquitable
  have hcount : bcount r.ptn level n = r.numcells := by
    simpa only [r] using hinv.run.searchOk.count.symm
  have hsub : SubtreeOk ctx level r :=
    subtreeOk_of_cheapautom hit heq hcount (by simpa only [r] using hcheap)
  have hpair : PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (fmptn r.lab r.ptn level n).1
      (fmptn r.lab r.ptn level n).2 := by
    apply pairOk_fmptn_of_subtree (ctx := ctx) (G := G)
      (r := r) hinv.nonempty hinv.positive
    · rw [hg]
      exact size_rowsOf G
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
theorem nextCheap {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
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
theorem recoverBoundary {G : Colored n k} {ctx : Ctx n}
    {tcLevel level inf : Nat} {fixedpts : VSet n} {stem fs : List Nat}
    {out : SearchSt n} {best : Option (Key n)} {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (hstem : stem.length = level) (hlevel : 1 ≤ level)
    (hinf : level < inf) :
    BoundaryOk G ctx level
      (Nauty.recover n inf level { out with fixedpts := fixedpts }) := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
    intro hboundary
    let cleaned : SearchSt n := { out with fixedpts := fixedpts }
    have hevent : RunEvent G ctx tcLevel current codes bestCodes fs cleaned
        best trail := event.setFixed fixedpts
    have hcurrent : level < current := by
      rw [← hstem]
      exact past
    have hncl : (Nauty.recover n inf level cleaned).noncheaplevel =
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
      (n := n) (inf := inf) (level := level) (saved := level)
      (Nat.le_of_eq hevent.cheap.ptnSize.symm)
      (Nat.le_trans hevent.cheap.rootEnd hlevel)
      (Nat.le_refl level) hinf
    change PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (fmptn (Nauty.recover n inf level cleaned).lab
        (Nauty.recover n inf level cleaned).ptn level n).1
      (fmptn (Nauty.recover n inf level cleaned).lab
        (Nauty.recover n inf level cleaned).ptn level n).2
    rw [hfm]
    exact hpair

end EventOut

/-! # Fixed-point equations for node prefixes -/

theorem firstLeafSt_fixedpts (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (firstLeafSt ctx level numcells st).fixedpts = st.fixedpts := by
  rfl

theorem otherLeafSt_fixedpts (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).fixedpts = st.fixedpts := by
  unfold otherLeafSt
  exact otherNodePrep_fixedpts _ _ _

theorem leafFinish_fixedpts (level : Nat) (st : SearchSt n) :
    (leafFinish level st).fixedpts = st.fixedpts := by
  rw [leafFinish]
  split <;> split <;> rfl

/-- Clearing a freshly inserted bit restores the original set. -/
theorem erase_insert_of_miss {s : VSet n} {v : Nat} (h : s.mem v = false) :
    (s.insert v).erase v = s := by
  apply VSet.ext
  intro u
  rw [VSet.mem_erase, VSet.mem_insert]
  rcases Decidable.em (v = u) with rfl | hne
  · simp only [beq_self_eq_true, Bool.not_true, 
      Bool.and_false]
    exact h.symm
  · have hb : (v == u) = false := by simp [hne]
    rw [hb]
    simp

/-- The discrete first-path arm restores its entry fixed-point set. -/
theorem firstPath_discrete_fixedpts (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n) :
    (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2.fixedpts =
      st.fixedpts := by
  rw [firstPath_discrete_state ctx inf tcLevel fuel level numcells st hnum]
  exact (firstterminal_fixedpts level _).trans
    (firstLeafSt_fixedpts ctx level numcells st)

/-- Every early off-path leaf return restores its entry fixed-point set. -/
theorem otherNode_leaf_early_fixedpts (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level) :
    (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2.fixedpts =
      st.fixedpts := by
  rw [otherNode_leaf_early ctx inf tcLevel fuel level numcells st hnum
    hearly]
  exact (processnode_fixedpts ctx level n _).trans
    (otherLeafSt_fixedpts ctx level numcells st)

/-- Every completed off-path leaf restores its entry fixed-point set. -/
theorem otherNode_leaf_done_fixedpts (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hdone : ¬((processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)) :
    (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2.fixedpts =
      st.fixedpts := by
  rw [otherNode_leaf_done_state ctx inf tcLevel fuel level numcells st
    hnum hdone]
  exact (leafFinish_fixedpts level _).trans
    ((processnode_fixedpts ctx level n _).trans
      (otherLeafSt_fixedpts ctx level numcells st))

/-- A semantic node outcome together with restoration of its entry
fixed-point set. -/
structure NodeProof (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  outcome : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
    numcells best outBest receiptTrail eventTrail r
  fixed : out.fixedpts = st.fixedpts

/-- The stronger off-path result retains the guide facts required by an
ordinary sibling loop. -/
structure OtherProof (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  outcome : OtherOutcome G ctx tcLevel specFuel runFuel level cs fs st out
    numcells best outBest receiptTrail eventTrail r
  fixed : out.fixedpts = st.fixedpts
  coset : out.cosetindex = st.cosetindex

/-- A semantic loop outcome together with restoration of the loop entry's
fixed-point set. -/
structure LoopProof (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  outcome : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
    codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
    outBest receiptTrail eventTrail r
  fixed : out.fixedpts = st.fixedpts

/-- An off-path loop additionally preserves the first-path coset cursor.
The analogous claim is false for `firstChildLoop`, which installs the
currently selected sibling before entering an off-path subtree. -/
structure OtherLoopProof (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  loop : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
    fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail eventTrail r
  coset : out.cosetindex = st.cosetindex

/-- The first leaf remembers every child selected on the unique initial
descent.  Unlike `RefTrail.first`, this history is independent of the
mutable `gcaFirst` return control: outer first-path loops reset that
control while the leaf remains a descendant of all their frozen frames. -/
structure FirstTrail (ctx : Ctx n) (current : Nat) (st : SearchSt n)
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

/-- Before the enclosing first-path node returns, its canonical reference
also remains inside every strictly older guiding child.  The current loop
frame is excluded because later siblings may replace the canonical child
there.  `FrameRefs` states what holds at that changing boundary. -/
structure CanonTrail (ctx : Ctx n) (current : Nat) (st : SearchSt n)
    (trail : FrameTrail) : Prop where
  reach : ∀ target entry, target < current →
    trail target = some entry →
    cellsPerm entry.frame.rsPtn target entry.frame.rsLab st.canonlab
  picked : ∀ target entry, target < current →
    trail target = some entry →
    ∃ len, IsCell entry.frame.rsPtn target entry.frame.tc len ∧
      entry.offset < len ∧
      st.canonlab[entry.frame.tc]! =
        entry.frame.rsLab[entry.frame.tc + entry.offset]!

/-- A comparison-frozen return retains the full deep code path while
exposing any ancestor prefix through `stem`.  The floor clause says the
return does not jump above the recorded downward divergence. -/
inductive FrozenOut (ctx : Ctx n) (stem : List Nat) (out : SearchSt n)
    (best : Option (Key n)) (r : Int) : Prop where
  | mk (current : Nat) (codes bestCodes : List Nat)
      (codeInv : CodeCmpInv n codes bestCodes out.canoncode
        out.canonlevel out.eqlevCanon (-1))
      (depth : current = codes.length)
      (stemEq : codes.take stem.length = stem)
      (installed : bestCodes ≠ [])
      (incumbent : best = some (incKey ctx bestCodes out.canonlab))
      (floor : Int.ofNat out.eqlevCanon.toNat ≤ r) :
      FrozenOut ctx stem out best r

namespace FrozenOut

/-- Every subtree below an exposed ancestor prefix is below the installed
incumbent once that ancestor lies strictly above the frozen return. -/
theorem keyLe {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r)
    {level : Nat} (hlevel : level = stem.length)
    (hbelow : r < Int.ofNat level) (K : Key n) :
    ∃ b, best = some b ∧ keyLe (prefixKey stem K) b := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, _, hinc, hfloor⟩
  have hM : out.eqlevCanon.toNat < level := by
    have hi : Int.ofNat out.eqlevCanon.toNat < Int.ofNat level :=
      Int.lt_of_le_of_lt hfloor hbelow
    exact Int.ofNat_lt.mp hi
  have hMcs : level ≤ codes.length := by
    have hlen := congrArg List.length hstem
    simp only [List.length_take] at hlen
    omega
  have htake : codes.take level = stem := by
    rw [hlevel]
    exact hstem
  refine ⟨incKey ctx bestCodes out.canonlab, hinc, ?_⟩
  rw [← htake]
  exact frozen_take_keyLe hcode hM hMcs K

/-- The frozen verdict bounds every still-live child of an abandoned
ancestor sweep. -/
theorem liveKeyLe {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r)
    {tcLevel specFuel level tail tc numcells : Nat} {tcell : VSet n}
    {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    (hlevel : level = stem.length) (hbelow : r < Int.ofNat level) :
    ∀ o, ChildLive rsLab tc (tail + 1) tcell cursor o →
      ∃ b, best = some b ∧ Hex.GraphIso.Nauty.keyLe
        (sweepKey ctx tcLevel specFuel level stem rsLab rsPtn tc numcells o)
        b := by
  intro o _
  simpa only [sweepKey] using h.keyLe hlevel hbelow
    (childKey ctx tcLevel specFuel level rsLab rsPtn tc numcells o)

/-- A frozen verdict always names the installed incumbent that caused the
comparison to stop. -/
theorem present {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r) :
    ∃ b, best = some b := by
  rcases h with ⟨_, _, bestCodes, _, _, _, _, hbest, _⟩
  exact ⟨incKey ctx bestCodes out.canonlab, hbest⟩

/-- The concrete state read agrees with the incumbent carried by a frozen
comparison. -/
theorem read {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r) :
    stInc ctx out = best := by
  rcases h with
    ⟨_, _, bestCodes, hcode, _, _, hbestCodes, hbest, _⟩
  rw [stInc_eq_ghost hcode (by decide), ghostInc]
  simp only [hbestCodes, ↓reduceIte, hbest]

/-- Coverage of the explored prefix and a frozen comparison of the live
suffix recover the exact maximum of an abandoned parent sweep. -/
theorem exactLoop {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {outBest best : Option (Key n)} {r : Int}
    {tcLevel specFuel level tail tc numcells : Nat} {tcell : VSet n}
    {rsLab rsPtn : Array Nat} {cursor : Option Nat} {bound : Key n}
    (h : FrozenOut ctx stem out outBest r)
    (hlevel : level = stem.length) (hbelow : r < Int.ofNat level)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level stem rsLab rsPtn tc numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level stem rsLab rsPtn tc
          numcells (o + 1)))
    (hcover : SweepCover ctx tcLevel specFuel level stem rsLab rsPtn tc
      (tail + 1) numcells tcell cursor outBest)
    (hsound : LoopSound ctx bound best outBest) :
    outBest = some (incMax best bound) := by
  obtain ⟨b, hout⟩ := h.present
  apply SweepCover.exactLive hbound hcover hsound hout
  intro o ho
  obtain ⟨b', hout', hle⟩ := h.liveKeyLe hlevel hbelow o ho
  have hbb : b' = b := Option.some.inj (hout'.symm.trans hout)
  rwa [hbb] at hle

end FrozenOut

/-- What a first-path node may export.  A locally absorbed or pruned node
exports its exact maximum, and a genuine generator unwind directly names
the first or canonical reference child.  The orbit-pointer arm is resolved
by `firstChildLoop` and does not appear here. -/
inductive NodeEscape (ctx : Ctx n) (tcLevel specFuel level : Nat)
    (cs : List Nat) (st out : SearchSt n) (numcells : Nat)
    (best outBest : Option (Key n)) (trail : FrameTrail) (r : Int) : Prop where
  | full (eq : outBest = some (incMax best
      (nodeKey ctx tcLevel specFuel level cs st numcells)))
  | first (target : Nat) (returned : r = Int.ofNat target)
      (below : target < level) (anchor : Anchor ctx tcLevel target outBest)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace)
      (located : anchor.Located trail)
  | canon (target : Nat) (returned : r = Int.ofNat target)
      (below : target < level) (anchor : Anchor ctx tcLevel target outBest)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
      (located : anchor.Located trail)

/-- The corresponding first-path loop exit.  Fuel-exhausted intermediate
tails may still return `none`, and sufficient outer cursor fuel rules that
arm out. -/
inductive LoopEscape (ctx : Ctx n) (tcLevel level : Nat) (bound : Key n)
    (out : SearchSt n) (best outBest : Option (Key n)) (trail : FrameTrail)
    (r : Option Int) : Prop where
  | full (eq : outBest = some (incMax best bound))
  | first (target : Nat) (returned : r = some (Int.ofNat target))
      (below : target < level) (anchor : Anchor ctx tcLevel target outBest)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace)
      (located : anchor.Located trail)
  | canon (target : Nat) (returned : r = some (Int.ofNat target))
      (below : target < level) (anchor : Anchor ctx tcLevel target outBest)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
      (located : anchor.Located trail)
  | pending (returned : r = none)

namespace NodeEscape

/-- First-path sweep cleanup changes no data named by an escape witness. -/
theorem firstFinish {ctx : Ctx n} {tcLevel specFuel level numcells size index : Nat}
    {cs : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : NodeEscape ctx tcLevel specFuel level cs st out numcells best
      outBest trail r) :
    NodeEscape ctx tcLevel specFuel level cs st
      (Nauty.firstFinish level size index out) numcells best outBest trail r := by
  cases h with
  | full eq => exact .full eq
  | first target returned below anchor carrier located =>
      apply NodeEscape.first target returned below anchor
      · rw [Nauty.firstFinish]
        split <;> exact carrier
      · exact located
  | canon target returned below anchor carrier located =>
      apply NodeEscape.canon target returned below anchor
      · rw [Nauty.firstFinish]
        split <;> exact carrier
      · exact located

end NodeEscape

namespace LoopEscape

/-- Rebase direct escape locations onto a trail agreeing below the loop. -/
theorem retrail {ctx : Ctx n} {tcLevel level : Nat} {bound : Key n}
    {out : SearchSt n} {best outBest : Option (Key n)}
    {source dest : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : LoopEscape ctx tcLevel level bound out best outBest source r) :
    LoopEscape ctx tcLevel level bound out best outBest dest r := by
  cases h with
  | full eq => exact .full eq
  | first target returned below anchor carrier located =>
      apply LoopEscape.first target returned below anchor carrier
      unfold Anchor.Located at located ⊢
      rw [← htrail target below]
      exact located
  | canon target returned below anchor carrier located =>
      apply LoopEscape.canon target returned below anchor carrier
      unfold Anchor.Located at located ⊢
      rw [← htrail target below]
      exact located
  | pending returned => exact .pending returned

/-- Prepending a sound loop fragment adjusts only the incoming incumbent. -/
theorem prepend {ctx : Ctx n} {tcLevel level : Nat} {bound : Key n}
    {out : SearchSt n} {best mid outBest : Option (Key n)}
    {trail : FrameTrail} {r : Option Int}
    (hpre : LoopSound ctx bound best mid)
    (h : LoopEscape ctx tcLevel level bound out mid outBest trail r) :
    LoopEscape ctx tcLevel level bound out best outBest trail r := by
  cases h with
  | full eq =>
      have hsound := hpre.trans (LoopSound.ofExact eq)
      exact .full (hsound.exact eq (keyLe_incMax_right mid bound))
  | first target returned below anchor carrier located =>
      exact .first target returned below anchor carrier located
  | canon target returned below anchor carrier located =>
      exact .canon target returned below anchor carrier located
  | pending returned => exact .pending returned

end LoopEscape

/-- A first-path node proof additionally retains the unconditional history
of the first leaf through every active ancestor frame. -/
structure FirstProof (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  node : NodeProof G ctx tcLevel specFuel runFuel level cs fs st out
    numcells none outBest receiptTrail eventTrail r
  escape : NodeEscape ctx tcLevel specFuel level cs st out numcells none
    outBest receiptTrail r
  trail : FirstTrail ctx level out eventTrail
  canonTrail : CanonTrail ctx level out eventTrail
  resumable : Int.ofNat level - 1 ≤ r → level - 1 ≤ out.gcaFirst
  order : out.gcaFirst ≤ out.gcaCanon

/-- A first-path loop keeps the current frozen frame in the first leaf's
history until the loop is converted back to its parent node result. -/
structure FirstLoopProof (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  loop : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
    fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail eventTrail r
  escape : LoopEscape ctx tcLevel level bound out best outBest receiptTrail r
  trail : FirstTrail ctx (level + 1) out eventTrail
  canonTrail : CanonTrail ctx level out eventTrail
  guideLevel : level ≤ out.gcaFirst
  order : out.gcaFirst ≤ out.gcaCanon

namespace FirstTrail

/-- Reindex first-leaf history along an output trail extension and a state
update that leaves the stored first leaf unchanged. -/
theorem retrail {ctx : Ctx n} {current : Nat} {st out : SearchSt n}
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
theorem lower {ctx : Ctx n} {current : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : FirstTrail ctx (current + 1) st trail) :
    FirstTrail ctx current st trail := by
  constructor
  · intro target entry htarget hentry
    exact h.reach target entry (by omega) hentry
  · intro target entry htarget hentry
    exact h.picked target entry (by omega) hentry

end FirstTrail

namespace CanonTrail

theorem retrail {ctx : Ctx n} {current : Nat} {st out : SearchSt n}
    {source dest : FrameTrail}
    (h : CanonTrail ctx current st source)
    (hcanon : out.canonlab = st.canonlab)
    (hext : TrailExt current source dest) :
    CanonTrail ctx current out dest := by
  constructor
  · intro target entry htarget hentry
    rw [hext target htarget] at hentry
    rw [hcanon]
    exact h.reach target entry htarget hentry
  · intro target entry htarget hentry
    rw [hext target htarget] at hentry
    obtain ⟨len, hcell, hoff, hat⟩ :=
      h.picked target entry htarget hentry
    exact ⟨len, hcell, hoff, by simpa only [hcanon] using hat⟩

theorem lower {ctx : Ctx n} {current : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : CanonTrail ctx (current + 1) st trail) :
    CanonTrail ctx current st trail := by
  constructor
  · intro target entry htarget hentry
    exact h.reach target entry (by omega) hentry
  · intro target entry htarget hentry
    exact h.picked target entry (by omega) hentry

end CanonTrail

/-- First-path sweep cleanup changes only `allsamelevel`. -/
theorem firstFinish_firstlab (level size index : Nat) (st : SearchSt n) :
    (firstFinish level size index st).firstlab = st.firstlab := by
  rw [firstFinish]
  split <;> rfl

theorem firstFinish_canonlab (level size index : Nat) (st : SearchSt n) :
    (firstFinish level size index st).canonlab = st.canonlab := by
  rw [firstFinish]
  split <;> rfl

namespace EventOut

/-- Recovering a guiding-child event whose first control has been reset to
the parent produces the live first-path loop package.  Return stabilization
at that exact control is precisely the store-wide stabilization required
for the frozen parent frame. -/
theorem recoverFirst {G : Colored n k} {ctx : Ctx n}
    {tcLevel level inf numcells : Nat} {fixedpts : VSet n} {tv1 : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int} {rsLab rsPtn : Array Nat}
    (h : EventOut G ctx tcLevel stem fs
      { out with gcaFirst := level, stabvertex := tv1 } best trail r)
    (hreturn : r = Int.ofNat level) (hstem : stem.length = level)
    (hlevel : 1 ≤ level) (hinf : level < inf)
    (hok : SearchOk G level numcells
      (recover n inf level
        { out with fixedpts := fixedpts, gcaFirst := level, stabvertex := tv1 }))
    (horder : level ≤ out.gcaCanon)
    (hframe : trail level = some
      ⟨⟨specFuel, codes, rsLab, rsPtn, tc, frameNumcells⟩, offset⟩) :
    ∃ bs,
      RunInv G ctx tcLevel level stem bs fs numcells
          (recover n inf level
            { out with fixedpts := fixedpts, gcaFirst := level, stabvertex := tv1 })
          best trail ∧
        FirstLive ctx level
          (recover n inf level
            { out with fixedpts := fixedpts, gcaFirst := level, stabvertex := tv1 })
          trail rsLab rsPtn := by
  let prepared : SearchSt n :=
    { out with gcaFirst := level, stabvertex := tv1 }
  let cleaned : SearchSt n := { prepared with fixedpts := fixedpts }
  let recovered := recover n inf level cleaned
  have hfirst : cleaned.gcaFirst ≤ level := by
    simp only [cleaned, prepared]
    exact Nat.le_refl level
  obtain ⟨bs, hrun, hstable, hhistory⟩ :=
    h.setFixed fixedpts |>.recoverRun hreturn hstem hlevel hinf hfirst
      (by simpa only [cleaned, prepared, recovered] using hok)
  have hfirstRec : recovered.gcaFirst = level := by
    rw [show recovered = recover n inf level cleaned by rfl,
      (recover_frames n inf level cleaned).2.2.2.2.2.2.1]
  have hcanonRec : recovered.gcaCanon = level := by
    rw [show recovered = recover n inf level cleaned by rfl,
      recover_gcaCanon]
    change (if level < out.gcaCanon then level else out.gcaCanon) = level
    split <;> omega
  refine ⟨bs, by simpa only [cleaned, prepared, recovered] using hrun, ?_⟩
  constructor
  · constructor
    · simpa only [cleaned, prepared, recovered] using hhistory
    · rw [hfirstRec, hcanonRec]
      exact Nat.le_refl level
    · simpa only [cleaned, prepared, recovered, hfirstRec] using hstable
  · intro gamma hgamma
    have hs := hstable level
      ⟨⟨specFuel, codes, rsLab, rsPtn, tc, frameNumcells⟩, offset⟩
      (by rw [hfirstRec]; exact Int.le_refl _) hframe gamma hgamma
    exact hs

end EventOut

/-- A completed child, cleanup, and recovery restore both parent path
facts.  The selected vertex is fresh because it lies in a non-singleton
target cell while all older fixed vertices occupy singleton cells. -/
theorem LoopInv.recoverPath {G : Colored n k} {ctx : Ctx n}
    {rootPtn rootLab rsLab rsPtn : Array Nat}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {currentOffset inf : Nat}
    {codes bs fs : List Nat} {cursor : Option Nat}
    {base st out : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx rootPtn rootLab level st)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      out)
    (hfixed : out.fixedpts =
      st.fixedpts.insert st.lab[tc + currentOffset]!)
    (hinf : inf = n + 2) (hcurrent : currentOffset < len) :
    let cleaned : SearchSt n :=
      { out with
        fixedpts := out.fixedpts.erase st.lab[tc + currentOffset]! }
    let recovered := Nauty.recover n inf level cleaned
    PathOk ctx rootPtn rootLab level recovered ∧
      recovered.fixedpts = st.fixedpts := by
  dsimp only
  let cleaned : SearchSt n :=
    { out with
      fixedpts := out.fixedpts.erase st.lab[tc + currentOffset]! }
  let recovered := Nauty.recover n inf level cleaned
  have hok := hinv.run.searchOk
  have hlab : LabOk st.lab n :=
    labOk_of_reach hok.labSize hok.reach
  have hinj : LabInj st.lab n :=
    labInj_of_reach hok.labSize hinv.nonempty hok.reach
  have hfresh : st.fixedpts.mem st.lab[tc + currentOffset]! = false :=
    hpath.fixed.fresh hlab hinj hok.labSize hinv.currentCell
      hinv.lenTwo hinv.range hcurrent
  have hcleaned : cleaned.fixedpts = st.fixedpts := by
    change out.fixedpts.erase st.lab[tc + currentOffset]! = st.fixedpts
    rw [hfixed, erase_insert_of_miss hfresh]
  have hparent : SearchOut G level level st out := by
    apply breakout_child_out hinv.nonempty hok hinv.positive
      hinv.currentCell hinv.lenTwo hinv.range hcurrent hout
    · rfl
    · exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!
    · rfl
    · rfl
  have hclean : SearchOut G level level st cleaned :=
    hparent.congr rfl rfl rfl rfl
  have hrec := hclean.recoverOk hinf hinv.positive hok
  have hrecovered : recovered.fixedpts = st.fixedpts := by
    exact (recover_fixedpts n inf level cleaned).trans hcleaned
  exact ⟨hpath.ofSearchOut hinv.nonempty hinv.positive hrecovered
    hok hrec.2 hrec.1, hrecovered⟩

namespace NodeProof

theorem firstFinish {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs fs : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
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
theorem stateEq {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level : Nat} {st out : SearchSt n}
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
theorem individualize {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level tc len o : Nat} {st : SearchSt n}
    (h : PathOk ctx rootPtn rootLab level st)
    (hinj : LabInj st.lab n) (hlab : LabOk st.lab n)
    (hsize : st.lab.size = n) (hpsize : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len)
    (hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1) :
    PathOk ctx rootPtn rootLab (level + 1)
      { st with
        lab := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]! } := by
  constructor
  · exact h.fixed.breakout hinj hsize hpsize hcell hlen hrange ho
  · exact h.stab.breakout hcell (by rw [hpsize]; exact hrange)
      (hsize.trans hpsize.symm) hlab ho hlen hend hvals

end PathOk

namespace FirstInv

/-- A discrete first-path leaf supplies the coupled node result and
restores the fixed-point frame with which the node was entered. -/
theorem terminalProof {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt n} {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [rs.longcode]
    let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
    NodeProof G ctx tcLevel (specFuel + 1) (fuel + 1) level cs full st
      out.2 numcells none (some (pathLeafKey ctx full rs.lab)) trail trail
      out.1 := by
  dsimp only
  exact ⟨h.terminalOutcome hn0 hlevel hnum,
    firstPath_discrete_fixedpts ctx inf tcLevel fuel level numcells st hnum⟩

/-- The first leaf also turns the accumulated active descent into an
unconditional history of the selected child at every ancestor frame. -/
theorem terminalFirstProof {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt n} {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n) :
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
    simpa only [rs, full, leaf] using h.terminal hn0 hlevel
  have hdisc : discreteAt rs.ptn level n = true := by
    rw [← refine_discrete_iff hn0 h.searchOk (by omega)]
    exact hnum
  have hnode : nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      pathLeafKey ctx full rs.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey]
  constructor
  · exact h.terminalProof hn0 hlevel hnum
  · apply NodeEscape.full
    simp only [incMax, hnode, rs, full]
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
  · rw [hstate]
    constructor
    · intro target entry htarget hentry
      rw [firstterminal_canonlab]
      exact hrun.trailOk.reach target entry htarget hentry
    · intro target entry htarget hentry
      obtain ⟨len, hcell, hoff, -, -, hat⟩ :=
        hrun.trailOk.picked target entry htarget hentry
      refine ⟨len, hcell, hoff, ?_⟩
      rw [firstterminal_canonlab]
      exact hat
  · intro _
    rw [hstate]
    change level - 1 ≤ (firstterminal level leaf).gcaFirst
    rw [(firstterminal_state level leaf).2.2.1]
    omega
  · rw [hstate]
    rw [(firstterminal_state level leaf).2.2.1,
      (firstterminal_state level leaf).2.2.2.1]
    exact Nat.le_refl level

/-- The executable first-child prefix preserves and extends the root path
facts before the first incumbent exists. -/
theorem childPath {G : Colored n k} {ctx : Ctx n}
    {rootPtn rootLab : Array Nat}
    {level numcells tc len o : Nat} {cs : List Nat}
    {st : SearchSt n} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hpath : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hp : PathOk ctx rootPtn rootLab level st)
    (hcell : IsCell
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tc len)
    (hlen : 2 ≤ len) (hrange : tc + len ≤ n) (ho : o < len) :
    let r := refine ctx level st.lab st.ptn st.active numcells
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
      lab := (Nauty.breakout n pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).1
      ptn := (Nauty.breakout n pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.1
      active := (Nauty.breakout n pre.lab pre.ptn (level + 1) tc
        pre.lab[tc + o]!).2.2
      fixedpts := pre.fixedpts.insert pre.lab[tc + o]!
      cosetindex := pre.lab[tc + o]! }
    PathOk ctx rootPtn rootLab (level + 1) child := by
  dsimp only
  let r := refine ctx level st.lab st.ptn st.active numcells
  let refined : SearchSt n := { st with
    lab := r.lab, ptn := r.ptn, active := r.active }
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
    lab := (Nauty.breakout n pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).1
    ptn := (Nauty.breakout n pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).2.1
    active := (Nauty.breakout n pre.lab pre.ptn (level + 1) tc
      pre.lab[tc + o]!).2.2
    fixedpts := pre.fixedpts.insert pre.lab[tc + o]!
    cosetindex := pre.lab[tc + o]! }
  have hlevel : 1 ≤ level := by omega
  have href := h.refined hg hn0 hlevel
  have hpRefined : PathOk ctx rootPtn rootLab level refined := by
    exact hp.refine hn0 hlevel (by rw [hg]; exact size_rowsOf G)
      h.searchOk h.activeStarts
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
  have hpreSize : pre.lab.size = n := by
    rw [hpreLab]
    exact href.1.ok.labSize
  have hprePsize : pre.ptn.size = n := by
    rw [hprePtn]
    exact href.1.ok.ptnSize
  have hpreLabOk : LabOk pre.lab n := by
    rw [hpreLab]
    exact href.1.ok.labOk
  have hpreInj : LabInj pre.lab n := by
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
    rcases Decidable.em (q < n) with hq | hq
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

theorem otherLeafSt_coset (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).cosetindex = st.cosetindex := by
  unfold otherLeafSt
  exact otherNodePrep_coset _ _ _

/-- A completed off-path child of the first-path loop consumes its current
sibling.  Here `cosetindex` is sound: the child record installs `tv`, and
the whole `otherNode` result preserves it. -/
theorem firstCover {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len tv offset currentOffset : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hg : ctx.g = rowsOf G)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (h : OtherProof G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]!
        cosetindex := tv }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level))
    (hnext : tcell.nextElem cursor = some tv)
    (hoffset : offset < len) (htv : rsLab[tc + offset]! = tv)
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.2
            fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]!
            cosetindex := tv }
          (numcells + 1)) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) outBest := by
  apply hinv.cover.receipt hnext h.outcome.node.receipt hfuel
      (h.outcome.node.parentReturn hfuel hstay) heq hoffset htv
  · exact h.coset
  · rw [hg]
    exact size_rowsOf G
  · intro γ hγ
    cases h.outcome.node.event with
    | intro current cs' bs' event depth stemEq past returned stable history =>
        exact event.genTraceOk.check hγ
  · exact hinv.frozenLabSize
  · rw [← hinv.baseLab, hinv.baseOk.labSize]
    exact labInj_of_reach hinv.baseOk.labSize hinv.nonempty
      hinv.baseOk.reach
  · exact hinv.frozenLabOk
  · exact hinv.frozenPtnSize
  · exact hinv.frozenEnd
  · exact hinv.values
  · exact hinv.cell
  · exact hinv.range
  · exact hinv.fuelBound

/-- Package any early off-path leaf outcome with its fixed-frame
equation. -/
theorem ofLeafEarly {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes fs : List Nat} {st : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail}
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hout : OtherOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes fs st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest receiptTrail eventTrail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1) :
    OtherProof G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 numcells
      best outBest receiptTrail eventTrail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  refine ⟨hout, otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
    numcells st hnum hearly, ?_⟩
  rw [otherNode_leaf_early ctx inf tcLevel fuel level numcells st hnum
    hearly]
  exact (processnode_coset ctx level n _).trans
    (otherLeafSt_coset ctx level numcells st)

/-- Package any completed off-path leaf outcome with its fixed-frame
equation. -/
theorem ofLeafDone {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes fs : List Nat} {st : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail}
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hdone : ¬((processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level))
    (hout : OtherOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes fs st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest receiptTrail eventTrail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1) :
    OtherProof G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 numcells
      best outBest receiptTrail eventTrail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  refine ⟨hout, otherNode_leaf_done_fixedpts ctx inf tcLevel fuel level
    numcells st hnum hdone, ?_⟩
  rw [otherNode_leaf_done_state ctx inf tcLevel fuel level numcells st
    hnum hdone]
  exact (leafFinish_coset level _).trans
    ((processnode_coset ctx level n _).trans
      (otherLeafSt_coset ctx level numcells st))

theorem node {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {cs fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)} {r : Int}
    {receiptTrail eventTrail : FrameTrail}
    (h : OtherProof G ctx tcLevel specFuel runFuel level cs fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeProof G ctx tcLevel specFuel runFuel level cs fs st out numcells
      best outBest receiptTrail eventTrail r :=
  ⟨h.outcome.node, h.fixed⟩

end OtherProof

namespace LoopProof

theorem reindexSet {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell tcell' : VSet n} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r) :
    LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.outcome.reindexSet, h.fixed⟩

theorem step {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell (some tv) bound st out best
      outBest receiptTrail eventTrail r) :
    LoopProof G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.outcome.step ha, h.fixed⟩

theorem retrail {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {source dest eventTrail : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      source eventTrail r) :
    LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      dest eventTrail r :=
  ⟨h.outcome.retrail htrail, h.fixed⟩

theorem prepend {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st recSt out : SearchSt n} {best mid outBest : Option (Key n)}
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

namespace OtherLoopProof

theorem reindexSet {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell tcell' : VSet n} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : OtherLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    OtherLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.loop.reindexSet, h.coset⟩

theorem step {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : OtherLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound st out best
      outBest receiptTrail eventTrail r) :
    OtherLoopProof G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r :=
  ⟨h.loop.step ha, h.coset⟩

theorem retrail {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {source dest eventTrail : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : OtherLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest source eventTrail r) :
    OtherLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      dest eventTrail r :=
  ⟨h.loop.retrail htrail, h.coset⟩

theorem prepend {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st recSt out : SearchSt n} {best mid outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (h : OtherLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound recSt out mid
      outBest receiptTrail eventTrail r) :
    OtherLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.loop.prepend hfixed hpre, h.coset.trans hcoset⟩

end OtherLoopProof

namespace FirstLoopProof

/-- An early-returning first-path loop supplies its enclosing first-path
node while dropping the loop's own frozen frame from the active history. -/
theorem toNodeSome {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level : Nat}
    {nodeCs loopCs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCs nodeSt
      nodeNumcells)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstLoopProof G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCs loopCs fs rsLab rsPtn tc len loopNumcells tcell cursor bound
      loopSt out none outBest receiptTrail eventTrail (some r)) :
    FirstProof G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCs fs nodeSt
      out nodeNumcells outBest receiptTrail eventTrail r :=
  by
    have hescape : NodeEscape ctx tcLevel nodeSpecFuel level nodeCs nodeSt
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
    exact ⟨⟨h.loop.outcome.toNodeSome hbound, h.loop.fixed.trans hfixed⟩,
      hescape, h.trail.lower, h.canonTrail, fun _ =>
        Nat.le_trans (Nat.sub_le level 1) h.guideLevel,
      h.order⟩

/-- A fully exhausted first-path loop supplies its enclosing node once
cursor fuel proves that exhaustion means complete child coverage. -/
theorem toNodeNone {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCs loopCs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
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
    (hfuel : n < cursorRank cursor + loopFuel)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level
      nodeCs loopCs fs rsLab rsPtn tc len loopNumcells tcell cursor bound
      loopSt out none outBest receiptTrail eventTrail none) :
    FirstProof G ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCs fs
      nodeSt out nodeNumcells outBest receiptTrail eventTrail
      (Int.ofNat level - 1) :=
  by
    have hfull : outBest = some (incMax none bound) := by
      cases h.loop.outcome.receipt with
      | complete returned sound installed read finalSet finalCursor cover empty =>
          rw [hlen] at cover empty
          exact cover.exact_of_read (hbound.trans hchildren) empty sound
            installed read
      | unwind sound target returned below payload located => cases returned
      | pruned target returned below sound installed read full => cases returned
      | exhausted returned sound finalSet finalCursor cover progress bounded =>
          exact (LoopResult.exhaustion_false hfuel progress bounded).elim
    have hescape : NodeEscape ctx tcLevel (specFuel + 1) level nodeCs
        nodeSt out nodeNumcells none outBest receiptTrail
        (Int.ofNat level - 1) := by
      apply NodeEscape.full
      simpa only [hbound] using hfull
    exact ⟨⟨h.loop.outcome.toNodeNone hbound hchildren hlen hfuel,
        h.loop.fixed.trans hfixed⟩,
      hescape, h.trail.lower, h.canonTrail, fun _ =>
        Nat.le_trans (Nat.sub_le level 1) h.guideLevel,
      h.order⟩

theorem reindexSet {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell tcell' : VSet n} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.loop.reindexSet, h.escape, h.trail, h.canonTrail, h.guideLevel,
    h.order⟩

theorem step {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound st out
      best outBest receiptTrail eventTrail r) :
    FirstLoopProof G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r :=
  ⟨h.loop.step ha, h.escape, h.trail, h.canonTrail, h.guideLevel,
    h.order⟩

theorem retrail {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {source dest eventTrail : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest source eventTrail r) :
    FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      dest eventTrail r :=
  ⟨h.loop.retrail htrail, h.escape.retrail htrail, h.trail, h.canonTrail,
    h.guideLevel, h.order⟩

theorem prepend {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st recSt out : SearchSt n} {best mid outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (h : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound recSt out mid
      outBest receiptTrail eventTrail r) :
    FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
      fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.loop.prepend hfixed hpre, h.escape.prepend hpre, h.trail,
    h.canonTrail, h.guideLevel, h.order⟩

end FirstLoopProof

namespace FirstProof

/-- A first-path child that stays at its parent boundary consumes the
selected child.  `NodeEscape` rules out the orbit-pointer arm here: a
deeper first-path loop resolves that arm before returning. -/
theorem cover {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st child out : SearchSt n}
    {outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st none trail)
    (h : FirstProof G ctx tcLevel specFuel runFuel (level + 1) codes fs
      child out (numcells + 1) outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level))
    (hnext : tcell.nextElem cursor = some tv)
    (hoffset : offset < len) (htv : rsLab[tc + offset]! = tv)
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes child
          (numcells + 1)) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) outBest := by
  have hinc := (h.node.outcome.receipt.sound hfuel).grows
  cases h.escape with
  | full eq => exact hinv.cover.advanceKey hnext eq heq
  | first target returned below anchor carrier located =>
      have hle : level ≤ target := by
        apply Int.ofNat_le.mp
        rw [returned] at hstay
        exact Int.not_lt.mp hstay
      have htarget : target = level := by omega
      subst target
      have hrange : tc + len ≤ rsLab.size := by
        rw [hinv.frozenLabSize]
        exact hinv.range
      have hinj : LabInj rsLab rsLab.size := by
        rw [← hinv.baseLab, hinv.baseOk.labSize]
        exact labInj_of_reach hinv.baseOk.labSize hinv.nonempty
          hinv.baseOk.reach
      exact hinv.cover.locatedAnchor hinc hnext anchor located
        (FrameTrail.push_self trail level _) htv hinj hrange (by omega)
  | canon target returned below anchor carrier located =>
      have hle : level ≤ target := by
        apply Int.ofNat_le.mp
        rw [returned] at hstay
        exact Int.not_lt.mp hstay
      have htarget : target = level := by omega
      subst target
      have hrange : tc + len ≤ rsLab.size := by
        rw [hinv.frozenLabSize]
        exact hinv.range
      have hinj : LabInj rsLab rsLab.size := by
        rw [← hinv.baseLab, hinv.baseOk.labSize]
        exact labInj_of_reach hinv.baseOk.labSize hinv.nonempty
          hinv.baseOk.reach
      exact hinv.cover.locatedAnchor hinc hnext anchor located
        (FrameTrail.push_self trail level _) htv hinj hrange (by omega)

/-- After first-child cleanup and recovery, both reference leaves still
lie below the selected guiding child.  Thus the one absorbed child backs
both current-frame reference controls, whichever controls recover to the
parent level. -/
theorem recoverRefs {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len offset tv1 inf : Nat} {fixedpts : VSet n}
    {cs fs : List Nat} {rsLab rsPtn : Array Nat}
    {child out : SearchSt n} {outBest : Option (Key n)}
    {trail eventTrail : FrameTrail} {r : Int}
    (h : FirstProof G ctx tcLevel specFuel runFuel (level + 1) cs fs child
      out (numcells + 1) outBest
      (trail.push level
        ⟨sweepFrame specFuel cs rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hdone : ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells outBest offset)
    (hoff : offset < len) :
    FrameRefs ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (recover n inf level
        { out with fixedpts := fixedpts, gcaFirst := level, stabvertex := tv1 })
      outBest := by
  let entry : TrailEntry :=
    ⟨sweepFrame specFuel cs rsLab rsPtn tc numcells, offset⟩
  have hentry : eventTrail level = some entry :=
    h.node.outcome.preserved.pushAt
  have hfirstReach : cellsPerm rsPtn level rsLab out.firstlab := by
    simpa only [entry, sweepFrame] using
      h.trail.reach level entry (by omega) hentry
  obtain ⟨_, _, _, hfirstAt⟩ :=
    h.trail.picked level entry (by omega) hentry
  have hcanonReach : cellsPerm rsPtn level rsLab out.canonlab := by
    simpa only [entry, sweepFrame] using
      h.canonTrail.reach level entry (by omega) hentry
  obtain ⟨_, _, _, hcanonAt⟩ :=
    h.canonTrail.picked level entry (by omega) hentry
  let cleaned : SearchSt n :=
    { out with fixedpts := fixedpts, gcaFirst := level, stabvertex := tv1 }
  have hframes := recover_frames n inf level cleaned
  have hfirstLab := hframes.2.2.2.2.1
  have hcanonLab := hframes.1
  constructor
  · intro _
    refine ⟨offset, hoff, hdone, ?_, ?_⟩
    · rw [hfirstLab]
      simpa only [entry, sweepFrame] using hfirstAt
    · rw [hfirstLab]
      exact hfirstReach
  · intro _
    refine ⟨offset, hoff, hdone, ?_, ?_⟩
    · rw [hcanonLab]
      simpa only [entry, sweepFrame] using hcanonAt
    · rw [hcanonLab]
      exact hcanonReach

/-- Cleanup, first-control installation, and recovery change neither leaf
reference.  The first trail therefore keeps the current frozen frame,
while the canonical trail can be lowered to the shallower frames of the
enclosing first-path node. -/
theorem recoverTrails {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tv1 inf : Nat} {fixedpts : VSet n}
    {cs fs : List Nat} {child out : SearchSt n} {outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : FirstProof G ctx tcLevel specFuel runFuel (level + 1) cs fs child
      out (numcells + 1) outBest receiptTrail eventTrail r) :
    FirstTrail ctx (level + 1)
        (recover n inf level
          { out with fixedpts := fixedpts, gcaFirst := level, stabvertex := tv1 })
        eventTrail ∧
      CanonTrail ctx level
        (recover n inf level
          { out with fixedpts := fixedpts, gcaFirst := level, stabvertex := tv1 })
        eventTrail := by
  let cleaned : SearchSt n :=
    { out with fixedpts := fixedpts, gcaFirst := level, stabvertex := tv1 }
  have hframes := recover_frames n inf level cleaned
  have hfirst : (recover n inf level cleaned).firstlab = out.firstlab :=
    hframes.2.2.2.2.1
  have hcanon : (recover n inf level cleaned).canonlab = out.canonlab :=
    hframes.1
  constructor
  · exact h.trail.retrail hfirst (TrailExt.refl (level + 1) eventTrail)
  · exact (h.canonTrail.retrail hcanon
      (TrailExt.refl (level + 1) eventTrail)).lower

/-- A completed guiding child installs a located first-reference guide at
its parent frame.  The unconditional first trail supplies both the exact
selected vertex and the cell-permutation reachability that the mutable GCA
control alone cannot recover. -/
theorem setFirstEvent {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len offset tv1 : Nat}
    {cs fs : List Nat} {rsLab rsPtn : Array Nat}
    {child out : SearchSt n} {outBest : Option (Key n)}
    {trail eventTrail : FrameTrail} {r : Int}
    (hpath : cs.length = level)
    (hreturn : r = Int.ofNat level)
    (h : FirstProof G ctx tcLevel specFuel runFuel (level + 1) cs fs child
      out (numcells + 1) outBest
      (trail.push level
        ⟨sweepFrame specFuel cs rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hdone : ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells outBest offset)
    (hlevel : 1 ≤ level) (hls : rsLab.size = n)
    (hlab : LabOk rsLab n) (hps : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = n + 2)
    (hcell : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hoff : offset < len) (hfuel : level + 1 + specFuel ≤ n + 1) :
    EventOut G ctx tcLevel cs fs
      { out with gcaFirst := level, stabvertex := tv1 }
      outBest eventTrail r := by
  let entry : TrailEntry :=
    ⟨sweepFrame specFuel cs rsLab rsPtn tc numcells, offset⟩
  have hentry : eventTrail level = some entry := by
    exact h.node.outcome.preserved.pushAt
  have hreach : cellsPerm rsPtn level rsLab out.firstlab := by
    simpa only [entry, sweepFrame] using
      h.trail.reach level entry (by omega) hentry
  obtain ⟨_, _, _, hat⟩ := h.trail.picked level entry (by omega) hentry
  have hat' : out.firstlab[tc]! = rsLab[tc + offset]! := by
    simpa only [entry, sweepFrame] using hat
  cases hevent : h.node.outcome.event with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      have hcurrent : level < current := by omega
      let g := Guide.ofSweep hlevel hdone hls hlab hps hend hvals hcell
        hrange hoff hfuel hat' event.leafRefs.firstSize
        hreach
      have hlocated : g.Located eventTrail := by
        refine ⟨entry, hentry, ?_⟩
        simp only [g, Guide.ofSweep, Guide.frame, entry, sweepFrame]
      have hguides : GuideStore ctx tcLevel current
          { out with gcaFirst := level, stabvertex := tv1 }
          outBest eventTrail := by
        constructor
        · intro hp hlt
          change 0 < level at hp
          change level < current at hlt
          exact ⟨g, rfl, hlocated⟩
        · intro hp hlt
          exact event.guides.canon hp hlt
      have event' := event.setFirst hguides (by omega) (by omega)
      have hhistory : RefTrail ctx current
          { out with gcaFirst := level, stabvertex := tv1 } eventTrail := by
        constructor
        · exact history.frameSize
        · intro target found htarget hbound hfound
          change target ≤ level at hbound
          exact h.trail.reach target found (by omega) hfound
        · exact history.canon
      have hstable : ReturnStab eventTrail
          (Int.ofNat level)
          { out with gcaFirst := level, stabvertex := tv1 } := by
        have hgca : level ≤ out.gcaFirst := by
          apply h.resumable
          rw [hreturn]
          simp
        have hmin : min r (Int.ofNat out.gcaFirst) =
            Int.ofNat level := by
          rw [hreturn]
          exact Int.min_eq_left (Int.ofNat_le.mpr hgca)
        rw [hmin] at stable
        exact stable.setFirst level tv1
      exact .intro current codes bestCodes event' depth stemEq past returned
        (by simpa [hreturn, Int.min_self] using hstable) hhistory

/-- The final first-path `allsamelevel` adjustment preserves both the
semantic result and the stored first-leaf history. -/
theorem firstFinish {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs fs : List Nat} {st out : SearchSt n} {outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : FirstProof G ctx tcLevel specFuel runFuel level cs fs st out
      numcells outBest receiptTrail eventTrail r) :
  FirstProof G ctx tcLevel specFuel runFuel level cs fs st
      (Nauty.firstFinish level size index out) numcells outBest
      receiptTrail eventTrail r :=
  ⟨h.node.firstFinish hfuel,
    h.escape.firstFinish,
    h.trail.retrail (firstFinish_firstlab level size index out)
      (TrailExt.refl level eventTrail),
    h.canonTrail.retrail (firstFinish_canonlab level size index out)
      (TrailExt.refl level eventTrail),
    fun hr => by
      rw [Nauty.firstFinish]
      split <;> exact h.resumable hr,
    by
      rw [Nauty.firstFinish]
      split <;> exact h.order⟩

end FirstProof

namespace LoopInv

/-- Exhausting first-path loop fuel retains both the semantic event and
the unchanged fixed-point frame.  The outer node later rules this case
out from the cursor-progress bound. -/
theorem firstZero {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv1 index : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tv? cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hcursor : ∀ v, cursor = some v → v < n) :
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
theorem otherZero {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv1 : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tv? cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hcursor : ∀ v, cursor = some v → v < n) :
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
theorem firstDoneProof {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 index : Nat} {tcell : VSet n}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : tcell.nextElem cursor = none)
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
theorem otherDoneProof {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 : Nat} {tcell : VSet n}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : tcell.nextElem cursor = none)
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

namespace OtherLoopProof

/-- The zero-fuel off-path loop preserves the coset cursor literally. -/
theorem zero {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv1 : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tv? cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hcursor : ∀ v, cursor = some v → v < n) :
    OtherLoopProof G ctx tcLevel specFuel runFuel 0 level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).1 := by
  refine ⟨hinv.otherZero hpath hstem hpast hnp hlive hcursor, ?_⟩
  unfold otherChildLoop
  rfl

/-- A positive-fuel loop with no next child likewise returns its state
unchanged. -/
theorem done {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 : Nat} {tcell : VSet n}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : tcell.nextElem cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    OtherLoopProof G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).1 := by
  refine ⟨hinv.otherDoneProof hpath hstem hpast hnext hnp hlive, ?_⟩
  unfold otherChildLoop
  rfl

end OtherLoopProof

namespace FirstLoopProof

/-- A zero-fuel first-path loop is a pending tail and preserves all
first-descent history literally. -/
theorem zero {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv1 index : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tv? cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hcursor : ∀ v, cursor = some v → v < n)
    (hfirst : FirstTrail ctx (level + 1) st trail)
    (hcanon : CanonTrail ctx level st trail)
    (hguide : level ≤ st.gcaFirst) (horder : st.gcaFirst ≤ st.gcaCanon) :
    FirstLoopProof G ctx tcLevel specFuel runFuel 0 level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).1 := by
  refine ⟨hinv.firstZero hpath hstem hpast hnp hlive hcursor, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact .pending (by unfold firstChildLoop; rfl)
  · simpa only [firstChildLoop] using hfirst
  · simpa only [firstChildLoop] using hcanon
  · simpa only [firstChildLoop] using hguide
  · simpa only [firstChildLoop] using horder

/-- A positive-fuel first-path loop with no next child has covered its
fixed specification bound. -/
theorem done {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 index tail : Nat} {tcell : VSet n}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : tcell.nextElem cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hfirst : FirstTrail ctx (level + 1) st trail)
    (hcanon : CanonTrail ctx level st trail)
    (hguide : level ≤ st.gcaFirst) (horder : st.gcaFirst ≤ st.gcaCanon) :
    FirstLoopProof G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).1 := by
  have hloop := hinv.firstDoneProof (inf := inf) (runFuel := runFuel)
    (loopFuel := loopFuel) (tv1 := tv1) (index := index)
    (bound := bound)
    hpath hstem hpast hnext hnp hlive
  have hread : stInc ctx st = best := hinv.run.read (by omega)
  have hreadSome : stInc ctx st = some (incKey ctx bs st.canonlab) :=
    hread.trans hinv.run.incumbent
  have hinstalled : st.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc hreadSome
  have hempty : ∀ o, ¬ ChildLive rsLab tc len tcell cursor o := by
    intro o ho
    exact no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2
  have hfull : best = some (incMax best bound) := by
    rw [hlen] at hinv hempty
    exact hinv.cover.exact_of_read hbound hempty
      (.refl ctx bound best) hinstalled hread
  refine ⟨hloop, .full hfull, ?_, ?_, ?_, ?_⟩
  · simpa only [firstChildLoop] using hfirst
  · simpa only [firstChildLoop] using hcanon
  · simpa only [firstChildLoop] using hguide
  · simpa only [firstChildLoop] using horder

end FirstLoopProof

end Hex.GraphIso.Nauty
