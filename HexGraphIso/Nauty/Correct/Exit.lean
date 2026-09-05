/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.RunInv
import all HexGraphIso.Nauty.Search

public section

/-!
The final corrected mutual induction for the transcribed search, its
comparison-prune producers, and the classification of why a node returned
early.

Local exactness and the reason for an early return are kept separate: a
comparison-frozen or cheap-cell child may be exact at its own node while
still causing its parent loop to skip a suffix.
-/

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
@[expose] def BoundaryOk (G : Colored n k) (ctx : Ctx n)
    (level : Nat) (st : SearchSt n) : Prop :=
  st.noncheaplevel = level →
    PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (fmptn st.lab st.ptn level n).1
      (fmptn st.lab st.ptn level n).2

namespace BoundaryOk

/-- Parking strictly past a loop makes its equality obligation vacuous. -/
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
descent.  Unlike `RefTrail.first`, this history is deliberately independent
of the mutable `gcaFirst` return control: outer first-path loops reset that
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
there; `FrameRefs` owns that changing boundary. -/
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

/-- What a first-path node may export.  A locally absorbed/pruned node
exports its exact maximum; a genuine generator unwind directly names the
first or canonical reference child.  The orbit-pointer arm is resolved by
`firstChildLoop` and is intentionally absent. -/
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
tails may still return `none`; sufficient outer cursor fuel later rules
that arm out. -/
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
while the canonical trail can be lowered to the older frames owned by the
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

/-! Comparison-prune producers for the corrected search outcomes. -/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Below a saved cheap-cell boundary, the current refined node remains in
the small-cell subtree generated at that boundary.  At the boundary itself
the implication is dormant until the executable guard either validates the
shape or parks the boundary at the child. -/
@[expose] def CheapDesc (ctx : Ctx n) (level boundary : Nat)
    (st : RefineSt n) : Prop :=
  boundary < level → SubtreeOk ctx level st

namespace CheapDesc

/-- A boundary created at the current node has no strict descendant
obligation yet. -/
theorem same (ctx : Ctx n) (level : Nat) (st : RefineSt n) :
    CheapDesc ctx level level st := by
  intro h
  omega

/-- At an entered sibling sweep, a saved boundary at or above the current
node supplies the small-cell subtree fact.  A strictly older boundary uses
the inherited descent invariant; equality is exactly the case in which the
current cheap-cell guard must have succeeded. -/
theorem atLevel {ctx : Ctx n} {level boundary : Nat} {st : RefineSt n}
    (h : CheapDesc ctx level boundary st)
    (hit : IterOk ctx level st) (heq : Equitable ctx level st.lab st.ptn)
    (hcount : bcount st.ptn level n = st.numcells)
    (hle : boundary ≤ level)
    (hguard : boundary = level → cheapautom st.ptn level n = true) :
    SubtreeOk ctx level st := by
  rcases Nat.lt_or_eq_of_le hle with hlt | heqBoundary
  · exact h hlt
  · exact subtreeOk_of_cheapautom hit heq hcount
      (hguard heqBoundary)

/-- The executable cheap-cell boundary update carries the small-cell
subtree invariant into every individualized child. -/
theorem child {ctx : Ctx n} {level boundary tc len o : Nat}
    {st : RefineSt n}
    (h : CheapDesc ctx level boundary st)
    (hit : IterOk ctx level st) (heq : Equitable ctx level st.lab st.ptn)
    (hcount : bcount st.ptn level n = st.numcells)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hlvl : level < n)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    let boundary' := if boundary ≥ level ∧
        ¬cheapautom st.ptn level n then level + 1 else boundary
    CheapDesc ctx (level + 1) boundary'
      (childSt ctx level st tc st.lab[tc + o]!) := by
  dsimp only
  let boundary' := if boundary ≥ level ∧
      ¬cheapautom st.ptn level n then level + 1 else boundary
  intro hbelow
  have hparent : SubtreeOk ctx level st := by
    rcases Nat.lt_or_ge boundary level with hold | hge
    · exact h hold
    · have hcheap : cheapautom st.ptn level n = true := by
        rcases hc : cheapautom st.ptn level n with _ | _
        · have hguard : boundary ≥ level ∧
              ¬cheapautom st.ptn level n := ⟨hge, by simp [hc]⟩
          change (if boundary ≥ level ∧
            ¬cheapautom st.ptn level n then level + 1 else boundary) <
              level + 1 at hbelow
          rw [ite_eq_left hguard] at hbelow
          exfalso
          omega
        · rfl
      exact subtreeOk_of_cheapautom hit heq hcount hcheap
  exact subtreeOk_child hparent hlvl hsymm
    (mem_cells_of_isCell (by rw [hit.ok.ptnSize]; exact Nat.le_refl _)
      hit.ok.ptnEnd hcell (by omega)
      (by rw [hit.ok.ptnSize]; exact hrange))
    (by omega) (by omega)

end CheapDesc

namespace FrozenOut

/-- Expose a shorter ancestor prefix while retaining the same frozen
comparison.  This is the transport used as an early return crosses nested
node and loop frames. -/
theorem shrink {ctx : Ctx n} {stem ancestor : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int}
    (h : FrozenOut ctx stem out best r)
    (hprefix : stem.take ancestor.length = ancestor) :
    FrozenOut ctx ancestor out best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  apply FrozenOut.mk current codes bestCodes hcode hdepth
  · have hlen := congrArg List.length hprefix
    simp only [List.length_take] at hlen
    have hle : ancestor.length ≤ stem.length := by omega
    calc
      codes.take ancestor.length =
          (codes.take stem.length).take ancestor.length := by
            rw [List.take_take, Nat.min_eq_left hle]
      _ = ancestor := by rw [hstem, hprefix]
  · exact hinstalled
  · exact hbest
  · exact hfloor

/-- Fixed-point cleanup changes none of a frozen comparison's fields. -/
theorem setFixed {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r)
    (fixedpts : VSet n) :
    FrozenOut ctx stem { out with fixedpts := fixedpts } best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  exact .mk current codes bestCodes hcode hdepth hstem hinstalled hbest
    hfloor

/-- Resetting first-path return controls changes none of a frozen
comparison's fields. -/
theorem setFirst {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r)
    (gcaFirst stabvertex : Nat) :
    FrozenOut ctx stem
      { out with gcaFirst := gcaFirst, stabvertex := stabvertex } best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  exact .mk current codes bestCodes hcode hdepth hstem hinstalled hbest
    hfloor

end FrozenOut

namespace RunPrep

/-- A negative comparison branch whose prune tail stays below the recorded
divergence produces a frozen-code witness without changing the incumbent. -/
theorem frozen {G : Colored n k} {ctx : Ctx n}
    {tcLevel current numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
   
    (h : RunPrep G ctx tcLevel current codes bs fs numcells st best trail)
    (hpath : current = codes.length)
    (hstem : codes.take stem.length = stem)
    (hfirst : st.eqlevFirst ≠ current) (hneg : st.compCanon < 0)
    (hfloor : Int.ofNat st.eqlevCanon.toNat ≤
      pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon) :
    FrozenOut ctx stem (processnode ctx current numcells st).2 best
      (processnode ctx current numcells st).1 := by
  have hcc : st.compCanon = -1 := by
    rcases h.codeInv.tri with hzero |
      ⟨_, _, _, _, _, _, hdown | hup⟩
    · omega
    · exact hdown.1
    · omega
  have hinv := h.codeInv
  rw [hcc] at hinv
  obtain ⟨hr, _, heq, hcode, hcanonlevel, hcanonlab, _, _⟩ :=
    processnode_fast (ctx := ctx) (level := current)
      (numcells := numcells) (st := st) ⟨hfirst, hneg⟩
  apply FrozenOut.mk current codes bs
  · rw [hcode, hcanonlevel, heq]
    exact hinv
  · exact hpath
  · exact hstem
  · exact h.bestCodes
  · rw [hcanonlab]
    exact h.incumbent
  · rw [heq, hr]
    exact hfloor

/-- Every negative off-path leaf prune is either comparison-frozen or a
jump to the saved cheap-cell boundary. -/
theorem pruneMode {G : Colored n k} {ctx : Ctx n}
    {tcLevel current numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
   
    (h : RunPrep G ctx tcLevel current codes bs fs numcells st best trail)
    (hpath : current = codes.length)
    (hstem : codes.take stem.length = stem)
    (hfirst : st.eqlevFirst ≠ current) (hneg : st.compCanon < 0) :
    FrozenOut ctx stem (processnode ctx current numcells st).2 best
        (processnode ctx current numcells st).1 ∨
      (processnode ctx current numcells st).1 =
        Int.ofNat st.noncheaplevel - 1 := by
  have hr := (processnode_fast (ctx := ctx) (level := current)
    (numcells := numcells) (st := st) ⟨hfirst, hneg⟩).1
  rcases pruneReturn_split h.codeInv.eqlev_nonneg with hfloor | hjump
  · exact Or.inl (h.frozen hpath hstem hfirst hneg hfloor)
  · exact Or.inr (hr.trans hjump)

end RunPrep

end Hex.GraphIso.Nauty

/-!
Return classifications for the corrected mutual search induction.

Local exactness and the reason for an early return are deliberately
separate.  A comparison-frozen or cheap-cell child may be exact at its own
node while still causing its parent loop to skip a suffix; the extra
payload is what justifies that skipped suffix.
-/

namespace Hex.GraphIso.Nauty

/-- Two states describe the same recovered search frame at `level` when
their partitions agree and their current labellings differ only within
that partition's cells. -/
structure FrameRel (level : Nat) (st out : SearchSt n) : Prop where
  ptn : out.ptn = st.ptn
  lab : cellsPerm st.ptn level st.lab out.lab

namespace FrameRel

theorem refl (level : Nat) (st : SearchSt n) : FrameRel level st st :=
  ⟨rfl, cellsPerm_refl _ _ _⟩

theorem symm {level : Nat} {st out : SearchSt n}
    (h : FrameRel level st out) : FrameRel level out st := by
  constructor
  · exact h.ptn.symm
  · rw [h.ptn]
    exact cellsPerm_symm h.lab

theorem trans {level : Nat} {a b c : SearchSt n}
    (hab : FrameRel level a b) (hbc : FrameRel level b c) :
    FrameRel level a c := by
  constructor
  · exact hbc.ptn.trans hab.ptn
  · have hbcLab := hbc.lab
    rw [hab.ptn] at hbcLab
    exact cellsPerm_trans hab.lab hbcLab

/-- A recovered `SearchOut` between valid endpoints is exactly a frame
relation. -/
theorem ofSearchOut {G : Colored n k} {level numcells : Nat}
    {st out : SearchSt n} (h : SearchOut G level level st out)
    (hst : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out) : FrameRel level st out :=
  ⟨h.ptnEq hst hout, h.perm⟩

end FrameRel

/-- The guide-control facts preserved by every off-path search fragment.
The second canonical alternative records a newly installed descendant of
the fragment's entry frame. -/
structure GuideRel (level : Nat) (st out : SearchSt n) : Prop where
  first : out.gcaFirst = st.gcaFirst
  order : out.gcaFirst ≤ out.gcaCanon
  canon :
    (out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (level ≤ out.gcaCanon ∧ cellsPerm st.ptn level st.lab out.canonlab)

namespace GuideRel

theorem refl {level : Nat} {st : SearchSt n}
    (horder : st.gcaFirst ≤ st.gcaCanon) : GuideRel level st st :=
  ⟨rfl, horder, Or.inl ⟨rfl, rfl⟩⟩

/-- Guide relations compose across an equivalent recovered frame. -/
theorem trans {level : Nat} {a b c : SearchSt n}
    (hab : GuideRel level a b) (hbc : GuideRel level b c)
    (hframe : FrameRel level a b) : GuideRel level a c := by
  constructor
  · exact hbc.first.trans hab.first
  · exact hbc.order
  · rcases hbc.canon with hold | hnew
    · rw [hold.1, hold.2]
      exact hab.canon
    · right
      refine ⟨hnew.1, ?_⟩
      rw [hframe.ptn] at hnew
      exact cellsPerm_trans hframe.lab hnew.2

end GuideRel

/-- Result of one node call.  `done` is the ordinary one-level return;
`frozen` and `cheap` retain the distinct witnesses needed when the return
crosses more than one loop; `unwind` is reserved for stored generators. -/
inductive NodeExit (ctx : Ctx n) (tcLevel specFuel runFuel level : Nat)
    (codes : List Nat) (st out : SearchSt n) (numcells : Nat)
    (best outBest : Option (Key n)) (trail : FrameTrail) (r : Int) : Prop where
  | done
      (returned : r = Int.ofNat level - 1)
      (exact : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level codes st numcells)))
  | unwind (target : Nat)
      (returned : r = Int.ofNat target) (below : target < level)
      (sound : NodeSound ctx tcLevel specFuel level codes st numcells
        best outBest)
      (payload : Unwind ctx tcLevel target out outBest)
      (located : payload.Located trail)
      (control : target = out.gcaFirst ∨ target = out.gcaCanon)
  | frozen
      (below : r < Int.ofNat level)
      (exact : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level codes st numcells)))
      (freeze : FrozenOut ctx codes out outBest r)
  | cheap (boundary : Nat)
      (returned : r = Int.ofNat boundary - 1)
      (positive : 1 ≤ boundary) (atOrAbove : boundary ≤ level)
      (saved : out.noncheaplevel = boundary)
      (exact : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level codes st numcells)))
  | exhausted
      (returned : r = 0) (state : out = st) (incumbent : outBest = best)
      (emptyFuel : runFuel = 0)

/-- Provenance of the newest workspace pair while the one-shot
`needshortprune` request is live.  Explicit code-two pairs are already
valid at their returned frame.  Implicit cheap-cell pairs retain root
validity and the deeper boundary needed to localize them when the return
reaches its receiving loop. -/
inductive ShortSource (G : Colored n k) (ctx : Ctx n) (out : SearchSt n)
    (trail : FrameTrail) (r : Int) : Prop where
  | explicit (target : Nat) (fix mcr : VSet n)
      (returned : r = Int.ofNat target)
      (back : out.autos.back? = some (fix, mcr))
      (valid : ∀ entry, trail target = some entry →
        PairOk ctx.g entry.frame.rsPtn entry.frame.rsLab target
          fix mcr)
  | implicit (target : Nat)
      (returned : r = Int.ofNat target)
      (below : target < out.noncheaplevel)
      (back : out.autos.back? = some
        (fmptn out.lab out.ptn out.noncheaplevel n))
      (root : PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1
        (fmptn out.lab out.ptn out.noncheaplevel n).1
        (fmptn out.lab out.ptn out.noncheaplevel n).2)

namespace ShortSource

/-- Fixed-point cleanup after a child return does not affect the stored
pair or its source evidence. -/
theorem setFixed {G : Colored n k} {ctx : Ctx n} {out : SearchSt n}
    {trail : FrameTrail} {r : Int}
    (h : ShortSource G ctx out trail r) (fixedpts : VSet n) :
    ShortSource G ctx { out with fixedpts := fixedpts } trail r := by
  cases h with
  | explicit target fix mcr returned back valid =>
      exact .explicit target fix mcr returned back valid
  | implicit target returned below back root =>
      exact .implicit target returned below back root

/-- The final first-path counter adjustment changes none of the fields
used by a live short-prune source. -/
theorem firstFinish {G : Colored n k} {ctx : Ctx n} {out : SearchSt n}
    {trail : FrameTrail} {r : Int} {level size index : Nat}
    (h : ShortSource G ctx out trail r) :
    ShortSource G ctx (Nauty.firstFinish level size index out) trail r := by
  rw [Nauty.firstFinish]
  split
  · cases h with
    | explicit target fix mcr returned back valid =>
        exact .explicit target fix mcr returned back valid
    | implicit target returned below back root =>
        exact .implicit target returned below back root
  · exact h

end ShortSource

namespace NodeExit

/-- Every result of a positive-level node lies strictly below that node's
level.  This is the one-step bound that lets a receiving loop identify an
explicit or implicit short-prune source with its own level. -/
theorem below {ctx : Ctx n} {tcLevel specFuel runFuel level numcells : Nat}
    {codes : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
      best outBest trail r) (hlevel : 0 < level) :
    r < Int.ofNat level := by
  cases h with
  | done returned exact => rw [returned]; omega
  | unwind target returned below sound payload located control =>
      rw [returned]
      exact Int.ofNat_lt.mpr below
  | frozen below exact freeze => exact below
  | cheap boundary returned positive atOrAbove saved exact =>
      rw [returned]
      simp only [Int.ofNat_eq_natCast]
      omega
  | exhausted returned state incumbent emptyFuel =>
      rw [returned]
      exact Int.natCast_pos.mpr hlevel

/-- The final first-path counter adjustment preserves every corrected node
exit, including the payload of a located unwind. -/
theorem firstFinish {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {codes : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
      best outBest trail r) :
    NodeExit ctx tcLevel specFuel runFuel level codes st
      (Nauty.firstFinish level size index out) numcells best outBest trail
      r := by
  cases h with
  | done returned exact => exact .done returned exact
  | unwind target returned below sound payload located control =>
      apply NodeExit.unwind target returned below sound payload.firstFinish
        located.firstFinish
      unfold Nauty.firstFinish
      split <;> exact control
  | frozen below exact freeze =>
      apply NodeExit.frozen below exact
      rw [Nauty.firstFinish]
      split
      · cases freeze with
        | mk current cs bs codeInv depth stemEq installed incumbent floor =>
            exact .mk current cs bs codeInv depth stemEq installed incumbent
              floor
      · exact freeze
  | cheap boundary returned positive atOrAbove saved exact =>
      apply NodeExit.cheap boundary returned positive atOrAbove
      · unfold Nauty.firstFinish
        split <;> exact saved
      · exact exact
  | exhausted returned state incumbent emptyFuel =>
      exact (hfuel emptyFuel).elim

end NodeExit

/-- Result of a sibling loop.  Early comparison and cheap-cell exits carry
both the exact loop maximum and the payload required to cross an older
frame.  Cursor-fuel exhaustion remains explicit and cannot be confused
with completion. -/
inductive LoopExit (ctx : Ctx n) (tcLevel specFuel runFuel loopFuel level : Nat)
    (codes : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n)) (trail : FrameTrail)
    (r : Option Int) : Prop where
  | done
      (returned : r = none)
      (exact : outBest = some (incMax best bound))
  | unwind (target : Nat)
      (returned : r = some (Int.ofNat target)) (below : target < level)
      (sound : LoopSound ctx bound best outBest)
      (payload : Unwind ctx tcLevel target out outBest)
      (located : payload.Located trail)
      (control : target = out.gcaFirst ∨ target = out.gcaCanon)
  | frozen (value : Int)
      (returned : r = some value)
      (below : value < Int.ofNat level)
      (exact : outBest = some (incMax best bound))
      (freeze : FrozenOut ctx codes out outBest value)
  | cheap (boundary : Nat)
      (returned : r = some (Int.ofNat boundary - 1))
      (positive : 1 ≤ boundary) (below : boundary ≤ level)
      (saved : out.noncheaplevel = boundary)
      (exact : outBest = some (incMax best bound))
  | exhausted
      (returned : r = none) (finalCursor : Option Nat)
      (progress : cursorRank cursor + loopFuel ≤ cursorRank finalCursor)
      (bounded : ∀ v, finalCursor = some v → v < n)

/-- Concrete node result paired with the corrected return classification.
The event and trail clauses are independent of the semantic maximum and
remain reusable from the established leaf machinery. -/
structure NodeRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (codes fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  exit : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
    best outBest receiptTrail r
  event : EventOut G ctx tcLevel codes fs out outBest eventTrail r
  preserved : TrailExt level receiptTrail eventTrail
  fixed : out.fixedpts = st.fixedpts
  short : out.needshortprune = true →
    ShortSource G ctx out eventTrail r

/-- Off-path nodes additionally preserve the first-path control and coset
cursor needed by their enclosing sibling loop. -/
structure OtherRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (codes fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  node : NodeRun G ctx tcLevel specFuel runFuel level codes fs st out
    numcells best outBest receiptTrail eventTrail r
  firstGuide : out.gcaFirst = st.gcaFirst
  order : out.gcaFirst ≤ out.gcaCanon
  canonGuide :
    (out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (level ≤ out.gcaCanon ∧ cellsPerm st.ptn level st.lab out.canonlab)
  coset : out.cosetindex = st.cosetindex

/-- A sibling-loop proof paired with its corrected exit reason.  The
established proof retains coverage, event, and recovery facts; `exit`
separately records why an unfinished suffix is nevertheless absorbed. -/
structure LoopRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  proof : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
    fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail eventTrail r
  exit : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
    rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail r
  short : out.needshortprune = true → ∃ value,
    r = some value ∧ ShortSource G ctx out eventTrail value

/-- An off-path sibling sweep additionally retains its coset cursor. -/
structure OtherLoopRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  proof : OtherLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
    codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
    outBest receiptTrail eventTrail r
  exit : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
    rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail r
  short : out.needshortprune = true → ∃ value,
    r = some value ∧ ShortSource G ctx out eventTrail value

/-- The first-path sibling sweep retains both reference histories in its
established proof and the corrected reason for abandoning any suffix. -/
structure FirstLoopRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  proof : FirstLoopProof G ctx tcLevel specFuel runFuel loopFuel level stem
    codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
    outBest receiptTrail eventTrail r
  exit : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
    rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail r
  short : out.needshortprune = true → ∃ value,
    r = some value ∧ ShortSource G ctx out eventTrail value

namespace NodeRun

/-- A corrected node run can be viewed through the older local outcome
interface.  This conversion is safe at one node: both early exit variants
already carry exactness for that node.  What is deliberately not recovered
is the old loop rule that treated such an exit as coverage of every later
sibling. -/
theorem toOutcome {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : NodeRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeOutcome G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r := by
  have hreceipt : NodeReceipt receiptTrail ctx tcLevel specFuel runFuel
      level codes st out numcells best outBest r := by
    cases h.exit with
    | done returned exact =>
        apply NodeReceipt.complete (NodeSound.ofExact exact) returned
        · exact canonlevel_ne_zero_of_stInc (h.event.read.trans exact)
        · exact h.event.read
        · exact exact
    | unwind target returned below sound payload located control =>
        exact NodeReceipt.unwind sound target returned below payload located
    | frozen below exact freeze =>
        apply NodeReceipt.pruned (NodeSound.ofExact exact) r rfl below
        · exact canonlevel_ne_zero_of_stInc (h.event.read.trans exact)
        · exact h.event.read
        · exact exact
    | cheap boundary returned positive atOrAbove saved exact =>
        apply NodeReceipt.pruned (NodeSound.ofExact exact) r rfl
        · rw [returned]
          simp only [Int.ofNat_eq_natCast]
          omega
        · exact canonlevel_ne_zero_of_stInc (h.event.read.trans exact)
        · exact h.event.read
        · exact exact
    | exhausted returned state incumbent emptyFuel =>
        exact NodeReceipt.exhausted emptyFuel returned state incumbent
  exact ⟨hreceipt, h.event, h.preserved⟩

/-- Restore the established result interface used by the invariant
transport lemmas after the corrected exit has been classified. -/
theorem toProof {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : NodeRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeProof G ctx tcLevel specFuel runFuel level codes fs st out numcells
      best outBest receiptTrail eventTrail r :=
  ⟨h.toOutcome, h.fixed⟩

end NodeRun

namespace OtherRun

/-- Forget the semantic receipt and expose the off-path guide relation. -/
theorem guide {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : OtherRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    GuideRel level st out :=
  ⟨h.firstGuide, h.order, h.canonGuide⟩

/-- Restore the established off-path interface for ordinary parent-level
consumption and recovery. -/
theorem toProof {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : OtherRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    OtherProof G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r :=
  ⟨⟨h.node.toOutcome, h.firstGuide, h.order, h.canonGuide⟩,
    h.node.fixed, h.coset⟩

end OtherRun

namespace LoopExit

/-- Changing only the mutable live set leaves an already classified loop
exit unchanged. -/
theorem reindexSet {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tc len numcells : Nat}
    {tcell tcell' : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Option Int}
    (h : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest trail r) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell' cursor bound st out best outBest trail r := by
  cases h with
  | done returned exact => exact .done returned exact
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below sound payload located control
  | frozen value returned below exact freeze =>
      exact .frozen value returned below exact freeze
  | cheap boundary returned positive below saved exact =>
      exact .cheap boundary returned positive below saved exact
  | exhausted returned finalCursor progress bounded =>
      exact .exhausted returned finalCursor progress bounded

/-- One processed cursor step increases both the loop fuel and its
starting-rank budget. -/
theorem step {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv tc len numcells : Nat} {tcell : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
      rsPtn tc len numcells tcell (some tv) bound st out best outBest trail
      r) :
    LoopExit ctx tcLevel specFuel runFuel (loopFuel + 1) level codes rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest trail r := by
  cases h with
  | done returned exact => exact .done returned exact
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below sound payload located control
  | frozen value returned below exact freeze =>
      exact .frozen value returned below exact freeze
  | cheap boundary returned positive below saved exact =>
      exact .cheap boundary returned positive below saved exact
  | exhausted returned finalCursor progress bounded =>
      apply LoopExit.exhausted returned finalCursor
      · have hrank := cursorRank_step ha
        omega
      · exact bounded

/-- A sound processed child changes only the incoming incumbent of the
classified recursive tail. -/
theorem prepend {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tc len numcells : Nat} {tcell : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {trail : FrameTrail} {r : Option Int}
    (hpre : LoopSound ctx bound best mid)
    (h : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
      rsPtn tc len numcells tcell cursor bound recSt out mid outBest trail
      r) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell cursor bound st out best outBest trail r := by
  cases h with
  | done returned exact =>
      exact .done returned
        ((hpre.trans (LoopSound.ofExact exact)).exact exact
          (keyLe_incMax_right mid bound))
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below (hpre.trans sound) payload located
        control
  | frozen value returned below exact freeze =>
      exact .frozen value returned below
        ((hpre.trans (LoopSound.ofExact exact)).exact exact
          (keyLe_incMax_right mid bound)) freeze
  | cheap boundary returned positive below saved exact =>
      exact .cheap boundary returned positive below saved
        ((hpre.trans (LoopSound.ofExact exact)).exact exact
          (keyLe_incMax_right mid bound))
  | exhausted returned finalCursor progress bounded =>
      exact .exhausted returned finalCursor progress bounded

/-- At a small-cell node, exactness of the selected child is exactness of
the whole sibling sweep, so the saved-boundary return remains a cheap exit
after fixed-point cleanup. -/
theorem ofCheap {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level boundary tc len numcells : Nat} {tcell fixedpts : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound childKey : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail}
    (hboundary : 1 ≤ boundary) (hbelow : boundary ≤ level)
    (hsaved : out.noncheaplevel = boundary)
    (hbound : bound = childKey)
    (hexact : outBest = some (incMax best childKey)) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell cursor bound st { out with fixedpts := fixedpts }
      best outBest trail (some (Int.ofNat boundary - 1)) := by
  apply LoopExit.cheap boundary rfl hboundary hbelow
  · simpa only using hsaved
  rwa [hbound]

/-- An early frozen child absorbs both the explored prefix and every live
suffix child, yielding the exact loop maximum while retaining the frozen
payload for the next enclosing frame. -/
theorem ofFrozen {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tail tc len numcells : Nat} {tcell fixedpts : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail} {value : Int}
    (hfreeze : FrozenOut ctx codes out outBest value)
    (hlevel : level = codes.length) (hbelow : value < Int.ofNat level)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1)
    (hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc
      len numcells tcell cursor outBest)
    (hsound : LoopSound ctx bound best outBest) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell cursor bound st { out with fixedpts := fixedpts }
      best outBest trail (some value) := by
  have hfreeze' := hfreeze.setFixed fixedpts
  apply LoopExit.frozen value rfl hbelow
  · rw [hlen] at hcover
    exact hfreeze.exactLoop hlevel hbelow hbound hcover hsound
  · exact hfreeze'

/-- Convert an integer-valued loop exit to the enclosing node, shortening
the frozen comparison prefix at the node boundary. -/
theorem toNodeSome {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail} {value : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail (some value)) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail value := by
  cases h with
  | done returned => cases returned
  | unwind target returned below sound payload located control =>
      refine NodeExit.unwind (target := target)
        (returned := Option.some.inj returned) (below := below)
        (sound := ?_) (payload := payload) located control
      constructor
      · intro b hb
        rw [← hbound]
        exact sound.upper b hb
      · exact sound.grows
  | frozen value returned below exact freeze =>
      cases Option.some.inj returned
      apply NodeExit.frozen
      · exact below
      · simpa only [← hbound] using exact
      · exact (freeze.shrink hprefix)
  | cheap boundary returned positive below saved exact =>
      apply NodeExit.cheap boundary (Option.some.inj returned) positive below
      · exact saved
      simpa only [← hbound] using exact
  | exhausted returned => cases returned

/-- With nonzero cursor fuel, a `none` loop result is genuine completion
and supplies the enclosing node's ordinary one-level return. -/
theorem toNodeNone {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hfuel : n < cursorRank cursor + loopFuel)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail none) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail (Int.ofNat level - 1) := by
  cases h with
  | done _ exact =>
      apply NodeExit.done rfl
      simpa only [← hbound] using exact
  | unwind _ returned => cases returned
  | frozen _ returned => cases returned
  | cheap _ returned => cases returned
  | exhausted _ finalCursor progress bounded =>
      exact (LoopResult.exhaustion_false hfuel progress bounded).elim

end LoopExit

namespace RunPrep

/-- A fresh request from the frozen-downward `processnode` arm records
the implicit pair admitted at the saved cheap-cell boundary. -/
theorem fastSource {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hbound : st.noncheaplevel ≤ level)
    (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0)
    (hclear : st.needshortprune = false)
    (hshort : (processnode ctx level numcells st).2.needshortprune = true) :
    ShortSource G ctx (processnode ctx level numcells st).2 trail
      (processnode ctx level numcells st).1 := by
  let value := pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon
  have hnonneg : 0 ≤ value :=
    pruneReturn_nonneg h.cheap.positive h.codeInv.eqlev_nonneg
  have hne : level ≠ st.noncheaplevel :=
    processnode_fast_short_ne hg hclear hshort
  apply ShortSource.implicit value.toNat
  · rw [(processnode_fast hg).1]
    exact (Int.toNat_of_nonneg hnonneg).symm
  · rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.2.1]
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg hnonneg]
    exact pruneReturn_lt
  · rw [processnode_fast_autos hg]
    have hback := pruneAutos_back h.workspace hne
    rw [(processnode_frames ctx level numcells st).1,
      (processnode_frames ctx level numcells st).2.1,
      (processnode_frames ctx level numcells st).2.2.2.2.2.2.2.1]
    exact hback
  · rw [(processnode_frames ctx level numcells st).1,
      (processnode_frames ctx level numcells st).2.1,
      (processnode_frames ctx level numcells st).2.2.2.2.2.2.2.1]
    exact h.cheap.ready hbound hne

end RunPrep

namespace NodeInv

/-- A negative, non-generator discrete leaf produces the corrected exit:
ordinary comparison pruning retains its frozen prefix, while the only
remaining return is the explicit cheap-cell jump. -/
theorem negativeLeaf {G : Colored n k} {ctx : Ctx n}
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
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hgen : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  obtain ⟨outBest, houtcome, hexact⟩ := hnode.plainLeaf
    (inf := inf) (specFuel := specFuel) (fuel := fuel) hn0
    hsymm hloop hlevel hpath hcheap hnum hdisc hef hgen hearly hlive
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hfirstNe : leaf.eqlevFirst ≠ level := by
    intro heq
    apply hef
    simp only [leaf, heq, beq_self_eq_true]
  have hmode := hprep.pruneMode hfull hstem hfirstNe hneg
  have hexit : NodeExit ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    rcases hmode with hfreeze | hjump
    · rw [hout]
      apply NodeExit.frozen hearly hexact
      have hreadOut : stInc ctx (processnode ctx level n leaf).2 =
          outBest := by
        rw [← hout]
        exact houtcome.event.read
      have hsame : best = outBest := hfreeze.read.symm.trans hreadOut
      rw [← hsame]
      simpa only [leaf] using hfreeze
    · apply NodeExit.cheap leaf.noncheaplevel
      · rw [hout]
        exact hjump
      · exact hprep.cheap.positive
      · exact hcheap'
      · rw [hout]
        exact (processnode_frames ctx level n leaf).2.2.2.2.2.2.2.1
      · exact hexact
  refine ⟨outBest, ?_⟩
  exact {
    exit := hexit
    event := houtcome.event
    preserved := houtcome.preserved
    fixed := otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
      numcells st hnum hearly
    short := by
      rw [hout]
      intro hshort
      apply hprep.fastSource hcheap' ⟨hfirstNe, hneg⟩
        (by rw [otherLeafSt_short, hnode.shortClear]) hshort }

/-- An early off-path leaf also preserves the guide and coset fields used
when its unwind stops at the immediately enclosing sibling loop. -/
theorem earlyOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best outBest : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hrun : NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs
      st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  let leaf := otherLeafSt ctx level numcells st
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hprep := hnode.run.otherLeaf hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hfirst : (processnode ctx level n leaf).2.gcaFirst =
      st.gcaFirst :=
    (processnode_frames ctx level n leaf).2.2.2.2.2.2.1 |>.trans
      (by simpa only [leaf] using
        (RefTrail.otherLeaf_gcaFirst ctx level numcells st))
  have horder : (processnode ctx level n leaf).2.gcaFirst ≤
      (processnode ctx level n leaf).2.gcaCanon :=
    (hlive'.processnode (by simpa only [leaf] using hprep.trailOk)
      (by simpa only [leaf] using hprep.firstBound)).2
  have hleafCanonGca : leaf.gcaCanon = st.gcaCanon := by
    simpa only [leaf] using
      (RefTrail.otherLeaf_gcaCanon ctx level numcells st)
  have hleafCanonLab : leaf.canonlab = st.canonlab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    change (otherNodePrep level rs.longcode base).canonlab = st.canonlab
    rw [(otherNodePrep_frames level rs.longcode base).1]
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    change (otherNodePrep level rs.longcode base).lab = rs.lab
    exact (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hcanon :
      ((processnode ctx level n leaf).2.gcaCanon = st.gcaCanon ∧
          (processnode ctx level n leaf).2.canonlab = st.canonlab) ∨
        (level ≤ (processnode ctx level n leaf).2.gcaCanon ∧
          cellsPerm st.ptn level st.lab
            (processnode ctx level n leaf).2.canonlab) := by
    rcases processnode_canonGuide ctx level n leaf with hold | hnew
    · exact Or.inl ⟨hold.1.trans hleafCanonGca,
        hold.2.trans hleafCanonLab⟩
    · right
      constructor
      · rw [hnew.1]
        exact Nat.le_refl level
      · rw [hnew.2, hleafLab]
        exact (refine_refInv (ctx := ctx)
          (by
            rw [hnode.run.searchOk.ptnSize]
            exact Nat.le_refl n)
          (hnode.run.searchOk.labSize.trans
            hnode.run.searchOk.ptnSize.symm)
          (searchOk_end hn0 hnode.run.searchOk hlevel)).perm
  exact {
    node := hrun
    firstGuide := by rw [hout]; exact hfirst
    order := by rw [hout]; exact horder
    canonGuide := by rw [hout]; exact hcanon
    coset := by
      rw [hout]
      exact (processnode_coset ctx level n leaf).trans
        (by simpa only [leaf] using
          (OtherProof.otherLeafSt_coset ctx level numcells st)) }

/-- A code-one automorphism leaf returns the stored first-path unwind,
with all off-path control fields retained for the enclosing sibling loop. -/
theorem firstOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hnp : (otherLeafSt ctx level numcells st).compCanon ≤ 0)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true)
    (hsent : (otherLeafSt ctx level numcells st).firstcode[level + 1]! =
      codeSentinel)
    (hpass : isautom ctx (firstScatter n
      (otherLeafSt ctx level numcells st).firstlab
      (otherLeafSt ctx level numcells st).lab) = true)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  obtain ⟨houtcome, target, hreturned, hbelow, hcontrol, payload, hloc⟩ :=
    hnode.firstLeaf (inf := inf) (specFuel := specFuel) (fuel := fuel)
      hn0 hgsz hsymm hloop hlevel hpath hnum hnp heq hsent hpass
      hlive
  let leaf := otherLeafSt ctx level numcells st
  have hfirstBelow : leaf.gcaFirst < level := by
    change (otherLeafSt ctx level numcells st).gcaFirst < level
    rw [RefTrail.otherLeaf_gcaFirst]
    exact hnode.firstBelow
  have hreturn := (processnode_auto (ctx := ctx) (level := level)
    (numcells := n) (st := leaf) heq hsent (by simp) hpass).1
  have hearly : (processnode ctx level n leaf).1 <
      Int.ofNat level := by
    rw [hreturn]
    exact Int.ofNat_lt.mpr hfirstBelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hrun : NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := {
    exit := NodeExit.unwind target hreturned hbelow
      (NodeSound.refl ctx tcLevel (specFuel + 1) level codes st numcells
        best)
      payload hloc hcontrol
    event := houtcome.event
    preserved := houtcome.preserved
    fixed := otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
      numcells st hnum hearly
    short := by
      intro hshort
      rw [hout] at hshort
      have hleafClear : leaf.needshortprune = false := by
        rw [otherLeafSt_short, hnode.shortClear]
      rw [processnode_auto_short heq hsent (by simp) hpass,
        hleafClear] at hshort
      cases hshort }
  exact hnode.earlyOther hn0 hlevel hpath hnum hearly hlive hrun

/-- A code-two row tie returns either its canonical guide or its
first-ancestor orbit guide, retaining the chosen unwind explicitly. -/
theorem tiedOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hcc : (otherLeafSt ctx level numcells st).compCanon = 0)
    (hge : ¬(level < (otherLeafSt ctx level numcells st).canonlevel))
    (htie : (testcanlab ctx (updatecan ctx
      (otherLeafSt ctx level numcells st).canong
      (otherLeafSt ctx level numcells st).canonlab
      (otherLeafSt ctx level numcells st).samerows)
      (otherLeafSt ctx level numcells st).lab).1 = 0)
    (hcoset : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.cosetindex < n)
    (horbit : OrbSound (OrbConn (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace.toList n)
      (processnode ctx level n
        (otherLeafSt ctx level numcells st)).2.orbits n)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  obtain ⟨houtcome, target, hreturned, hbelow, hcontrol, payload, hloc⟩ :=
    hnode.tiedLeaf (inf := inf) (specFuel := specFuel) (fuel := fuel)
      hn0 hgsz hsymm hloop hlevel hpath hcheap hnum hef hcc hge
      htie hcoset horbit hlive
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcanonBelow : leaf.gcaCanon < level := by
    change (otherLeafSt ctx level numcells st).gcaCanon < level
    rw [RefTrail.otherLeaf_gcaCanon]
    exact hnode.canonBelow
  have hfirstBelow : leaf.gcaFirst < level :=
    Nat.lt_of_le_of_lt hlive'.order hcanonBelow
  have hreturns := (processnode_rowTie (ctx := ctx) (level := level)
    (numcells := n) (st := leaf) hef (by simp) hcc hge htie).1
  have hearly : (processnode ctx level n leaf).1 <
      Int.ofNat level := by
    rcases hreturns with hfirst | hcanon
    · rw [hfirst]
      exact Int.ofNat_lt.mpr hfirstBelow
    · rw [hcanon]
      exact Int.ofNat_lt.mpr hcanonBelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hrun : NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := {
    exit := NodeExit.unwind target hreturned hbelow
      (NodeSound.refl ctx tcLevel (specFuel + 1) level codes st numcells
        best)
      payload hloc hcontrol
    event := houtcome.event
    preserved := houtcome.preserved
    fixed := otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
      numcells st hnum hearly
    short := by
      rw [hout]
      intro hshort
      have hleafClear : leaf.needshortprune = false := by
        rw [otherLeafSt_short, hnode.shortClear]
      apply ShortSource.explicit leaf.gcaCanon
        (fmperm (canonScatter n leaf.canonlab leaf.lab) n).1
        (fmperm (canonScatter n leaf.canonlab leaf.lab) n).2
      · exact processnode_rowTie_short hef (by simp) hcc hge htie
          hleafClear hshort
      · exact hprep.rowTieBack hef (by simp) hcc hge htie
      · intro entry hentry
        exact hlive'.rowTiePair hn0 hprep hcanonBelow htie hentry }
  exact hnode.earlyOther hn0 hlevel hpath hnum hearly hlive hrun

/-- The negative non-generator leaf, with the off-path fields needed by
its parent loop retained. -/
theorem negativeOther {G : Colored n k} {ctx : Ctx n}
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
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hgen : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  obtain ⟨outBest, hrun⟩ := hnode.negativeLeaf
    (inf := inf) (specFuel := specFuel) (fuel := fuel) hn0 hsymm
    hloop hlevel hpath hcheap hnum hdisc hef hneg hgen hearly hlive
  exact ⟨outBest, hnode.earlyOther hn0 hlevel hpath hnum hearly
    hlive hrun⟩

/-- A non-generator leaf whose return remains at the current boundary is
an ordinary exact off-path node run. -/
theorem doneLeaf {G : Colored n k} {ctx : Ctx n}
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
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hgen : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hdone : ¬((processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  obtain ⟨outBest, houtcome, hexact⟩ := hnode.plainLeafDone
    (inf := inf) (specFuel := specFuel) (fuel := fuel) hn0 hsymm
    hloop hlevel hpath hcheap hnum hdisc hef hgen hdone hlive
  let leaf := otherLeafSt ctx level numcells st
  let final := leafFinish level (processnode ctx level n leaf).2
  have hout := otherNode_leaf_done_state ctx inf tcLevel fuel level
    numcells st hnum hdone
  have hfirstProc : (processnode ctx level n leaf).2.gcaFirst =
      leaf.gcaFirst :=
    (processnode_frames ctx level n leaf).2.2.2.2.2.2.1
  have hfirstLeaf : leaf.gcaFirst = st.gcaFirst := by
    simpa only [leaf] using
      (RefTrail.otherLeaf_gcaFirst ctx level numcells st)
  have hfirst : final.gcaFirst = st.gcaFirst := by
    have heq : final.gcaFirst =
        (processnode ctx level n leaf).2.gcaFirst := by
      unfold final
      rw [leafFinish]
      split <;> split <;> rfl
    exact heq.trans (hfirstProc.trans hfirstLeaf)
  have horderProc : (processnode ctx level n leaf).2.gcaFirst ≤
      (processnode ctx level n leaf).2.gcaCanon :=
    (hlive.otherLeaf (numcells := numcells) |>.processnode
      (by simpa only [leaf] using
        (hnode.run.otherLeaf hn0 hlevel hpath).trailOk)
      (by simpa only [leaf] using
        (hnode.run.otherLeaf hn0 hlevel hpath).firstBound)).2
  have horder : final.gcaFirst ≤ final.gcaCanon := by
    have hfirstEq : final.gcaFirst =
        (processnode ctx level n leaf).2.gcaFirst := by
      unfold final
      rw [leafFinish]
      split <;> split <;> rfl
    have hcanonEq : final.gcaCanon =
        (processnode ctx level n leaf).2.gcaCanon := by
      unfold final
      rw [leafFinish]
      split <;> split <;> rfl
    rw [hfirstEq, hcanonEq]
    exact horderProc
  have hcanonGca : final.gcaCanon =
      (processnode ctx level n leaf).2.gcaCanon := by
    unfold final
    rw [leafFinish]
    split <;> split <;> rfl
  have hcanonLab : final.canonlab =
      (processnode ctx level n leaf).2.canonlab := by
    unfold final
    rw [leafFinish]
    split <;> split <;> rfl
  have hleafCanonGca : leaf.gcaCanon = st.gcaCanon := by
    simpa only [leaf] using
      (RefTrail.otherLeaf_gcaCanon ctx level numcells st)
  have hleafCanonLab : leaf.canonlab = st.canonlab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    change (otherNodePrep level rs.longcode base).canonlab = st.canonlab
    rw [(otherNodePrep_frames level rs.longcode base).1]
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    change (otherNodePrep level rs.longcode base).lab = rs.lab
    exact (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hcanon :
      (final.gcaCanon = st.gcaCanon ∧ final.canonlab = st.canonlab) ∨
        (level ≤ final.gcaCanon ∧
          cellsPerm st.ptn level st.lab final.canonlab) := by
    rcases processnode_canonGuide ctx level n leaf with hold | hnew
    · left
      exact ⟨hcanonGca.trans (hold.1.trans hleafCanonGca),
        hcanonLab.trans (hold.2.trans hleafCanonLab)⟩
    · right
      constructor
      · rw [hcanonGca, hnew.1]
        exact Nat.le_refl level
      · rw [hcanonLab, hnew.2, hleafLab]
        exact (refine_refInv (ctx := ctx)
          (by
            rw [hnode.run.searchOk.ptnSize]
            exact Nat.le_refl n)
          (hnode.run.searchOk.labSize.trans
            hnode.run.searchOk.ptnSize.symm)
          (searchOk_end hn0 hnode.run.searchOk hlevel)).perm
  have hother : OtherOutcome G ctx tcLevel (specFuel + 1) (fuel + 1)
      level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := {
    node := houtcome
    firstGuide := by rw [hout]; exact hfirst
    order := by rw [hout]; exact horder
    canonGuide := by rw [hout]; exact hcanon }
  have hproof := OtherProof.ofLeafDone hnum hdone hother
  refine ⟨outBest, ?_⟩
  exact {
    node := {
      exit := NodeExit.done (congrArg Prod.fst hout) hexact
      event := houtcome.event
      preserved := houtcome.preserved
      fixed := hproof.fixed
      short := by
        intro hshort
        rw [hout, leafFinish_short] at hshort
        cases hshort }
    firstGuide := hproof.outcome.firstGuide
    order := hproof.outcome.order
    canonGuide := hproof.outcome.canonGuide
    coset := hproof.coset }

end NodeInv

end Hex.GraphIso.Nauty
