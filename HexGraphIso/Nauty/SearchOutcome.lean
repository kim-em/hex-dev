/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.LoopCoverage
public import HexGraphIso.Nauty.QuartetStmt
public import HexGraphIso.Nauty.AutosLedger
import all HexGraphIso.Nauty.OrbJoin
import all HexGraphIso.Nauty.EquitableStep
import HexGraphIso.Nauty.QuartetLoop

public section

/-!
Outcome types for the verified search refinement.

The return integer alone does not distinguish a completed sweep, a
generator unwind, a comparison prune, and exhausted loop fuel.  In
particular, an unwind to `level - 1` has the same integer as ordinary
node completion.  The indexed types below keep those cases separate and
also keep logical specification fuel distinct from the two runtime fuels.

A generator or comparison unwind carries the ancestor child it has already
shown to be bounded by the incumbent.  Intermediate calls merely transport
that anchor.  At its indexed target loop, the anchor becomes ordinary child
coverage and the sweep continues.
-/

namespace Hex.GraphIso.Nauty

/-- A checked generator maps one labelling pointwise onto another. -/
@[expose] def LabelCarrier (ctx : Ctx) (ref cur : Array Nat)
    (store : Array (Array Nat)) : Prop :=
  ∃ γ ∈ store, checkAutom ctx.g γ ctx.n = true ∧
    ∀ i, i < ctx.n → γ[ref[i]!]! = cur[i]!

/-- At a valid leaf event, either no generator is recorded or the output
store contains a checked carrier from the first or incumbent leaf. -/
theorem processnode_labelCarrier {G : Colored n k} {ctx : Ctx}
    {rlab rptn : Array Nat} {cs bs fs : List Nat}
    {numcells level nc : Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hdom : DomOk G ctx rlab rptn cs bs fs numcells st)
    (hdesc : FirstDescOk ctx st)
    (hfsz : st.firstlab.size = n) (hfre : CellsReach G st.firstlab)
    (hcsz : st.canonlab.size = n) (hcre : CellsReach G st.canonlab) :
    (processnode ctx level nc st).2.genTrace = st.genTrace ∨
      LabelCarrier ctx st.firstlab st.lab
        (processnode ctx level nc st).2.genTrace ∨
      LabelCarrier ctx st.canonlab st.lab
        (processnode ctx level nc st).2.genTrace := by
  subst hn
  rcases processnode_carrier hgb hsymm hloop hfsz
      (labOk_of_reach hfsz hfre) (labInj_of_reach hfsz hn0 hfre)
      hdom.searchOk.labSize
      (labOk_of_reach hdom.searchOk.labSize hdom.searchOk.reach)
      (labInj_of_reach hdom.searchOk.labSize hn0 hdom.searchOk.reach)
      hcsz (labOk_of_reach hcsz hcre)
      (labInj_of_reach hcsz hn0 hcre)
      (fun hgate => rows_eq_of_firstDescOk hgsz hgb hsymm hloop hdesc
        hgate)
      (fun htie => rows_eq_of_testcanlab_tie hdom.canongInv htie) with
    h | ⟨γ, hpush, hcheck, hmap⟩
  · exact Or.inl h
  · have hmem : γ ∈ (processnode ctx level nc st).2.genTrace := by
      rw [hpush]
      exact Array.mem_push.mpr (Or.inr rfl)
    rcases hmap with hfirst | hcanon
    · exact Or.inr (Or.inl ⟨γ, hmem, hcheck, hfirst⟩)
    · exact Or.inr (Or.inr ⟨γ, hmem, hcheck, hcanon⟩)

/-- Vertices strictly after the loop cursor. -/
@[expose] def After (cursor : Option Nat) (v : Nat) : Prop :=
  match cursor with
  | none => True
  | some u => u < v

/-- Numeric rank used to count strict cursor progress. -/
@[expose] def cursorRank : Option Nat → Nat
  | none => 0
  | some v => v + 1

/-- Moving to a vertex after the cursor increases its rank. -/
theorem cursorRank_step {cursor : Option Nat} {v : Nat}
    (h : After cursor v) : cursorRank cursor + 1 ≤ cursorRank (some v) := by
  cases cursor <;> simp only [After, cursorRank] at h ⊢ <;> omega

/-- A bounded cursor has rank at most the vertex count. -/
theorem cursorRank_le {cursor : Option Nat} {n : Nat}
    (h : ∀ v, cursor = some v → v < n) : cursorRank cursor ≤ n := by
  cases cursor with
  | none => simp only [cursorRank]; omega
  | some v =>
      have := h v rfl
      simp only [cursorRank]
      omega

/-- A loop cannot consume more fuel than the remaining bounded cursor
range.  This is the contradiction used to rule out the exhaustion outcome
of the executable root sweeps. -/
theorem LoopResult.exhaustion_false {ctx : Ctx}
    {cursor finalCursor : Option Nat} {loopFuel : Nat}
    (hfuel : ctx.n < cursorRank cursor + loopFuel)
    (hprogress : cursorRank cursor + loopFuel ≤ cursorRank finalCursor)
    (hbounded : ∀ v, finalCursor = some v → v < ctx.n) : False := by
  have := cursorRank_le hbounded
  omega

/-- The prefixed specification key of offset `o` in a refined target
cell. -/
@[expose] def sweepKey (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc numcells o : Nat) : Key :=
  prefixKey cs
    (childKey ctx tcLevel specFuel level rsLab rsPtn tc numcells o)

/-- A checked label carrier identifies the two children selected at an
ancestor, once the two leaf labellings are known at that ancestor's
individualized position. -/
theorem sweepKey_of_carrier {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) {ref cur : Array Nat}
    {store : Array (Array Nat)} (hcarrier : LabelCarrier ctx ref cur store)
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells oRef oCur : Nat}
    (hstab : ∀ γ ∈ store, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (href : oRef < len) (hcur : oCur < len)
    (hlf : level + 1 + specFuel ≤ n + 1)
    (hatRef : ref[tc]! = rsLab[tc + oRef]!)
    (hatCur : cur[tc]! = rsLab[tc + oCur]!) :
    sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells oCur =
      sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells oRef := by
  obtain ⟨γ, hγ, haut, hmap⟩ := hcarrier
  apply congrArg (prefixKey cs)
  apply childKey_of_carried hn hgsz haut tcLevel specFuel level
    (hstab γ hγ) hs hok hsp hend hvals hic hrange hcur href hlf
  have htc : tc < ctx.n := by
    rw [hn]
    omega
  have hm := hmap tc htc
  rwa [hatRef, hatCur] at hm

/-- The key of a non-discrete node is the maximum of the keys swept by
its child loop.  The loop prefix contains the node's refinement code. -/
theorem nodeKey_children {ctx : Ctx} {tcLevel fuel level numcells len : Nat}
    {cs : List Nat} {st : SearchSt}
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = false)
    (hlen : (specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn level
      tcLevel).2.2 = len + 1) :
    nodeKey ctx tcLevel (fuel + 1) level cs st numcells =
      keysMax
        (sweepKey ctx tcLevel fuel level
          (cs ++ [(refine ctx level st.lab st.ptn st.active
            numcells).longcode])
          (refine ctx level st.lab st.ptn st.active numcells).lab
          (refine ctx level st.lab st.ptn st.active numcells).ptn
          (specMaketargetcell ctx
            (refine ctx level st.lab st.ptn st.active numcells).lab
            (refine ctx level st.lab st.ptn st.active numcells).ptn level
            tcLevel).1
          (refine ctx level st.lab st.ptn st.active numcells).numcells 0)
        ((List.range len).map fun o =>
          sweepKey ctx tcLevel fuel level
            (cs ++ [(refine ctx level st.lab st.ptn st.active
              numcells).longcode])
            (refine ctx level st.lab st.ptn st.active numcells).lab
            (refine ctx level st.lab st.ptn st.active numcells).ptn
            (specMaketargetcell ctx
              (refine ctx level st.lab st.ptn st.active numcells).lab
              (refine ctx level st.lab st.ptn st.active numcells).ptn level
              tcLevel).1
            (refine ctx level st.lab st.ptn st.active numcells).numcells
            (o + 1)) := by
  rw [nodeKey, specNode_internal cs hdisc hlen]
  rfl

/-- Offset `o` has been absorbed by the semantic incumbent.  This is
explicit rather than read from `SearchSt`: during an upward code
comparison the executable overwrites `canoncode` before it installs the
new leaf, so the state temporarily contains no faithful incumbent key. -/
@[expose] def ChildDone (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (best : Option Key) (o : Nat) : Prop :=
  ∃ b, best = some b ∧
    keyLe (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells o) b

/-- Offset `o` is still eligible after the loop cursor. -/
@[expose] def ChildLive (rsLab : Array Nat) (tc len tcell : Nat)
    (cursor : Option Nat) (o : Nat) : Prop :=
  o < len ∧ elem tcell rsLab[tc + o]! = true ∧
    After cursor rsLab[tc + o]!

/-- The evolving invariant of a mutable target-cell sweep.

`cover` follows removed children transitively to the current live suffix.
`past` records the ordering fact needed when a pruning automorphism carries
a live vertex backwards: every retained vertex at or before the cursor has
already been absorbed. -/
structure SweepCover (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells tcell : Nat)
    (cursor : Option Nat) (best : Option Key) : Prop where
  cover : ChildCover
    (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells)
    (fun o => rsLab[tc + o]!)
    (fun o => o < len)
    (ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells best)
    (ChildLive rsLab tc len tcell cursor)
  past : ∀ o, o < len → elem tcell rsLab[tc + o]! = true →
    ¬ After cursor rsLab[tc + o]! →
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells best o

/-- Before the first iteration, the whole target-cell window is live. -/
theorem sweepCover_init (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells : Nat)
    (best : Option Key) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (windowSet rsLab tc len) none best := by
  constructor
  · intro o ho
    refine Or.inr ⟨o, ⟨ho, ?_, trivial⟩, rfl, Nat.le_refl _⟩
    rw [elem_windowSet, segN]
    exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho, rfl⟩
  · intro o ho hm hpast
    exact absurd trivial hpast

/-- Coverage crosses an arbitrary loop step once old covered children stay
covered and every old survivor is either covered or replaced by a
key-equivalent new survivor. -/
theorem SweepCover.step {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor cursor' : Option Nat}
    {best best' : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      (∀ j, sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells j =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells o →
          ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
            best' j) ∨
        ∃ j, ChildLive rsLab tc len tcell' cursor' j ∧
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells j ∧
          rsLab[tc + j]! ≤ rsLab[tc + o]!)
    (hd : ∀ o,
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells best o →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        best' o)
    (hpast : ∀ o, o < len → elem tcell' rsLab[tc + o]! = true →
      ¬ After cursor' rsLab[tc + o]! →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        best' o) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor' best' := by
  exact ⟨ChildCover.step h.cover hs hd, hpast⟩

/-- Previously covered children remain covered when the incumbent grows. -/
theorem ChildDone.mono {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc numcells o : Nat}
    {best best' : Option Key}
    (h : ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      best o)
    (hinc : ∀ b, best = some b →
      ∃ b', best' = some b' ∧ keyLe b b') :
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      best' o := by
  rcases h with ⟨b, hb, hkb⟩
  obtain ⟨b', hb', hbb'⟩ := hinc b hb
  exact ⟨b', hb', keyLe_trans hkb hbb'⟩

/-- Coverage transfers across equality of two child keys. -/
theorem ChildDone.ofEq {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc numcells oRef oCur : Nat}
    {best : Option Key}
    (h : ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      best oRef)
    (heq : sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells oCur =
        sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells oRef) :
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      best oCur := by
  obtain ⟨b, hb, hle⟩ := h
  refine ⟨b, hb, ?_⟩
  rw [heq]
  exact hle

/-- A filter preserves sweep coverage when every old live child is either
absorbed or carried to a key-equivalent new survivor, and filtering adds no
vertices.  A carried survivor before the cursor is discharged through
`past`; it need not remain in the live suffix. -/
theorem SweepCover.filter {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor : Option Nat} {best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      (∀ j, sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells j =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells o →
          ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
            best j) ∨
        ∃ j, ChildLive rsLab tc len tcell' cursor j ∧
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells j ∧
          rsLab[tc + j]! ≤ rsLab[tc + o]!)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor best := by
  refine ⟨ChildCover.step h.cover hs (fun _ hx => hx), ?_⟩
  intro o ho hm hpast
  exact h.past o ho (hsub _ hm) hpast

/-- Cursor eligibility is decidable without asking typeclass search to
reduce the opaque `After` definition. -/
theorem after_or_not (cursor : Option Nat) (v : Nat) :
    After cursor v ∨ ¬ After cursor v := by
  rcases cursor with _ | u
  · exact Or.inl trivial
  · rcases Nat.lt_or_ge u v with h | h
    · exact Or.inl h
    · exact Or.inr (by
        dsimp only [After]
        omega)

/-- A filter's natural preservation rule: every old live child is carried
to a key-equivalent member of the filtered set.  The member may lie before
the cursor; `past` converts that case to completed coverage. -/
theorem SweepCover.filterCarried {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor : Option Nat} {best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      ∃ j, j < len ∧ elem tcell' rsLab[tc + j]! = true ∧
        sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
            numcells j ∧
        rsLab[tc + j]! ≤ rsLab[tc + o]!)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor best := by
  apply h.filter _ hsub
  intro o ho
  obtain ⟨j, hj, hm, hkey, hrank⟩ := hs o ho
  rcases after_or_not cursor rsLab[tc + j]! with ha | ha
  · exact Or.inr ⟨j, ⟨hj, hm, ha⟩, hkey, hrank⟩
  · left
    have hdone := h.past j hj (hsub _ hm) ha
    intro z hz
    rcases hdone with ⟨b, hb, hle⟩
    refine ⟨b, hb, ?_⟩
    rw [hz, hkey]
    exact hle

/-- The form used by executable prune filters.  A current live child either
survives unchanged or is carried to a strictly smaller child of the full
target cell.  Ranked coverage follows the latter through any earlier
filters until it reaches an already-covered child or a new survivor. -/
theorem SweepCover.filterDesc {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor : Option Nat} {best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      elem tcell' rsLab[tc + o]! = true ∨
        ∃ j, j < len ∧
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells j ∧
          rsLab[tc + j]! < rsLab[tc + o]!)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor best := by
  constructor
  · apply ChildCover.filterDesc h.cover
    · intro x y hkey hdone
      rcases hdone with ⟨b, hb, hle⟩
      refine ⟨b, hb, ?_⟩
      rw [hkey]
      exact hle
    · intro o ho
      rcases hs o ho with hm | ⟨j, hj, hkey, hrank⟩
      · exact Or.inl ⟨ho.1, hm, ho.2.2⟩
      · exact Or.inr ⟨j, hj, hkey, hrank⟩
  · intro o ho hm hpast
    exact h.past o ho (hsub _ hm) hpast

/-- Cell-stabilizing downward automorphism carriers discharge the abstract
descending-filter rule. -/
theorem SweepCover.filterAutom {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor : Option Nat} {best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hgsz : ctx.g.size = ctx.n) (hs : rsLab.size = ctx.n)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1)
    (hdrop : ∀ o, ChildLive rsLab tc len tcell cursor o →
      elem tcell' rsLab[tc + o]! = false →
      ∃ γ, checkAutom ctx.g γ ctx.n = true ∧
        CellStab rsPtn level rsLab γ ∧
        γ[rsLab[tc + o]!]! < rsLab[tc + o]!)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor best := by
  apply h.filterDesc _ hsub
  intro o ho
  rcases hm : elem tcell' rsLab[tc + o]! with _ | _
  · obtain ⟨γ, hγ, hstab, hlt⟩ := hdrop o ho hm
    have hW : elem (windowSet rsLab tc len) γ[rsLab[tc + o]!]! = true :=
      windowSet_carry hstab hic (by rw [hs]; exact hrange)
        (elem_windowSet.mpr (List.mem_map.mpr
          ⟨o, List.mem_range.mpr ho.1, rfl⟩))
    obtain ⟨j, hj, hcarry⟩ := List.mem_map.mp (elem_windowSet.mp hW)
    have hjlt : j < len := List.mem_range.mp hj
    have hkey : childKey ctx tcLevel specFuel level rsLab rsPtn tc
        numcells j = childKey ctx tcLevel specFuel level rsLab rsPtn tc
          numcells o :=
      childKey_of_carried (n := ctx.n) (ctx := ctx) rfl hgsz hγ
        tcLevel specFuel level hstab hs hok hsp hend hvals hic hrange
        hjlt ho.1 hlf hcarry.symm
    exact Or.inr ⟨j, hjlt, by
      unfold sweepKey
      rw [hkey], by simpa [hcarry] using hlt⟩
  · exact Or.inl rfl

/-- `longprune` preserves the evolving sweep under the autos ledger. -/
theorem SweepCover.longprune {ctx : Ctx}
    {tcLevel specFuel level fixedpts : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {best : Option Key} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hgsz : ctx.g.size = ctx.n) (hs : rsLab.size = ctx.n)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1)
    (haut : ∀ p ∈ out.autos.toList,
      (fixedpts &&& p.1 == fixedpts) = true →
      PairOk ctx.g rsPtn rsLab level ctx.n p.1 p.2) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (longprune tcell fixedpts out.autos) cursor best := by
  apply h.filterAutom hgsz hs hok hsp hend hvals hic hrange hlf
  · intro o ho hm
    change o < len ∧ elem tcell rsLab[tc + o]! = true ∧
      After cursor rsLab[tc + o]! at ho
    exact longprune_drop (hok _ (by omega)) ho.2.1 hm haut
  · exact fun _ hm => longprune_subset hm

/-- `shortprune` preserves the evolving sweep under the last-pair ledger. -/
theorem SweepCover.shortprune {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {best : Option Key} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hgsz : ctx.g.size = ctx.n) (hs : rsLab.size = ctx.n)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1)
    (hlast : ∀ fix mcr, out.autos.back? = some (fix, mcr) →
      PairOk ctx.g rsPtn rsLab level ctx.n fix mcr) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (shortprune tcell out) cursor best := by
  apply h.filterAutom hgsz hs hok hsp hend hvals hic hrange hlf
  · intro o ho hm
    change o < len ∧ elem tcell rsLab[tc + o]! = true ∧
      After cursor rsLab[tc + o]! at ho
    exact shortprune_drop (hok _ (by omega)) ho.2.1 hm hlast
  · exact fun _ hm => shortprune_subset hm

/-- At loop completion the evolving coverage invariant says that every
offset in the original target cell has been absorbed. -/
theorem SweepCover.finish {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat}
    {best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hempty : ∀ o, ¬ ChildLive rsLab tc len tcell cursor o) :
    ∀ o, o < len → ChildDone ctx tcLevel specFuel level cs rsLab rsPtn
      tc numcells best o :=
  ChildCover.finish h.cover hempty

/-- Completed child coverage bounds the maximum over the whole original
target cell, not merely the final filtered set. -/
theorem SweepCover.maxLe {ctx : Ctx} {tcLevel specFuel level tail : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat}
    {tc numcells tcell : Nat} {cursor : Option Nat} {best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc
      (tail + 1) numcells tcell cursor best)
    (hempty : ∀ o, ¬ ChildLive rsLab tc (tail + 1) tcell cursor o)
    {b : Key} (hout : best = some b) :
    keyLe
      (keysMax
        (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
            numcells (o + 1))) b := by
  apply keysMax_le
  · obtain ⟨b', hb', hle⟩ := h.finish hempty 0 (by omega)
    have : b' = b := Option.some.inj (hb'.symm.trans hout)
    rwa [this] at hle
  · intro y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hy
    obtain ⟨b', hb', hle⟩ := h.finish hempty (o + 1)
      (by have := List.mem_range.mp ho; omega)
    have : b' = b := Option.some.inj (hb'.symm.trans hout)
    rwa [this] at hle

/-- A `none` cursor result means that no set member remains after the
cursor. -/
theorem no_child_after {s : Nat} {cursor : Option Nat}
    (hnext : nextElem s cursor = none) :
    ∀ v, elem s v = true → After cursor v → False := by
  intro v hv ha
  rw [nextElem.eq_def] at hnext
  rcases cursor with _ | p
  · dsimp only at hnext ha
    split at hnext
    · next hz =>
      rw [hz, elem, Nat.zero_testBit] at hv
      cases hv
    · cases hnext
  · dsimp only at hnext ha
    change p < v at ha
    split at hnext
    · next hz =>
      have hbit : (((s >>> (p + 1)) <<< (p + 1)).testBit v) = true := by
        rw [Nat.testBit_shiftLeft]
        rw [show decide (p + 1 ≤ v) = true by simp; omega]
        rw [Nat.testBit_shiftRight]
        rw [show p + 1 + (v - (p + 1)) = v by omega]
        exact hv
      rw [hz, Nat.zero_testBit] at hbit
      cases hbit
    · cases hnext

/-- A successful `nextElem` lies strictly after its cursor. -/
theorem nextElem_after {s v : Nat} {cursor : Option Nat}
    (hnext : nextElem s cursor = some v) : After cursor v := by
  rw [nextElem.eq_def] at hnext
  rcases cursor with _ | p
  · trivial
  · change p < v
    dsimp only at hnext
    split at hnext
    · cases hnext
    · next hn =>
      injection hnext with hv
      subst v
      have hbit := testBit_lowBit _ hn
      rw [Nat.testBit_shiftLeft] at hbit
      have hle : p + 1 ≤ lowBit ((s >>> (p + 1)) <<< (p + 1)) :=
        of_decide_eq_true ((Bool.and_eq_true _ _).mp hbit).1
      omega

/-- `nextElem` returns the least set member strictly after its cursor. -/
theorem nextElem_le {s v w : Nat} {cursor : Option Nat}
    (hnext : nextElem s cursor = some v)
    (hw : elem s w = true) (ha : After cursor w) : v ≤ w := by
  rw [nextElem.eq_def] at hnext
  rcases cursor with _ | p
  · dsimp only at hnext
    split at hnext
    · cases hnext
    · next hn =>
      injection hnext with hv
      subst v
      apply Nat.le_of_not_gt
      intro hle
      have hz := testBit_lt_lowBit s w hle
      change s.testBit w = true at hw
      rw [hz] at hw
      cases hw
  · dsimp only at hnext
    change p < w at ha
    split at hnext
    · cases hnext
    · next hn =>
      injection hnext with hv
      subst v
      have hmasked :
          (((s >>> (p + 1)) <<< (p + 1)).testBit w) = true := by
        rw [Nat.testBit_shiftLeft]
        rw [show decide (p + 1 ≤ w) = true by simp; omega]
        rw [Nat.testBit_shiftRight]
        rw [show p + 1 + (w - (p + 1)) = w by omega]
        exact hw
      apply Nat.le_of_not_gt
      intro hle
      have hz := testBit_lt_lowBit ((s >>> (p + 1)) <<< (p + 1)) w
        hle
      rw [hz] at hmasked
      cases hmasked

/-- Advancing to the least remaining vertex preserves sweep coverage once
that vertex's child is absorbed.  The `hcur` premise identifies every
offset carrying the chosen vertex; callers normally discharge it from
labelling injectivity. -/
theorem SweepCover.advance {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells tv : Nat}
    {tcell : Nat} {cursor : Option Nat} {best best' : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = some tv)
    (hcur : ∀ o, o < len → rsLab[tc + o]! = tv →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        best' o)
    (hd : ∀ o,
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells best o →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        best' o) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell (some tv) best' := by
  refine SweepCover.step h ?_ hd ?_
  · intro o ho
    change o < len ∧ elem tcell rsLab[tc + o]! = true ∧
      After cursor rsLab[tc + o]! at ho
    rcases ho with ⟨ho, hm, ha⟩
    have hle := nextElem_le hnext hm ha
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · left
      have hdone := hcur o ho heq.symm
      intro j hj
      rcases hdone with ⟨b, hb, hkb⟩
      refine ⟨b, hb, ?_⟩
      rw [hj]
      exact hkb
    · exact Or.inr ⟨o, ⟨ho, hm, hlt⟩, rfl, Nat.le_refl _⟩
  · intro o ho hm hpast
    change ¬ tv < rsLab[tc + o]! at hpast
    rcases cursor with _ | u
    · have hle := nextElem_le hnext hm trivial
      exact hcur o ho (Nat.le_antisymm (Nat.le_of_not_gt hpast) hle)
    · rcases Nat.lt_or_ge u rsLab[tc + o]! with ha | ha
      · have hle := nextElem_le hnext hm ha
        exact hcur o ho (Nat.le_antisymm (Nat.le_of_not_gt hpast) hle)
      · exact hd o (h.past o ho hm (by
          dsimp only [After]
          omega))

/-- A child whose key is carried to a strictly smaller target-cell vertex
is already covered when the loop is about to visit the least eligible
vertex.  Any live witness supplied by ranked coverage would be both below
and at least that least vertex, a contradiction. -/
theorem SweepCover.done_of_smaller {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tv o j tcell : Nat}
    {cursor : Option Nat} {best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = some tv)
    (hj : j < len)
    (hkey : sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
        numcells o =
      sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells j)
    (hrank : rsLab[tc + j]! < tv) :
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells best o := by
  rcases h.cover j hj with hjd | ⟨z, hzl, hjz, hzr⟩
  · rcases hjd with ⟨b, hb, hle⟩
    refine ⟨b, hb, ?_⟩
    rw [hkey]
    exact hle
  · have htvz := nextElem_le hnext hzl.2.1 hzl.2.2
    have : rsLab[tc + z]! < tv := Nat.lt_of_le_of_lt hzr hrank
    omega

/-- The non-root arm of the first-path orbit test is a covered skip.  Orbit
soundness supplies a smaller word-connected pointer target; cell
stabilization keeps that target in the sibling cell, and ranked coverage
shows it was already absorbed. -/
theorem SweepCover.orbitSkip {ctx : Ctx}
    {tcLevel specFuel level tv o : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {best : Option Key} {out : SearchSt}
    {gens : List (Array Nat)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
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
    (hsound : OrbSound (OrbConn gens ctx.n) out.orbits ctx.n)
    (hne : out.orbits[tv]! ≠ tv) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell (some tv) best := by
  have hvn : tv < ctx.n := by rw [← htv]; exact hok _ (by omega)
  obtain ⟨_, hconn⟩ := orbConn_of_ptr hsound hvn
  unfold WordConn at hconn
  obtain ⟨w, hw, happ⟩ := hconn
  obtain ⟨_, hwstab, hwpoint⟩ :=
    wordPerm_spec hbg hok hsp hs hend hv hstab w hw
  have hW : elem (windowSet rsLab tc len) out.orbits[tv]! = true := by
    have := windowSet_carry hwstab hic (by rw [hs]; exact hrange)
      (elem_windowSet.mpr (List.mem_map.mpr
        ⟨o, List.mem_range.mpr ho, rfl⟩))
    rw [htv, hwpoint _ hvn, happ] at this
    exact this
  obtain ⟨j, hj, hptr⟩ := List.mem_map.mp (elem_windowSet.mp hW)
  have hjlt : j < len := List.mem_range.mp hj
  have hptr' : out.orbits[rsLab[tc + o]!]! = rsLab[tc + j]! := by
    rw [htv]
    exact hptr.symm
  have hkey : sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells o =
        sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells j := by
    unfold sweepKey
    rw [childKey_of_orbitPtr (n := ctx.n) (ctx := ctx) rfl hgsz hbg hv
      tcLevel specFuel level hstab hs hok hsp hend hvals hic hrange ho
      hjlt hlf hsound hptr']
  have hjrank : rsLab[tc + j]! < tv := by
    have hle := (hsound.2 tv hvn).1
    rw [hptr]
    omega
  have hdone := h.done_of_smaller hnext hjlt hkey hjrank
  apply h.advance hnext _ (fun _ hx => hx)
  intro q hq hqtv
  unfold LabInj at hinj
  have hqo' : tc + q = tc + o := hinj (tc + q) (tc + o)
    (by rw [hs]; omega) (by rw [hs]; omega) (hqtv.trans htv.symm)
  have hqo : q = o := by omega
  rwa [hqo]

/-- The executable loop terminator discharges the live-set premise of
`SweepCover.finish`. -/
theorem SweepCover.finish_of_nextElem {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = none) :
    ∀ o, o < len → ChildDone ctx tcLevel specFuel level cs rsLab rsPtn
      tc numcells best o := by
  apply h.finish
  intro o ho
  exact no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- A child at an ancestor has already been absorbed.  The arrays and
offset are stored explicitly because neither `gcaFirst` nor `gcaCanon`
retains this path history. -/
structure Anchor (ctx : Ctx) (tcLevel target : Nat)
    (best : Option Key) where
  positive : 1 ≤ target
  specFuel : Nat
  codes : List Nat
  rsLab : Array Nat
  rsPtn : Array Nat
  tc : Nat
  numcells : Nat
  offset : Nat
  done : ChildDone ctx tcLevel specFuel target codes rsLab rsPtn tc
    numcells best offset

/-- Turn an already-covered reference child into the current child's
unwind anchor using a checked carrier between their leaf labellings. -/
def Anchor.ofCarrier {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) {tcLevel level specFuel : Nat}
    {codes : List Nat} {rsLab rsPtn ref cur : Array Nat}
    {store : Array (Array Nat)} {tc len numcells oRef oCur : Nat}
    {best : Option Key} (hpos : 1 ≤ level)
    (hdone : ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells best oRef)
    (hcarrier : LabelCarrier ctx ref cur store)
    (hstab : ∀ γ ∈ store, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (href : oRef < len) (hcur : oCur < len)
    (hlf : level + 1 + specFuel ≤ n + 1)
    (hatRef : ref[tc]! = rsLab[tc + oRef]!)
    (hatCur : cur[tc]! = rsLab[tc + oCur]!) :
    Anchor ctx tcLevel level best := by
  refine ⟨hpos, specFuel, codes, rsLab, rsPtn, tc, numcells, oCur, ?_⟩
  apply hdone.ofEq
  exact sweepKey_of_carrier hn hgsz hcarrier hstab hs hok hsp hend hvals
    hic hrange href hcur hlf hatRef hatCur

/-- Why an early return is sound.  Code one and code two retain their
different reference labellings; comparison pruning has no generator. -/
inductive Unwind (ctx : Ctx) (tcLevel target : Nat)
    (out : SearchSt) (best : Option Key) : Prop where
  | first (anchor : Anchor ctx tcLevel target best)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace)
  | canon (anchor : Anchor ctx tcLevel target best)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
  | frozen (anchor : Anchor ctx tcLevel target best)

/-- A semantic incumbent can only improve across a search fragment. -/
@[expose] def IncGrows (best out : Option Key) : Prop :=
  ∀ b, best = some b → ∃ b', out = some b' ∧ keyLe b b'

/-- Every installed output came from the incoming incumbent or this
node's specification subtree, and the incoming incumbent was not lost. -/
structure NodeSound (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (st : SearchSt) (numcells : Nat)
    (best out : Option Key) : Prop where
  upper : ∀ b, out = some b →
    keyLe b (incMax best
      (nodeKey ctx tcLevel specFuel level cs st numcells))
  grows : IncGrows best out

/-- The state component common to both successful loop outcomes.  The
loop may stop early, but every incumbent it installs is still bounded by
the incoming incumbent and the whole parent subtree. -/
structure LoopSound (ctx : Ctx) (bound : Key)
    (best out : Option Key) : Prop where
  upper : ∀ b, out = some b → keyLe b (incMax best bound)
  grows : IncGrows best out

theorem IncGrows.refl (best : Option Key) : IncGrows best best := by
  intro b hb
  exact ⟨b, hb, keyLe_refl b⟩

/-- Folding one key into an incumbent preserves the old incumbent. -/
theorem IncGrows.incMax (best : Option Key) (K : Key) :
    IncGrows best (some (incMax best K)) := by
  intro b hb
  rcases best with _ | a
  · cases hb
  · injection hb with hab
    subst hab
    exact ⟨Nauty.incMax (some a) K, rfl,
      keyLe_iff.mpr (keyMax_not_lt_left a K)⟩

theorem NodeSound.refl (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (st : SearchSt) (numcells : Nat) (best : Option Key) :
    NodeSound ctx tcLevel specFuel level cs st numcells best best := by
  constructor
  · intro b hb
    rw [hb, incMax]
    exact keyLe_iff.mpr (keyMax_not_lt_left _ _)
  · exact IncGrows.refl best

/-- An exact node maximum supplies both clauses of `NodeSound`. -/
theorem NodeSound.ofExact {ctx : Ctx} {tcLevel specFuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {best out : Option Key}
    (h : out = some (incMax best
      (nodeKey ctx tcLevel specFuel level cs st numcells))) :
    NodeSound ctx tcLevel specFuel level cs st numcells best out := by
  constructor
  · intro b hb
    rw [h] at hb
    injection hb with he
    subst he
    exact keyLe_refl _
  · rw [h]
    exact IncGrows.incMax best _

theorem LoopSound.refl (ctx : Ctx) (bound : Key) (best : Option Key) :
    LoopSound ctx bound best best := by
  constructor
  · intro b hb
    rw [hb, incMax]
    exact keyLe_iff.mpr (keyMax_not_lt_left _ _)
  · exact IncGrows.refl best

/-- An exact loop maximum supplies both clauses of `LoopSound`. -/
theorem LoopSound.ofExact {ctx : Ctx} {bound : Key}
    {best out : Option Key}
    (h : out = some (incMax best bound)) :
    LoopSound ctx bound best out := by
  constructor
  · intro b hb
    rw [h] at hb
    injection hb with he
    subst he
    exact keyLe_refl _
  · rw [h]
    exact IncGrows.incMax best bound

theorem keyMax_le_of_le {a b c : Key} (ha : keyLe a c)
    (hb : keyLe b c) : keyLe (keyMax a b) c := by
  rcases keyMax_mem a b with h | h
  · rwa [h]
  · rwa [h]

theorem keyLe_incMax_right (inc : Option Key) (b : Key) :
    keyLe b (incMax inc b) := by
  rcases inc with _ | a
  · exact keyLe_refl b
  · exact keyLe_iff.mpr (keyMax_not_lt_right a b)

theorem incMax_mono_right (inc : Option Key) {a b : Key}
    (h : keyLe a b) : keyLe (incMax inc a) (incMax inc b) := by
  rcases inc with _ | x
  · exact h
  · apply keyMax_le_of_le
    · exact keyLe_iff.mpr (keyMax_not_lt_left x b)
    · exact keyLe_trans h (keyLe_iff.mpr (keyMax_not_lt_right x b))

theorem IncGrows.trans {best mid out : Option Key}
    (h₁ : IncGrows best mid) (h₂ : IncGrows mid out) :
    IncGrows best out := by
  intro b hb
  obtain ⟨m, hm, hbm⟩ := h₁ b hb
  obtain ⟨c, hc, hmc⟩ := h₂ m hm
  exact ⟨c, hc, keyLe_trans hbm hmc⟩

/-- A sound child step is sound against any larger fixed loop bound. -/
theorem LoopSound.ofNode {ctx : Ctx} {tcLevel specFuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {bound : Key}
    {best out : Option Key}
    (h : NodeSound ctx tcLevel specFuel level cs st numcells best out)
    (hle : keyLe (nodeKey ctx tcLevel specFuel level cs st numcells)
      bound) : LoopSound ctx bound best out := by
  constructor
  · intro b hb
    exact keyLe_trans (h.upper b hb)
      (incMax_mono_right best hle)
  · exact h.grows

/-- Consecutive fragments with the same fixed bound compose. -/
theorem LoopSound.trans {ctx : Ctx} {bound : Key}
    {best mid out : Option Key} (h₁ : LoopSound ctx bound best mid)
    (h₂ : LoopSound ctx bound mid out) : LoopSound ctx bound best out := by
  constructor
  · intro b hb
    have hb₂ := h₂.upper b hb
    rcases hm : mid with _ | m
    · rw [hm, incMax] at hb₂
      exact keyLe_trans hb₂ (keyLe_incMax_right best bound)
    · rw [hm, incMax] at hb₂
      apply keyLe_trans hb₂
      apply keyMax_le_of_le
      · exact h₁.upper m hm
      · exact keyLe_incMax_right best bound
  · exact h₁.grows.trans h₂.grows

/-- Matching upper and lower bounds turn loop soundness into the exact
incumbent equation required when a parent node completes. -/
theorem LoopSound.exact {ctx : Ctx} {bound b : Key}
    {best out : Option Key} (h : LoopSound ctx bound best out)
    (hout : out = some b) (hlower : keyLe bound b) :
    out = some (incMax best bound) := by
  have hupper := h.upper b hout
  have hlower' : keyLe (incMax best bound) b := by
    rcases hin : best with _ | a
    · rw [incMax]
      exact hlower
    · obtain ⟨b', hb', hab'⟩ := h.grows a hin
      have hbb' : b = b' := Option.some.inj (hout.symm.trans hb')
      rw [incMax]
      apply keyMax_le_of_le
      · rwa [← hbb'] at hab'
      · exact hlower
  rw [hout]
  exact congrArg some (keyLe_antisym hupper hlower')

/-- A completed sweep whose fixed loop bound is the maximum of its
original children recovers the exact final incumbent. -/
theorem SweepCover.exact {ctx : Ctx} {tcLevel specFuel level tail : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat}
    {tc numcells tcell : Nat} {cursor : Option Nat}
    {best out : Option Key} {b : Key}
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc
      (tail + 1) numcells tcell cursor out)
    (hempty : ∀ o,
      ¬ ChildLive rsLab tc (tail + 1) tcell cursor o)
    (hsound : LoopSound ctx
      (keysMax
        (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells (o + 1))) best out)
    (hout : out = some b) :
    out = some (incMax best
      (keysMax
        (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
            numcells (o + 1)))) :=
  hsound.exact hout (hcover.maxLe hempty hout)

/-- The result of a node call, with logical and runtime fuel separated.

`complete` and `unwind` may have the same return integer.  The latter is
therefore a constructor, not an inequality side condition. -/
inductive NodeResult (ctx : Ctx) (tcLevel specFuel runFuel level : Nat)
    (cs : List Nat) (st out : SearchSt) (numcells : Nat)
    (best outBest : Option Key) (r : Int) : Prop where
  | complete (sound : NodeSound ctx tcLevel specFuel level cs st numcells
      best outBest)
      (returned : r = Int.ofNat level - 1)
      (installed : out.canonlevel ≠ 0)
      (read : stInc ctx out = outBest)
      (full : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level cs st numcells)))
  | unwind (sound : NodeSound ctx tcLevel specFuel level cs st numcells
      best outBest)
      (target : Nat) (returned : r = Int.ofNat target)
      (below : target < level)
      (payload : Unwind ctx tcLevel target out outBest)
  | exhausted (empty : runFuel = 0) (returned : r = 0)
      (unchanged : out = st) (bestUnchanged : outBest = best)

/-- The result of a child-loop call.  Exhaustion is distinct from a
completed empty remainder, so a general theorem cannot accidentally treat
the `cfuel = 0` arm as coverage of every child. -/
inductive LoopResult (ctx : Ctx) (tcLevel specFuel runFuel loopFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells tcell : Nat)
    (cursor : Option Nat) (bound : Key) (st out : SearchSt)
    (best outBest : Option Key) (r : Option Int) : Prop where
  | complete
      (returned : r = none)
      (sound : LoopSound ctx bound best outBest)
      (finalSet : Nat) (finalCursor : Option Nat)
      (cover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
        numcells finalSet finalCursor outBest)
      (empty : ∀ o, ¬ ChildLive rsLab tc len finalSet finalCursor o)
  | unwind (sound : LoopSound ctx bound best outBest)
      (target : Nat) (returned : r = some (Int.ofNat target))
      (below : target < level)
      (payload : Unwind ctx tcLevel target out outBest)
  | exhausted
      (returned : r = none)
      (sound : LoopSound ctx bound best outBest)
      (finalSet : Nat) (finalCursor : Option Nat)
      (cover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
        numcells finalSet finalCursor outBest)
      (progress : cursorRank cursor + loopFuel ≤ cursorRank finalCursor)
      (bounded : ∀ v, finalCursor = some v → v < ctx.n)

/-- The entry set only describes where the call begins.  Every constructor
records the final set, so the result can cross a filter exposed in the
caller. -/
theorem LoopResult.reindexSet {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell tcell' : Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best outBest : Option Key}
    {r : Option Int}
    (h : LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest r) :
    LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab rsPtn
      tc len numcells tcell' cursor bound st out best outBest r := by
  cases h with
  | complete returned sound finalSet finalCursor cover empty =>
      exact .complete returned sound finalSet finalCursor cover empty
  | unwind sound target returned below payload =>
      exact .unwind sound target returned below payload
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned sound finalSet finalCursor cover progress bounded

/-- One successful cursor step transports every recursive loop outcome.
For exhaustion, its rank certificate accounts for the fuel consumed by
the exposed iteration. -/
theorem LoopResult.step {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level tv : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best outBest : Option Key}
    {r : Option Int}
    (ha : After cursor tv)
    (h : LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab
      rsPtn tc len numcells tcell (some tv) bound st out best outBest r) :
    LoopResult ctx tcLevel specFuel runFuel (loopFuel + 1) level cs rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest r := by
  cases h with
  | complete returned sound finalSet finalCursor cover empty =>
      exact .complete returned sound finalSet finalCursor cover empty
  | unwind sound target returned below payload =>
      exact .unwind sound target returned below payload
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned sound finalSet finalCursor cover
        (Nat.le_trans (by
          have := cursorRank_step ha
          omega) progress) bounded

/-- The corrected node outcome closes domination at the root.  Exhaustion
is impossible with the root runtime fuel, and every unwind anchor has a
positive target, so neither non-complete constructor survives at level
one. -/
theorem dominated_of_result {n k : Nat} {G : Colored n k} (hn0 : n ≠ 0)
    {best : Option Key}
    (hroot : NodeResult { n := n, g := rowsOf G } 100 n (n + 2) 1 []
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      (rootOut n (rowsOf G) (initialPartition G).1
        (initialPartition G).2)
      (initialPartition G).2.length
      none best
      (firstPathNode { n := n, g := rowsOf G } (n + 2) 100 (n + 2) 1
        (initialPartition G).2.length
        (rootSt n (initialPartition G).1 (initialPartition G).2)).1) :
    canonSpecKey G = tracedKey G := by
  cases hroot with
  | complete sound returned installed read full =>
      rw [stInc_final hn0 installed] at read
      rw [incMax, nodeKey_root hn0] at full
      exact (Option.some.inj (read.trans full)).symm
  | unwind sound target returned below payload =>
      cases payload with
      | first anchor carrier =>
          exact ((Nat.not_lt_of_ge anchor.positive) below).elim
      | canon anchor carrier =>
          exact ((Nat.not_lt_of_ge anchor.positive) below).elim
      | frozen anchor =>
          exact ((Nat.not_lt_of_ge anchor.positive) below).elim
  | exhausted empty returned unchanged bestUnchanged => omega

/-- Certificate-checked canonicalization is total once the corrected root
node outcome has been established. -/
theorem certifyCanon?_isSome_of_result {n k : Nat} {G : Colored n k}
    (hn0 : n ≠ 0) {best : Option Key}
    (hroot : NodeResult { n := n, g := rowsOf G } 100 n (n + 2) 1 []
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      (rootOut n (rowsOf G) (initialPartition G).1
        (initialPartition G).2)
      (initialPartition G).2.length
      none best
      (firstPathNode { n := n, g := rowsOf G } (n + 2) 100 (n + 2) 1
        (initialPartition G).2.length
        (rootSt n (initialPartition G).1 (initialPartition G).2)).1) :
    (certifyCanon? G).isSome :=
  certifyCanon?_isSome_of_keyEq G (dominated_of_result hn0 hroot)

end Hex.GraphIso.Nauty
