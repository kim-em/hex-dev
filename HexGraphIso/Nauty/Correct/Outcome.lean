/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Coverage
public import HexGraphIso.Nauty.Invariant.Incumbent
public import HexGraphIso.Nauty.Invariant.Autos
import all HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Equitable.Step
import HexGraphIso.Nauty.Invariant.Closure

public section

/-!
Outcome types for the search correctness proof.

The return integer alone does not distinguish a completed sweep, a
generator unwind, a comparison prune, and exhausted loop fuel.  In
particular, an unwind to `level - 1` has the same integer as ordinary
node completion.  The indexed types below keep those cases separate and
also keep logical specification fuel distinct from the two runtime fuels.

A generator or comparison unwind carries the ancestor child it has already
shown to be bounded by the incumbent.  Intermediate calls merely transport
that anchor.  At its indexed target loop, the anchor becomes ordinary child
coverage and the sweep continues.

This is the first module of `HexGraphIso.Nauty.Correct`.  `Correct.Base`
and `Correct.Unwind.Target` build on the types defined here, and every
later module of the correctness proof states its results in terms of
them.
-/

namespace Hex.GraphIso.Nauty

/-- Public eliminator for injective labellings in downstream outcome
modules, where the defining predicate is opaque. -/
theorem LabInj.eq {lab : Array Nat} {nn i j : Nat} (h : LabInj lab nn)
    (hi : i < nn) (hj : j < nn) (heq : lab[i]! = lab[j]!) : i = j := by
  unfold LabInj at h
  exact h i j hi hj heq

/-- A checked generator maps one labelling pointwise onto another. -/
@[expose] def LabelCarrier (ctx : Ctx n) (ref cur : Array Nat)
    (store : Array (Array Nat)) : Prop :=
  ∃ γ ∈ store, checkAutom ctx.g γ = true ∧
    ∀ i, i < n → γ[ref[i]!]! = cur[i]!

/-- A checked carrier whose witnessing generator stabilizes one ancestor
frame.  Direct generator unwinds need only this witness.  Requiring every
recorded generator to stabilize the frame is stronger, and it fails away
from the first-path loop that consumes an orbit closure. -/
@[expose] def CellCarrier (ctx : Ctx n) (ptn : Array Nat) (level : Nat)
    (base ref cur : Array Nat) (store : Array (Array Nat)) : Prop :=
  ∃ γ ∈ store, checkAutom ctx.g γ = true ∧
    (∀ i, i < n → γ[ref[i]!]! = cur[i]!) ∧
    CellStab ptn level base γ

theorem CellCarrier.toLabel {ctx : Ctx n} {ptn : Array Nat} {level : Nat}
    {base ref cur : Array Nat} {store : Array (Array Nat)}
    (h : CellCarrier ctx ptn level base ref cur store) :
    LabelCarrier ctx ref cur store := by
  obtain ⟨γ, hmem, haut, hmap, _⟩ := h
  exact ⟨γ, hmem, haut, hmap⟩

/-- A checked carrier identifies the relabelled leaf rows of its two
permutation labellings. -/
theorem LabelCarrier.leafRows {ctx : Ctx n} {ref cur : Array Nat}
    {store : Array (Array Nat)}
    (h : LabelCarrier ctx ref cur store)
    (hgsz : ctx.g.size = n)
    (hrefsz : ref.size = n) (hrefok : LabOk ref n)
    (hcursz : cur.size = n) :
    leafRows ctx cur = leafRows ctx ref := by
  obtain ⟨γ, _, hcheck, hmap⟩ := h
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound hgsz hcheck
  have hcur : cur = ref.map σ.toFun := by
    refine Array.ext (by rw [Array.size_map, hrefsz, hcursz])
      fun i hi hri => ?_
    rw [Array.getElem_map]
    have hrefi : i < ref.size := by omega
    have hm : γ[ref[i]]! = cur[i] := by
      simpa only [getElem!_pos ref i hrefi, getElem!_pos cur i hi] using
        hmap i (by omega)
    have hb : ref[i] < n := by
      simpa only [getElem!_pos ref i hrefi] using hrefok i (by omega)
    have hs := hσ ref[i] hb
    exact hm.symm.trans hs.symm
  rw [hcur]
  exact leafRows_map σ hrows hrefok hrefsz

/-- At a valid leaf event, either no generator is recorded or the output
store contains a checked carrier from the first or incumbent leaf. -/
theorem processnode_labelCarrier {G : Colored n k} {ctx : Ctx n}
    {rlab rptn : Array Nat} {cs bs fs : List Nat}
    {numcells level nc : Nat} {st : SearchSt n}
    (hn0 : 0 < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hdom : DomOk G ctx rlab rptn cs bs fs numcells st)
    (hfsz : st.firstlab.size = n) (hfre : CellsReach G st.firstlab)
    (hcsz : st.canonlab.size = n) (hcre : CellsReach G st.canonlab) :
    (processnode ctx level nc st).2.genTrace = st.genTrace ∨
      LabelCarrier ctx st.firstlab st.lab
        (processnode ctx level nc st).2.genTrace ∨
      LabelCarrier ctx st.canonlab st.lab
        (processnode ctx level nc st).2.genTrace := by
  rcases processnode_carrier hsymm hloop hfsz
      (labOk_of_reach hfsz hfre) (labInj_of_reach hfsz hn0 hfre)
      hdom.searchOk.labSize
      (labOk_of_reach hdom.searchOk.labSize hdom.searchOk.reach)
      (labInj_of_reach hdom.searchOk.labSize hn0 hdom.searchOk.reach)
      hcsz (labOk_of_reach hcsz hcre)
      (labInj_of_reach hcsz hn0 hcre)
      (fun htie => rows_eq_of_testcanlab_tie hdom.canongInv htie) with
    h | ⟨γ, hpush, hcheck, hmap⟩
  · exact Or.inl h
  · have hmem : γ ∈ (processnode ctx level nc st).2.genTrace := by
      rw [hpush]
      exact Array.mem_push.mpr (Or.inr rfl)
    rcases hmap with hfirst | hcanon
    · exact Or.inr (Or.inl ⟨γ, hmem, hcheck, hfirst⟩)
    · exact Or.inr (Or.inr ⟨γ, hmem, hcheck, hcanon⟩)

/-- The guarded code-one event yields the first-reference carrier directly,
without routing through the event-wide carrier disjunction. -/
theorem processnode_firstLabelCarrier {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n}
    (hsz₁ : st.firstlab.size = n)
    (hp₁ : st.firstlab.toList.Perm (List.range n))
    (hsz₂ : st.lab.size = n)
    (hp₂ : st.lab.toList.Perm (List.range n))
    (hsymm : ∀ i j, i < n → j < n →
      (ctx.g[i]!).mem j = (ctx.g[j]!).mem i)
    (hloop : ∀ i, i < n → (ctx.g[i]!).mem i = false)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == n) = true)
    (hpass : isautom ctx (firstScatter n st.firstlab st.lab) = true) :
    LabelCarrier ctx st.firstlab st.lab
      (processnode ctx level numcells st).2.genTrace := by
  obtain ⟨γ, hmem, hcheck, hmap⟩ := processnode_firstCarrier
    hsz₁ hp₁ hsz₂ hp₂ hsymm hloop heq hsent hnc
    (by simpa only [firstScatter] using hpass)
  exact ⟨γ, hmem, hcheck, hmap⟩

/-- The guarded code-two event yields the incumbent-reference carrier
directly, independently of its chosen return ancestor. -/
theorem processnode_canonLabelCarrier {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n}
    (hsz₁ : st.canonlab.size = n)
    (hp₁ : st.canonlab.toList.Perm (List.range n))
    (hsz₂ : st.lab.size = n)
    (hp₂ : st.lab.toList.Perm (List.range n))
    (hrows : leafRows ctx st.canonlab = leafRows ctx st.lab)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    LabelCarrier ctx st.canonlab st.lab
      (processnode ctx level numcells st).2.genTrace := by
  obtain ⟨γ, hmem, hcheck, hmap⟩ := processnode_canonCarrier
    hsz₁ hp₁ hsz₂ hp₂ hrows hef hnc hcc hge htie
  exact ⟨γ, hmem, hcheck, hmap⟩

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

/-- Consuming one cursor step preserves the strict remaining-fuel bound
used to rule out loop exhaustion. -/
theorem cursorFuel_step {cursor : Option Nat} {v fuel n : Nat}
    (hnext : After cursor v)
    (hfuel : n < cursorRank cursor + (fuel + 1)) :
    n < cursorRank (some v) + fuel := by
  have hstep := cursorRank_step hnext
  omega

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
theorem LoopResult.exhaustion_false
    {cursor finalCursor : Option Nat} {loopFuel : Nat}
    (hfuel : n < cursorRank cursor + loopFuel)
    (hprogress : cursorRank cursor + loopFuel ≤ cursorRank finalCursor)
    (hbounded : ∀ v, finalCursor = some v → v < n) : False := by
  have := cursorRank_le hbounded
  omega

/-- The prefixed specification key of offset `o` in a refined target
cell. -/
@[expose] def sweepKey (ctx : Ctx n) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc numcells o : Nat) : Key n :=
  prefixKey cs
    (childKey ctx tcLevel specFuel level rsLab rsPtn tc numcells o)

/-- A checked label carrier identifies the two children selected at an
ancestor, once the two leaf labellings are known at that ancestor's
individualized position. -/
theorem sweepKey_of_cellCarrier {ctx : Ctx n}
    (hgsz : ctx.g.size = n) {ref cur : Array Nat}
    {store : Array (Array Nat)} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells oRef oCur : Nat}
    (hcarrier : CellCarrier ctx rsPtn level rsLab ref cur store)
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
  obtain ⟨γ, _, haut, hmap, hstab⟩ := hcarrier
  apply congrArg (prefixKey cs)
  apply childKey_of_carried hgsz haut tcLevel specFuel level
    hstab hs hok hsp hend hvals hic hrange hcur href hlf
  have htc : tc < n := by
    omega
  have hm := hmap tc htc
  rwa [hatRef, hatCur] at hm

/-- The store-wide stabilization form used by orbit-local callers. -/
theorem sweepKey_of_carrier {ctx : Ctx n}
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
  exact sweepKey_of_cellCarrier hgsz
    ⟨γ, hγ, haut, hmap, hstab γ hγ⟩ hs hok hsp hend hvals hic
      hrange href hcur hlf hatRef hatCur

/-- The key of a non-discrete node is the maximum of the keys swept by
its child loop.  The loop prefix contains the node's refinement code. -/
theorem nodeKey_children {ctx : Ctx n} {tcLevel fuel level numcells len : Nat}
    {cs : List Nat} {st : SearchSt n}
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = false)
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
explicit rather than read from `SearchSt n`: during an upward code
comparison the executable overwrites `canoncode` before it installs the
new leaf, so the state temporarily contains no faithful incumbent key. -/
@[expose] def ChildDone (ctx : Ctx n) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (best : Option (Key n)) (o : Nat) : Prop :=
  ∃ b, best = some b ∧
    keyLe (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells o) b

/-- Offset `o` is still eligible after the loop cursor. -/
@[expose] def ChildLive (rsLab : Array Nat) (tc len : Nat) (tcell : VSet n)
    (cursor : Option Nat) (o : Nat) : Prop :=
  o < len ∧ tcell.mem rsLab[tc + o]! = true ∧
    After cursor rsLab[tc + o]!

/-- The evolving invariant of a mutable target-cell sweep.

`cover` follows removed children transitively to the current live suffix.
`past` records the ordering fact needed when a pruning automorphism carries
a live vertex backwards: every retained vertex at or before the cursor has
already been absorbed. -/
structure SweepCover (ctx : Ctx n) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells : Nat) (tcell : VSet n)
    (cursor : Option Nat) (best : Option (Key n)) : Prop where
  cover : ChildCover
    (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells)
    (fun o => rsLab[tc + o]!)
    (fun o => o < len)
    (ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells best)
    (ChildLive rsLab tc len tcell cursor)
  past : ∀ o, o < len → tcell.mem rsLab[tc + o]! = true →
    ¬ After cursor rsLab[tc + o]! →
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells best o

/-- Before the first iteration, the whole target-cell window is live. -/
theorem sweepCover_init (ctx : Ctx n) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells : Nat)
    (best : Option (Key n)) (hok : ∀ o, o < len → rsLab[tc + o]! < n) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (windowSet n rsLab tc len) none best := by
  constructor
  · intro o ho
    refine Or.inr ⟨o, ⟨ho, ?_, trivial⟩, rfl, Nat.le_refl _⟩
    refine mem_windowSet.mpr ⟨hok o ho, ?_⟩
    rw [segN]
    exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho, rfl⟩
  · intro o ho hm hpast
    exact absurd trivial hpast

/-- Coverage crosses an arbitrary loop step once old covered children stay
covered and every old survivor is either covered or replaced by a
key-equivalent new survivor. -/
theorem SweepCover.step {ctx : Ctx n} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : VSet n} {cursor cursor' : Option Nat}
    {best best' : Option (Key n)}
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
    (hpast : ∀ o, o < len → tcell'.mem rsLab[tc + o]! = true →
      ¬ After cursor' rsLab[tc + o]! →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        best' o) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor' best' := by
  exact ⟨ChildCover.step h.cover hs hd, hpast⟩

/-- Previously covered children remain covered when the incumbent grows. -/
theorem ChildDone.mono {ctx : Ctx n} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc numcells o : Nat}
    {best best' : Option (Key n)}
    (h : ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      best o)
    (hinc : ∀ b, best = some b →
      ∃ b', best' = some b' ∧ keyLe b b') :
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      best' o := by
  rcases h with ⟨b, hb, hkb⟩
  obtain ⟨b', hb', hbb'⟩ := hinc b hb
  exact ⟨b', hb', keyLe_trans hkb hbb'⟩

/-- The evolving sweep remains valid when the semantic incumbent grows. -/
theorem SweepCover.grow {ctx : Ctx n} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {best best' : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hinc : ∀ b, best = some b →
      ∃ b', best' = some b' ∧ keyLe b b') :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell cursor best' := by
  apply h.step
  · intro o ho
    exact Or.inr ⟨o, ho, rfl, Nat.le_refl _⟩
  · intro o hdone
    exact hdone.mono hinc
  · intro o ho hm hpast
    exact (h.past o ho hm hpast).mono hinc

/-- Coverage transfers across equality of two child keys. -/
theorem ChildDone.ofEq {ctx : Ctx n} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc numcells oRef oCur : Nat}
    {best : Option (Key n)}
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
`past`.  It need not remain in the live suffix. -/
theorem SweepCover.filter {ctx : Ctx n} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : VSet n} {cursor : Option Nat} {best : Option (Key n)}
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
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
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
the cursor, and `past` converts that case to completed coverage. -/
theorem SweepCover.filterCarried {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : VSet n} {cursor : Option Nat} {best : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      ∃ j, j < len ∧ tcell'.mem rsLab[tc + j]! = true ∧
        sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
            numcells j ∧
        rsLab[tc + j]! ≤ rsLab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
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
theorem SweepCover.filterDesc {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : VSet n} {cursor : Option Nat} {best : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      tcell'.mem rsLab[tc + o]! = true ∨
        ∃ j, j < len ∧
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells j ∧
          rsLab[tc + j]! < rsLab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
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
theorem SweepCover.filterAutom {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : VSet n} {cursor : Option Nat} {best : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hgsz : ctx.g.size = n) (hs : rsLab.size = n)
    (hok : LabOk rsLab n) (hsp : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hlf : level + 1 + specFuel ≤ n + 1)
    (hdrop : ∀ o, ChildLive rsLab tc len tcell cursor o →
      tcell'.mem rsLab[tc + o]! = false →
      ∃ γ, checkAutom ctx.g γ = true ∧
        CellStab rsPtn level rsLab γ ∧
        γ[rsLab[tc + o]!]! < rsLab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor best := by
  apply h.filterDesc _ hsub
  intro o ho
  rcases hm : tcell'.mem rsLab[tc + o]! with _ | _
  · obtain ⟨γ, hγ, hstab, hlt⟩ := hdrop o ho hm
    have hW : (windowSet n rsLab tc len).mem γ[rsLab[tc + o]!]! = true :=
      windowSet_carry hstab hic (by rw [hs]; exact hrange) hok
        (mem_windowSet.mpr ⟨hok _ (by have := ho.1; omega), by
          rw [segN]
          exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho.1, rfl⟩⟩)
    have hW' := (mem_windowSet.mp hW).2
    rw [segN] at hW'
    obtain ⟨j, hj, hcarry⟩ := List.mem_map.mp hW'
    have hjlt : j < len := List.mem_range.mp hj
    have hkey : childKey ctx tcLevel specFuel level rsLab rsPtn tc
        numcells j = childKey ctx tcLevel specFuel level rsLab rsPtn tc
          numcells o :=
      childKey_of_carried (n := n) (ctx := ctx) hgsz hγ
        tcLevel specFuel level hstab hs hok hsp hend hvals hic hrange
        hjlt ho.1 hlf hcarry.symm
    exact Or.inr ⟨j, hjlt, by
      unfold sweepKey
      rw [hkey], by simpa [hcarry] using hlt⟩
  · exact Or.inl rfl

/-- `longprune` preserves the evolving sweep under the autos ledger. -/
theorem SweepCover.longprune {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {fixedpts : VSet n} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {best : Option (Key n)} {out : SearchSt n}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hgsz : ctx.g.size = n) (hs : rsLab.size = n)
    (hok : LabOk rsLab n) (hsp : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hlf : level + 1 + specFuel ≤ n + 1)
    (haut : ∀ p ∈ out.autos.toList,
      (fixedpts.subset p.1) = true →
      PairOk ctx.g rsPtn rsLab level p.1 p.2) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (longprune tcell fixedpts out.autos) cursor best := by
  apply h.filterAutom hgsz hs hok hsp hend hvals hic hrange hlf
  · intro o ho hm
    change o < len ∧ tcell.mem rsLab[tc + o]! = true ∧
      After cursor rsLab[tc + o]! at ho
    exact longprune_drop (hok _ (by omega)) ho.2.1 hm haut
  · exact fun _ hm => longprune_subset hm

/-- `shortprune` preserves the evolving sweep under the last-pair ledger. -/
theorem SweepCover.shortprune {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {best : Option (Key n)} {out : SearchSt n}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hgsz : ctx.g.size = n) (hs : rsLab.size = n)
    (hok : LabOk rsLab n) (hsp : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hlf : level + 1 + specFuel ≤ n + 1)
    (hlast : ∀ fix mcr : VSet n, out.autos.back? = some (fix, mcr) →
      PairOk ctx.g rsPtn rsLab level fix mcr) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (shortprune tcell out) cursor best := by
  apply h.filterAutom hgsz hs hok hsp hend hvals hic hrange hlf
  · intro o ho hm
    change o < len ∧ tcell.mem rsLab[tc + o]! = true ∧
      After cursor rsLab[tc + o]! at ho
    exact shortprune_drop (hok _ (by omega)) ho.2.1 hm hlast
  · exact fun _ hm => shortprune_subset hm

/-- At loop completion the evolving coverage invariant says that every
offset in the original target cell has been absorbed. -/
theorem SweepCover.finish {ctx : Ctx n} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat}
    {best : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hempty : ∀ o, ¬ ChildLive rsLab tc len tcell cursor o) :
    ∀ o, o < len → ChildDone ctx tcLevel specFuel level cs rsLab rsPtn
      tc numcells best o :=
  ChildCover.finish h.cover hempty

/-- Completed child coverage bounds the maximum over the whole original
target cell, not merely the final filtered set. -/
theorem SweepCover.maxLe {ctx : Ctx n} {tcLevel specFuel level tail : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat}
    {tc numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {best : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc
      (tail + 1) numcells tcell cursor best)
    (hempty : ∀ o, ¬ ChildLive rsLab tc (tail + 1) tcell cursor o)
    {b : Key n} (hout : best = some b) :
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

/-- A partially explored sweep has the same maximum bound when every
remaining live representative is already dominated by the installed
incumbent. -/
theorem SweepCover.maxLeLive {ctx : Ctx n}
    {tcLevel specFuel level tail : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {best : Option (Key n)} {b : Key n}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc
      (tail + 1) numcells tcell cursor best)
    (hout : best = some b)
    (hlive : ∀ o, ChildLive rsLab tc (tail + 1) tcell cursor o →
      keyLe
        (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o)
        b) :
    keyLe
      (keysMax
        (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
            numcells (o + 1))) b := by
  have hall := h.cover.boundLive (b := b)
    (fun o hdone => by
      obtain ⟨b', hb', hle⟩ := hdone
      have : b' = b := Option.some.inj (hb'.symm.trans hout)
      rwa [this] at hle)
    hlive
  apply keysMax_le
  · exact hall 0 (by omega)
  · intro y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hy
    exact hall (o + 1) (by have := List.mem_range.mp ho; omega)

/-- A `none` cursor result means that no set member remains after the
cursor. -/
theorem no_child_after {s : VSet n} {cursor : Option Nat}
    (hnext : s.nextElem cursor = none) :
    ∀ v, s.mem v = true → After cursor v → False := by
  intro v hv ha
  have h := VSet.nextElem_none hnext v ?_
  · rw [hv] at h
    cases h
  · rcases cursor with _ | p
    · exact Nat.zero_le _
    · exact ha

/-- A successful `nextElem` lies strictly after its cursor. -/
theorem nextElem_after {s : VSet n} {v : Nat} {cursor : Option Nat}
    (hnext : s.nextElem cursor = some v) : After cursor v := by
  have h := (VSet.nextElem_eq_some_iff.mp hnext).2.1
  rcases cursor with _ | p
  · trivial
  · exact h

/-- `nextElem` returns the least set member strictly after its cursor. -/
theorem nextElem_le {s : VSet n} {v w : Nat} {cursor : Option Nat}
    (hnext : s.nextElem cursor = some v)
    (hw : s.mem w = true) (ha : After cursor w) : v ≤ w := by
  have h := (VSet.nextElem_eq_some_iff.mp hnext).2.2 w
  apply Nat.le_of_not_gt
  intro hlt
  have hz := h ?_ hlt
  · rw [hw] at hz
    cases hz
  · rcases cursor with _ | p
    · exact Nat.zero_le _
    · exact ha

/-- Advancing to the least remaining vertex preserves sweep coverage once
that vertex's child is absorbed.  The `hcur` premise identifies every
offset carrying the chosen vertex.  Callers normally discharge it from
labelling injectivity. -/
theorem SweepCover.advance {ctx : Ctx n} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells tv : Nat}
    {tcell : VSet n} {cursor : Option Nat} {best best' : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : tcell.nextElem cursor = some tv)
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
    change o < len ∧ tcell.mem rsLab[tc + o]! = true ∧
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
theorem SweepCover.done_of_smaller {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tv o j : Nat} {tcell : VSet n}
    {cursor : Option Nat} {best : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : tcell.nextElem cursor = some tv)
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
soundness supplies a smaller word-connected pointer target.  Cell
stabilization keeps that target in the sibling cell, and ranked coverage
shows it was already absorbed. -/
theorem SweepCover.orbitSkip {ctx : Ctx n}
    {tcLevel specFuel level tv o : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {best : Option (Key n)} {out : SearchSt n}
    {gens : List (Array Nat)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : tcell.nextElem cursor = some tv) (ho : o < len)
    (htv : rsLab[tc + o]! = tv)
    (hgsz : ctx.g.size = n)
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ = true)
    (hstab : ∀ γ ∈ gens, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hinj : LabInj rsLab rsLab.size)
    (hok : LabOk rsLab n) (hsp : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hlf : level + 1 + specFuel ≤ n + 1)
    (hsound : OrbSound (OrbConn gens n) out.orbits n)
    (hne : out.orbits[tv]! ≠ tv) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell (some tv) best := by
  have hvn : tv < n := by rw [← htv]; exact hok _ (by omega)
  obtain ⟨_, hconn⟩ := orbConn_of_ptr hsound hvn
  unfold WordConn at hconn
  obtain ⟨w, hw, happ⟩ := hconn
  obtain ⟨_, hwstab, hwpoint⟩ :=
    wordPerm_spec hok hsp hs hend hv hstab w hw
  have hW : (windowSet n rsLab tc len).mem out.orbits[tv]! = true := by
    have := windowSet_carry (u := rsLab[tc + o]!) hwstab hic
      (by rw [hs]; exact hrange) hok
      (mem_windowSet.mpr ⟨hok _ (by omega), by
        rw [segN]
        exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho, rfl⟩⟩)
    rw [htv, hwpoint _ hvn, happ] at this
    exact this
  have hW' := (mem_windowSet.mp hW).2
  rw [segN] at hW'
  obtain ⟨j, hj, hptr⟩ := List.mem_map.mp hW'
  have hjlt : j < len := List.mem_range.mp hj
  have hptr' : out.orbits[rsLab[tc + o]!]! = rsLab[tc + j]! := by
    rw [htv]
    exact hptr.symm
  have hkey : sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells o =
        sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells j := by
    unfold sweepKey
    rw [childKey_of_orbitPtr (n := n) (ctx := ctx) hgsz hv
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
theorem SweepCover.finish_of_nextElem {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {best : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : tcell.nextElem cursor = none) :
    ∀ o, o < len → ChildDone ctx tcLevel specFuel level cs rsLab rsPtn
      tc numcells best o := by
  apply h.finish
  intro o ho
  exact no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- A child at an ancestor has already been absorbed.  The arrays and
offset are stored explicitly because neither `gcaFirst` nor `gcaCanon`
retains this path history. -/
structure Anchor (ctx : Ctx n) (tcLevel target : Nat)
    (best : Option (Key n)) where
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
@[expose] def Anchor.ofCellCarrier {ctx : Ctx n}
    (hgsz : ctx.g.size = n) {tcLevel level specFuel : Nat}
    {codes : List Nat} {rsLab rsPtn ref cur : Array Nat}
    {store : Array (Array Nat)} {tc len numcells oRef oCur : Nat}
    {best : Option (Key n)} (hpos : 1 ≤ level)
    (hdone : ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells best oRef)
    (hcarrier : CellCarrier ctx rsPtn level rsLab ref cur store)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (href : oRef < len) (hcur : oCur < len)
    (hlf : level + 1 + specFuel ≤ n + 1)
    (hatRef : ref[tc]! = rsLab[tc + oRef]!)
    (hatCur : cur[tc]! = rsLab[tc + oCur]!) :
    Anchor ctx tcLevel level best := by
  refine ⟨hpos, specFuel, codes, rsLab, rsPtn, tc, numcells, oCur, ?_⟩
  apply hdone.ofEq
  exact sweepKey_of_cellCarrier hgsz hcarrier hs hok hsp hend hvals
    hic hrange href hcur hlf hatRef hatCur

/-- Store-wide stabilization implies the witness-local form. -/
@[expose] def Anchor.ofCarrier {ctx : Ctx n}
    (hgsz : ctx.g.size = n) {tcLevel level specFuel : Nat}
    {codes : List Nat} {rsLab rsPtn ref cur : Array Nat}
    {store : Array (Array Nat)} {tc len numcells oRef oCur : Nat}
    {best : Option (Key n)} (hpos : 1 ≤ level)
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
  exact sweepKey_of_carrier hgsz hcarrier hstab hs hok hsp hend hvals
    hic hrange href hcur hlf hatRef hatCur

/-- A code-two return to `gcaFirst` is justified by the updated orbit
pointer rather than by the direct canonical carrier.  The receiving loop
uses this sound pointer together with its own coverage frame. -/
structure OrbitUnwind (ctx : Ctx n) (target : Nat) (out : SearchSt n) : Prop where
  positive : 1 ≤ target
  bound : target ≤ out.gcaFirst
  currentLt : out.cosetindex < n
  smaller : out.orbits[out.cosetindex]! < out.cosetindex
  sound : OrbSound (OrbConn out.genTrace.toList n) out.orbits n

/-- The evidence carried by a generator unwind.  Code one and the
ordinary code-two return retain their different reference labellings.
Code two's special `gcaFirst` return retains the sound orbit pointer that
selected an earlier child.  Non-generator pruning instead returns a
locally complete maximum and therefore has its own result constructor. -/
inductive Unwind (ctx : Ctx n) (tcLevel target : Nat)
    (out : SearchSt n) (best : Option (Key n)) where
  | first (anchor : Anchor ctx tcLevel target best)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace)
  | canon (anchor : Anchor ctx tcLevel target best)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
  | orbit (payload : OrbitUnwind ctx target out)

/-- Updating the first-path return controls changes none of the fields
carried by a generator unwind. -/
@[expose] def Unwind.setFirst {ctx : Ctx n} {tcLevel target : Nat}
    {out : SearchSt n} {best : Option (Key n)} (h : Unwind ctx tcLevel target out best)
    (gcaFirst stabvertex : Nat) (hbound : target ≤ gcaFirst) :
    Unwind ctx tcLevel target
      { out with gcaFirst := gcaFirst, stabvertex := stabvertex } best := by
  cases h with
  | first anchor carrier => exact .first anchor carrier
  | canon anchor carrier => exact .canon anchor carrier
  | orbit payload =>
      apply Unwind.orbit
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact payload.positive
      · exact hbound
      · exact payload.currentLt
      · exact payload.smaller
      · exact payload.sound

/-- Removing a loop's temporary fixed vertex changes none of the fields
carried by a generator unwind. -/
@[expose] def Unwind.setFixed {ctx : Ctx n} {tcLevel target : Nat}
    {out : SearchSt n} {best : Option (Key n)} (h : Unwind ctx tcLevel target out best)
    (fixedpts : VSet n) :
    Unwind ctx tcLevel target { out with fixedpts := fixedpts } best := by
  cases h with
  | first anchor carrier => exact .first anchor carrier
  | canon anchor carrier => exact .canon anchor carrier
  | orbit payload =>
      apply Unwind.orbit
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact payload.positive
      · exact payload.bound
      · exact payload.currentLt
      · exact payload.smaller
      · exact payload.sound

/-- A semantic incumbent can only improve across a search fragment. -/
@[expose] def IncGrows (best out : Option (Key n)) : Prop :=
  ∀ b, best = some b → ∃ b', out = some b' ∧ keyLe b b'

/-- A previously explored child together with the ancestor geometry needed
to reuse it as a generator guide.  Unlike `gcaFirst` and `gcaCanon`, this
keeps the reference labelling and the exact target-cell frame. -/
structure Guide (ctx : Ctx n) (tcLevel target : Nat)
    (best : Option (Key n)) where
  positive : 1 ≤ target
  specFuel : Nat
  codes : List Nat
  rsLab : Array Nat
  rsPtn : Array Nat
  ref : Array Nat
  tc : Nat
  len : Nat
  numcells : Nat
  offset : Nat
  done : ChildDone ctx tcLevel specFuel target codes rsLab rsPtn tc
    numcells best offset
  labSize : rsLab.size = n
  labOk : LabOk rsLab n
  ptnSize : rsPtn.size = n
  endClosed : rsPtn[rsPtn.size - 1]! ≤ target
  values : ∀ q : Nat, rsPtn[q]! ≤ target ∨
    rsPtn[q]! = n + 2
  cell : IsCell rsPtn target tc len
  range : tc + len ≤ n
  offsetLt : offset < len
  fuelBound : target + 1 + specFuel ≤ n + 1
  atRef : ref[tc]! = rsLab[tc + offset]!
  refSize : ref.size = n
  refReach : cellsPerm rsPtn target rsLab ref

/-- A guide remains usable after the incumbent grows.  Cell stabilization
of the current generator store and the current child's ancestor position
are the only facts that must be supplied at the leaf event. -/
@[expose] def Guide.anchor {ctx : Ctx n} {tcLevel target : Nat}
    {best best' : Option (Key n)} (g : Guide ctx tcLevel target best)
    (hgsz : ctx.g.size = n) (hinc : IncGrows best best')
    {cur : Array Nat} {store : Array (Array Nat)} {oCur : Nat}
    (hcarrier : LabelCarrier ctx g.ref cur store)
    (hstab : ∀ γ ∈ store, CellStab g.rsPtn target g.rsLab γ)
    (hcur : oCur < g.len)
    (hatCur : cur[g.tc]! = g.rsLab[g.tc + oCur]!) :
    Anchor ctx tcLevel target best' := by
  apply Anchor.ofCarrier hgsz g.positive (g.done.mono hinc)
    hcarrier hstab g.labSize g.labOk g.ptnSize g.endClosed g.values
    g.cell g.range g.offsetLt hcur g.fuelBound g.atRef hatCur

/-- A witness-local carrier is enough for a direct generator unwind. -/
@[expose] def Guide.anchorCell {ctx : Ctx n} {tcLevel target : Nat}
    {best best' : Option (Key n)} (g : Guide ctx tcLevel target best)
    (hgsz : ctx.g.size = n) (hinc : IncGrows best best')
    {cur : Array Nat} {store : Array (Array Nat)} {oCur : Nat}
    (hcarrier : CellCarrier ctx g.rsPtn target g.rsLab g.ref cur store)
    (hcur : oCur < g.len)
    (hatCur : cur[g.tc]! = g.rsLab[g.tc + oCur]!) :
    Anchor ctx tcLevel target best' := by
  apply Anchor.ofCellCarrier hgsz g.positive (g.done.mono hinc)
    hcarrier g.labSize g.labOk g.ptnSize g.endClosed g.values
    g.cell g.range g.offsetLt hcur g.fuelBound g.atRef hatCur

/-- A successful code-one leaf admission, paired with its concrete
first-path guide, produces the corresponding generator unwind payload. -/
theorem Guide.firstUnwind {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : SearchSt n} {best : Option (Key n)}
    (g : Guide ctx tcLevel st.gcaFirst best)
    (href : g.ref = st.firstlab)
    (hgsz : ctx.g.size = n)
    (hsz₁ : st.firstlab.size = n)
    (hp₁ : st.firstlab.toList.Perm (List.range n))
    (hsz₂ : st.lab.size = n)
    (hp₂ : st.lab.toList.Perm (List.range n))
    (hsymm : ∀ i j, i < n → j < n →
      (ctx.g[i]!).mem j = (ctx.g[j]!).mem i)
    (hloop : ∀ i, i < n → (ctx.g[i]!).mem i = false)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == n) = true)
    (hpass : isautom ctx (firstScatter n st.firstlab st.lab) = true)
    (hcurReach : cellsPerm g.rsPtn st.gcaFirst g.rsLab st.lab)
    {oCur : Nat} (hcur : oCur < g.len)
    (hatCur : st.lab[g.tc]! = g.rsLab[g.tc + oCur]!) :
    Nonempty (Unwind ctx tcLevel st.gcaFirst
      (processnode ctx level numcells st).2 best) := by
  have hcarrier := processnode_firstLabelCarrier hsz₁ hp₁ hsz₂ hp₂
    hsymm hloop heq hsent hnc hpass
  have hcarrierG : LabelCarrier ctx g.ref st.lab
      (processnode ctx level numcells st).2.genTrace := by
    rw [href]
    exact hcarrier
  obtain ⟨γ, hγ, haut, hmap⟩ := hcarrierG
  have hrefReach : cellsPerm g.rsPtn st.gcaFirst g.rsLab st.firstlab := by
    rw [← href]
    exact g.refReach
  have hcell : CellCarrier ctx g.rsPtn st.gcaFirst g.rsLab g.ref st.lab
      (processnode ctx level numcells st).2.genTrace :=
    ⟨γ, hγ, haut, hmap,
      cellStab_of_scatter g.ptnSize g.labSize hsz₁ g.endClosed
        hrefReach hcurReach (by simpa only [href] using hmap)⟩
  have hinc : IncGrows best best := by
    intro b hb
    exact ⟨b, hb, keyLe_refl b⟩
  have hanchor := g.anchorCell hgsz hinc hcell hcur hatCur
  have hframes := processnode_frames ctx level numcells st
  rcases hframes with ⟨hlab, _, _, _, hfirst, _, _, _, _⟩
  refine ⟨Unwind.first hanchor ?_⟩
  rw [hfirst, hlab]
  exact hcarrier

/-- A successful code-two leaf admission, paired with the selected
canonical guide, produces the corresponding generator unwind payload. -/
theorem Guide.canonUnwind {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : SearchSt n} {best : Option (Key n)}
    (g : Guide ctx tcLevel st.gcaCanon best)
    (href : g.ref = st.canonlab)
    (hgsz : ctx.g.size = n)
    (hsz₁ : st.canonlab.size = n)
    (hp₁ : st.canonlab.toList.Perm (List.range n))
    (hsz₂ : st.lab.size = n)
    (hp₂ : st.lab.toList.Perm (List.range n))
    (hrows : leafRows ctx st.canonlab = leafRows ctx st.lab)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0)
    (hcurReach : cellsPerm g.rsPtn st.gcaCanon g.rsLab st.lab)
    {oCur : Nat} (hcur : oCur < g.len)
    (hatCur : st.lab[g.tc]! = g.rsLab[g.tc + oCur]!) :
    Nonempty (Unwind ctx tcLevel st.gcaCanon
      (processnode ctx level numcells st).2 best) := by
  have hcarrier := processnode_canonLabelCarrier hsz₁ hp₁ hsz₂ hp₂
    hrows hef hnc hcc hge htie
  have hcarrierG : LabelCarrier ctx g.ref st.lab
      (processnode ctx level numcells st).2.genTrace := by
    rw [href]
    exact hcarrier
  obtain ⟨γ, hγ, haut, hmap⟩ := hcarrierG
  have hrefReach : cellsPerm g.rsPtn st.gcaCanon g.rsLab st.canonlab := by
    rw [← href]
    exact g.refReach
  have hcell : CellCarrier ctx g.rsPtn st.gcaCanon g.rsLab g.ref st.lab
      (processnode ctx level numcells st).2.genTrace :=
    ⟨γ, hγ, haut, hmap,
      cellStab_of_scatter g.ptnSize g.labSize hsz₁ g.endClosed
        hrefReach hcurReach (by simpa only [href] using hmap)⟩
  have hinc : IncGrows best best := by
    intro b hb
    exact ⟨b, hb, keyLe_refl b⟩
  have hanchor := g.anchorCell hgsz hinc hcell hcur hatCur
  obtain ⟨_, _, _, _, _, hcanon, _, _⟩ :=
    processnode_rowTie hef hnc hcc hge htie
  have hframes := processnode_frames ctx level numcells st
  refine ⟨Unwind.canon hanchor ?_⟩
  rw [hcanon, hframes.1]
  exact hcarrier

/-- A row-tied code-two event is either the direct canonical-guide unwind,
or the special first-ancestor orbit unwind selected by a smaller pointer. -/
theorem Guide.tiedUnwind {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : SearchSt n} {best : Option (Key n)}
    (g : Guide ctx tcLevel st.gcaCanon best)
    (href : g.ref = st.canonlab)
    (hgsz : ctx.g.size = n)
    (hsz₁ : st.canonlab.size = n)
    (hp₁ : st.canonlab.toList.Perm (List.range n))
    (hsz₂ : st.lab.size = n)
    (hp₂ : st.lab.toList.Perm (List.range n))
    (hrows : leafRows ctx st.canonlab = leafRows ctx st.lab)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0)
    (hcanonBelow : st.gcaCanon < level)
    (hfirstPos : 1 ≤ st.gcaFirst) (hfirstBelow : st.gcaFirst < level)
    (hcurReach : cellsPerm g.rsPtn st.gcaCanon g.rsLab st.lab)
    {oCur : Nat} (hcur : oCur < g.len)
    (hatCur : st.lab[g.tc]! = g.rsLab[g.tc + oCur]!)
    (hcoset : (processnode ctx level numcells st).2.cosetindex < n)
    (horbit : OrbSound
      (OrbConn (processnode ctx level numcells st).2.genTrace.toList n)
      (processnode ctx level numcells st).2.orbits n) :
    ∃ target, (processnode ctx level numcells st).1 = Int.ofNat target ∧
      target < level ∧
      Nonempty (Unwind ctx tcLevel target
        (processnode ctx level numcells st).2 best) := by
  rcases processnode_rowTie_orbit hef hnc hcc hge htie with hcanon |
      ⟨hfirst, hsmaller⟩
  · exact ⟨st.gcaCanon, hcanon, hcanonBelow,
      g.canonUnwind href hgsz hsz₁ hp₁ hsz₂ hp₂ hrows
        hef hnc hcc hge htie hcurReach hcur hatCur⟩
  · exact ⟨st.gcaFirst, hfirst, hfirstBelow,
      ⟨.orbit ⟨hfirstPos, by
        rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
        exact Nat.le_refl _, hcoset, hsmaller, horbit⟩⟩⟩

/-- A guide's covered child remains covered when the incumbent grows. -/
@[expose] def Guide.mono {ctx : Ctx n} {tcLevel target : Nat}
    {best best' : Option (Key n)} (g : Guide ctx tcLevel target best)
    (hinc : IncGrows best best') : Guide ctx tcLevel target best' :=
  { g with done := g.done.mono hinc }

/-- The first and canonical generator guides that are live strictly above
the current node.  A guide at the current level is not required: leaf
installation temporarily sets a gca to the leaf level, and the parent
loop replaces it with a concrete explored-child guide. -/
structure Guides (ctx : Ctx n) (tcLevel level : Nat) (st : SearchSt n)
    (best : Option (Key n)) : Prop where
  first : 0 < st.gcaFirst → st.gcaFirst < level →
    ∃ g : Guide ctx tcLevel st.gcaFirst best, g.ref = st.firstlab
  canon : 0 < st.gcaCanon → st.gcaCanon < level →
    ∃ g : Guide ctx tcLevel st.gcaCanon best, g.ref = st.canonlab

/-- Both guide ledgers survive an incumbent increase. -/
theorem Guides.grow {ctx : Ctx n} {tcLevel level : Nat} {st : SearchSt n}
    {best best' : Option (Key n)} (h : Guides ctx tcLevel level st best)
    (hinc : IncGrows best best') : Guides ctx tcLevel level st best' := by
  constructor
  · intro hp hlt
    obtain ⟨g, href⟩ := h.first hp hlt
    exact ⟨g.mono hinc, href⟩
  · intro hp hlt
    obtain ⟨g, href⟩ := h.canon hp hlt
    exact ⟨g.mono hinc, href⟩

/-- The root has no live generator guide. -/
theorem Guides.root {n : Nat} (g : Array (VSet n)) (lab : Array Nat) (cellEnds : List Nat)
    (tcLevel : Nat) (best : Option (Key n)) :
    Guides { g := g } tcLevel 1 (rootSt n lab cellEnds) best := by
  constructor <;> intro hp _ <;> simp [rootSt] at hp

/-- Every installed output came from the incoming incumbent or this
node's specification subtree, and the incoming incumbent was not lost. -/
structure NodeSound (ctx : Ctx n) (tcLevel specFuel level : Nat)
    (cs : List Nat) (st : SearchSt n) (numcells : Nat)
    (best out : Option (Key n)) : Prop where
  upper : ∀ b, out = some b →
    keyLe b (incMax best
      (nodeKey ctx tcLevel specFuel level cs st numcells))
  grows : IncGrows best out

/-- The state component common to both successful loop outcomes.  The
loop may stop early, but every incumbent it installs is still bounded by
the incoming incumbent and the whole parent subtree. -/
structure LoopSound (ctx : Ctx n) (bound : Key n)
    (best out : Option (Key n)) : Prop where
  upper : ∀ b, out = some b → keyLe b (incMax best bound)
  grows : IncGrows best out

theorem IncGrows.refl (best : Option (Key n)) : IncGrows best best := by
  intro b hb
  exact ⟨b, hb, keyLe_refl b⟩

/-- Folding one key into an incumbent preserves the incoming incumbent. -/
theorem IncGrows.incMax (best : Option (Key n)) (K : Key n) :
    IncGrows best (some (incMax best K)) := by
  intro b hb
  rcases best with _ | a
  · cases hb
  · injection hb with hab
    subst hab
    exact ⟨Nauty.incMax (some a) K, rfl,
      keyLe_iff.mpr (keyMax_not_lt_left a K)⟩

theorem NodeSound.refl (ctx : Ctx n) (tcLevel specFuel level : Nat)
    (cs : List Nat) (st : SearchSt n) (numcells : Nat) (best : Option (Key n)) :
    NodeSound ctx tcLevel specFuel level cs st numcells best best := by
  constructor
  · intro b hb
    rw [hb, incMax]
    exact keyLe_iff.mpr (keyMax_not_lt_left _ _)
  · exact IncGrows.refl best

/-- An exact node maximum supplies both clauses of `NodeSound`. -/
theorem NodeSound.ofExact {ctx : Ctx n} {tcLevel specFuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt n} {best out : Option (Key n)}
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

theorem LoopSound.refl (ctx : Ctx n) (bound : Key n) (best : Option (Key n)) :
    LoopSound ctx bound best best := by
  constructor
  · intro b hb
    rw [hb, incMax]
    exact keyLe_iff.mpr (keyMax_not_lt_left _ _)
  · exact IncGrows.refl best

/-- An exact loop maximum supplies both clauses of `LoopSound`. -/
theorem LoopSound.ofExact {ctx : Ctx n} {bound : Key n}
    {best out : Option (Key n)}
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

theorem keyMax_le_of_le {a b c : Key n} (ha : keyLe a c)
    (hb : keyLe b c) : keyLe (keyMax a b) c := by
  rcases keyMax_mem a b with h | h
  · rwa [h]
  · rwa [h]

theorem keyLe_incMax_right (inc : Option (Key n)) (b : Key n) :
    keyLe b (incMax inc b) := by
  rcases inc with _ | a
  · exact keyLe_refl b
  · exact keyLe_iff.mpr (keyMax_not_lt_right a b)

/-- An exactly completed child is covered in its parent sweep.  The three
field equations identify the executable state after `breakout` with the
specification child used by `sweepKey`. -/
theorem ChildDone.ofExact {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc numcells o : Nat}
    {child : SearchSt n} {best out : Option (Key n)}
    (hfull : out = some (incMax best
      (nodeKey ctx tcLevel specFuel (level + 1) cs child
        (numcells + 1))))
    (hlab : child.lab =
      (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1)
    (hptn : child.ptn =
      (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1)
    (hactive : child.active =
      (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2) :
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      out o := by
  refine ⟨incMax best
    (nodeKey ctx tcLevel specFuel (level + 1) cs child
      (numcells + 1)), hfull, ?_⟩
  have heq : sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells o =
      nodeKey ctx tcLevel specFuel (level + 1) cs child
        (numcells + 1) := by
    unfold sweepKey nodeKey childKey
    rw [hlab, hptn, hactive]
  rw [heq]
  exact keyLe_incMax_right best _

/-- Exact completion of the selected child advances the mutable sweep
cursor and preserves all earlier coverage. -/
theorem SweepCover.advanceExact {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tv : Nat} {tcell : VSet n}
    {cursor : Option Nat} {child : SearchSt n} {best out : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : tcell.nextElem cursor = some tv)
    (hfull : out = some (incMax best
      (nodeKey ctx tcLevel specFuel (level + 1) cs child
        (numcells + 1))))
    (hlab : child.lab =
      (breakout n rsLab rsPtn (level + 1) tc tv).1)
    (hptn : child.ptn =
      (breakout n rsLab rsPtn (level + 1) tc tv).2.1)
    (hactive : child.active =
      (breakout n rsLab rsPtn (level + 1) tc tv).2.2) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell (some tv) out := by
  apply h.advance hnext
  · intro o ho hotv
    apply ChildDone.ofExact hfull
    · simpa only [hotv] using hlab
    · simpa only [hotv] using hptn
    · simpa only [hotv] using hactive
  · intro o hdone
    exact hdone.mono (hfull ▸ IncGrows.incMax best _)

theorem incMax_mono_right (inc : Option (Key n)) {a b : Key n}
    (h : keyLe a b) : keyLe (incMax inc a) (incMax inc b) := by
  rcases inc with _ | x
  · exact h
  · apply keyMax_le_of_le
    · exact keyLe_iff.mpr (keyMax_not_lt_left x b)
    · exact keyLe_trans h (keyLe_iff.mpr (keyMax_not_lt_right x b))

theorem IncGrows.trans {best mid out : Option (Key n)}
    (h₁ : IncGrows best mid) (h₂ : IncGrows mid out) :
    IncGrows best out := by
  intro b hb
  obtain ⟨m, hm, hbm⟩ := h₁ b hb
  obtain ⟨c, hc, hmc⟩ := h₂ m hm
  exact ⟨c, hc, keyLe_trans hbm hmc⟩

/-- A sound child step is sound against any larger fixed loop bound. -/
theorem LoopSound.ofNode {ctx : Ctx n} {tcLevel specFuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt n} {bound : Key n}
    {best out : Option (Key n)}
    (h : NodeSound ctx tcLevel specFuel level cs st numcells best out)
    (hle : keyLe (nodeKey ctx tcLevel specFuel level cs st numcells)
      bound) : LoopSound ctx bound best out := by
  constructor
  · intro b hb
    exact keyLe_trans (h.upper b hb)
      (incMax_mono_right best hle)
  · exact h.grows

/-- Consecutive fragments with the same fixed bound compose. -/
theorem LoopSound.trans {ctx : Ctx n} {bound : Key n}
    {best mid out : Option (Key n)} (h₁ : LoopSound ctx bound best mid)
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
theorem LoopSound.exact {ctx : Ctx n} {bound b : Key n}
    {best out : Option (Key n)} (h : LoopSound ctx bound best out)
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

/-- Loop soundness plus domination of every live suffix recovers the
exact fixed bound without pretending that the executable loop completed. -/
theorem SweepCover.exactLive {ctx : Ctx n}
    {tcLevel specFuel level tail : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound b : Key n} {best out : Option (Key n)}
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells (o + 1)))
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc
      (tail + 1) numcells tcell cursor out)
    (hsound : LoopSound ctx bound best out)
    (hout : out = some b)
    (hlive : ∀ o, ChildLive rsLab tc (tail + 1) tcell cursor o →
      keyLe
        (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o)
        b) :
    out = some (incMax best bound) := by
  apply hsound.exact hout
  rw [hbound]
  exact h.maxLeLive hout hlive

/-- A completed sweep whose fixed loop bound is the maximum of its
original children recovers the exact final incumbent. -/
theorem SweepCover.exact {ctx : Ctx n} {tcLevel specFuel level tail : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat}
    {tc numcells : Nat} {tcell : VSet n} {cursor : Option Nat}
    {best out : Option (Key n)} {b : Key n}
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

/-- An installed mutable incumbent always has a concrete key. -/
theorem stInc_isSome {ctx : Ctx n} {st : SearchSt n}
    (h : st.canonlevel ≠ 0) : ∃ b, stInc ctx st = some b := by
  rw [stInc, ite_eq_right h]
  exact ⟨_, rfl⟩

/-- A completed covered sweep with a readable installed state has exactly
folded its fixed child maximum into the incoming incumbent. -/
theorem SweepCover.exact_of_read {ctx : Ctx n}
    {tcLevel specFuel level tail : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {st : SearchSt n}
    {best out : Option (Key n)}
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
        numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells (o + 1)))
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc
      (tail + 1) numcells tcell cursor out)
    (hempty : ∀ o, ¬ ChildLive rsLab tc (tail + 1) tcell cursor o)
    (hsound : LoopSound ctx bound best out)
    (hinstalled : st.canonlevel ≠ 0) (hread : stInc ctx st = out) :
    out = some (incMax best bound) := by
  obtain ⟨b, hb⟩ := stInc_isSome hinstalled
  have hout : out = some b := hread.symm.trans hb
  rw [hbound]
  exact hcover.exact hempty (hbound ▸ hsound) hout

/-- The result of a node call, with logical and runtime fuel separated.

`complete` and `unwind` may have the same return integer.  The latter is
therefore a constructor, not an inequality side condition. -/
inductive NodeResult (ctx : Ctx n) (tcLevel specFuel runFuel level : Nat)
    (cs : List Nat) (st out : SearchSt n) (numcells : Nat)
    (best outBest : Option (Key n)) (r : Int) : Prop where
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
  | pruned (sound : NodeSound ctx tcLevel specFuel level cs st numcells
      best outBest)
      (target : Int) (returned : r = target)
      (below : target < Int.ofNat level)
      (installed : out.canonlevel ≠ 0)
      (read : stInc ctx out = outBest)
      (full : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level cs st numcells)))
  | exhausted (empty : runFuel = 0) (returned : r = 0)
      (unchanged : out = st) (bestUnchanged : outBest = best)

/-- When a child does not return past its parent, it either completed its
whole subtree (including a local comparison prune), or its generator
payload is addressed exactly to that parent. -/
theorem NodeResult.parentReturn {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat}
    {cs : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
    {r : Int}
    (h : NodeResult ctx tcLevel specFuel runFuel (level + 1) cs st out
      numcells best outBest r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level)) :
    outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel (level + 1) cs st numcells)) ∨
      Nonempty (Unwind ctx tcLevel level out outBest) := by
  cases h with
  | complete sound returned installed read full => exact Or.inl full
  | unwind sound target returned below payload =>
      have hle : level ≤ target := by
        apply Int.ofNat_le.mp
        rw [returned] at hstay
        exact Int.not_lt.mp hstay
      have htarget : target = level := by
        omega
      subst target
      exact Or.inr ⟨payload⟩
  | pruned sound target returned below installed read full => exact Or.inl full
  | exhausted empty returned unchanged bestUnchanged => exact (hfuel empty).elim

/-- The result of a child-loop call.  Exhaustion is distinct from a
completed empty remainder, so a general theorem cannot accidentally treat
the `cfuel = 0` arm as coverage of every child. -/
inductive LoopResult (ctx : Ctx n) (tcLevel specFuel runFuel loopFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells : Nat) (tcell : VSet n)
    (cursor : Option Nat) (bound : Key n) (st out : SearchSt n)
    (best outBest : Option (Key n)) (r : Option Int) : Prop where
  | complete
      (returned : r = none)
      (sound : LoopSound ctx bound best outBest)
      (installed : out.canonlevel ≠ 0)
      (read : stInc ctx out = outBest)
      (finalSet : VSet n) (finalCursor : Option Nat)
      (cover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
        numcells finalSet finalCursor outBest)
      (empty : ∀ o, ¬ ChildLive rsLab tc len finalSet finalCursor o)
  | unwind (sound : LoopSound ctx bound best outBest)
      (target : Nat) (returned : r = some (Int.ofNat target))
      (below : target < level)
      (payload : Unwind ctx tcLevel target out outBest)
  | pruned (target : Int) (returned : r = some target)
      (below : target < Int.ofNat level)
      (sound : LoopSound ctx bound best outBest)
      (installed : out.canonlevel ≠ 0)
      (read : stInc ctx out = outBest)
      (full : outBest = some (incMax best bound))
  | exhausted
      (returned : r = none)
      (sound : LoopSound ctx bound best outBest)
      (finalSet : VSet n) (finalCursor : Option Nat)
      (cover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
        numcells finalSet finalCursor outBest)
      (progress : cursorRank cursor + loopFuel ≤ cursorRank finalCursor)
      (bounded : ∀ v, finalCursor = some v → v < n)

/-- A child generator unwind strictly past its parent lifts through the
parent loop's temporary fixed-vertex cleanup. -/
theorem LoopResult.ofChildUnwind {ctx : Ctx n}
    {tcLevel childFuel childRunFuel parentFuel loopFuel level : Nat}
    {childCs loopCs : List Nat} {childNumcells loopNumcells : Nat}
    {childSt loopSt out : SearchSt n} {best outBest : Option (Key n)}
    {target : Nat} {fixedpts : VSet n}
    {rsLab rsPtn : Array Nat} {tc len : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n}
    (hsound : NodeSound ctx tcLevel childFuel (level + 1) childCs childSt
      childNumcells best outBest)
    (hkey : keyLe
      (nodeKey ctx tcLevel childFuel (level + 1) childCs childSt
        childNumcells) bound)
    (hbelow : target < level)
    (hpayload : Unwind ctx tcLevel target out outBest) :
    LoopResult ctx tcLevel parentFuel childRunFuel loopFuel level loopCs
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt
      { out with fixedpts := fixedpts } best outBest
      (some (Int.ofNat target)) := by
  apply LoopResult.unwind
  · constructor
    · intro b hb
      exact keyLe_trans (hsound.upper b hb) (incMax_mono_right best hkey)
    · exact hsound.grows
  · rfl
  · exact hbelow
  · exact hpayload.setFixed fixedpts

/-- A readable completed child sweep constructs ordinary node completion
once the specification identifies that sweep's fixed bound with the node
subtree. -/
theorem NodeResult.complete_of_sweep {ctx : Ctx n}
    {tcLevel specFuel runFuel level nodeNumcells loopNumcells tail : Nat}
    {nodeCs loopCs : List Nat} {st out : SearchSt n}
    {best outBest : Option (Key n)}
    {r : Int} {rsLab rsPtn : Array Nat} {tc : Nat} {tcell : VSet n}
    {cursor : Option Nat}
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCs st nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hsound : LoopSound ctx
      (nodeKey ctx tcLevel (specFuel + 1) level nodeCs st nodeNumcells)
      best outBest)
    (hinstalled : out.canonlevel ≠ 0) (hread : stInc ctx out = outBest)
    (hcover : SweepCover ctx tcLevel specFuel level loopCs rsLab rsPtn tc
      (tail + 1) loopNumcells tcell cursor outBest)
    (hempty : ∀ o, ¬ ChildLive rsLab tc (tail + 1) tcell cursor o)
    (hreturn : r = Int.ofNat level - 1) :
    NodeResult ctx tcLevel (specFuel + 1) runFuel level nodeCs st out
      nodeNumcells best outBest r := by
  have hfull := hcover.exact_of_read hchildren hempty hsound
    hinstalled hread
  exact .complete (NodeSound.ofExact hfull) hreturn hinstalled hread hfull

/-- A loop that has already absorbed its fixed child bound constructs the
corresponding pruned node outcome when that bound is the node subtree. -/
theorem NodeResult.pruned_of_loop {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat}
    {cs : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
    {r target : Int}
    (hinstalled : out.canonlevel ≠ 0) (hread : stInc ctx out = outBest)
    (hfull : outBest = some (incMax best
      (nodeKey ctx tcLevel specFuel level cs st numcells)))
    (hreturn : r = target) (hbelow : target < Int.ofNat level) :
    NodeResult ctx tcLevel specFuel runFuel level cs st out numcells
      best outBest r :=
  .pruned (NodeSound.ofExact hfull) target hreturn hbelow hinstalled hread
    hfull

/-- A loop return carrying an integer lifts directly through its parent
node.  The impossible completed and exhausted constructors are excluded by
the loop's return option itself. -/
theorem NodeResult.of_loop_some {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level : Nat}
    {nodeCs loopCs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCs nodeSt nodeNumcells)
    (h : LoopResult ctx tcLevel loopSpecFuel runFuel loopFuel level loopCs rsLab
      rsPtn tc len loopNumcells tcell cursor bound loopSt out best outBest
        (some r)) :
    NodeResult ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCs nodeSt out nodeNumcells
      best outBest r := by
  cases h with
  | complete returned => simp at returned
  | unwind sound target returned below payload =>
      have hsound : NodeSound ctx tcLevel nodeSpecFuel level nodeCs nodeSt nodeNumcells
          best outBest := by
        constructor
        · intro b hb
          rw [← hbound]
          exact sound.upper b hb
        · exact sound.grows
      exact .unwind hsound target (Option.some.inj returned) below payload
  | pruned target returned below sound installed read full =>
      have hsound : NodeSound ctx tcLevel nodeSpecFuel level nodeCs nodeSt nodeNumcells
          best outBest := by
        constructor
        · intro b hb
          rw [← hbound]
          exact sound.upper b hb
        · exact sound.grows
      have hfull : outBest = some (incMax best
          (nodeKey ctx tcLevel nodeSpecFuel level nodeCs nodeSt nodeNumcells)) := by
        rwa [← hbound]
      exact .pruned hsound target (Option.some.inj returned) below installed
        read hfull
  | exhausted returned => simp at returned

/-- A completed loop with enough ranked cursor fuel lifts to ordinary node
completion.  Cursor exhaustion is ruled out by the same finite-range bound
used by the executable root search. -/
theorem NodeResult.of_loop_none {ctx : Ctx n}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCs loopCs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)}
    (hbound : bound = nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt nodeNumcells)
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
          loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hlen : len = tail + 1)
    (hfuel : n < cursorRank cursor + loopFuel)
    (h : LoopResult ctx tcLevel specFuel runFuel loopFuel level loopCs
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best outBest
        none) :
    NodeResult ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCs nodeSt out nodeNumcells
      best outBest (Int.ofNat level - 1) := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      rw [hbound] at sound
      rw [hlen] at cover empty
      exact NodeResult.complete_of_sweep hchildren sound installed read cover
        empty rfl
  | unwind sound target returned below payload => cases returned
  | pruned target returned below sound installed read full => cases returned
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact (LoopResult.exhaustion_false hfuel progress bounded).elim

/-- Prepending a sound child fragment transports every recursive loop
outcome.  In the prune case, the recursive exact incumbent and the
composed upper bound recover exactness relative to the original incumbent. -/
theorem LoopResult.prefix {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {st recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {r : Option Int}
    (hpre : LoopSound ctx bound best mid)
    (h : LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab
      rsPtn tc len numcells tcell cursor bound recSt out mid outBest r) :
    LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab rsPtn
      tc len numcells tcell cursor bound st out best outBest r := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      exact .complete returned (hpre.trans sound) installed read finalSet
        finalCursor cover empty
  | unwind sound target returned below payload =>
      exact .unwind (hpre.trans sound) target returned below payload
  | pruned target returned below sound installed read full =>
      have hsound := hpre.trans sound
      have hfull := hsound.exact full (keyLe_incMax_right mid bound)
      exact .pruned target returned below hsound installed read hfull
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned (hpre.trans sound) finalSet finalCursor cover
        progress bounded

/-- The entry set only describes where the call begins.  Every constructor
records the final set, so the result can cross a filter exposed in the
caller. -/
theorem LoopResult.reindexSet {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell tcell' : VSet n}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)}
    {r : Option Int}
    (h : LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest r) :
    LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab rsPtn
      tc len numcells tcell' cursor bound st out best outBest r := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      exact .complete returned sound installed read finalSet finalCursor
        cover empty
  | unwind sound target returned below payload =>
      exact .unwind sound target returned below payload
  | pruned target returned below sound installed read full =>
      exact .pruned target returned below sound installed read full
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned sound finalSet finalCursor cover progress bounded

/-- One successful cursor step transports every recursive loop outcome.
For exhaustion, its rank certificate accounts for the fuel consumed by
the exposed iteration. -/
theorem LoopResult.step {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)}
    {r : Option Int}
    (ha : After cursor tv)
    (h : LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab
      rsPtn tc len numcells tcell (some tv) bound st out best outBest r) :
    LoopResult ctx tcLevel specFuel runFuel (loopFuel + 1) level cs rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest r := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      exact .complete returned sound installed read finalSet finalCursor
        cover empty
  | unwind sound target returned below payload =>
      exact .unwind sound target returned below payload
  | pruned target returned below sound installed read full =>
      exact .pruned target returned below sound installed read full
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned sound finalSet finalCursor cover
        (Nat.le_trans (by
          have := cursorRank_step ha
          omega) progress) bounded

end Hex.GraphIso.Nauty
