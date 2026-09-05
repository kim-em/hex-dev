/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Unwind.Target
public import HexGraphIso.Nauty.Correct.Base

public section

/-!
Frame-aware generator guides and their composition rules.

The scalar `gcaFirst` and `gcaCanon` controls name ancestor levels, but
the executable state does not retain the frozen labelling of those
ancestors.  `GuideStore` strengthens `Guides` by locating every live
guide in the explicit active-frame trail, and the operational lemmas
compose the resulting receipts across a refinement.
-/

/-!
Frame-aware generator guides for the search induction.

The scalar `gcaFirst` and `gcaCanon` controls name ancestor levels, but
the executable state does not retain the frozen labelling of those
ancestors.  `GuideStore` strengthens `Guides` by locating every live
guide in the explicit active-frame trail used to consume an unwind.
-/

namespace Hex.GraphIso.Nauty

/-- Live first-path and canonical guides, each tied to its active
ancestor frame. -/
structure GuideStore (ctx : Ctx n) (tcLevel level : Nat) (st : SearchSt n)
    (best : Option (Key n)) (trail : FrameTrail) : Prop where
  first : 0 < st.gcaFirst → st.gcaFirst < level →
    ∃ g : Guide ctx tcLevel st.gcaFirst best,
      g.ref = st.firstlab ∧ g.Located trail
  canon : 0 < st.gcaCanon → st.gcaCanon < level →
    ∃ g : Guide ctx tcLevel st.gcaCanon best,
      g.ref = st.canonlab ∧ g.Located trail

/-- Forgetting frame locations recovers the guide invariant used by the
leaf-event lemmas. -/
theorem GuideStore.toGuides {ctx : Ctx n} {tcLevel level : Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : GuideStore ctx tcLevel level st best trail) :
    Guides ctx tcLevel level st best := by
  constructor
  · intro hp hlt
    obtain ⟨g, href, _⟩ := h.first hp hlt
    exact ⟨g, href⟩
  · intro hp hlt
    obtain ⟨g, href, _⟩ := h.canon hp hlt
    exact ⟨g, href⟩

/-- Growing a guide's incumbent changes neither its frame nor its
location in the active trail. -/
theorem Guide.Located.mono {ctx : Ctx n} {tcLevel level : Nat}
    {before best : Option (Key n)} {trail : FrameTrail}
    (g : Guide ctx tcLevel level before) (hloc : g.Located trail)
    (hinc : IncGrows before best) : (g.mono hinc).Located trail := by
  simpa only [Guide.Located, Guide.frame, Guide.mono] using hloc

/-- Both located guide ledgers survive an incumbent increase. -/
theorem GuideStore.grow {ctx : Ctx n} {tcLevel level : Nat}
    {st : SearchSt n} {before best : Option (Key n)} {trail : FrameTrail}
    (h : GuideStore ctx tcLevel level st before trail)
    (hinc : IncGrows before best) :
    GuideStore ctx tcLevel level st best trail := by
  constructor
  · intro hp hlt
    obtain ⟨g, href, hloc⟩ := h.first hp hlt
    exact ⟨g.mono hinc, href, Guide.Located.mono g hloc hinc⟩
  · intro hp hlt
    obtain ⟨g, href, hloc⟩ := h.canon hp hlt
    exact ⟨g.mono hinc, href, Guide.Located.mono g hloc hinc⟩

/-- The root has no live guide, independently of the empty trail. -/
theorem GuideStore.root {n : Nat} (g : Array (VSet n)) (lab : Array Nat)
    (cellEnds : List Nat) (tcLevel : Nat) (best : Option (Key n))
    (trail : FrameTrail) :
    GuideStore { g := g } tcLevel 1
      (rootSt n lab cellEnds) best trail := by
  constructor <;> intro hp _ <;> simp [rootSt] at hp

/-- Descending through a newly recorded parent child preserves every
older guide and installs any guide whose control points at the parent.

The two last premises isolate the only new obligations: a control equal
to `level` must be backed by a guide in the newly extended trail. -/
theorem GuideStore.push {ctx : Ctx n} {tcLevel level : Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : GuideStore ctx tcLevel level st best trail)
    (entry : TrailEntry)
    (hfirst : st.gcaFirst = level → 0 < st.gcaFirst →
      ∃ g : Guide ctx tcLevel st.gcaFirst best,
        g.ref = st.firstlab ∧ g.Located (trail.push level entry))
    (hcanon : st.gcaCanon = level → 0 < st.gcaCanon →
      ∃ g : Guide ctx tcLevel st.gcaCanon best,
        g.ref = st.canonlab ∧ g.Located (trail.push level entry)) :
    GuideStore ctx tcLevel (level + 1) st best
      (trail.push level entry) := by
  constructor
  · intro hp hlt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | hhere
    · obtain ⟨g, href, hloc⟩ := h.first hp hold
      exact ⟨g, href, hloc.push (Nat.ne_of_lt hold)⟩
    · exact hfirst hhere hp
  · intro hp hlt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | hhere
    · obtain ⟨g, href, hloc⟩ := h.canon hp hold
      exact ⟨g, href, hloc.push (Nat.ne_of_lt hold)⟩
    · exact hcanon hhere hp

/-- Reindex a located guide invariant across state fields that do not
change either guide control or reference labelling. -/
theorem GuideStore.stateEq {ctx : Ctx n} {tcLevel level : Nat}
    {st st' : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : GuideStore ctx tcLevel level st best trail)
    (hfirst : st'.gcaFirst = st.gcaFirst)
    (hfirstlab : st'.firstlab = st.firstlab)
    (hcanon : st'.gcaCanon = st.gcaCanon)
    (hcanonlab : st'.canonlab = st.canonlab) :
    GuideStore ctx tcLevel level st' best trail := by
  constructor
  · intro hp hlt
    rw [hfirst] at hp hlt ⊢
    obtain ⟨g, href, hloc⟩ := h.first hp hlt
    exact ⟨g, href.trans hfirstlab.symm, hloc⟩
  · intro hp hlt
    rw [hcanon] at hp hlt ⊢
    obtain ⟨g, href, hloc⟩ := h.canon hp hlt
    exact ⟨g, href.trans hcanonlab.symm, hloc⟩

/-- Cell-equivalent node labellings with the same partition and active
set have the same specification key. -/
theorem nodeKey_perm {ctx : Ctx n}
    (tcLevel fuel level : Nat) (cs : List Nat)
    (st st' : SearchSt n) (numcells : Nat)
    (hcp : cellsPerm st.ptn level st.lab st'.lab)
    (hls : st'.lab.size = st.lab.size)
    (hsl : st.lab.size = n)
    (hlab : LabOk st.lab n) (hlab' : LabOk st'.lab n)
    (hptn : st'.ptn = st.ptn) (hactive : st'.active = st.active)
    (hsp : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, st.active.mem v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level)
    (hvals : ∀ q : Nat, st.ptn[q]! ≤ level ∨
      st.ptn[q]! = n + 2)
    (hlf : level + fuel ≤ n + 1) :
    nodeKey ctx tcLevel fuel level cs st numcells =
      nodeKey ctx tcLevel fuel level cs st' numcells := by
  unfold nodeKey
  apply congrArg (prefixKey cs)
  rw [hptn, hactive]
  exact specNode_perm tcLevel fuel level st.lab st'.lab st.ptn
    st.active numcells hcp hls hsl hlab hlab' hsp hend hstarts
    hvals hlf

/-- Exact completion of a key-equivalent executable child covers the
corresponding frozen specification child. -/
theorem ChildDone.ofKeyEq {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc numcells o : Nat}
    {child : SearchSt n} {best out : Option (Key n)}
    (hfull : out = some (incMax best
      (nodeKey ctx tcLevel specFuel (level + 1) cs child
        (numcells + 1))))
    (heq : sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells o = nodeKey ctx tcLevel specFuel (level + 1) cs child
        (numcells + 1)) :
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      out o := by
  refine ⟨incMax best
    (nodeKey ctx tcLevel specFuel (level + 1) cs child
      (numcells + 1)), hfull, ?_⟩
  rw [heq]
  exact keyLe_incMax_right best _

/-- A key-equivalent completed child advances the mutable sweep. -/
theorem SweepCover.advanceKey {ctx : Ctx n}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tv : Nat} {tcell : VSet n}
    {cursor : Option Nat} {child : SearchSt n} {best out : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : tcell.nextElem cursor = some tv)
    (hfull : out = some (incMax best
      (nodeKey ctx tcLevel specFuel (level + 1) cs child
        (numcells + 1))))
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) cs child
          (numcells + 1)) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell (some tv) out := by
  apply h.advance hnext
  · intro o ho hotv
    exact ChildDone.ofKeyEq hfull (heq o ho hotv)
  · intro o hdone
    exact hdone.mono (hfull ▸ IncGrows.incMax best _)

/-- A node outcome whose generator unwind, when present, is tied to the
active frame trail.  The constructors mirror `NodeResult`; keeping the
location in the unwind constructor prevents a caller from forgetting the
only evidence that lets the receiving loop consume that return. -/
inductive NodeReceipt (trail : FrameTrail) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (cs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (best outBest : Option (Key n))
    (r : Int) : Prop where
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
      (located : payload.Located trail)
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

/-- Forgetting a node receipt's frame location recovers its ordinary
semantic result. -/
theorem NodeReceipt.toResult {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {cs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)} {r : Int}
    (h : NodeReceipt trail ctx tcLevel specFuel runFuel level cs st out
      numcells best outBest r) :
    NodeResult ctx tcLevel specFuel runFuel level cs st out numcells best
      outBest r := by
  cases h with
  | complete sound returned installed read full =>
      exact .complete sound returned installed read full
  | unwind sound target returned below payload located =>
      exact .unwind sound target returned below payload
  | pruned sound target returned below installed read full =>
      exact .pruned sound target returned below installed read full
  | exhausted empty returned unchanged bestUnchanged =>
      exact .exhausted empty returned unchanged bestUnchanged

/-- A positive-fuel receipt always carries the node soundness shared by
its non-exhausted outcomes. -/
theorem NodeReceipt.sound {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {cs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)} {r : Int}
    (h : NodeReceipt trail ctx tcLevel specFuel runFuel level cs st out
      numcells best outBest r) (hfuel : runFuel ≠ 0) :
    NodeSound ctx tcLevel specFuel level cs st numcells best outBest := by
  cases h with
  | complete sound => exact sound
  | unwind sound => exact sound
  | pruned sound => exact sound
  | exhausted empty => exact (hfuel empty).elim

/-- A loop outcome with every transported generator unwind located in
the active frame trail. -/
inductive LoopReceipt (trail : FrameTrail) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat) (cs : List Nat)
    (rsLab rsPtn : Array Nat) (tc len numcells : Nat) (tcell : VSet n)
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
      (located : payload.Located trail)
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

/-- Forgetting a loop receipt's frame location recovers its ordinary
semantic result. -/
theorem LoopReceipt.toResult {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tc len numcells : Nat} {tcell : VSet n}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {r : Option Int}
    (h : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest r) :
    LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab rsPtn
      tc len numcells tcell cursor bound st out best outBest r := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      exact .complete returned sound installed read finalSet finalCursor
        cover empty
  | unwind sound target returned below payload located =>
      exact .unwind sound target returned below payload
  | pruned target returned below sound installed read full =>
      exact .pruned target returned below sound installed read full
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned sound finalSet finalCursor cover progress
        bounded

/-- At a parent boundary, a located child receipt either supplies the
exact child maximum or a located unwind addressed to that parent. -/
theorem NodeReceipt.parentReturn {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {cs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)} {r : Int}
    (h : NodeReceipt trail ctx tcLevel specFuel runFuel (level + 1) cs st
      out numcells best outBest r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level)) :
    outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel (level + 1) cs st numcells)) ∨
      ∃ payload : Unwind ctx tcLevel level out outBest,
        payload.Located trail := by
  cases h with
  | complete sound returned installed read full => exact Or.inl full
  | unwind sound target returned below payload located =>
      have hle : level ≤ target := by
        apply Int.ofNat_le.mp
        rw [returned] at hstay
        exact Int.not_lt.mp hstay
      have htarget : target = level := by omega
      subst target
      exact Or.inr ⟨payload, located⟩
  | pruned sound target returned below installed read full => exact Or.inl full
  | exhausted empty returned unchanged bestUnchanged => exact (hfuel empty).elim

/-- A resolved child receipt advances its parent's coverage.  Exact
children may use cell-permutation key equivalence; generator children use
their location in the just-pushed parent frame, with stabilization required
only by an orbit-pointer unwind. -/
theorem SweepCover.receipt {ctx : Ctx n}
    {tcLevel specFuel runFuel level tc len numcells : Nat} {tcell : VSet n} {tv offset : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option (Key n)}
    {child out : SearchSt n} {r : Int} {trail : FrameTrail}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hnext : tcell.nextElem cursor = some tv)
    (hchild : NodeReceipt
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      ctx tcLevel specFuel runFuel (level + 1) codes child out
      (numcells + 1) before best r)
    (hfuel : runFuel ≠ 0)
    (hreturn :
      best = some (incMax before
        (nodeKey ctx tcLevel specFuel (level + 1) codes child
          (numcells + 1))) ∨
      ∃ payload : Unwind ctx tcLevel level out best,
        payload.Located
          (trail.push level
            ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) ∧
        payload.FrameStable rsPtn level rsLab)
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes child
          (numcells + 1))
    (ho : offset < len) (htv : rsLab[tc + offset]! = tv)
    (hcoset : out.cosetindex = tv)
    (hgsz : ctx.g.size = n)
    (hv : ∀ γ ∈ out.genTrace.toList,
      checkAutom ctx.g γ = true)
    (hs : rsLab.size = n) (hinj : LabInj rsLab rsLab.size)
    (hok : LabOk rsLab n) (hsp : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hlf : level + 1 + specFuel ≤ n + 1) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) best := by
  have hsound := hchild.sound hfuel
  rcases hreturn with hfull | ⟨payload, hloc, hstab⟩
  · exact h.advanceKey hnext hfull heq
  · exact h.unwind hsound.grows hnext hloc
      (FrameTrail.push_self trail level _) ho htv hcoset hgsz hv
      hstab
      hs hinj hok hsp hend hvals hic hrange hlf

/-- A located unwind from an off-path child cannot use the orbit arm at
its parent: that arm returns to `gcaFirst`, which is strictly below this
loop.  The two direct carrier arms therefore advance coverage without a
`cosetindex` premise. -/
theorem SweepCover.offPathUnwind {ctx : Ctx n}
    {tcLevel specFuel level tc len numcells : Nat} {tcell : VSet n} {tv offset : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option (Key n)} {out : SearchSt n}
    {trail : FrameTrail} {payload : Unwind ctx tcLevel level out best}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : tcell.nextElem cursor = some tv)
    (hloc : payload.Located trail)
    (hframe : trail level = some
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
    (hoffset : offset < len)
    (htv : rsLab[tc + offset]! = tv)
    (hfirst : out.gcaFirst < level)
    (hs : rsLab.size = n) (hinj : LabInj rsLab rsLab.size)
    (hrange : tc + len ≤ n) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) best := by
  have hrange' : tc + len ≤ rsLab.size := by rwa [hs]
  have hoff : tc + offset < rsLab.size := by omega
  cases payload with
  | first anchor carrier =>
      cases hloc with
      | first _ _ located =>
          exact h.locatedAnchor hinc hnext anchor located hframe htv hinj
            hrange' hoff
  | canon anchor carrier =>
      cases hloc with
      | canon _ _ located =>
          exact h.locatedAnchor hinc hnext anchor located hframe htv hinj
            hrange' hoff
  | orbit orbitPayload =>
      exact (Nat.not_lt_of_ge orbitPayload.bound hfirst).elim

/-- Updating the first-path return controls preserves the source
location of a generator unwind. -/
theorem Unwind.Located.setFirst {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel target : Nat} {out : SearchSt n} {best : Option (Key n)}
    {payload : Unwind ctx tcLevel target out best}
    (h : payload.Located trail) (gcaFirst stabvertex : Nat)
    (hbound : target ≤ gcaFirst) :
    ∃ payload' : Unwind ctx tcLevel target
        { out with gcaFirst := gcaFirst, stabvertex := stabvertex } best,
      payload'.Located trail := by
  let out' : SearchSt n :=
    { out with gcaFirst := gcaFirst, stabvertex := stabvertex }
  change ∃ payload' : Unwind ctx tcLevel target out' best,
    payload'.Located trail
  cases h with
  | first anchor carrier located =>
      have carrier' : LabelCarrier ctx out'.firstlab out'.lab
          out'.genTrace := by
        simpa only [out'] using carrier
      refine ⟨Unwind.first anchor carrier', ?_⟩
      exact Unwind.Located.first anchor carrier' located
  | canon anchor carrier located =>
      have carrier' : LabelCarrier ctx out'.canonlab out'.lab
          out'.genTrace := by
        simpa only [out'] using carrier
      refine ⟨Unwind.canon anchor carrier', ?_⟩
      exact Unwind.Located.canon anchor carrier' located
  | orbit orbitPayload =>
      let orbitPayload' : OrbitUnwind ctx target out' := {
        positive := orbitPayload.positive
        bound := hbound
        currentLt := orbitPayload.currentLt
        smaller := orbitPayload.smaller
        sound := orbitPayload.sound }
      exact ⟨.orbit orbitPayload', .orbit orbitPayload'⟩

/-- Removing a loop's temporary fixed vertex preserves the source
location of a generator unwind. -/
theorem Unwind.Located.setFixed {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel target : Nat} {out : SearchSt n} {best : Option (Key n)}
    {payload : Unwind ctx tcLevel target out best}
    (h : payload.Located trail) (fixedpts : VSet n) :
    ∃ payload' : Unwind ctx tcLevel target
        { out with fixedpts := fixedpts } best,
      payload'.Located trail := by
  let out' : SearchSt n := { out with fixedpts := fixedpts }
  change ∃ payload' : Unwind ctx tcLevel target out' best,
    payload'.Located trail
  cases h with
  | first anchor carrier located =>
      have carrier' : LabelCarrier ctx out'.firstlab out'.lab
          out'.genTrace := by
        simpa only [out'] using carrier
      refine ⟨Unwind.first anchor carrier', ?_⟩
      exact Unwind.Located.first anchor carrier' located
  | canon anchor carrier located =>
      have carrier' : LabelCarrier ctx out'.canonlab out'.lab
          out'.genTrace := by
        simpa only [out'] using carrier
      refine ⟨Unwind.canon anchor carrier', ?_⟩
      exact Unwind.Located.canon anchor carrier' located
  | orbit orbitPayload =>
      let orbitPayload' : OrbitUnwind ctx target out' := {
        positive := orbitPayload.positive
        bound := orbitPayload.bound
        currentLt := orbitPayload.currentLt
        smaller := orbitPayload.smaller
        sound := orbitPayload.sound }
      exact ⟨.orbit orbitPayload', .orbit orbitPayload'⟩

/-- A located child unwind strictly past its parent lifts through the
parent loop's fixed-vertex cleanup. -/
theorem LoopReceipt.ofChildUnwind {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel childFuel childRunFuel parentFuel loopFuel level : Nat}
    {childCs loopCs : List Nat} {childNumcells loopNumcells : Nat}
    {childSt loopSt out : SearchSt n} {best outBest : Option (Key n)}
    {target : Nat} {fixedpts : VSet n} {rsLab rsPtn : Array Nat}
    {tc len : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    (hsound : NodeSound ctx tcLevel childFuel (level + 1) childCs childSt
      childNumcells best outBest)
    (hkey : keyLe
      (nodeKey ctx tcLevel childFuel (level + 1) childCs childSt
        childNumcells) bound)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target out outBest)
    (hloc : payload.Located trail) :
    LoopReceipt trail ctx tcLevel parentFuel childRunFuel loopFuel level
      loopCs rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt
      { out with fixedpts := fixedpts } best outBest
      (some (Int.ofNat target)) := by
  obtain ⟨payload', hloc'⟩ := hloc.setFixed fixedpts
  have hsound' : LoopSound ctx bound best outBest := by
    constructor
    · intro b hb
      exact keyLe_trans (hsound.upper b hb) (incMax_mono_right best hkey)
    · exact hsound.grows
  exact .unwind hsound' target rfl hbelow payload' hloc'

/-- A located loop return carrying an integer lifts directly through its
parent node. -/
theorem NodeReceipt.ofLoopSome {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level : Nat}
    {nodeCs loopCs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCs nodeSt
      nodeNumcells)
    (h : LoopReceipt trail ctx tcLevel loopSpecFuel runFuel loopFuel level
      loopCs rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out
      best outBest (some r)) :
    NodeReceipt trail ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCs
      nodeSt out nodeNumcells best outBest r := by
  cases h with
  | complete returned => simp at returned
  | unwind sound target returned below payload located =>
      have hsound : NodeSound ctx tcLevel nodeSpecFuel level nodeCs nodeSt
          nodeNumcells best outBest := by
        constructor
        · intro b hb
          rw [← hbound]
          exact sound.upper b hb
        · exact sound.grows
      exact .unwind hsound target (Option.some.inj returned) below payload
        located
  | pruned target returned below sound installed read full =>
      have hsound : NodeSound ctx tcLevel nodeSpecFuel level nodeCs nodeSt
          nodeNumcells best outBest := by
        constructor
        · intro b hb
          rw [← hbound]
          exact sound.upper b hb
        · exact sound.grows
      have hfull : outBest = some (incMax best
          (nodeKey ctx tcLevel nodeSpecFuel level nodeCs nodeSt
            nodeNumcells)) := by
        rwa [← hbound]
      exact .pruned hsound target (Option.some.inj returned) below installed
        read hfull
  | exhausted returned => simp at returned

/-- A located completed loop with enough cursor fuel lifts to node
completion. -/
theorem NodeReceipt.ofLoopNone {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCs loopCs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)}
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
    (h : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level
      loopCs rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out
      best outBest none) :
    NodeReceipt trail ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCs
      nodeSt out nodeNumcells best outBest (Int.ofNat level - 1) := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      rw [hbound] at sound
      rw [hlen] at cover empty
      have hfull := cover.exact_of_read hchildren empty sound installed read
      exact .complete (NodeSound.ofExact hfull) rfl installed read hfull
  | unwind sound target returned below payload located => cases returned
  | pruned target returned below sound installed read full => cases returned
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact (LoopResult.exhaustion_false hfuel progress bounded).elim

/-- Prepending a sound child fragment preserves the location carried by
every recursive loop outcome. -/
theorem LoopReceipt.prefix {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {st recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {r : Option Int}
    (hpre : LoopSound ctx bound best mid)
    (h : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
      rsLab rsPtn tc len numcells tcell cursor bound recSt out mid outBest r) :
    LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest r := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      exact .complete returned (hpre.trans sound) installed read finalSet
        finalCursor cover empty
  | unwind sound target returned below payload located =>
      exact .unwind (hpre.trans sound) target returned below payload located
  | pruned target returned below sound installed read full =>
      have hsound := hpre.trans sound
      have hfull := hsound.exact full (keyLe_incMax_right mid bound)
      exact .pruned target returned below hsound installed read hfull
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned (hpre.trans sound) finalSet finalCursor cover
        progress bounded

/-- Reindex the entry set of a located loop result. -/
theorem LoopReceipt.reindexSet {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell tcell' : VSet n}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {r : Option Int}
    (h : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest r) :
    LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs rsLab
      rsPtn tc len numcells tcell' cursor bound st out best outBest r := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      exact .complete returned sound installed read finalSet finalCursor
        cover empty
  | unwind sound target returned below payload located =>
      exact .unwind sound target returned below payload located
  | pruned target returned below sound installed read full =>
      exact .pruned target returned below sound installed read full
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned sound finalSet finalCursor cover progress
        bounded

/-- One successful cursor step preserves located recursive outcomes. -/
theorem LoopReceipt.step {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {r : Option Int}
    (ha : After cursor tv)
    (h : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
      rsLab rsPtn tc len numcells tcell (some tv) bound st out best outBest r) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest r := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      exact .complete returned sound installed read finalSet finalCursor
        cover empty
  | unwind sound target returned below payload located =>
      exact .unwind sound target returned below payload located
  | pruned target returned below sound installed read full =>
      exact .pruned target returned below sound installed read full
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned sound finalSet finalCursor cover
        (Nat.le_trans (by
          have := cursorRank_step ha
          omega) progress) bounded

end Hex.GraphIso.Nauty

/-!
Operational composition lemmas for frame-aware search receipts.
-/

namespace Hex.GraphIso.Nauty

/-- Once both ends of a loop frame are recovered at the same level, the
`SearchOut` low-boundary contract identifies their partitions exactly.
The labelling may still differ by a within-cell permutation. -/
theorem SearchOut.ptnEq {G : Colored n k} {level numcells : Nat}
    {st out : SearchSt n} (h : SearchOut G level level st out)
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
    {st out : SearchSt n} (h : SearchOut G level level st out)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    ∃ oCur, oCur < len ∧ out.lab[tc + oCur]! = st.lab[tc + o]! ∧
      cellsPerm (st.ptn.set! tc (level + 1)) (level + 1)
        (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (breakout n out.lab out.ptn (level + 1) tc st.lab[tc + o]!).1 := by
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
  have hb := breakout_cellsPerm_map (n := n)
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

/-- The active singleton created by individualization marks a cell start
of the split partition. -/
theorem split_starts {ptn : Array Nat} {level tc len : Nat}
    (hcell : IsCell ptn level tc len)
    (hrange : tc + len ≤ n) :
    ∀ v : Nat, ((VSet.empty : VSet n).insert tc).mem v = true →
      v = 0 ∨ (ptn.set! tc (level + 1))[v - 1]! ≤ level + 1 := by
  intro v hv
  have htc : tc < n := by
    have := hcell.1
    omega
  rw [mem_single htc] at hv
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
theorem SearchOut.breakoutKey {G : Colored n k} {ctx : Ctx n}
    {level numcells tc len o specFuel tcLevel : Nat}
    {st out child : SearchSt n}
    (h : SearchOut G level level st out)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len)
    (hclab : child.lab = (breakout n out.lab out.ptn (level + 1) tc
      st.lab[tc + o]!).1)
    (hcptn : child.ptn = (breakout n out.lab out.ptn (level + 1) tc
      st.lab[tc + o]!).2.1)
    (hcactive : child.active = (breakout n out.lab out.ptn (level + 1) tc
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
  have hclab' : child.lab = (breakout n out.lab out.ptn (level + 1) tc
      out.lab[tc + oCur]!).1 := by
    rw [hat]
    exact hclab
  have hcptn' : child.ptn = out.ptn.set! tc (level + 1) := by
    rw [hcptn, breakout_ptn]
  have hchildOk := breakout_searchOk (st' := child) hn0 hout hlevel
    hcellOut hlen hrange hoCur hclab' hcptn' hcanon
  let refChild : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.2 }
  have hrefOk : SearchOk G (level + 1) (numcells + 1) refChild := by
    apply breakout_searchOk hn0 hok hlevel hcell hlen hrange ho
    · rfl
    · exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!
    · rfl
  change nodeKey ctx tcLevel specFuel (level + 1) codes refChild
      (numcells + 1) =
    nodeKey ctx tcLevel specFuel (level + 1) codes child
      (numcells + 1)
  apply nodeKey_perm tcLevel specFuel (level + 1) codes refChild child
    (numcells + 1)
  · change cellsPerm
      (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.1 (level + 1)
      (breakout n st.lab st.ptn (level + 1) tc
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
  · exact split_end (searchOk_end hn0 hok hlevel) (by
      rw [hok.ptnSize]
      omega)
  · exact split_starts hcell (by omega)
  · intro q
    rcases Nat.lt_or_ge q n with hq | hq
    · exact hrefOk.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [hrefOk.ptnSize]; omega)]
      exact Nat.zero_le _
  · exact hfuel

/-- First-path exit bookkeeping preserves the location of a transported
generator unwind. -/
theorem Unwind.Located.firstFinish {ctx : Ctx n}
    {tcLevel target level size index : Nat} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
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
theorem NodeReceipt.firstFinish {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
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
theorem firstPath_internal_receipt (ctx : Ctx n)
    (inf tcLevel specFuel fuel level numcells tail : Nat)
    (cs : List Nat) (st : SearchSt n) (best outBest : Option (Key n))
    (trail : FrameTrail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ n)
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
    let pre0 : SearchSt n := { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      firstcode := st.firstcode.set! level rs.longcode
      firsttc := st.firsttc.set! level (Int.ofNat mt.1)
      numnodes := st.numnodes + 1
      tctotal := st.tctotal + mt.2.2 }
    let pre := if pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level n then
      { pre0 with noncheaplevel := level + 1 }
    else pre0
    let L := firstChildLoop ctx inf tcLevel fuel (n + 1) level
      rs.numcells mt.1 ((mt.2.1.nextElem none).getD 0)
      (mt.2.1.nextElem none) mt.2.1 0 pre
    LoopReceipt trail ctx tcLevel specFuel fuel (n + 1) level
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
  generalize hL : firstChildLoop ctx inf tcLevel fuel (n + 1)
      level _ _ _ _ _ _ _ = L at hloop ⊢
  rcases L with ⟨r, index, out⟩
  cases r with
  | none =>
      have hnode := NodeReceipt.ofLoopNone (ctx := ctx)
        (nodeRunFuel := fuel + 1) (cursor := none)
        (loopFuel := n + 1) rfl hchildren hlen
        (by simp only [cursorRank]; omega) hloop
      exact hnode.firstFinish (by omega)
  | some r =>
      exact NodeReceipt.ofLoopSome (ctx := ctx)
        (nodeRunFuel := fuel + 1) rfl hloop

/-- Once the imperative prefix exposes an off-path child loop, its
located receipt constructs the corresponding located node receipt. -/
theorem otherNode_receipt {ctx : Ctx n}
    {inf tcLevel specFuel fuel level nodeNumcells loopNumcells tail : Nat}
    {nodeCs loopCs : List Nat} {nodeSt loopSt : SearchSt n}
    {rsLab rsPtn : Array Nat} {tc len : Nat} {tcell : VSet n}
    {best outBest : Option (Key n)} {trail : FrameTrail}
    {L : Option Int × SearchSt n}
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
    (hloop : LoopReceipt trail ctx tcLevel specFuel fuel (n + 1) level
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
        (loopFuel := n + 1) rfl hchildren hlen
        (by simp only [cursorRank]; omega) hloop
  | some r =>
      exact NodeReceipt.ofLoopSome (ctx := ctx)
        (nodeRunFuel := fuel + 1) rfl hloop

/-- An off-path child generator unwind strictly past this loop returns
with its frame location intact after fixed-vertex cleanup. -/
theorem otherLoop_childReceipt (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (tcell : VSet n)
    (cursor : Option Nat) (bound : Key n) (st : SearchSt n)
    (best outBest : Option (Key n)) (target : Nat) (trail : FrameTrail)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      (numcells + 1)) bound)
    (hreturn : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }).1 = Int.ofNat target)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv }).2 outBest)
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
theorem firstLoop_zeroReceipt (ctx : Ctx n)
    (inf tcLevel specFuel runFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tv? cursor : Option Nat) (tcell : VSet n) (index : Nat) (bound : Key n)
    (st : SearchSt n) (best : Option (Key n)) (trail : FrameTrail)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hcursor : ∀ v, cursor = some v → v < n) :
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
theorem otherLoop_zeroReceipt (ctx : Ctx n)
    (inf tcLevel specFuel runFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tv? cursor : Option Nat) (tcell : VSet n) (bound : Key n) (st : SearchSt n)
    (best : Option (Key n)) (trail : FrameTrail)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hcursor : ∀ v, cursor = some v → v < n) :
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
theorem firstLoop_doneReceipt (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tcell : VSet n) (index : Nat) (cursor : Option Nat) (bound : Key n)
    (st : SearchSt n) (best : Option (Key n)) (trail : FrameTrail)
    (hinstalled : st.canonlevel ≠ 0) (hread : stInc ctx st = best)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : tcell.nextElem cursor = none) :
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
theorem otherLoop_doneReceipt (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (tcell : VSet n)
    (cursor : Option Nat) (bound : Key n) (st : SearchSt n)
    (best : Option (Key n)) (trail : FrameTrail)
    (hinstalled : st.canonlevel ≠ 0) (hread : stInc ctx st = best)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : tcell.nextElem cursor = none) :
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
theorem firstLoop_orbitReceipt (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (tcell : VSet n) (index o : Nat)
    (cursor : Option Nat) (bound : Key n) (st : SearchSt n)
    (best : Option (Key n)) (trail : FrameTrail)
    (gens : List (Array Nat))
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
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
    (hsound : OrbSound (OrbConn gens n) st.orbits n)
    (horbit : (st.orbits[tv]! == tv) = false)
    (hrec : ∀ index',
      SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
        tcell (some tv) best →
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells tcell (some tv) bound st
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (tcell.nextElem (some tv)) tcell index' st).2.2
        best best
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (tcell.nextElem (some tv)) tcell index' st).1) :
    LoopReceipt trail ctx tcLevel specFuel runFuel (loopFuel + 1) level cs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best best
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  have hne : st.orbits[tv]! ≠ tv := by
    simpa only [beq_eq_false_iff_ne] using horbit
  have hcover' := hcover.orbitSkip hnext ho htv hgsz hv hstab hs hinj
    hok hsp hend hvals hic hrange hlf hsound hne
  unfold firstChildLoop
  simp only [horbit, Bool.false_eq_true, ite_false, Id.run_pure,
    apply_ite Id.run]
  rcases hidx : (st.orbits[tv]! == tv1) with _ | _ <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    exact (hrec _ hcover').step (nextElem_after hnext)

/-- An off-path child of the first-path loop transports a located unwind
strictly past the loop. -/
theorem firstLoop_otherReceipt (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (tcell : VSet n) (index : Nat)
    (cursor : Option Nat) (bound : Key n) (st : SearchSt n)
    (best outBest : Option (Key n)) (target : Nat) (trail : FrameTrail)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hother : (tv == tv1) = false)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      (numcells + 1)) bound)
    (hreturn : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }).1 = Int.ofNat target)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv
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
theorem firstLoop_guideReceipt (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (tcell : VSet n) (index : Nat)
    (cursor : Option Nat) (bound : Key n) (st : SearchSt n)
    (best outBest : Option (Key n)) (target : Nat) (trail : FrameTrail)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hfirst : (tv == tv1) = true)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      (numcells + 1)) bound)
    (hreturn : (firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }).1 = Int.ofNat target)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target
      (firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv
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
theorem otherLoop_nextReceipt (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (tcell : VSet n)
    (cursor : Option Nat) (bound : Key n) (st : SearchSt n)
    (best mid outBest : Option (Key n)) (r : Int) (trail : FrameTrail)
    (hnext : tcell.nextElem cursor = some tv)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      (numcells + 1) best mid)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) cs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      (numcells + 1)) bound)
    (hreturn : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }).1 = r)
    (hstay : ¬ r < Int.ofNat level)
    (hshort : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }).2.needshortprune = false)
    (hother : (tv == tv1) = false)
    (hrec : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level
      cs rsLab rsPtn tc len numcells tcell (some tv) bound
      (recover n inf level
        { (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := st.fixedpts.insert tv }).2 with
          fixedpts := (otherNode ctx inf tcLevel runFuel (level + 1)
            (numcells + 1)
            { st with
              lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
              ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
              active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
              fixedpts := st.fixedpts.insert tv }).2.fixedpts.erase tv })
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (tcell.nextElem (some tv)) tcell
        (recover n inf level
          { (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
            { st with
              lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
              ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
              active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
              fixedpts := st.fixedpts.insert tv }).2 with
            fixedpts := (otherNode ctx inf tcLevel runFuel (level + 1)
              (numcells + 1)
              { st with
                lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
                ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
                active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
                fixedpts := st.fixedpts.insert tv }).2.fixedpts.erase tv })).2
      mid outBest
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (tcell.nextElem (some tv)) tcell
        (recover n inf level
          { (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
            { st with
              lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
              ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
              active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
              fixedpts := st.fixedpts.insert tv }).2 with
            fixedpts := (otherNode ctx inf tcLevel runFuel (level + 1)
              (numcells + 1)
              { st with
                lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
                ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
                active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
                fixedpts := st.fixedpts.insert tv }).2.fixedpts.erase tv })).1) :
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
theorem firstLoop_otherNext (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (tcell : VSet n) (index : Nat)
    (cursor : Option Nat) (bound : Key n) (st child recSt : SearchSt n)
    (best mid outBest : Option (Key n)) (r : Int) (trail : FrameTrail)
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = false)
    (hrecover : recSt = recover n inf level
      { child with fixedpts := child.fixedpts.erase tv })
    (hpre : LoopSound ctx bound best mid)
    (hrec : ∀ index',
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells tcell (some tv) bound recSt
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (tcell.nextElem (some tv)) tcell index' recSt).2.2
        mid outBest
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (tcell.nextElem (some tv)) tcell index' recSt).1) :
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
theorem firstLoop_guideNext (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (tcell : VSet n) (index : Nat)
    (cursor : Option Nat) (bound : Key n) (st child recSt : SearchSt n)
    (best mid outBest : Option (Key n)) (r : Int) (trail : FrameTrail)
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = false)
    (hrecover : recSt = recover n inf level
      { child with
        fixedpts := child.fixedpts.erase tv
        gcaFirst := level
        stabvertex := tv1 })
    (hpre : LoopSound ctx bound best mid)
    (hrec : ∀ index',
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells tcell (some tv) bound recSt
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (tcell.nextElem (some tv)) tcell index' recSt).2.2
        mid outBest
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (tcell.nextElem (some tv)) tcell index' recSt).1) :
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
theorem otherLoop_longNext (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (filtered : VSet n) (tcell : VSet n)
    (cursor : Option Nat) (bound : Key n) (st child recSt : SearchSt n)
    (best mid outBest : Option (Key n)) (r : Int) (trail : FrameTrail)
    (hnext : tcell.nextElem cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = false)
    (hfirst : (tv == tv1) = true)
    (hfiltered : filtered = longprune tcell
      (child.fixedpts.erase tv) child.autos)
    (hrecover : recSt = recover n inf level
      { child with fixedpts := child.fixedpts.erase tv })
    (hpre : LoopSound ctx bound best mid)
    (hrec : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level
      cs rsLab rsPtn tc len numcells filtered (some tv) bound recSt
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (filtered.nextElem (some tv)) filtered recSt).2
      mid outBest
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (filtered.nextElem (some tv)) filtered recSt).1) :
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
theorem otherLoop_shortNext (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat) (filtered : VSet n) (tcell : VSet n)
    (cursor : Option Nat) (bound : Key n) (st child recSt : SearchSt n)
    (best mid outBest : Option (Key n)) (r : Int) (trail : FrameTrail)
    (hnext : tcell.nextElem cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = true)
    (hother : (tv == tv1) = false)
    (hfiltered : filtered = shortprune tcell
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hrecover : recSt = recover n inf level
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hpre : LoopSound ctx bound best mid)
    (hrec : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level
      cs rsLab rsPtn tc len numcells filtered (some tv) bound recSt
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (filtered.nextElem (some tv)) filtered recSt).2
      mid outBest
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (filtered.nextElem (some tv)) filtered recSt).1) :
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
theorem otherLoop_bothNext (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat)
    (len : Nat) (shortSet : VSet n) (filtered : VSet n) (tcell : VSet n)
    (cursor : Option Nat) (bound : Key n) (st child recSt : SearchSt n)
    (best mid outBest : Option (Key n)) (r : Int) (trail : FrameTrail)
    (hnext : tcell.nextElem cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = true)
    (hfirst : (tv == tv1) = true)
    (hshortSet : shortSet = shortprune tcell
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hfiltered : filtered = longprune shortSet
      (child.fixedpts.erase tv) child.autos)
    (hrecover : recSt = recover n inf level
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hpre : LoopSound ctx bound best mid)
    (hrec : LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level
      cs rsLab rsPtn tc len numcells filtered (some tv) bound recSt
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (filtered.nextElem (some tv)) filtered recSt).2
      mid outBest
      (otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (filtered.nextElem (some tv)) filtered recSt).1) :
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
theorem firstLoop_otherShort (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat)
    (len index : Nat) (filtered : VSet n) (tcell : VSet n)
    (cursor : Option Nat) (bound : Key n) (st child recSt : SearchSt n)
    (best mid outBest : Option (Key n)) (r : Int) (trail : FrameTrail)
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = true)
    (hfiltered : filtered = shortprune tcell
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hrecover : recSt = recover n inf level
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hpre : LoopSound ctx bound best mid)
    (hrec : ∀ index',
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells filtered (some tv) bound recSt
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (filtered.nextElem (some tv)) filtered index' recSt).2.2
        mid outBest
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (filtered.nextElem (some tv)) filtered index' recSt).1) :
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
theorem firstLoop_guideShort (ctx : Ctx n)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat)
    (len index : Nat) (filtered : VSet n) (tcell : VSet n)
    (cursor : Option Nat) (bound : Key n) (st child recSt : SearchSt n)
    (best mid outBest : Option (Key n)) (r : Int) (trail : FrameTrail)
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (r, child))
    (hstay : ¬ r < Int.ofNat level)
    (hshort : child.needshortprune = true)
    (hfiltered : filtered = shortprune tcell
      { child with
        fixedpts := child.fixedpts.erase tv
        gcaFirst := level
        stabvertex := tv1
        needshortprune := false })
    (hrecover : recSt = recover n inf level
      { child with
        fixedpts := child.fixedpts.erase tv
        gcaFirst := level
        stabvertex := tv1
        needshortprune := false })
    (hpre : LoopSound ctx bound best mid)
    (hrec : ∀ index',
      LoopReceipt trail ctx tcLevel specFuel runFuel loopFuel level cs
        rsLab rsPtn tc len numcells filtered (some tv) bound recSt
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (filtered.nextElem (some tv)) filtered index' recSt).2.2
        mid outBest
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (filtered.nextElem (some tv)) filtered index' recSt).1) :
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
