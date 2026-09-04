/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeTarget

public section

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
structure GuideStore (ctx : Ctx) (tcLevel level : Nat) (st : SearchSt)
    (best : Option Key) (trail : FrameTrail) : Prop where
  first : 0 < st.gcaFirst → st.gcaFirst < level →
    ∃ g : Guide ctx tcLevel st.gcaFirst best,
      g.ref = st.firstlab ∧ g.Located trail
  canon : 0 < st.gcaCanon → st.gcaCanon < level →
    ∃ g : Guide ctx tcLevel st.gcaCanon best,
      g.ref = st.canonlab ∧ g.Located trail

/-- Forgetting frame locations recovers the guide invariant used by the
leaf-event lemmas. -/
theorem GuideStore.toGuides {ctx : Ctx} {tcLevel level : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
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
theorem Guide.Located.mono {ctx : Ctx} {tcLevel level : Nat}
    {before best : Option Key} {trail : FrameTrail}
    (g : Guide ctx tcLevel level before) (hloc : g.Located trail)
    (hinc : IncGrows before best) : (g.mono hinc).Located trail := by
  simpa only [Guide.Located, Guide.frame, Guide.mono] using hloc

/-- Both located guide ledgers survive an incumbent increase. -/
theorem GuideStore.grow {ctx : Ctx} {tcLevel level : Nat}
    {st : SearchSt} {before best : Option Key} {trail : FrameTrail}
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
theorem GuideStore.root {n : Nat} (g lab : Array Nat)
    (cellEnds : List Nat) (tcLevel : Nat) (best : Option Key)
    (trail : FrameTrail) :
    GuideStore { n := n, g := g } tcLevel 1
      (rootSt n lab cellEnds) best trail := by
  constructor <;> intro hp _ <;> simp [rootSt] at hp

/-- Descending through a newly recorded parent child preserves every
older guide and installs any guide whose control points at the parent.

The two last premises isolate the only new obligations: a control equal
to `level` must be backed by a guide in the newly extended trail. -/
theorem GuideStore.push {ctx : Ctx} {tcLevel level : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
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
theorem GuideStore.stateEq {ctx : Ctx} {tcLevel level : Nat}
    {st st' : SearchSt} {best : Option Key} {trail : FrameTrail}
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
theorem nodeKey_perm {ctx : Ctx} (hn : ctx.n = n)
    (tcLevel fuel level : Nat) (cs : List Nat)
    (st st' : SearchSt) (numcells : Nat)
    (hcp : cellsPerm st.ptn level st.lab st'.lab)
    (hls : st'.lab.size = st.lab.size)
    (hsl : st.lab.size = n)
    (hlab : LabOk st.lab n) (hlab' : LabOk st'.lab n)
    (hptn : st'.ptn = st.ptn) (hactive : st'.active = st.active)
    (hsp : st.ptn.size = n) (hact : st.active < 2 ^ n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, elem st.active v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level)
    (hvals : ∀ q : Nat, st.ptn[q]! ≤ level ∨
      st.ptn[q]! = n + 2)
    (hlf : level + fuel ≤ n + 1) :
    nodeKey ctx tcLevel fuel level cs st numcells =
      nodeKey ctx tcLevel fuel level cs st' numcells := by
  unfold nodeKey
  apply congrArg (prefixKey cs)
  rw [hptn, hactive]
  exact specNode_perm hn tcLevel fuel level st.lab st'.lab st.ptn
    st.active numcells hcp hls hsl hlab hlab' hsp hact hend hstarts
    hvals hlf

/-- Exact completion of a key-equivalent executable child covers the
corresponding frozen specification child. -/
theorem ChildDone.ofKeyEq {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc numcells o : Nat}
    {child : SearchSt} {best out : Option Key}
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
theorem SweepCover.advanceKey {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tv tcell : Nat}
    {cursor : Option Nat} {child : SearchSt} {best out : Option Key}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = some tv)
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
inductive NodeReceipt (trail : FrameTrail) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (cs : List Nat)
    (st out : SearchSt) (numcells : Nat) (best outBest : Option Key)
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
theorem NodeReceipt.toResult {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {cs : List Nat}
    {st out : SearchSt} {best outBest : Option Key} {r : Int}
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
theorem NodeReceipt.sound {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {cs : List Nat}
    {st out : SearchSt} {best outBest : Option Key} {r : Int}
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
inductive LoopReceipt (trail : FrameTrail) (ctx : Ctx)
    (tcLevel specFuel runFuel loopFuel level : Nat) (cs : List Nat)
    (rsLab rsPtn : Array Nat) (tc len numcells tcell : Nat)
    (cursor : Option Nat) (bound : Key) (st out : SearchSt)
    (best outBest : Option Key) (r : Option Int) : Prop where
  | complete
      (returned : r = none)
      (sound : LoopSound ctx bound best outBest)
      (installed : out.canonlevel ≠ 0)
      (read : stInc ctx out = outBest)
      (finalSet : Nat) (finalCursor : Option Nat)
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
      (finalSet : Nat) (finalCursor : Option Nat)
      (cover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
        numcells finalSet finalCursor outBest)
      (progress : cursorRank cursor + loopFuel ≤ cursorRank finalCursor)
      (bounded : ∀ v, finalCursor = some v → v < ctx.n)

/-- Forgetting a loop receipt's frame location recovers its ordinary
semantic result. -/
theorem LoopReceipt.toResult {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level tc len numcells tcell : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key} {st out : SearchSt} {best outBest : Option Key}
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
theorem NodeReceipt.parentReturn {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {cs : List Nat}
    {st out : SearchSt} {best outBest : Option Key} {r : Int}
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

/-- A completed or target-addressed child receipt advances its parent's
coverage.  Exact children may use cell-permutation key equivalence;
generator children use their location in the just-pushed parent frame. -/
theorem SweepCover.receipt {ctx : Ctx}
    {tcLevel specFuel runFuel level tc len numcells tcell tv offset : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option Key}
    {child out : SearchSt} {r : Int} {trail : FrameTrail}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hnext : nextElem tcell cursor = some tv)
    (hchild : NodeReceipt
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      ctx tcLevel specFuel runFuel (level + 1) codes child out
      (numcells + 1) before best r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level))
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes child
          (numcells + 1))
    (ho : offset < len) (htv : rsLab[tc + offset]! = tv)
    (hcoset : out.cosetindex = tv)
    (hgsz : ctx.g.size = ctx.n)
    (hbg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hv : ∀ γ ∈ out.genTrace.toList,
      checkAutom ctx.g γ ctx.n = true)
    (hstab : ∀ γ ∈ out.genTrace.toList,
      CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = ctx.n) (hinj : LabInj rsLab rsLab.size)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) best := by
  have hsound := hchild.sound hfuel
  rcases hchild.parentReturn hfuel hstay with hfull | ⟨payload, hloc⟩
  · exact h.advanceKey hnext hfull heq
  · exact h.unwind hsound.grows hnext hloc
      (FrameTrail.push_self trail level _) ho htv hcoset hgsz hbg hv hstab
      hs hinj hok hsp hend hvals hic hrange hlf

/-- Updating the first-path return controls preserves the source
location of a generator unwind. -/
theorem Unwind.Located.setFirst {trail : FrameTrail} {ctx : Ctx}
    {tcLevel target : Nat} {out : SearchSt} {best : Option Key}
    {payload : Unwind ctx tcLevel target out best}
    (h : payload.Located trail) (gcaFirst stabvertex : Nat) :
    ∃ payload' : Unwind ctx tcLevel target
        { out with gcaFirst := gcaFirst, stabvertex := stabvertex } best,
      payload'.Located trail := by
  let out' : SearchSt :=
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
        currentLt := orbitPayload.currentLt
        smaller := orbitPayload.smaller
        sound := orbitPayload.sound }
      exact ⟨.orbit orbitPayload', .orbit orbitPayload'⟩

/-- Removing a loop's temporary fixed vertex preserves the source
location of a generator unwind. -/
theorem Unwind.Located.setFixed {trail : FrameTrail} {ctx : Ctx}
    {tcLevel target : Nat} {out : SearchSt} {best : Option Key}
    {payload : Unwind ctx tcLevel target out best}
    (h : payload.Located trail) (fixedpts : Nat) :
    ∃ payload' : Unwind ctx tcLevel target
        { out with fixedpts := fixedpts } best,
      payload'.Located trail := by
  let out' : SearchSt := { out with fixedpts := fixedpts }
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
        currentLt := orbitPayload.currentLt
        smaller := orbitPayload.smaller
        sound := orbitPayload.sound }
      exact ⟨.orbit orbitPayload', .orbit orbitPayload'⟩

/-- A located child unwind strictly past its parent lifts through the
parent loop's fixed-vertex cleanup. -/
theorem LoopReceipt.ofChildUnwind {trail : FrameTrail} {ctx : Ctx}
    {tcLevel childFuel childRunFuel parentFuel loopFuel level : Nat}
    {childCs loopCs : List Nat} {childNumcells loopNumcells : Nat}
    {childSt loopSt out : SearchSt} {best outBest : Option Key}
    {target fixedpts : Nat} {rsLab rsPtn : Array Nat}
    {tc len tcell : Nat} {cursor : Option Nat} {bound : Key}
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
theorem NodeReceipt.ofLoopSome {trail : FrameTrail} {ctx : Ctx}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level : Nat}
    {nodeCs loopCs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {best outBest : Option Key} {r : Int}
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
theorem NodeReceipt.ofLoopNone {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCs loopCs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {best outBest : Option Key}
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
theorem LoopReceipt.prefix {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {st recSt out : SearchSt}
    {best mid outBest : Option Key} {r : Option Int}
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
theorem LoopReceipt.reindexSet {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell tcell' : Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best outBest : Option Key} {r : Option Int}
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
theorem LoopReceipt.step {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level tv : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best outBest : Option Key} {r : Option Int}
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
