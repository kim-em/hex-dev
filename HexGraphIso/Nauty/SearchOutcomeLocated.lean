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

end Hex.GraphIso.Nauty
