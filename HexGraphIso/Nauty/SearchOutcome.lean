/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.LoopCoverage
public import HexGraphIso.Nauty.QuartetStmt
public import HexGraphIso.Nauty.AutosLedger

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

/-- Vertices strictly after the loop cursor. -/
@[expose] def After (cursor : Option Nat) (v : Nat) : Prop :=
  match cursor with
  | none => True
  | some u => u < v

/-- The prefixed specification key of offset `o` in a refined target
cell. -/
@[expose] def sweepKey (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc numcells o : Nat) : Key :=
  prefixKey cs
    (childKey ctx tcLevel specFuel level rsLab rsPtn tc numcells o)

/-- Offset `o` has been absorbed by the incumbent in `out`. -/
@[expose] def ChildDone (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (out : SearchSt) (o : Nat) : Prop :=
  ∃ b, stInc ctx out = some b ∧
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
    (cursor : Option Nat) (out : SearchSt) : Prop where
  cover : ChildCover
    (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells)
    (fun o => o < len)
    (ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells out)
    (ChildLive rsLab tc len tcell cursor)
  past : ∀ o, o < len → elem tcell rsLab[tc + o]! = true →
    ¬ After cursor rsLab[tc + o]! →
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells out o

/-- Before the first iteration, the whole target-cell window is live. -/
theorem sweepCover_init (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells : Nat)
    (out : SearchSt) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (windowSet rsLab tc len) none out := by
  constructor
  · intro o ho
    refine Or.inr ⟨o, ⟨ho, ?_, trivial⟩, rfl⟩
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
    {out out' : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      (∀ j, sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells j =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells o →
          ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
            out' j) ∨
        ∃ j, ChildLive rsLab tc len tcell' cursor' j ∧
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells j)
    (hd : ∀ o,
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells out o →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        out' o)
    (hpast : ∀ o, o < len → elem tcell' rsLab[tc + o]! = true →
      ¬ After cursor' rsLab[tc + o]! →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        out' o) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor' out' := by
  exact ⟨ChildCover.step h.cover hs hd, hpast⟩

/-- Previously covered children remain covered when the incumbent grows. -/
theorem ChildDone.mono {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc numcells o : Nat}
    {out out' : SearchSt}
    (h : ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      out o)
    (hinc : ∀ b, stInc ctx out = some b →
      ∃ b', stInc ctx out' = some b' ∧ keyLe b b') :
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      out' o := by
  rcases h with ⟨b, hb, hkb⟩
  obtain ⟨b', hb', hbb'⟩ := hinc b hb
  exact ⟨b', hb', keyLe_trans hkb hbb'⟩

/-- A filter preserves sweep coverage when every old live child is either
absorbed or carried to a key-equivalent new survivor, and filtering adds no
vertices.  A carried survivor before the cursor is discharged through
`past`; it need not remain in the live suffix. -/
theorem SweepCover.filter {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor : Option Nat} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      (∀ j, sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells j =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells o →
          ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
            out j) ∨
        ∃ j, ChildLive rsLab tc len tcell' cursor j ∧
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells j)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor out := by
  refine ⟨ChildCover.step h.cover hs (fun _ hx => hx), ?_⟩
  intro o ho hm hpast
  exact h.past o ho (hsub _ hm) hpast

/-- At loop completion the evolving coverage invariant says that every
offset in the original target cell has been absorbed. -/
theorem SweepCover.finish {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat}
    {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hempty : ∀ o, ¬ ChildLive rsLab tc len tcell cursor o) :
    ∀ o, o < len → ChildDone ctx tcLevel specFuel level cs rsLab rsPtn
      tc numcells out o :=
  ChildCover.finish h.cover hempty

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

/-- The executable loop terminator discharges the live-set premise of
`SweepCover.finish`. -/
theorem SweepCover.finish_of_nextElem {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hnext : nextElem tcell cursor = none) :
    ∀ o, o < len → ChildDone ctx tcLevel specFuel level cs rsLab rsPtn
      tc numcells out o := by
  apply h.finish
  intro o ho
  exact no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- A child at an ancestor has already been absorbed.  The arrays and
offset are stored explicitly because neither `gcaFirst` nor `gcaCanon`
retains this path history. -/
structure Anchor (ctx : Ctx) (tcLevel target : Nat)
    (out : SearchSt) where
  specFuel : Nat
  codes : List Nat
  rsLab : Array Nat
  rsPtn : Array Nat
  tc : Nat
  numcells : Nat
  offset : Nat
  done : ChildDone ctx tcLevel specFuel target codes rsLab rsPtn tc
    numcells out offset

/-- Why an early return is sound.  Code one and code two retain their
different reference labellings; comparison pruning has no generator. -/
inductive Unwind (ctx : Ctx) (tcLevel target : Nat)
    (out : SearchSt) : Prop where
  | first (anchor : Anchor ctx tcLevel target out)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace)
  | canon (anchor : Anchor ctx tcLevel target out)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
  | frozen (anchor : Anchor ctx tcLevel target out)

/-- Every installed output key came from the incoming incumbent or this
node's specification subtree. -/
structure NodeSound (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (st out : SearchSt) (numcells : Nat) : Prop where
  upper : ∀ b, stInc ctx out = some b →
    keyLe b (incMax (stInc ctx st)
      (nodeKey ctx tcLevel specFuel level cs st numcells))

/-- The result of a node call, with logical and runtime fuel separated.

`complete` and `unwind` may have the same return integer.  The latter is
therefore a constructor, not an inequality side condition. -/
inductive NodeResult (ctx : Ctx) (tcLevel specFuel runFuel level : Nat)
    (cs : List Nat) (st out : SearchSt) (numcells : Nat)
    (r : Int) : Prop where
  | complete (sound : NodeSound ctx tcLevel specFuel level cs st out
      numcells)
      (returned : r = Int.ofNat level - 1)
      (installed : out.canonlevel ≠ 0)
      (full : stInc ctx out = some (incMax (stInc ctx st)
        (nodeKey ctx tcLevel specFuel level cs st numcells)))
  | unwind (sound : NodeSound ctx tcLevel specFuel level cs st out
      numcells)
      (target : Nat) (returned : r = Int.ofNat target)
      (below : target < level) (payload : Unwind ctx tcLevel target out)
  | exhausted (empty : runFuel = 0) (returned : r = 0) (unchanged : out = st)

/-- The result of a child-loop call.  Exhaustion is distinct from a
completed empty remainder, so a general theorem cannot accidentally treat
the `cfuel = 0` arm as coverage of every child. -/
inductive LoopResult (ctx : Ctx) (tcLevel specFuel runFuel loopFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells tcell : Nat)
    (cursor : Option Nat) (st out : SearchSt) (r : Option Int) : Prop where
  | complete
      (returned : r = none)
      (cover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
        numcells tcell cursor out)
      (empty : ∀ o, ¬ ChildLive rsLab tc len tcell cursor o)
  | unwind (target : Nat) (returned : r = some (Int.ofNat target))
      (below : target < level) (payload : Unwind ctx tcLevel target out)
  | exhausted (empty : loopFuel = 0) (returned : r = none)
      (unchanged : out = st)

end Hex.GraphIso.Nauty
