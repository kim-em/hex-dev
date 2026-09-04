/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeMutual

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

namespace OtherProof

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

end Hex.GraphIso.Nauty
