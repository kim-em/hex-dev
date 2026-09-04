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
