/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcome

public section

/-!
Consumption rules for search unwinds at their target child loop.

The executable state does not retain a parent loop's refined labelling:
`recover` reopens the partition but deliberately leaves the descendant
labelling in `SearchSt`.  A direct unwind therefore needs an explicit
relation between its stored anchor and the frozen loop frame.  Orbit
unwinds instead resolve through the receiving loop's evolving coverage.
-/

namespace Hex.GraphIso.Nauty

/-- An unwind anchor belongs to the indicated frozen child-loop frame. -/
structure Anchor.At {ctx : Ctx} {tcLevel level : Nat}
    {best : Option Key} (a : Anchor ctx tcLevel level best)
    (specFuel : Nat) (codes : List Nat) (rsLab rsPtn : Array Nat)
    (tc numcells : Nat) : Prop where
  fuel : a.specFuel = specFuel
  codePath : a.codes = codes
  lab : a.rsLab = rsLab
  ptn : a.rsPtn = rsPtn
  cell : a.tc = tc
  cells : a.numcells = numcells

/-- A located anchor supplies coverage of its stored child offset in the
receiving loop's frame. -/
theorem Anchor.doneAt {ctx : Ctx} {tcLevel level specFuel tc numcells : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {best : Option Key}
    (a : Anchor ctx tcLevel level best)
    (h : a.At specFuel codes rsLab rsPtn tc numcells) :
    ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc numcells
      best a.offset := by
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact a.done

/-- A direct generator anchor addressed to this loop advances coverage
past the current child. -/
theorem SweepCover.anchor {ctx : Ctx}
    {tcLevel specFuel level tc len numcells tcell tv : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : nextElem tcell cursor = some tv)
    (a : Anchor ctx tcLevel level best)
    (hat : a.At specFuel codes rsLab rsPtn tc numcells)
    (htv : rsLab[tc + a.offset]! = tv)
    (hinj : LabInj rsLab rsLab.size)
    (hrange : tc + len ≤ rsLab.size)
    (hoff : tc + a.offset < rsLab.size) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) best := by
  have hgrown := h.grow hinc
  apply hgrown.advance hnext
  · intro o ho heq
    have hidx : tc + o = tc + a.offset := hinj.eq
      (by omega) hoff (heq.trans htv.symm)
    have : o = a.offset := by omega
    subst o
    exact a.doneAt hat
  · intro _ hdone
    exact hdone

/-- An orbit unwind addressed to this loop advances coverage through its
strictly smaller, sound pointer. -/
theorem SweepCover.orbitUnwind {ctx : Ctx}
    {tcLevel specFuel level tc len numcells tcell tv o : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option Key} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : nextElem tcell cursor = some tv)
    (ho : o < len) (htv : rsLab[tc + o]! = tv)
    (payload : OrbitUnwind ctx level out)
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
  have hne : out.orbits[tv]! ≠ tv := by
    rw [← hcoset]
    exact Nat.ne_of_lt payload.smaller
  exact (h.grow hinc).orbitSkip hnext ho htv hgsz hbg hv hstab hs hinj
    hok hsp hend hvals hic hrange hlf payload.sound hne

end Hex.GraphIso.Nauty
