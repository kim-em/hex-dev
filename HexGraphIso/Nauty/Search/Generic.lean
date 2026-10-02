/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search.Refine

public section

/-!
A search policy supplies the operations at nodes and between children.
The recursion transports nonlocal exits without interpreting them. A
short-prune request is consumed only by the receiving sweep.
-/

namespace Hex.GraphIso.Nauty.Generic

/-- Completion of a sweep, an unwind to a level with an optional short
prune, or exhaustion of the recursion bound. -/
inductive Exit where
  | done
  | unwind (target : Nat) (short : Bool)
  | fuel
  deriving BEq, Repr, Inhabited

/-- The five node classifications in nauty's `processnode`. A better
leaf carries the number of adjacency rows shared with the incumbent. -/
inductive Leaf where
  | internal
  | autoFirst
  | autoCanon
  | better (sr : Nat)
  | bad
  deriving BEq, Repr, Inhabited

/-- The local operations of an individualization-refinement search.
The state includes the partition and any policy-specific bookkeeping.
Sweep entries are indices below `n`; a policy may interpret them as
vertex labels or target-cell offsets. -/
class Policy (σ : Type) (n : outParam Nat) {γ : outParam Type} where
  /-- Refine a node and return its cell count and code. -/
  visit : γ → Nat → Nat → σ → Nat × Nat × σ
  /-- Save a first-path refinement code. -/
  recordFirst : Nat → Nat → σ → σ
  /-- Compare an off-path refinement code with the reference paths. -/
  compareCodes : Nat → Nat → σ → σ
  /-- Choose a target cell, its sweep entries, and its size. -/
  chooseTarget : Bool → γ → Nat → Nat → Nat → σ → Int × VSet n × Nat × σ
  /-- Install the first discrete leaf. -/
  firstterminal : Nat → σ → σ
  /-- Classify an off-path node. -/
  classify : γ → Nat → Nat → σ → Leaf × σ
  /-- Act on a node classification. -/
  leafExit : Leaf → Nat → σ → Exit × σ
  /-- Update the cheap-automorphism boundary. -/
  cheapCheck : Bool → Nat → σ → σ
  /-- Individualize the child identified by a sweep entry. -/
  child : Bool → Nat → Nat → Nat → σ → σ
  /-- Update first-path controls after the leftmost child. -/
  afterChildFirst : Nat → Nat → σ → σ
  /-- Remove a child's temporary bookkeeping. -/
  leaveChild : Nat → σ → σ
  /-- Read the representative used to skip a sweep entry. -/
  orbit : σ → Nat → Nat
  /-- Restrict the remaining sweep entries using the newest pair. -/
  shortprune : VSet n → σ → VSet n
  /-- Restrict the remaining sweep entries using the stored pairs. -/
  longprune : VSet n → σ → VSet n
  /-- Restore the parent partition and comparison controls. -/
  recover : Nat → Nat → σ → σ
  /-- Finish a complete sweep. -/
  afterSweep : Bool → Nat → Nat → Nat → σ → σ

variable {n : Nat} {σ : Type} {γ : Type} [Policy σ n (γ := γ)]

/-- A node continuation with its recursion bound supplied by the caller. -/
abbrev NodeFn (σ : Type) := Bool → Nat → Nat → σ → Exit × σ

/-- A sweep continuation with both recursion bounds supplied by the caller. -/
abbrev SweepFn (σ : Type) (n : Nat) :=
  Bool → Nat → Nat → Nat → Nat → Option Nat → VSet n → Nat → σ → Exit × Nat × σ

/-- The local node operations, followed by a supplied child sweep. -/
@[expose] def nodeStep (ctx : γ) (tcLevel : Nat) (next : SweepFn σ n)
    (first : Bool) (level numcells : Nat) (st : σ) : Exit × σ :=
  Id.run do
    let (numcells, refcode, st) := Policy.visit (n := n) ctx level numcells st
    let st := if first then Policy.recordFirst (n := n) level refcode st else Policy.compareCodes (n := n) level refcode st
    let (tc, tcell, tcellsize, st) := Policy.chooseTarget (n := n) first ctx tcLevel level numcells st
    let mut st := st
    if first then
      if numcells == n then
        return (.unwind (level - 1) false, Policy.firstterminal (n := n) level st)
    else
      let (leaf, st') := Policy.classify (n := n) ctx level numcells st
      let (exit, st') := Policy.leafExit (n := n) leaf level st'
      st := st'
      match exit with
      | .done => pure ()
      | _ => return (exit, st)
    st := Policy.cheapCheck (n := n) first level st
    let tv := tcell.nextElem none
    let (exit, index, st') := next first
      level numcells tc.toNat (tv.getD 0) tv tcell 0 st
    match exit with
    | .done => return (.unwind (level - 1) false, Policy.afterSweep (n := n) first level tcellsize index st')
    | _ => return (exit, st')

/-- Apply the long filter, recover the parent, and visit the next surviving entry. -/
@[expose] def resume (inf : Nat) (next : SweepFn σ n)
    (first : Bool) (level numcells tc tv1 tv : Nat) (cell : VSet n) (index : Nat) (st : σ) :
    Exit × Nat × σ := Id.run do
  let mut cell := cell
  if !first && tv == tv1 then cell := Policy.longprune (n := n) cell st
  let st := Policy.recover (n := n) inf level st
  let index := if first && Policy.orbit (n := n) st tv == tv1 then index + 1 else index
  return next first level numcells tc tv1 (cell.nextElem (some tv)) cell index st

/-- Consume a child's exit after fixed-point cleanup, passing a deeper
unwind outward or filtering and resuming the current sweep. -/
@[expose] def advance (inf : Nat) (next : SweepFn σ n)
    (first : Bool) (level numcells tc tv1 tv : Nat) (cell : VSet n) (index : Nat) (st : σ) (exit : Exit) :
    Exit × Nat × σ := Id.run do
  let mut cell := cell
  match exit with
  | .fuel => return (.fuel, index, st)
  | .unwind target short =>
    if target < level then return (exit, index, st)
    if short then cell := Policy.shortprune (n := n) cell st
  | .done => pure ()
  return resume inf next first level numcells tc tv1 tv cell index st

/-- One target vertex, followed by supplied node and sweep continuations. -/
@[expose] def sweepStep (inf : Nat) (descend : NodeFn σ) (next : SweepFn σ n)
    (first : Bool) (level numcells tc tv1 tv : Nat) (tcell : VSet n)
    (index : Nat) (st : σ) : Exit × Nat × σ :=
  Id.run do
    let mut st := st
    if !first || Policy.orbit (n := n) st tv == tv then
      st := Policy.child (n := n) first level tc tv st
      let (exit, st') := descend (first && tv == tv1)
        (level + 1) (numcells + 1) st
      st := st'
      if first && tv == tv1 then
        st := Policy.afterChildFirst (n := n) level tv1 st
      st := Policy.leaveChild (n := n) tv st
      return advance inf next first level numcells tc tv1 tv tcell index st exit
    let index := if first && Policy.orbit (n := n) st tv == tv1 then index + 1 else index
    return next first level numcells tc tv1
      (tcell.nextElem (some tv)) tcell index st

mutual

/-- Refine a node, classify it, and sweep its surviving children. -/
@[expose] def node (first : Bool) (ctx : γ) (inf tcLevel fuel : Nat)
    (level numcells : Nat) (st : σ) : Exit × σ :=
  match fuel with
  | 0 => (.fuel, st)
  | fuel + 1 =>
    nodeStep ctx tcLevel
      (fun first level numcells tc tv1 cursor cell index st =>
        sweep first ctx inf tcLevel fuel (n + 1)
          level numcells tc tv1 cursor cell index st)
      first level numcells st
termination_by (fuel, 0, 0)

/-- Sweep surviving vertices, transporting exits below this level. -/
@[expose] def sweep (first : Bool) (ctx : γ) (inf tcLevel fuel cfuel : Nat)
    (level numcells tc tv1 : Nat) (tv? : Option Nat) (tcell : VSet n)
    (index : Nat) (st : σ) : Exit × Nat × σ :=
  match tv?, cfuel with
  | none, _ => (.done, index, st)
  | some _, 0 => (.fuel, index, st)
  | some tv, cfuel + 1 =>
    sweepStep inf
      (fun first level numcells st => node first ctx inf tcLevel fuel level numcells st)
      (fun first level numcells tc tv1 cursor cell index st =>
        sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st)
      first level numcells tc tv1 tv tcell index st
termination_by (fuel, 1, cfuel)

end

end Hex.GraphIso.Nauty.Generic
