/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineLoop
public import HexGraphIso.Nauty.Sparse.DistanceTransport

public section

namespace Hex.GraphIso.Nauty.Sparse

/- Proof names for literal blocks of `refineWith`. These have no generated
executable code. `refineWith_parts` connects their composition to production. -/
noncomputable section
namespace Refinement

@[expose] def queue (active : VSet n) : Array Nat := Id.run do
  let mut initialQueue := #[]
  let mut next := active.nextElem none
  for _ in [0:n] do
    let some i := next | break
    initialQueue := initialQueue.push i
    next := active.nextElem (some i)
  return initialQueue

@[expose] def start (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (scratch : Scratch) : RefineSt n := {
  cellstart := scratch.cellstart, cellend := scratch.cellend, indexed := false
  hits := scratch.hits, marks := scratch.marks
  vmarks := scratch.vmarks, stamp := scratch.stamp
  lab, ptn, active, queue := queue active, numcells, longcode := numcells }

@[expose] def indexed (level : Nat) (s : RefineSt n) : RefineSt n :=
  let (starts, ends) := indexCells n s.lab s.ptn level s.cellstart s.cellend
  { s with cellstart := starts, cellend := ends, indexed := true }

@[expose] def distanceStart (g : Graph n) (s : RefineSt n) : RefineSt n := { s with
  queue := #[], active := s.active.erase s.queue[0]!
  hits := distvals g s.lab[s.queue[0]!]! }

@[expose] def distance (level : Nat) (s : RefineSt n) : RefineSt n := Id.run do
  let mut state := s
  let mut first := 0
  for _ in [0:n] do
    if first >= n then break
    let last := state.cellend[first]!
    if first < last then state := splitCounts level first true state
    first := last + 1
  return state

@[expose] def loop (g : Graph n) (level : Nat) (s : RefineSt n) : RefineSt n := Id.run do
  let mut s := s
  for _ in [0:n] do
    if s.queue.isEmpty || s.numcells >= n then break
    let mut pos := s.queue.size - 1
    for i in [0:min s.queue.size 10] do
      if s.ptn[s.queue[i]!]! <= level then
        pos := i
        break
    let split := s.queue[pos]!
    let queue := (s.queue.set! pos s.queue[s.queue.size - 1]!).pop
    s := { s with queue, active := s.active.erase split }
    s := s.hash split
    if s.ptn[split]! <= level then s := splitSingleton g level split s
    else s := splitNontrivial g level split s
  return s

@[expose] def finish (s : RefineSt n) : RefineSt n :=
  { s with longcode := cleanup (mash s.longcode s.numcells) }

end Refinement

/-- The proof blocks compose to exactly the executed refinement function,
including the early empty-queue return and shallow-distance guards. -/
theorem refineWith_parts (g : Graph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch) :
    refineWith g level lab ptn active numcells scratch =
      let s := Refinement.start lab ptn active numcells scratch
      if s.queue.isEmpty then { s with longcode := cleanup s.longcode } else
        let r := Refinement.indexed level s
        if level <= 2 && s.queue.size == 1 && ptn[s.queue[0]!]! <= level && numcells <= n / 8 then
          Refinement.finish (Refinement.loop g level
            (Refinement.distance level (Refinement.distanceStart g r)))
        else Refinement.finish (Refinement.loop g level r) := by
  rfl

end
end Hex.GraphIso.Nauty.Sparse
