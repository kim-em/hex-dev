/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Translated from nauty 2.9.3 nausparse.c, copyright Brendan McKay and
Adolfo Piperno, Apache 2.0.
-/
module

public import HexGraphIso.Nauty.Sparse.Refine

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse

/-- `bestcell_sg`: first nontrivial cell with the greatest number of
nontrivial joins. The source includes joins to the cell itself. -/
def bestcell (g : Graph n) (lab ptn : Array Nat) (level : Nat) : Nat := Id.run do
  let mut starts := #[]
  let mut sizes := #[]
  let mut nntcell := Array.replicate n n
  let mut first := 0
  for _ in [0:n] do
    if first >= n then break
    let last := cellEnd ptn level first
    if first < last then
      let index := starts.size
      starts := starts.push first
      sizes := sizes.push (last - first + 1)
      for j in [first:last + 1] do nntcell := nntcell.set! lab[j]! index
    first := last + 1
  if starts.isEmpty then return n
  let mut hits := Array.replicate starts.size 0
  let mut best := 0
  let mut maxcnt := 0
  for i in [0:starts.size] do
    let v := lab[starts[i]!]!
    for j in [g.offsets[v]!:g.offsets[v + 1]!] do
      let k := nntcell[g.neighbor j]!
      if k != n then hits := hits.set! k (hits[k]! + 1)
    let mut count := 0
    for j in [g.offsets[v]!:g.offsets[v + 1]!] do
      let k := nntcell[g.neighbor j]!
      if k != n then
        if hits[k]! > 0 && hits[k]! < sizes[k]! then count := count + 1
        hits := hits.set! k 0
    if count > maxcnt then
      best := i
      maxcnt := count
  return starts[best]!

/-- Honour a valid hint, otherwise use sparse best-cell selection through
the target level and the first nontrivial cell at greater depths. -/
def targetcell (g : Graph n) (lab ptn : Array Nat) (level tcLevel : Nat) (hint : Int) : Nat :=
  if hint >= 0 && ptn[hint.toNat]! > level &&
      (hint == 0 || ptn[hint.toNat - 1]! <= level) then hint.toNat
  else if level <= tcLevel then bestcell g lab ptn level
  else ((List.range n).find? fun i => ptn[i]! > level).getD 0

def maketargetcell (g : Graph n) (lab ptn : Array Nat) (level tcLevel : Nat) (hint : Int) :
    Nat × VSet n × Nat :=
  let first := targetcell g lab ptn level tcLevel hint
  let last := cellEnd ptn level first
  (first, worksetOf n lab first last, last - first + 1)

/-- The same joins and tie order as `bestcell`, reusing the vertex-to-cell
indices and endpoints maintained by refinement. -/
def bestcellCached (g : Graph n) (lab : Array Nat) (scratch : Scratch) : Nat × Scratch := Id.run do
  let mut hits := scratch.hits
  let scratch := { scratch with hits := #[] }
  let mut starts := #[]
  let mut cursor := 0
  for _ in [0:n] do
    if cursor >= n then break
    let last := scratch.cellend[cursor]!
    if cursor < last then
      starts := starts.push cursor
      hits := hits.set! cursor 0
    cursor := last + 1
  if starts.isEmpty then return (n, { scratch with hits })
  let mut best := starts[0]!
  let mut maxcnt := 0
  for first in starts do
    let v := lab[first]!
    for j in [g.offsets[v]!:g.offsets[v + 1]!] do
      let k := scratch.cellstart[g.neighbor j]!
      if k != n then hits := hits.set! k (hits[k]! + 1)
    let mut count := 0
    for j in [g.offsets[v]!:g.offsets[v + 1]!] do
      let k := scratch.cellstart[g.neighbor j]!
      if k != n then
        if hits[k]! > 0 && hits[k]! < scratch.cellend[k]! - k + 1 then count := count + 1
        hits := hits.set! k 0
    if count > maxcnt then
      best := first
      maxcnt := count
  return (best, { scratch with hits })

/-- Use cached partition data only when it describes the current refinement.
Empty-active entry and invalidated search states retain the standalone path. -/
def maketargetCached (g : Graph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (scratch : Scratch) : Nat × VSet n × Nat × Scratch := Id.run do
  if !scratch.indexed then
    let (first, cell, size) := maketargetcell g lab ptn level tcLevel hint
    return (first, cell, size, scratch)
  let (first, scratch) :=
    if hint >= 0 && ptn[hint.toNat]! > level &&
        (hint == 0 || ptn[hint.toNat - 1]! <= level) then (hint.toNat, scratch)
    else if level <= tcLevel then bestcellCached g lab scratch
    else (targetcell g lab ptn level tcLevel hint, scratch)
  let last := scratch.cellend[first]!
  return (first, worksetOf n lab first last, last - first + 1, scratch)

end Hex.GraphIso.Nauty.Sparse
