/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Translated from nauty 2.9.3 nausparse.c, copyright Brendan McKay and
Adolfo Piperno, Apache 2.0.
-/
module

public import HexGraphIso.Nauty.Sparse.Search
public import HexGraphIso.Nauty.Sparse.Literal.Refine

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Literal

def bestcell (g : Graph n) (lab ptn : Array Nat) (level : Nat) : Nat := Id.run do
  let mut starts := #[]
  let mut sizes := #[]
  let mut nntcell := Array.replicate n n
  let mut first := 0
  for _ in range (0) (n) do
    if first >= n then break
    let last := cellEnd ptn level first
    if first < last then
      let index := starts.size
      starts := starts.push first
      sizes := sizes.push (last - first + 1)
      for j in range (first) (last + 1) do nntcell := nntcell.set! lab[j]! index
    first := last + 1
  if starts.isEmpty then return n
  let mut hits := Array.replicate starts.size 0
  let mut best := 0
  let mut maxcnt := 0
  for i in range (0) (starts.size) do
    let v := lab[starts[i]!]!
    for j in range (g.offsets[v]!) (g.offsets[v + 1]!) do
      let k := nntcell[g.neighbor j]!
      if k != n then hits := hits.set! k (hits[k]! + 1)
    let mut count := 0
    for j in range (g.offsets[v]!) (g.offsets[v + 1]!) do
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

@[specialize] def initialPartitionWith (n k : Nat) (colors : Array α) (color : α → Nat) :
    Array Nat × List Nat := Id.run do
  let mut buckets : Array (List Nat) := Array.replicate k []
  for i in range (0) (n) do
    let c := if h : i < colors.size then color colors[i] else panic! "index out of bounds"
    buckets := buckets.set! c (i :: buckets[c]!)
  let mut lab := #[]
  let mut ends := []
  for bucket in buckets do
    if !bucket.isEmpty then
      for v in bucket.reverse do lab := lab.push v
      ends := (lab.size - 1) :: ends
  return (lab, ends.reverse)

theorem bestcell_eq : @bestcell = @Sparse.bestcell := by
  funext n g lab ptn level
  simp only [bestcell, Sparse.bestcell, range_forIn]

theorem targetcell_eq : @targetcell = @Sparse.targetcell := by
  funext n g lab ptn level tcLevel hint
  simp only [targetcell, Sparse.targetcell, bestcell_eq]

theorem maketargetcell_eq : @maketargetcell = @Sparse.maketargetcell := by
  funext n g lab ptn level tcLevel hint
  simp only [maketargetcell, Sparse.maketargetcell, targetcell_eq]

theorem initialPartitionWith_eq : @initialPartitionWith = @Sparse.initialPartitionWith := by
  funext α n k colors color
  simp only [initialPartitionWith, Sparse.initialPartitionWith, range_forIn]
  rfl

end Hex.GraphIso.Nauty.Sparse.Literal
