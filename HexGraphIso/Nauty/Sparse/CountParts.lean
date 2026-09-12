/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine

public section

namespace Hex.GraphIso.Nauty.Sparse

/- Proof names for literal blocks of `splitCounts`. These generate no
executable code; `splitCounts_parts` identifies their composition. -/
noncomputable section
namespace CountSort

@[expose] def firstRun (lab hits : Array Nat) (first last : Nat) : Nat := Id.run do
  let w1 := hits[lab[first]!]!
  let mut v2 := first + 1
  for _ in [first + 1:last] do
    if hits[lab[v2]!]! != w1 then break
    v2 := v2 + 1
  return v2

@[expose] def minima (lab hits : Array Nat) (cap first last begin : Nat) :
    Nat × Nat × Nat × Nat × Array Nat := Id.run do
  let mut w1 := hits[lab[first]!]!
  let mut v2 := begin
  let mut w2 := cap
  let mut v3 := v2
  let mut lab := lab
  for j in [v2:last] do
    let lj := lab[j]!
    let w3 := hits[lj]!
    if w3 == w1 then
      lab := lab.set! j lab[v3]!
      lab := lab.set! v3 lab[v2]!
      lab := lab.set! v2 lj
      v2 := v2 + 1
      v3 := v3 + 1
    else if w3 == w2 then
      lab := lab.set! j lab[v3]!
      lab := lab.set! v3 lj
      v3 := v3 + 1
    else if w3 < w1 then
      lab := lab.set! j lab[v2]!
      lab := lab.set! v2 lab[first]!
      lab := lab.set! first lj
      v3 := v2 + 1
      v2 := first + 1
      w2 := w1
      w1 := w3
    else if w3 < w2 then
      lab := lab.set! j lab[v2]!
      lab := lab.set! v2 lj
      v3 := v2 + 1
      w2 := w3
  return (w1, v2, w2, v3, lab)

@[expose] def finish (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat) : RefineSt n := Id.run do
  let mut s := (s.hash (if distance then w2 else w1)).hash v2
  if last == v2 then return s
  let mut starts := s.cellstart
  s := { s with cellstart := #[] }
  if v2 == first + 1 then starts := starts.set! s.lab[first]! n
  if v3 == v2 + 1 then starts := starts.set! s.lab[v2]! n
  else
    for k in [v2:v3] do starts := starts.set! s.lab[k]! v2
  s := { s with
    cellstart := starts, numcells := s.numcells + 1
    cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1)
    ptn := s.ptn.set! (v2 - 1) level }
  if last == v3 then
    if v2 - first <= v3 - v2 && !s.active.mem first then return s.push first
    else return s.push v2
  if !distance then s := s.hash v3
  s := { s with lab := Sort.indirect s.lab s.hits v3 (last - v3) }
  s := s.push v2
  let mut bigpos : Option Nat := none
  let mut bigsize := v2 - first
  if v2 - first < v3 - v2 then
    bigpos := some (s.queue.size - 1)
    bigsize := v3 - v2
    if !distance then s := s.hash bigsize
  let mut k := v3 - 1
  for _ in [v3:last] do
    if k >= last - 1 then break
    s := { s with ptn := s.ptn.set! k level, numcells := s.numcells + 1 }
    if distance then s := s.hash k
    let l := k + 1
    s := s.push l
    let w3 := s.hits[s.lab[l]!]!
    if !distance then s := s.hash w3
    k := l
    for _ in [l:last - 1] do
      if s.hits[s.lab[k + 1]!]! != w3 then break
      s := { s with cellstart := s.cellstart.set! s.lab[k + 1]! l }
      k := k + 1
    let size := k - l + 1
    s := { s with cellend := s.cellend.set! l k }
    if size == 1 then
      s := { s with cellstart := s.cellstart.set! s.lab[l]! n }
    else
      s := { s with cellstart := s.cellstart.set! s.lab[l]! l }
      if size > bigsize then
        bigsize := size
        bigpos := some (s.queue.size - 1)
  if let some pos := bigpos then
    if !s.active.mem first then
      if distance then s := s.hash pos
      s := { s with
        active := (s.active.erase s.queue[pos]!).insert first
        queue := s.queue.set! pos first }
  return s

end CountSort

set_option maxHeartbeats 1000000 in
/-- The named count-sort blocks are literally the executed splitter. -/
theorem splitCounts_parts (level first : Nat) (distance : Bool) (s : RefineSt n) :
    splitCounts level first distance s =
      let last := s.cellend[first]! + 1
      let r := s.hash first
      let v2 := CountSort.firstRun s.lab s.hits first last
      if v2 == last then r else
        let m := CountSort.minima s.lab s.hits (n + 2) first last v2
        CountSort.finish level first last distance { r with lab := m.2.2.2.2 }
          m.1 m.2.1 m.2.2.1 m.2.2.2.1 := by
  cases distance <;>
    simp only [splitCounts, CountSort.firstRun, CountSort.minima, CountSort.finish,
      RefineSt.hash, RefineSt.push, Id.run, bind, pure, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_true, ite_false]
  all_goals repeat first | rfl | split

end
end Hex.GraphIso.Nauty.Sparse
