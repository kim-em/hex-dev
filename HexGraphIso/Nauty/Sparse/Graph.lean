/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file translates graph operations from nauty 2.9.3 nausparse.c,
copyright Brendan McKay and Adolfo Piperno, Apache 2.0.
-/
module

public import HexGraph.Sparse
public import HexGraphIso.Nauty.Search.Refine

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Canonical rows retain nauty's unsorted neighbour order until the public
result is constructed. -/
structure Rows (n : Nat) where
  offsets : Array Nat
  neighbors : Array Nat
deriving Inhabited, Repr

/-- A view of native compressed adjacency, sharing its existing arrays. -/
structure Graph (n : Nat) where
  offsets : Array Nat
  neighbors : Array (Fin n)
deriving Inhabited, Repr

def Rows.degree (G : Rows n) (v : Nat) : Nat := G.offsets[v + 1]! - G.offsets[v]!

namespace Graph

def ofGraph (G : Hex.SparseGraph n) : Graph n :=
  ⟨G.offsets, G.neighbors⟩

/-- `Fin` proofs are erased; reading a native entry requires no converted
adjacency array or runtime vertex wrapper. -/
@[inline] def neighbor (G : Graph n) (i : Nat) : Nat :=
  if h : i < G.neighbors.size then G.neighbors[i].val
  else panic! "index out of bounds"

@[simp] theorem neighbor_ofGraph (G : Hex.SparseGraph n) (i : Nat)
    (h : i < G.neighbors.size) : (ofGraph G).neighbor i = G.neighbors[i].val := by
  simp [ofGraph, neighbor, h]

def degree (G : Graph n) (v : Nat) : Nat := G.offsets[v + 1]! - G.offsets[v]!

/-- Allocate the canonical store once, before the search. -/
def blank (G : Graph n) : Rows n :=
  ⟨Array.replicate (n + 1) 0, Array.replicate G.neighbors.size 0⟩

end Graph

/-- nausparse's `INVLAB` scatter. -/
def inverse (n : Nat) (lab : Array Nat) : Array Nat := Id.run do
  let mut inv := Array.replicate n 0
  for i in [0:n] do inv := inv.set! lab[i]! i
  return inv

/-- `isautom_sg`: compare degrees and marked image neighbours, skipping
fixed vertices in the undirected configuration. -/
def isautom (g : Graph n) (p : Array Nat) : Bool := Id.run do
  let mut marks := Array.replicate n 0
  for i in [0:n] do
    if p[i]! != i then
      let pi := p[i]!
      if g.degree pi != g.degree i then return false
      let stamp := i + 1
      for j in [g.offsets[i]!:g.offsets[i + 1]!] do
        marks := marks.set! p[g.neighbor j]! stamp
      for j in [g.offsets[pi]!:g.offsets[pi + 1]!] do
        if marks[g.neighbor j]! != stamp then return false
  return true

/-- `updatecan_sg`: retain the shared prefix and rewrite the remaining
contiguous rows using inverse labels. No row sorting occurs in the search. -/
def updatecan (g : Graph n) (canong : Rows n) (lab : Array Nat) (samerows : Nat) : Rows n := Id.run do
  let inv := inverse n lab
  let mut offsets := canong.offsets
  let mut neighbors := canong.neighbors
  let mut k := if samerows == 0 then 0 else offsets[samerows]!
  for i in [samerows:n] do
    offsets := offsets.set! i k
    let v := lab[i]!
    for j in [g.offsets[v]!:g.offsets[v + 1]!] do
      neighbors := neighbors.set! k inv[g.neighbor j]!
      k := k + 1
  offsets := offsets.set! n k
  return ⟨offsets, neighbors⟩

/-- `testcanlab_sg`: smaller degree is preferred, then adjacency at the
first differing vertex. Return the comparison and the equal row prefix. -/
def testcanlab (g : Graph n) (canong : Rows n) (lab : Array Nat) : Int × Nat := Id.run do
  let inv := inverse n lab
  let mut marks := Array.replicate n 0
  for i in [0:n] do
    let v := lab[i]!
    let di := canong.degree i
    let dli := g.degree v
    if di != dli then return (if di < dli then -1 else 1, i)
    let stamp := i + 1
    let mut mina := n
    for j in [canong.offsets[i]!:canong.offsets[i + 1]!] do
      marks := marks.set! canong.neighbors[j]! stamp
    for j in [g.offsets[v]!:g.offsets[v + 1]!] do
      let k := inv[g.neighbor j]!
      if marks[k]! == stamp then marks := marks.set! k 0
      else if k < mina then mina := k
    if mina != n then
      for j in [canong.offsets[i]!:canong.offsets[i + 1]!] do
        let k := canong.neighbors[j]!
        if marks[k]! == stamp && k < mina then return (-1, i)
      return (1, i)
  return (0, n)

/-- `distvals`: breadth-first distances, with `n` for unreachable vertices.
The queue stores each vertex once, so `n` iterations suffice. -/
def distvals (g : Graph n) (root : Nat) : Array Nat := Id.run do
  let mut dist := (Array.replicate n n).set! root 0
  let mut queue := (Array.replicate n 0).set! 0 root
  let mut head := 0
  let mut tail := 1
  for _ in [0:n] do
    if tail >= n || head >= tail then break
    let i := queue[head]!
    head := head + 1
    let next := dist[i]! + 1
    for j in [g.offsets[i]!:g.offsets[i + 1]!] do
      let k := g.neighbor j
      if dist[k]! == n then
        dist := dist.set! k next
        queue := queue.set! tail k
        tail := tail + 1
  return dist

end Hex.GraphIso.Nauty.Sparse
