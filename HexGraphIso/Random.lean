/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Colored

public section

/-!
Reproducible pseudo-random generation for the graph-isomorphism corpus.

All pseudo-random generation uses SplitMix64 with wrapping `UInt64`
arithmetic, with the update and output mixing fixed by the SPEC. The
corpus seeds start with `0x243F6A8885A308D3` and `0x13198A2E03707344`.
`nextBelow` uses threshold rejection sampling rather than `%`, so the
stream of accepted values is independent of modulo bias and of the
implementation language:

- `G(n, 1/2)` consumes one low bit for each pair `(i, j)` with `i < j` in
  lexicographic order;
- random relabelling uses Fisher-Yates from the last array position down;
- an onto `k`-colouring starts from `i % k` and shuffles that vector.
-/

namespace Hex.GraphIso.Random

/-- SplitMix64 state. -/
structure Gen where
  /-- The current stream state. -/
  state : UInt64
deriving Inhabited

/-- The first corpus seed. -/
@[expose] def seed1 : UInt64 := 0x243F6A8885A308D3

/-- The second corpus seed. -/
@[expose] def seed2 : UInt64 := 0x13198A2E03707344

/-- One SplitMix64 step: the next output and the advanced state. -/
@[expose] def next (g : Gen) : UInt64 × Gen :=
  let state := g.state + 0x9E3779B97F4A7C15
  let z := state
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), { state })

/-- A uniform value below `m` by threshold rejection: draws are discarded
while they lie at or above `2^64 - (2^64 % m)`, then reduced. `m = 0`
returns `0` without consuming the stream. -/
@[expose] def nextBelow (g : Gen) (m : Nat) : Nat × Gen :=
  if m = 0 then
    (0, g)
  else
    go g (64 + 2 * m)
where
  go (g : Gen) : Nat → Nat × Gen
    | 0 => (0, g)
    | fuel + 1 =>
      let (x, g) := next g
      let limit : Nat := 2 ^ 64 - (2 ^ 64) % m
      if x.toNat < limit then
        (x.toNat % m, g)
      else
        go g fuel

/-- The Erdős–Rényi graph `G(n, 1/2)`: one low bit per vertex pair
`(i, j)`, `i < j`, in lexicographic order. Returns the adjacency bitmask
over pairs in that order. -/
@[expose] def gnpMask (g : Gen) (n : Nat) : Nat × Gen := Id.run do
  let mut mask := 0
  let mut t := 0
  let mut gen := g
  for i in [0 : n] do
    for _j in [i + 1 : n] do
      let (x, g') := next gen
      gen := g'
      if x &&& 1 == 1 then
        mask := mask ||| (1 <<< t)
      t := t + 1
  return (mask, gen)

/-- Fisher-Yates shuffle from the last position down. -/
@[expose] def shuffle (g : Gen) (a : Array Nat) : Array Nat × Gen := Id.run do
  let mut a := a
  let mut gen := g
  let n := a.size
  for step in [0 : n - 1] do
    let i := n - 1 - step
    let (j, g') := nextBelow gen (i + 1)
    gen := g'
    let tmp := a[i]!
    a := (a.set! i a[j]!).set! j tmp
  return (a, gen)

/-- A uniformly shuffled onto `k`-colouring of `n ≥ k` vertices: start
from `i % k` and shuffle. -/
@[expose] def ontoColoring (g : Gen) (n k : Nat) : Array Nat × Gen :=
  let base := Array.ofFn (n := n) fun i => i.val % k
  shuffle g base

end Hex.GraphIso.Random
