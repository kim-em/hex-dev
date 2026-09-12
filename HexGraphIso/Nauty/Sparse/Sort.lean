/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Translated from nauty 2.9.3 sorttemplates.c (SORT_OF_SORT = 3),
copyright Brendan McKay, Apache 2.0.
-/
module

public import HexGraphIso.Nauty.Sparse.Graph

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

def median (a b c : Nat) : Nat :=
  if a ≤ b then (if b ≤ c then b else if c ≤ a then a else c)
  else if a ≤ c then a else if c ≤ b then b else c

/-- Insertion sort for the short segments in `sortindirect`. Equal keys
stay in their current order in this branch. -/
def insertion (x y : Array Nat) (start len : Nat) : Array Nat := Id.run do
  let mut x := x
  for i in [1:len] do
    let tmp := x[start + i]!
    let key := y[tmp]!
    let mut j := i
    for _ in [0:i] do
      if y[x[start + j - 1]!]! ≤ key then break
      x := x.set! (start + j) x[start + j - 1]!
      j := j - 1
      if j == 0 then break
    x := x.set! (start + j) tmp
  return x

/-- Pinned pivot sampling, including the median-of-nine threshold. -/
def pivot (x y : Array Nat) (start len : Nat) : Nat :=
  let keyAt := fun i => y[x[start + i]!]!
  if len < 320 then median (keyAt 0) (keyAt (len / 2)) (keyAt (len - 1))
  else median (median (keyAt 0) (keyAt 1) (keyAt 2))
    (median (keyAt (len / 2 - 1)) (keyAt (len / 2)) (keyAt (len / 2 + 1)))
    (median (keyAt (len - 3)) (keyAt (len - 2)) (keyAt (len - 1)))

/-- Bentley–McIlroy partition with nauty's exact swaps. Right cursors
are exclusive, avoiding C's temporary pointer just before the array. -/
def partition (x y : Array Nat) (start len : Nat) : Array Nat × Nat × Nat := Id.run do
  let v := pivot x y start len
  let mut x := x
  let mut a := start
  let mut b := start
  let mut c := start + len
  let mut d := c
  for _ in [0:len + 1] do
    for _ in [0:len] do
      if b >= c || y[x[b]!]! > v then break
      if y[x[b]!]! == v then
        x := x.swapIfInBounds a b
        a := a + 1
      b := b + 1
    for _ in [0:len] do
      if c <= b || y[x[c - 1]!]! < v then break
      if y[x[c - 1]!]! == v then
        x := x.swapIfInBounds (c - 1) (d - 1)
        d := d - 1
      c := c - 1
    if b >= c then break
    x := x.swapIfInBounds b (c - 1)
    b := b + 1
    c := c - 1
  let ba := b - a
  let dc := d - c
  let left := min (a - start) ba
  for i in [0:left] do x := x.swapIfInBounds (start + i) (b - left + i)
  let right := min dc (start + len - d)
  for i in [0:right] do x := x.swapIfInBounds (b + i) (start + len - right + i)
  return (x, ba, dc)

/-- The exact indirect sort used for three or more count fragments.
The explicit stack preserves nauty's smaller-side-first traversal.
Each partition removes its nonempty pivot class, so fewer than `2 * len`
stack entries are processed. -/
def indirect (x y : Array Nat) (start len : Nat) : Array Nat := Id.run do
  let mut x := x
  let mut stack := if len > 1 then [(start, len)] else []
  for _ in [0:2 * len + 1] do
    match stack with
    | [] => break
    | (start, size) :: rest =>
      stack := rest
      if size < 11 then
        x := insertion x y start size
      else
        let (next, ba, dc) := partition x y start size
        x := next
        if ba > dc then
          if ba > 1 then stack := (start, ba) :: stack
          if dc > 1 then stack := (start + size - dc, dc) :: stack
        else
          if dc > 1 then stack := (start + size - dc, dc) :: stack
          if ba > 1 then stack := (start, ba) :: stack
  return x

end Hex.GraphIso.Nauty.Sparse.Sort
