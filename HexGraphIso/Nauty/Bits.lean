/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.Conditional
public import Std

public section

/-!
Vertex-set primitives for the nauty-compatible search.

nauty stores a vertex set as packed setwords with vertex `0` at the most
significant bit, so unsigned setword comparison is lexicographic in vertex
order and `FIRSTBITNZ` returns the least vertex. This module models a
vertex set as a `Nat` bitset with bit `v` for vertex `v` and provides the
same observable operations: least-element extraction, ascending iteration
(`nextElem`), population count, and the vertex-order row comparison used
by `testcanlab`. The packed-word representation may replace this one later
only with a proof that no observable result changes.
-/

namespace Hex.GraphIso.Nauty

/-- The index of the least set bit. Returns `0` for the empty set; callers
guard on nonemptiness. -/
def lowBit (s : Nat) : Nat :=
  if h : s = 0 then
    0
  else if s % 2 = 1 then
    0
  else
    1 + lowBit (s / 2)
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

/-- The number of set bits. -/
def popCount (s : Nat) : Nat :=
  if h : s = 0 then
    0
  else
    s % 2 + popCount (s / 2)
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

/-- Membership test. -/
@[inline] def elem (s v : Nat) : Bool :=
  s.testBit v

/-- Insertion. -/
@[inline] def insert (s v : Nat) : Nat :=
  s ||| (1 <<< v)

/-- Deletion. -/
@[inline] def erase (s v : Nat) : Nat :=
  if s.testBit v then s ^^^ (1 <<< v) else s

/-- The least element of `s` greater than `pos`, or `none`: nauty's
`nextelement`, which iterates a set in ascending vertex order. `pos = none`
starts from the least element. -/
def nextElem (s : Nat) (pos : Option Nat) : Option Nat :=
  let s' :=
    match pos with
    | none => s
    | some p => (s >>> (p + 1)) <<< (p + 1)
  if s' = 0 then none else some (lowBit s')

/-- All elements of `s` below `n` in ascending order. -/
def toList (s n : Nat) : List Nat :=
  (List.range n).filter s.testBit

/-- nauty's row order: rows are compared as packed setwords with vertex `0`
most significant, so the least differing vertex decides and the row
containing it is greater. -/
def rowCmp (a b : Nat) : Ordering :=
  if a = b then
    .eq
  else if a.testBit (lowBit (a ^^^ b)) then
    .gt
  else
    .lt

/-- The image of a vertex set under a vertex map: nauty's `permset`. -/
def permset (s : Nat) (perm : Array Nat) (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc v => if s.testBit v then insert acc perm[v]! else acc) 0

end Hex.GraphIso.Nauty
