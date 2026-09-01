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
guard on nonemptiness. Structurally recursive on an always-sufficient
fuel so the kernel can replay it. -/
@[expose] def lowBit (s : Nat) : Nat :=
  go (s + 1) s
where
  go : Nat → Nat → Nat
    | 0, _ => 0
    | fuel + 1, s =>
      if s == 0 then 0
      else if s % 2 == 1 then 0
      else 1 + go fuel (s / 2)

theorem lowBit_go_congr :
    ∀ (f₁ : Nat) {f₂ s : Nat}, s < f₁ → s < f₂ →
      lowBit.go f₁ s = lowBit.go f₂ s
  | f₁ + 1, f₂ + 1, s, h₁, h₂ => by
    rw [lowBit.go, lowBit.go]
    rcases Decidable.em (s = 0) with rfl | hs
    · simp
    · rcases Decidable.em (s % 2 = 1) with ho | ho
      · simp [hs, ho]
      · have hlt : s / 2 < f₁ ∧ s / 2 < f₂ := by omega
        simp only [beq_iff_eq, hs, ho, ite_false]
        rw [lowBit_go_congr f₁ (f₂ := f₂) hlt.1 hlt.2]

/-- The unconditional unfolding of `lowBit`. -/
theorem lowBit_eq (s : Nat) :
    lowBit s = if s = 0 then 0 else if s % 2 = 1 then 0
      else 1 + lowBit (s / 2) := by
  rw [lowBit, lowBit, lowBit.go]
  rcases Decidable.em (s = 0) with rfl | hs
  · simp
  · rcases Decidable.em (s % 2 = 1) with ho | ho
    · simp [hs, ho]
    · simp only [beq_iff_eq, hs, ho, ite_false]
      rw [lowBit_go_congr s (f₂ := s / 2 + 1) (by omega) (by omega)]

/-- The number of set bits. Structurally recursive on an
always-sufficient fuel so the kernel can replay it. -/
@[expose] def popCount (s : Nat) : Nat :=
  go (s + 1) s
where
  go : Nat → Nat → Nat
    | 0, _ => 0
    | fuel + 1, s =>
      if s == 0 then 0
      else s % 2 + go fuel (s / 2)

theorem popCount_go_congr :
    ∀ (f₁ : Nat) {f₂ s : Nat}, s < f₁ → s < f₂ →
      popCount.go f₁ s = popCount.go f₂ s
  | f₁ + 1, f₂ + 1, s, h₁, h₂ => by
    rw [popCount.go, popCount.go]
    rcases Decidable.em (s = 0) with rfl | hs
    · simp
    · have hlt : s / 2 < f₁ ∧ s / 2 < f₂ := by omega
      simp only [beq_iff_eq, hs, ite_false]
      rw [popCount_go_congr f₁ (f₂ := f₂) hlt.1 hlt.2]

/-- The unconditional unfolding of `popCount`: also valid at zero. -/
theorem popCount_eq (s : Nat) :
    popCount s = s % 2 + popCount (s / 2) := by
  rw [popCount, popCount, popCount.go]
  rcases Decidable.em (s = 0) with rfl | hs
  · simp [popCount.go]
  · simp only [beq_iff_eq, hs, ite_false]
    rw [popCount_go_congr s (f₂ := s / 2 + 1) (by omega) (by omega)]

@[simp] theorem popCount_zero : popCount 0 = 0 := by
  rw [popCount, popCount.go]
  simp

/-- Membership test. -/
@[expose, inline] def elem (s v : Nat) : Bool :=
  s.testBit v

/-- Insertion. -/
@[expose, inline] def insert (s v : Nat) : Nat :=
  s ||| (1 <<< v)

/-- Deletion. -/
@[expose, inline] def erase (s v : Nat) : Nat :=
  if s.testBit v then s ^^^ (1 <<< v) else s

/-- The least element of `s` greater than `pos`, or `none`: nauty's
`nextelement`, which iterates a set in ascending vertex order. `pos = none`
starts from the least element. -/
@[expose] def nextElem (s : Nat) (pos : Option Nat) : Option Nat :=
  let s' :=
    match pos with
    | none => s
    | some p => (s >>> (p + 1)) <<< (p + 1)
  if s' = 0 then none else some (lowBit s')

/-- All elements of `s` below `n` in ascending order. -/
@[expose] def toList (s n : Nat) : List Nat :=
  (List.range n).filter s.testBit

/-- nauty's row order: rows are compared as packed setwords with vertex `0`
most significant, so the least differing vertex decides and the row
containing it is greater. -/
@[expose] def rowCmp (a b : Nat) : Ordering :=
  if a = b then
    .eq
  else if a.testBit (lowBit (a ^^^ b)) then
    .gt
  else
    .lt

/-- The image of a vertex set under a vertex map: nauty's `permset`. -/
@[expose] def permset (s : Nat) (perm : Array Nat) (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc v => if s.testBit v then insert acc perm[v]! else acc) 0

end Hex.GraphIso.Nauty
