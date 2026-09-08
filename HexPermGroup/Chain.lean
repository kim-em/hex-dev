/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Orbit.Schreier

public section

namespace Hex.PermGroup

/-- One raw chain level, including generator provenance in the preceding level
(or the original input array at level zero). -/
structure Level (n : Nat) where
  generators : Array (Perm n)
  words : Vector Program generators.size
  orbit : Orbit n

/-- Raw stabilizer-chain data. The terminal generator array is checked explicitly;
only a successful complete check makes this a group certificate. -/
inductive Chain (n : Nat) where
  | leaf (generators : Array (Perm n)) (words : Vector Program generators.size)
  | cons (level : Level n) (tail : Chain n)

/-- A raw sift records either all orbit digits or its first failure. Negative
results have mathematical meaning only after the chain has passed its checker. -/
inductive SiftResult (n : Nat) where
  | member (digits : List Nat)
  | missing (level : Nat) (image : Fin n)
  | residual (value : Perm n)
  | shape (level : Nat)

namespace SiftResult

@[expose] def accepted : SiftResult n → Bool
  | .member _ => true
  | _ => false

/-- Prepend the current orbit digit, preserving the first failure unchanged. -/
@[expose] def prepend (digit : Nat) : SiftResult n → SiftResult n
  | .member digits => .member (digit :: digits)
  | .missing level image => .missing level image
  | .residual value => .residual value
  | .shape level => .shape level

@[simp] theorem accepted_prepend (digit : Nat) (result : SiftResult n) :
    (result.prepend digit).accepted = result.accepted := by
  cases result <;> rfl

end SiftResult

namespace Chain

@[expose] def generators : Chain n → Array (Perm n)
  | .leaf S _ => S
  | .cons level _ => level.generators

@[expose] def words (c : Chain n) : Vector Program c.generators.size :=
  match c with
  | .leaf _ programs => programs
  | .cons level _ => level.words

/-- Number of stored nonterminal levels. The checker requires exactly the
remaining number of points in the fixed base. -/
@[expose] def length : Chain n → Nat
  | .leaf _ _ => 0
  | .cons _ tail => tail.length + 1

/-- Sift by multiplying the current residual on the left by the inverse of its
selected representative. Digits are stored with level zero most significant. -/
@[expose] def sift : Chain n → Nat → Perm n → SiftResult n
  | .leaf _ _, _, p =>
    if p = Perm.id n then .member [] else .residual p
  | .cons level tail, base, p =>
    if hb : base < n then
      let image := p.get ⟨base, hb⟩
      match level.orbit.lookup[image.val] with
      | none => .missing base image
      | some x =>
        (tail.sift (base + 1) (level.orbit.reps[x.val].inv.comp p)).prepend x.val
    else .shape base

/-- Boolean acceptance of a raw sift. This does not assert completeness. -/
@[expose] def accepts (c : Chain n) (base : Nat) (p : Perm n) : Bool :=
  (c.sift base p).accepted

@[simp] theorem accepts_leaf (S : Array (Perm n)) (w : Vector Program S.size)
    (base : Nat) (p : Perm n) :
    (Chain.leaf S w).accepts base p = decide (p = Perm.id n) := by
  simp only [accepts, sift]
  split <;> simp_all [SiftResult.accepted]

theorem accepts_cons (level : Level n) (tail : Chain n) (base : Nat) (p : Perm n) :
    (Chain.cons level tail).accepts base p =
      if hb : base < n then
        match level.orbit.lookup[(p.get ⟨base, hb⟩).val] with
        | none => false
        | some x => tail.accepts (base + 1) (level.orbit.reps[x.val].inv.comp p)
      else false := by
  simp only [accepts, sift]
  split
  · split
    · simp_all only
      rfl
    · simp_all only
      exact SiftResult.accepted_prepend _ _
  · rfl

/-- The raw orbit-size product, before its interpretation as a group order has
been justified by complete checking. -/
@[expose] def orbitProduct : Chain n → Nat
  | .leaf _ _ => 1
  | .cons level tail => level.orbit.points.size * tail.orbitProduct

end Chain

end Hex.PermGroup
