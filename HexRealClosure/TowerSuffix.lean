/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerTransport

public section

namespace Hex.RealClosure.Tower

open Lean SignDet

variable {registry : BaseContext.Registry}

/-- Append one validated root to a finite suffix over a fixed predecessor. -/
@[expose] def Suffix.snoc {source : Context registry} (suffix : Suffix source)
    (descriptor : SignDet.Descriptor suffix.context.Value Signature
      suffix.context.sign suffix.context.signature) : Suffix source :=
  match suffix with
  | .nil => .root descriptor .nil
  | .root first rest => .root first (rest.snoc descriptor)

/-- Concatenate two validated root suffixes in predecessor order. -/
@[expose] def Suffix.append {source : Context registry} :
    (first : Suffix source) → Suffix first.context → Suffix source
  | .nil, later => later
  | .root descriptor rest, later => .root descriptor (rest.append later)

/-- Concatenation ends in the context of its second suffix. -/
theorem Suffix.append_context {source : Context registry}
    (first : Suffix source) (later : Suffix first.context) :
    (first.append later).context = later.context := by
  induction first with
  | nil => rfl
  | root descriptor rest ih => exact ih later

/-- Concatenation respects an equality between the first suffix's target and
the second suffix's source. -/
theorem Suffix.append_cast_context {source other : Context registry}
    (first : Suffix source) (h : first.context = other)
    (later : Suffix other) :
    (first.append (h.symm ▸ later)).context = later.context := by
  cases h
  exact first.append_context later

/-- Appending no roots retains the original suffix. -/
theorem Suffix.append_nil {source : Context registry} (first : Suffix source) :
    first.append .nil = first := by
  induction first with
  | nil => rfl
  | root descriptor rest ih => exact congrArg (Suffix.root descriptor) ih

/-- Appending a root returns its actual native child context. -/
theorem Suffix.snoc_context {source : Context registry} (suffix : Suffix source)
    (descriptor : SignDet.Descriptor suffix.context.Value Signature
      suffix.context.sign suffix.context.signature) :
    (suffix.snoc descriptor).context = (suffix.context.adjoin descriptor).context := by
  induction suffix with
  | nil => rfl
  | root first rest ih => exact ih descriptor

/-- Appending a nonempty suffix first appends its initial root. -/
theorem Suffix.append_root {source : Context registry} (first : Suffix source)
    (descriptor : SignDet.Descriptor first.context.Value Signature
      first.context.sign first.context.signature)
    (rest : Suffix (first.context.adjoin descriptor).context) :
    first.append (.root descriptor rest) =
      (first.snoc descriptor).append
        ((Suffix.snoc_context first descriptor).symm ▸ rest) := by
  induction first with
  | nil => rfl
  | root head tail ih =>
    exact congrArg (Suffix.root head) (ih descriptor rest)

/-- Number of validated algebraic root levels in the suffix. -/
@[expose] def Suffix.length {source : Context registry} : Suffix source → Nat
  | .nil => 0
  | .root _ rest => rest.length + 1

/-- A packed tower context together with its staged base and all validated
root extensions in predecessor order. -/
inductive Origin (target : Context registry) : Type 1 where
  | pack {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
      (base : BaseContext.Context registry B sign)
      (suffix : Suffix (Context.base base))
      (target_eq : suffix.context = target) : Origin target

/-- Number of selected-root levels retained by the extracted suffix. -/
@[expose] def Origin.length {target : Context registry} (origin : Origin target) : Nat := by
  cases origin with
  | pack base suffix eq => exact suffix.length

/-- The staged base retained by a packed tower origin. -/
@[expose] def Origin.base {target : Context registry} (origin : Origin target) :
    BaseContext.PackedContext registry := by
  cases origin with
  | pack base suffix eq => exact .pack base

/-- The stored frame is exactly the frame returned by total adjoin. -/
theorem Context.adjoin_root_eq {E : Type} [Zero E] [DecidableEq E]
    [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
    {sign : E → Int} {clean : E → Bool} {codec : ValueCodec E} {binding : Signature}
    (chain : Chain registry E sign clean codec binding)
    (descriptor : SignDet.Descriptor E Signature sign binding)
    (frame : Literal)
    (encoded : Literal.ofJson (rootData codec descriptor) = some frame) :
    (Context.adjoin (.pack chain) descriptor).context =
      .pack (.root chain descriptor frame encoded) := by
  have hframe : (Context.adjoin (.pack chain) descriptor).frame = frame :=
    Option.some.inj ((Context.adjoin (.pack chain) descriptor).encoded.symm.trans encoded)
  cases hframe
  exact (Context.adjoin_native chain descriptor).1

/-- Reindex one stored descriptor along literal equality of its parent
contexts. This changes only its type, not its replay or selected root. -/
@[expose] def Context.castDescriptor {left right : Context registry}
    (h : left = right)
    (descriptor : SignDet.Descriptor right.Value Signature right.sign right.signature) :
    SignDet.Descriptor left.Value Signature left.sign left.signature := by
  cases h
  exact descriptor

/-- Adjoining after a context cast returns the same child context. -/
theorem Context.adjoin_cast {left right : Context registry}
    (h : left = right)
    (descriptor : SignDet.Descriptor right.Value Signature right.sign right.signature) :
    (left.adjoin (Context.castDescriptor h descriptor)).context =
      (right.adjoin descriptor).context := by
  cases h
  rfl

/-- Append an actual selected root to a packed origin. -/
@[expose] def Origin.snoc {parent : Context registry} (origin : Origin parent)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature) :
    Origin (parent.adjoin descriptor).context := by
  cases origin with
  | pack base suffix hparent =>
    let mapped := Context.castDescriptor hparent descriptor
    refine .pack base (suffix.snoc mapped) ?_
    rw [Suffix.snoc_context]
    exact Context.adjoin_cast hparent descriptor

/-- Follow the exact predecessor chain to recover its staged base and
validated descriptors without decoding serialized data. -/
@[expose] def Chain.origin {E : Type} [Zero E] [DecidableEq E]
    [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
    {sign : E → Int} {clean : E → Bool} {codec : ValueCodec E} {binding : Signature}
    (chain : Chain registry E sign clean codec binding) : Origin (.pack chain) := by
  cases chain with
  | base parentBase => exact .pack parentBase .nil rfl
  | root parent descriptor frame encoded =>
    let extended := (Chain.origin parent).snoc descriptor
    exact (Context.adjoin_root_eq parent descriptor frame encoded) ▸ extended

/-- Every validated packed tower has a staged base and an exact finite suffix
of its stored root extensions. No descriptor is reconstructed from a signature.
Consumers should use the original context for arithmetic and use the returned
equality only to align types; computing `Suffix.context` rebuilds frames. -/
@[expose] def Context.origin (context : Context registry) : Origin context := by
  cases context with
  | pack chain => exact chain.origin

/-- A packed staged base has an empty algebraic suffix. -/
theorem Context.origin_base {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign) :
    (Context.base base).origin = Origin.pack base .nil rfl := rfl

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.origin

/-- info: 'Hex.RealClosure.Tower.Context.origin_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.origin_base
