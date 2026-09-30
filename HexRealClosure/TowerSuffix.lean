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

/-- Appending a root returns its actual native child context. -/
theorem Suffix.snoc_context {source : Context registry} (suffix : Suffix source)
    (descriptor : SignDet.Descriptor suffix.context.Value Signature
      suffix.context.sign suffix.context.signature) :
    (suffix.snoc descriptor).context = (suffix.context.adjoin descriptor).context := by
  induction suffix with
  | nil => rfl
  | root first rest ih => exact ih descriptor

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

@[expose] def Origin.length {target : Context registry} (origin : Origin target) : Nat := by
  cases origin with
  | pack base suffix eq => exact suffix.length

private theorem Context.adjoin_root_eq {E : Type} [Zero E] [DecidableEq E]
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

private def Context.castDescriptor {left right : Context registry}
    (h : left = right)
    (descriptor : SignDet.Descriptor right.Value Signature right.sign right.signature) :
    SignDet.Descriptor left.Value Signature left.sign left.signature := by
  cases h
  exact descriptor

private theorem Context.adjoin_cast {left right : Context registry}
    (h : left = right)
    (descriptor : SignDet.Descriptor right.Value Signature right.sign right.signature) :
    (left.adjoin (Context.castDescriptor h descriptor)).context =
      (right.adjoin descriptor).context := by
  cases h
  rfl

private def Chain.origin {E : Type} [Zero E] [DecidableEq E]
    [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
    {sign : E → Int} {clean : E → Bool} {codec : ValueCodec E} {binding : Signature}
    (chain : Chain registry E sign clean codec binding) : Origin (.pack chain) := by
  cases chain with
  | base parentBase => exact .pack parentBase .nil rfl
  | root parent descriptor frame encoded =>
    obtain ⟨base, suffix, hparent⟩ := Chain.origin parent
    let native : SignDet.Descriptor (Context.pack parent).Value Signature
        (Context.pack parent).sign (Context.pack parent).signature := descriptor
    let mapped := Context.castDescriptor hparent native
    refine .pack base (suffix.snoc mapped) ?_
    rw [Suffix.snoc_context]
    change (suffix.context.adjoin mapped).context = _
    rw [show (suffix.context.adjoin mapped).context =
      ((Context.pack parent).adjoin descriptor).context from
      Context.adjoin_cast hparent native]
    exact Context.adjoin_root_eq parent descriptor frame encoded

/-- Every validated packed tower has a staged base and an exact finite suffix
of its stored root extensions. No descriptor is reconstructed from a signature. -/
def Context.origin (context : Context registry) : Origin context := by
  cases context with
  | pack chain => exact chain.origin

/-- Recover the number of validated root levels from the stored chain. -/
@[expose] def Context.rootDepth (context : Context registry) : Nat := context.origin.length

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.origin
