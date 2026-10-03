/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerContext

public section

namespace Hex.RealClosure.Tower

private def replayDecEq {E : Type} [Zero E] [DecidableEq E] :
    (left right : SignDet.Replay E Signature) → Decidable (left = right)
  | .leaf a, .leaf b => decidable_of_iff (a = b) (by simp)
  | .leaf _, .split _ _ _ => isFalse (by intro h; cases h)
  | .split _ _ _, .leaf _ => isFalse (by intro h; cases h)
  | .split a l r, .split b s t =>
    letI := replayDecEq l s
    letI := replayDecEq r t
    decidable_of_iff (a = b ∧ l = s ∧ r = t) (by simp)

private instance {E : Type} [Zero E] [DecidableEq E] :
    DecidableEq (SignDet.Replay E Signature) := replayDecEq

private instance {E : Type} [Zero E] [DecidableEq E] :
    DecidableEq (SignDet.RawDescriptor E Signature) := fun left right =>
  decidable_of_iff (left.context = right.context ∧ left.head = right.head ∧
    left.lower = right.lower ∧ left.upper = right.upper ∧
    left.indices = right.indices ∧ left.signs = right.signs) (by
      cases left
      cases right
      simp)

variable {registry : BaseContext.Registry}

/-- Check native context identity, including every descriptor and replay.
The returned equality aligns the original coefficient types. -/
def Chain.equal? {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Neg E]
    [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
    {sign : E → Int} {clean : E → Bool} {codec : SignDet.ValueCodec E}
    {binding : Signature} (left : Chain registry E sign clean codec binding)
    (right : Context registry) : Option (PLift (Context.pack left = right)) := by
  cases left with
  | base original =>
    cases right with
    | pack other =>
      cases other with
      | base other =>
        exact if same : BaseContext.PackedContext.pack original = .pack other then
          some ⟨by cases same; rfl⟩ else none
      | root => exact none
  | root parent descriptor frame encoded =>
    cases right with
    | pack other =>
      cases other with
      | base => exact none
      | root previous selected otherFrame otherEncoded =>
        exact match Chain.equal? parent (.pack previous) with
          | none => none
          | some ⟨same⟩ => by
            cases same
            exact if data : descriptor.raw = selected.raw ∧
                descriptor.evidence = selected.evidence then
              some ⟨by
                have descriptors : descriptor = selected := by
                  cases descriptor
                  cases selected
                  rcases data with ⟨rfl, rfl⟩
                  rfl
                cases descriptors
                have frames : frame = otherFrame :=
                  Option.some.inj (encoded.symm.trans otherEncoded)
                cases frames
                rfl⟩
            else none

def Context.equal? (left right : Context registry) : Option (PLift (left = right)) := by
  cases left with
  | pack chain => exact chain.equal? right

theorem Chain.equal?_self {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Neg E]
    [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
    {sign : E → Int} {clean : E → Bool} {codec : SignDet.ValueCodec E}
    {binding : Signature} (chain : Chain registry E sign clean codec binding) :
    chain.equal? (.pack chain) = some ⟨rfl⟩ := by
  induction chain with
  | base context => simp [Chain.equal?]
  | root parent descriptor frame encoded ih => simp [Chain.equal?, ih]

/-- Every immutable context is recognized as its own original owner. -/
theorem Context.equal?_self (context : Context registry) :
    context.equal? context = some ⟨rfl⟩ := by
  cases context with
  | pack chain => exact chain.equal?_self

/-- Native context equality has a sound pointer shortcut; otherwise every
actual predecessor, descriptor and replay is compared. -/
instance : DecidableEq (Context registry) := fun left right =>
  withPtrEqDecEq left right fun _ =>
    match checked : left.equal? right with
    | some ⟨same⟩ => isTrue same
    | none => isFalse (by
      intro same
      cases same
      rw [Context.equal?_self] at checked
      cases checked)

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.equal?_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.equal?_self
