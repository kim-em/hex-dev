/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.InversePacking
public import HexRealClosure.ReplayOperations
import all HexRealClosure.Algebraic

public section

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {Ctx : Type v} [zero : Zero E] [dec : DecidableEq E]
variable [one : One E] [add : Add E] [neg : Neg E] [sub : Sub E]
variable [mul : Mul E] [inv : Inv E] [div : Div E] [natCast : NatCast E]
variable [decCtx : DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- One typed inventory retains the packing equation and its checked inverse
operation together. The inner inverse record has a checked private factory. -/
structure InverseFact (context : Context E Ctx coeffSign parent) where
  entry : Packing context
  inverse : Packing.Inverse entry

/-- Match the exact nonzero operand, including its original stored polynomial
and cached tag. A same-value representative is a different request. -/
@[expose] def InverseFact.find (facts : List (InverseFact context)) (argument : Element context) :
    Option (InverseFact context) :=
  match facts with
  | [] => none
  | fact :: rest =>
    if fact.inverse.argument = argument then some fact else InverseFact.find rest argument

theorem InverseFact.find_argument (facts : List (InverseFact context)) (argument : Element context)
    {fact : InverseFact context} (found : InverseFact.find facts argument = some fact) :
    fact.inverse.argument = argument := by
  induction facts with
  | nil => simp [find] at found
  | cons first rest ih =>
    unfold find at found
    split at found
    · cases Option.some.inj found
      assumption
    · exact ih found

/-- Ordinary-kernel assembly cannot evaluate this branch without the extra
inverse-equation record. Compiled fallback remains total native inversion. -/
opaque Element.missingInverse (argument : Element context) :
    {value : Element context // value = argument⁻¹} := ⟨argument⁻¹, rfl⟩

/-- Nonzero inversion demands both its packing and inverse-equation evidence.
Canonical zero follows the native zero branch and needs no inverse candidate. -/
@[expose, instance_reducible] def Element.replayInverse (facts : List (InverseFact context)) :
    Inv (Element context) :=
  ⟨fun argument => match argument.stored with
    | none => 0
    | some _ => match InverseFact.find facts argument with
      | some fact => fact.entry.value
      | none => (Element.missingInverse argument).val⟩

theorem Element.replayInverse_eq (facts : List (InverseFact context)) :
    Element.replayInverse facts = (inferInstance : Inv (Element context)) := by
  apply congrArg Inv.mk
  funext argument
  cases stored : argument.stored with
  | none =>
    change (0 : Element context) = Element.inv argument
    unfold Element.inv
    rw [stored]
  | some value =>
    simp only
    cases found : InverseFact.find facts argument with
    | none => exact (Element.missingInverse argument).property
    | some fact =>
      exact fact.inverse.native.trans
        (congrArg (fun a : Element context => a⁻¹) (InverseFact.find_argument facts argument found))

local notation "Carrier" =>
  @Element E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent context
local notation "Record" =>
  @Packing E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent context
local notation "InverseRecord" =>
  @InverseFact E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent context

/-- Division retains the checked nonzero inverse before the original-key
packing of its product. Equal predecessor operations keep the original owner. -/
@[expose, instance_reducible] def Element.replayQuotient
    (predecessorAdd : Add E) (predecessorMul : Mul E)
    (sameAdd : predecessorAdd = add) (sameMul : predecessorMul = mul)
    (entries : List Record) (inverses : List InverseRecord) :
    Div Carrier :=
  let product := @Element.replayMul E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context predecessorAdd predecessorMul sameAdd sameMul entries
  let inverse := @Element.replayInverse E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context inverses
  ⟨fun a b => product.mul a (inverse.inv b)⟩

theorem Element.replayQuotient_eq
    (predecessorAdd : Add E) (predecessorMul : Mul E)
    (sameAdd : predecessorAdd = add) (sameMul : predecessorMul = mul)
    (entries : List Record) (inverses : List InverseRecord) :
    @Element.replayQuotient E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessorAdd predecessorMul sameAdd sameMul entries inverses =
      (inferInstance : Div Carrier) := by
  cases sameAdd
  cases sameMul
  unfold replayQuotient
  rw [Element.replayMul_eq, Element.replayInverse_eq]
  rfl

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Element.replayInverse_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.replayInverse_eq

/-- info: 'Hex.RealClosure.Algebraic.Element.replayQuotient_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.replayQuotient_eq
