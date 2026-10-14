/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteBase

public section
namespace Hex.RealClosure.Algebraic.Packing.Inventory
open Hex.SignDet HexRealRootsTheory HexPolyTheory.Interpret

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- All retained conditions at one coordinate: the original root selection,
full stored derivative-sign word, packing equations, input signs and inverse
equations. Each polynomial is read with the same predecessor interpretation. -/
structure Conditions (context : Context E Ctx coeffSign parent)
    (entries : List (Packing context)) (records : List (ValueSign context))
    (facts : List (InverseFact context)) (read : E → K) (x : K) : Prop where
  selected : x ∈ Tarski.rootsIn
      (interpret (fun y : K => y) (fun _ => Iff.rfl)
        (Transport.polynomial read context.root.raw.head))
      ((Transport.endpoint read context.root.raw.lower).map (fun y : K => y))
      ((Transport.endpoint read context.root.raw.upper).map (fun y : K => y)) ∧
    signsAt (fun y : K => y) (fun _ => Iff.rfl)
      (context.root.raw.queries.map (Transport.polynomial read)) x = context.root.raw.signs
  packings : ∀ entry ∈ entries,
    eval read x entry.value.polynomial = eval read x entry.original ∧
      (SignType.sign (eval read x entry.original) : Int) = entry.value.sign
  signs : ∀ record ∈ records,
    (SignType.sign (eval read x record.value.polynomial) : Int) = record.value.sign
  inverses : ∀ fact ∈ facts,
    eval read x fact.entry.value.polynomial = eval read x fact.entry.original ∧
      eval read x fact.entry.value.polynomial = (eval read x fact.inverse.argument.polynomial)⁻¹ ∧
      (SignType.sign (eval read x fact.entry.value.polynomial) : Int) = fact.entry.value.sign ∧
      (SignType.sign (eval read x fact.inverse.argument.polynomial) : Int) = fact.inverse.argument.sign

/-- The verified data produces all conditions at the level's one selected
point, rather than separate witnesses for its arithmetic and cached signs. -/
theorem Data.conditions {context : Context E Ctx coeffSign parent}
    {entries : List (Packing context)} {records : List (ValueSign context)}
    {facts : List (InverseFact context)} {read : E → K}
    (data : Data context entries records facts read) (zero : read 0 = 0) (unit : read 1 = 1) :
    Conditions context entries records facts read
      (context.finitePoint read zero unit data.descriptor) := by
  refine ⟨context.finitePoint_spec read zero unit data.descriptor, ?_, ?_, ?_⟩
  · intro entry member
    exact entry.atPoint read zero unit data.descriptor (data.packings entry member)
  · intro record member
    exact record.atPoint read zero unit data.descriptor (data.signs record member)
  · intro fact member
    exact fact.atPoint read zero unit data.descriptor (data.inverses fact member)

end Hex.RealClosure.Algebraic.Packing.Inventory

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inventory.Data.conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inventory.Data.conditions
