/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.PackingInventory
public import HexRealClosureMathlib.FiniteRead

public section

namespace Hex.RealClosure.Algebraic.Packing.Inventory

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable {C : Type z} [DecidableEq C] {binding : C}

/-- Retained original keys, signs and reached predecessor operations of the
next algebraic level. These include construction differences and inverse
products that native replay alone does not retain. The descriptor and all record replays keep their exact
query slices; no interpretation of the whole current extension is assumed. -/
structure NextData (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (next : Context (Element context) C Element.sign binding)
    (nextEntries : List (Packing next)) (nextRecords : List (ValueSign next))
    (nextFacts : List (InverseFact next)) : Prop where
  descriptor : Packing.DescriptorData entries records read next.root.raw next.root.evidence
  packingReplay : ∀ entry ∈ nextEntries,
    Packing.ReplayData entries records read next.root.raw.head next.root.raw.lower next.root.raw.upper
      (next.root.raw.queries ++ [entry.representative, entry.original - entry.representative])
      entry.signs.evidence
  packingDifference : ∀ entry ∈ nextEntries,
    Packing.DifferenceData entries read entry.original entry.representative
  signs : ∀ record ∈ nextRecords,
    Packing.ReplayData entries records read next.root.raw.head next.root.raw.lower next.root.raw.upper
      (next.root.raw.queries ++ [record.value.polynomial]) record.signs.evidence
  inversePacking : ∀ fact ∈ nextFacts,
    Packing.ReplayData entries records read next.root.raw.head next.root.raw.lower next.root.raw.upper
      (next.root.raw.queries ++ [fact.entry.representative,
        fact.entry.original - fact.entry.representative]) fact.entry.signs.evidence
  inverseOriginal : ∀ fact ∈ nextFacts,
    Packing.DifferenceData entries read fact.entry.original fact.entry.representative
  inverseReplay : ∀ fact ∈ nextFacts,
    Packing.ReplayData entries records read next.root.raw.head next.root.raw.lower next.root.raw.upper
      (next.root.raw.queries ++ [fact.inverse.argument.polynomial,
        fact.inverse.argument.polynomial * fact.entry.value.polynomial - 1])
      fact.inverse.signs.evidence
  inverseProduct : ∀ fact ∈ nextFacts,
    Packing.ProductData entries read fact.inverse.argument.polynomial fact.entry.value.polynomial
  inverseDifference : ∀ fact ∈ nextFacts,
    Packing.DifferenceData entries read (fact.inverse.argument.polynomial * fact.entry.value.polynomial) 1

/-- Given the retained keys and operations in `NextData`, assemble the next
level's finite premises at the predecessor's shared point. This follows each literal replay and primitive
operation; it uses no universally closed reader on algebraic syntax. -/
theorem advance (entries : List (Packing context)) (records : List (ValueSign context))
    (facts : List (InverseFact context)) (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (data : Data context entries records facts read)
    (next : Context (Element context) C Element.sign binding)
    (nextEntries : List (Packing next)) (nextRecords : List (ValueSign next))
    (nextFacts : List (InverseFact next))
    (nextData : NextData entries records read next nextEntries nextRecords nextFacts) :
    Data next nextEntries nextRecords nextFacts (context.finiteRead read zero unit data.descriptor) := by
  have equations : ∀ entry ∈ entries,
      eval read (context.finitePoint read zero unit data.descriptor) entry.value.polynomial =
        eval read (context.finitePoint read zero unit data.descriptor) entry.original :=
    fun entry member => (entry.atPoint read zero unit data.descriptor (data.packings entry member)).1
  refine ⟨Packing.lift_descriptor entries records read zero unit data.descriptor data.packings data.signs
      next.root.raw next.root.evidence nextData.descriptor, ?_, ?_, ?_⟩
  · intro entry member
    exact ⟨Packing.lift_replay entries records read zero unit data.descriptor data.packings data.signs
      _ _ _ _ _ (nextData.packingReplay entry member),
      Packing.lift_difference entries read zero _ _ _ equations (nextData.packingDifference entry member)⟩
  · intro record member
    exact ⟨Packing.lift_replay entries records read zero unit data.descriptor data.packings data.signs
      _ _ _ _ _ (nextData.signs record member)⟩
  · intro fact member
    exact ⟨Packing.lift_replay entries records read zero unit data.descriptor data.packings data.signs
        _ _ _ _ _ (nextData.inversePacking fact member),
      Packing.lift_difference entries read zero _ _ _ equations (nextData.inverseOriginal fact member),
      Packing.lift_replay entries records read zero unit data.descriptor data.packings data.signs
        _ _ _ _ _ (nextData.inverseReplay fact member),
      Packing.lift_product entries read zero _ _ _ equations (nextData.inverseProduct fact member),
      Packing.lift_difference entries read zero _ _ _ equations (nextData.inverseDifference fact member)⟩

end Hex.RealClosure.Algebraic.Packing.Inventory

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inventory.advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inventory.advance
