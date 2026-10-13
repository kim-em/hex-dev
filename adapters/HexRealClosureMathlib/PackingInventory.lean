/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FinitePoint
public import HexRealClosureMathlib.TransportInventory

public section

namespace Hex.RealClosure.Algebraic.Packing.Inventory

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K] [LinearOrder K]

/-- The predecessor coefficients for one exact packing record: its actual
joint replay and the operands of its original-minus-representative equation. -/
@[expose] def packing (entry : Packing context) : List E :=
  Transport.Inventory.replay context.root.raw.head context.root.raw.lower context.root.raw.upper
    (context.root.raw.queries ++ [entry.representative, entry.original - entry.representative])
    entry.signs.evidence ++
      (Transport.Inventory.coefficients entry.original ++
        Transport.Inventory.coefficients entry.representative)

/-- Derive every reached packing premise from agreement on that finite list
and arithmetic on the predecessor's actual guarded domain. -/
theorem packing_data (entry : Packing context) (read : E → K) (S : E → Prop)
    (closed : Transport.Closed read S)
    (data : Transport.Inventory.Agreement read S coeffSign
      (fun x : K => (SignType.sign x : Int)) (packing entry)) : Packing.Data entry read := by
  refine ⟨Transport.Finite.ReplayData.of_closed read S closed coeffSign _ _ _ _ _ _
      (Transport.Inventory.replay_data closed _ _ _ _ _ data.append.1), ?_⟩
  exact Transport.Difference.of_closed read S closed entry.original entry.representative
    data.append.2.append.1.members data.append.2.append.2.members

/-- The cached input sign needs the original descriptor and its exact stored
value's selected-sign replay, with the original query positions. -/
@[expose] def inputSign (record : ValueSign context) : List E :=
  Transport.Inventory.replay context.root.raw.head context.root.raw.lower context.root.raw.upper
    (context.root.raw.queries ++ [record.value.polynomial]) record.signs.evidence

/-- Assemble the input-sign premise from its own predecessor inventory. -/
theorem inputSign_data (record : ValueSign context) (read : E → K) (S : E → Prop)
    (closed : Transport.Closed read S)
    (data : Transport.Inventory.Agreement read S coeffSign
      (fun x : K => (SignType.sign x : Int)) (inputSign record)) : ValueSign.Data record read :=
  ⟨Transport.Finite.ReplayData.of_closed read S closed coeffSign _ _ _ _ _ _
    (Transport.Inventory.replay_data closed _ _ _ _ _ data)⟩

/-- The inverse retains both joint replays and the original operands of its
product-minus-one equation. The constant unit belongs to every closed domain. -/
@[expose] def inverse (fact : InverseFact context) : List E :=
  packing fact.entry ++
    (Transport.Inventory.replay context.root.raw.head context.root.raw.lower context.root.raw.upper
      (context.root.raw.queries ++ [fact.inverse.argument.polynomial,
        fact.inverse.argument.polynomial * fact.entry.value.polynomial - 1])
      fact.inverse.signs.evidence ++
    (Transport.Inventory.coefficients fact.inverse.argument.polynomial ++
      Transport.Inventory.coefficients fact.entry.value.polynomial))

/-- Assemble the exact inverse record's two replays, original equation and
finite product/subtraction operations from one predecessor inventory. -/
theorem inverse_data (fact : InverseFact context) (read : E → K) (S : E → Prop)
    (closed : Transport.Closed read S)
    (data : Transport.Inventory.Agreement read S coeffSign
      (fun x : K => (SignType.sign x : Int)) (inverse fact)) : InverseFact.Data fact read := by
  have ordinary := packing_data fact.entry read S closed data.append.1
  have argument := data.append.2.append.2.append.1.members
  have output := data.append.2.append.2.append.2.members
  refine ⟨ordinary.replay, ordinary.difference,
    Transport.Finite.ReplayData.of_closed read S closed coeffSign _ _ _ _ _ _
      (Transport.Inventory.replay_data closed _ _ _ _ _ data.append.2.append.1),
    Transport.Product.of_closed read S closed _ _ argument output, ?_⟩
  exact Transport.Difference.of_closed read S closed _ _
    (fun i _ => closed.coeff_mul read S _ _ argument output i)
    (fun i _ => closed.coeff_one read S i)

/-- Collect the full predecessor support before choosing any point at this
level. All three typed record inventories share the original descriptor. -/
@[expose] def level (context : Context E Ctx coeffSign parent)
    (entries : List (Packing context)) (records : List (ValueSign context))
    (facts : List (InverseFact context)) : List E :=
  Transport.Inventory.descriptor context.root.raw context.root.evidence ++
    (entries.flatMap packing ++ (records.flatMap inputSign ++ facts.flatMap inverse))

/-- All finite predecessor premises of one complete algebraic level. -/
structure Data (context : Context E Ctx coeffSign parent)
    (entries : List (Packing context)) (records : List (ValueSign context))
    (facts : List (InverseFact context)) (read : E → K) : Prop where
  descriptor : Transport.Finite.DescriptorData read coeffSign
    (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence
  packings : ∀ entry ∈ entries, Packing.Data entry read
  signs : ∀ record ∈ records, ValueSign.Data record read
  inverses : ∀ fact ∈ facts, InverseFact.Data fact read

/-- Assemble the complete level from one predecessor reader and its finite
agreement. No packing, sign or inverse record selects an independent point. -/
theorem level_data (context : Context E Ctx coeffSign parent)
    (entries : List (Packing context)) (records : List (ValueSign context))
    (facts : List (InverseFact context)) (read : E → K) (S : E → Prop)
    (closed : Transport.Closed read S)
    (data : Transport.Inventory.Agreement read S coeffSign
      (fun x : K => (SignType.sign x : Int)) (level context entries records facts)) :
    Data context entries records facts read := by
  refine ⟨Transport.Finite.DescriptorData.of_closed read S closed coeffSign _ _ _
    (Transport.Inventory.descriptor_data closed _ _ data.append.1), ?_, ?_, ?_⟩
  · intro entry member
    exact packing_data entry read S closed (data.append.2.append.1.flatMap entry member)
  · intro record member
    exact inputSign_data record read S closed
      (data.append.2.append.2.append.1.flatMap record member)
  · intro fact member
    exact inverse_data fact read S closed (data.append.2.append.2.append.2.flatMap fact member)

end Hex.RealClosure.Algebraic.Packing.Inventory

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inventory.packing_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inventory.packing_data

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inventory.inputSign_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inventory.inputSign_data

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inventory.inverse_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inventory.inverse_data

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inventory.level_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inventory.level_data
