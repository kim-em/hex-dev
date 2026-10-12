/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FiniteSupport
public meta import HexRealClosureMathlib.FiniteSupport

public section
namespace Hex.RealClosure.Algebraic.Packing.Inventory

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Every retained original equation holds at the level's one selected point. -/
theorem Data.equations {entries : List (Packing context)} {records : List (ValueSign context)}
    {facts : List (InverseFact context)} {read : E → K}
    (data : Data context entries records facts read) (zero : read 0 = 0) (unit : read 1 = 1) :
    ∀ entry ∈ entries,
      eval read (context.finitePoint read zero unit data.descriptor) entry.value.polynomial =
        eval read (context.finitePoint read zero unit data.descriptor) entry.original :=
  fun entry member => (entry.atPoint read zero unit data.descriptor (data.packings entry member)).1

end Hex.RealClosure.Algebraic.Packing.Inventory

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- One verified level, retaining its exact native owner and three inventories.
The reader's finite laws are generated from these records at its shared point. -/
structure Prefix where
  context : Expr
  entries : Expr
  records : Expr
  facts : Expr
  read : Expr
  zero : Expr
  unit : Expr
  data : Expr
  descriptor : Expr
  packings : Expr
  signs : Expr
  point : Expr
  reader : Expr
  equations : Expr

/-- Recover a level from its actual finite-data proof. No field instance or
global arithmetic law on the native algebraic carrier is installed. -/
def Prefix.ofData (data zero unit : Expr) : MetaM Prefix := do
  let type ← whnf (← inferType data)
  unless type.getAppFn.isConstOf ``Packing.Inventory.Data do
    throwError "expected a finite level-data proof"
  let args := type.getAppArgs
  unless args.size ≥ 5 do throwError "invalid finite level-data type"
  let context := args[args.size - 5]!
  let entries := args[args.size - 4]!
  let records := args[args.size - 3]!
  let facts := args[args.size - 2]!
  let read := args.back!
  let readerType ← whnf (← inferType read)
  let .forallE _ _ codomain _ := readerType | throwError "invalid predecessor reader"
  unless ← isDefEq codomain (mkConst ``Real) do throwError "finite prefix must interpret into the reals"
  let descriptor ← mkAppM ``Packing.Inventory.Data.descriptor #[data]
  let packings ← mkAppM ``Packing.Inventory.Data.packings #[data]
  let signs ← mkAppM ``Packing.Inventory.Data.signs #[data]
  let point ← mkAppM ``Context.finitePoint #[context, read, zero, unit, descriptor]
  let reader ← mkAppM ``Context.finiteRead #[context, read, zero, unit, descriptor]
  let equations ← mkAppM ``Packing.Inventory.Data.equations #[data, zero, unit]
  return {
    context := context
    entries := entries
    records := records
    facts := facts
    read := read
    zero := zero
    unit := unit
    data := data
    descriptor := descriptor
    packings := packings
    signs := signs
    point := point
    reader := reader
    equations := equations
  }

private def usesReader (level : Prefix) (reader : Expr) : MetaM Bool := do
  if reader == level.reader then return true
  -- Obligations on the retained predecessor belong to its supplier. Avoid
  -- unfolding the current selected point while dispatching those obligations.
  if reader == level.read then return false
  withTransparency .all (isDefEq reader level.reader)

private def operation (level : Prefix) (previous : Supplier) (type : Expr) :
    MetaM (Option Expr) := do
  let args := type.getAppArgs
  for (target, premise, theoremName, count) in #[
      (``Transport.Sum, ``Packing.SumData, ``Packing.lift_sum, 2),
      (``Transport.Product, ``Packing.ProductData, ``Packing.lift_product, 2),
      (``Transport.Difference, ``Packing.DifferenceData, ``Packing.lift_difference, 2),
      (``Transport.Scaling, ``Packing.ScalingData, ``Packing.lift_scaling, 2),
      (``Transport.Differentiation, ``Packing.DifferentiationData, ``Packing.lift_differentiation, 1),
      (``Transport.Evaluation, ``Packing.EvaluationData, ``Packing.lift_evaluation, 2)] do
    if type.getAppFn.isConstOf target then
      unless args.size ≥ count + 1 do throwError "invalid finite operation type"
      unless ← usesReader level args[args.size - count - 1]! do return none
      let operands := args.extract (args.size - count) args.size
      let required ← mkAppM premise (#[level.entries, level.read] ++ operands)
      let data ← build required previous
      let proof ← mkAppM theoremName
        (#[level.entries, level.read, level.zero, level.point] ++ operands ++
          #[level.equations, data])
      return some proof
  return none

private def replay (level : Prefix) (previous : Supplier) (type : Expr) :
    MetaM (Option Expr) := do
  let args := type.getAppArgs
  for (target, premise, theoremName, count) in #[
      (``Transport.Finite.DescriptorData, ``Packing.DescriptorData, ``Packing.lift_descriptor, 2),
      (``Transport.Finite.ReplayData, ``Packing.ReplayData, ``Packing.lift_replay, 5),
      (``Transport.Finite.NodeData, ``Packing.NodeData, ``Packing.lift_node, 5)] do
    if type.getAppFn.isConstOf target then
      unless args.size ≥ count + 3 do throwError "invalid finite replay type"
      unless ← usesReader level args[args.size - count - 3]! do return none
      let operands := args.extract (args.size - count) args.size
      let required ← mkAppM premise (#[level.entries, level.records, level.read] ++ operands)
      let data ← build required previous
      return some (← mkAppM theoremName
        (#[level.entries, level.records, level.read, level.zero, level.unit,
          level.descriptor, level.packings, level.signs] ++ operands ++ #[data]))
  return none

/-- Compose reached arithmetic and replay proofs with the predecessor supplier.
Every generated premise uses the retained inventories and shared point.
Unrecognized leaves remain the predecessor's responsibility; this is not a
global closure assertion or a source of independent real sign agreement. -/
def Prefix.supply (level : Prefix) (previous : Supplier) : Supplier := fun type => do
  if let some proof ← operation level previous type then return some proof
  if let some proof ← replay level previous type then return some proof
  if type.getAppFn.isConstOf ``Transport.Leading then
    let args := type.getAppArgs
    if ← usesReader level args[args.size - 2]! then
      let required ← mkAppM ``ValueSign.LeadingData #[level.records, args.back!]
      let data ← build required previous
      return some (← mkAppM ``ValueSign.lift_leading
        #[level.records, args.back!, level.read, level.zero, level.unit,
          level.descriptor, level.signs, data])
  previous type

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inventory.Data.equations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inventory.Data.equations
