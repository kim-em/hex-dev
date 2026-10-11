/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RecordReaders
public import HexRealClosure.ContextOperations
import all HexRealClosure.Algebraic

public section
namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} [zero : Zero E] [dec : DecidableEq E]
variable [ordinaryOne : One E] [ordinaryAdd : Add E] [ordinaryNeg : Neg E]
variable [ordinarySub : Sub E] [ordinaryMul : Mul E] [ordinaryInv : Inv E]
variable [ordinaryDiv : Div E] [ordinaryNatCast : NatCast E] [decCtx : DecidableEq Ctx]
variable {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable (operations : Hex.RealClosure.Replay.Operations coeffSign)

/-- Retain the original root and reduction policy while computing its
remainder with equal supplied coefficient operations. -/
@[expose] def Context.reduceOperations (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : DensePoly E :=
  let alternate := @Context.changeOps E Ctx zero dec decCtx
    operations.one operations.add operations.neg operations.sub operations.mul
    operations.inv operations.div operations.natCast
    ordinaryOne ordinaryAdd ordinaryNeg ordinarySub ordinaryMul ordinaryInv ordinaryDiv ordinaryNatCast
    operations.one_eq.symm operations.add_eq.symm operations.neg_eq.symm operations.sub_eq.symm
    operations.mul_eq.symm operations.inv_eq.symm operations.div_eq.symm operations.natCast_eq.symm
    coeffSign parent context
  @Context.reduce E Ctx zero dec operations.one operations.add operations.neg operations.sub
    operations.mul operations.inv operations.div operations.natCast decCtx coeffSign parent alternate p

theorem Context.reduceOperations_eq (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : context.reduceOperations operations p = context.reduce p := by
  cases operations with
  | mk one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn sign same =>
    cases ho; cases ha; cases hg; cases hs; cases hm; cases hi; cases hd; cases hn
    simp only [reduceOperations, Context.changeOps_self]

/-- Formal derivative queries computed with cached casts and multiplication. -/
@[expose] def Context.prefixOperations (context : Context E Ctx coeffSign parent) :
    List (DensePoly E) :=
  @RawDescriptor.queries E Ctx zero dec operations.natCast operations.mul context.root.raw

theorem Context.prefixOperations_eq (context : Context E Ctx coeffSign parent) :
    context.prefixOperations operations = context.root.raw.queries := by
  cases operations with
  | mk one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn sign same =>
    cases ho; cases ha; cases hg; cases hs; cases hm; cases hi; cases hd; cases hn
    rfl

/-- The original packing query and its exact zero-difference request. -/
@[expose] def Packing.queriesOperations (reduce : DensePoly E → DensePoly E)
    (p : DensePoly E) : List (DensePoly E) :=
  letI := operations.sub
  [reduce p, p - reduce p]

theorem Packing.queriesOperations_eq (reduce : DensePoly E → DensePoly E)
    (p : DensePoly E) : Packing.queriesOperations operations reduce p = [reduce p, p - reduce p] := by
  cases operations with
  | mk one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn sign same =>
    cases ho; cases ha; cases hg; cases hs; cases hm; cases hi; cases hd; cases hn
    rfl

/-- The original inverse equation with supplied polynomial arithmetic. -/
@[expose] def Packing.Inverse.queriesOperations (argument : Element context)
    (entry : Packing context) : List (DensePoly E) :=
  let left := argument.polynomial
  let right := entry.value.polynomial
  match operations with
  | ⟨one, _, _, sub, mul, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ =>
    letI := one
    letI := sub
    letI := mul
    [left, left * right - 1]

theorem Packing.Inverse.queriesOperations_eq (argument : Element context)
    (entry : Packing context) : Packing.Inverse.queriesOperations operations argument entry =
      [argument.polynomial, argument.polynomial * entry.value.polynomial - 1] := by
  cases operations with
  | mk one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn sign same =>
    cases ho; cases ha; cases hg; cases hs; cases hm; cases hi; cases hd; cases hn
    rfl

/-- Compute the actual splitting inverse candidate with equal coefficient
operations, without packing or replacing the original operand. -/
@[expose] def Element.inverseOperations (argument : Element context) : DensePoly E :=
  let head := context.root.raw.head
  let polynomial := argument.polynomial
  match operations with
  | ⟨one, add, neg, sub, mul, inv, div, natCast, _, _, _, _, _, _, _, _, _, _⟩ =>
    letI := one
    letI := add
    letI := neg
    letI := sub
    letI := mul
    letI := inv
    letI := div
    letI := natCast
    Element.inversePolynomial head polynomial

theorem Element.inverseOperations_eq (argument : Element context) :
    argument.inverseOperations operations = argument.inverseCandidate := by
  cases operations with
  | mk one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn sign same =>
    cases ho; cases ha; cases hg; cases hs; cases hm; cases hi; cases hd; cases hn
    rfl

end Hex.RealClosure.Algebraic
