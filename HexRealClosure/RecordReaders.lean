/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RecordQueries
import all HexRealClosure.RecordPackets
import all HexRealClosure.InversePackets

public section
namespace Hex.RealClosure.Replay

variable {E : Type} [ordinaryOne : One E] [ordinaryAdd : Add E]
variable [ordinaryNeg : Neg E] [ordinarySub : Sub E] [ordinaryMul : Mul E]
variable [ordinaryInv : Inv E] [ordinaryDiv : Div E] [ordinaryNatCast : NatCast E]

/-- Supplied validation operations and sign reads on the original carrier,
with literal equalities to its ordinary implementations. -/
structure Operations (original : E → Int) where
  one : One E
  add : Add E
  neg : Neg E
  sub : Sub E
  mul : Mul E
  inv : Inv E
  div : Div E
  natCast : NatCast E
  one_eq : one = ordinaryOne
  add_eq : add = ordinaryAdd
  neg_eq : neg = ordinaryNeg
  sub_eq : sub = ordinarySub
  mul_eq : mul = ordinaryMul
  inv_eq : inv = ordinaryInv
  div_eq : div = ordinaryDiv
  natCast_eq : natCast = ordinaryNatCast
  sign : E → Int
  sign_eq : sign = original

end Hex.RealClosure.Replay

namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable (operations : Hex.RealClosure.Replay.Operations coeffSign)

/-- Check packing at its original request with cached validation and equal supplied queries.
The original owner is retained; only checked acceptance proofs are transported. -/
@[expose, macro_inline] def Packing.readPacketOperations?
    (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = context.reduce)
    (facts : List (SignFact context)) (p : DensePoly E)
    (queries : List (DensePoly E)) (hq : queries = [reduce p, p - reduce p])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    (packet : Codec.Json) : Option (Packing context) := do
  let raw := context.root.raw
  let (memo, index) ← Hex.RealClosure.Replay.readPacketMemoOperations?
    operations.one operations.add operations.sub operations.mul operations.natCast
    operations.one_eq operations.add_eq operations.sub_eq operations.mul_eq operations.natCast_eq
    operations.sign coeffSign operations.sign_eq
    codec ctx parent raw.head raw.lower raw.upper packet
  Packing.readMemoQueries? reduce hr facts p queries hq preceding hp memo index

/-- Equal operations, sign reads and query computations preserve the complete
native result, including malformed input and validation rejection. -/
theorem Packing.readPacketOperations_eq
    (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = context.reduce)
    (facts : List (SignFact context)) (p : DensePoly E)
    (queries : List (DensePoly E)) (hq : queries = [reduce p, p - reduce p])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    (packet : Codec.Json) :
    Packing.readPacketOperations? operations
      codec ctx reduce hr facts p queries hq preceding hp packet =
    Packing.readPacket? codec ctx reduce hr facts p packet := by
  unfold Packing.readPacketOperations?
  simp only [Hex.RealClosure.Replay.readPacketMemoOperations_eq, Packing.readMemoQueries_eq]
  unfold Hex.RealClosure.Replay.readPacketMemo? Packing.readPacket?
  cases decoded : (Codec.readGraph codec ctx parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper packet).toOption with
  | none => simp only [decoded, bind, Option.bind]
  | some graph =>
    simp only [decoded, bind, Option.bind]
    cases checked : graph.validate? coeffSign parent context.root.raw.head
      context.root.raw.lower context.root.raw.upper with
    | none => simp only [checked, Option.bind]
    | some memo => simp only [checked, Option.bind]
                   rfl

/-- Check the exact stored operand with cached validation and equal supplied queries.
The original owner is retained; only checked acceptance proofs are transported. -/
@[expose, macro_inline] def ValueSign.readPacketOperations?
    (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (value : Element context)
    (queries : List (DensePoly E)) (hq : queries = [value.polynomial])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    (packet : Codec.Json) : Option (ValueSign context) := do
  let raw := context.root.raw
  let (memo, index) ← Hex.RealClosure.Replay.readPacketMemoOperations?
    operations.one operations.add operations.sub operations.mul operations.natCast
    operations.one_eq operations.add_eq operations.sub_eq operations.mul_eq operations.natCast_eq
    operations.sign coeffSign operations.sign_eq
    codec ctx parent raw.head raw.lower raw.upper packet
  ValueSign.readMemoQueries? value queries hq preceding hp memo index

/-- Equal operations, sign reads and query computations preserve the complete
native result, including malformed input and validation rejection. -/
theorem ValueSign.readPacketOperations_eq
    (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (value : Element context)
    (queries : List (DensePoly E)) (hq : queries = [value.polynomial])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    (packet : Codec.Json) :
    ValueSign.readPacketOperations? operations
      codec ctx value queries hq preceding hp packet =
    ValueSign.readPacket? codec ctx value packet := by
  unfold ValueSign.readPacketOperations?
  simp only [Hex.RealClosure.Replay.readPacketMemoOperations_eq, ValueSign.readMemoQueries_eq]
  unfold Hex.RealClosure.Replay.readPacketMemo? ValueSign.readPacket?
  cases decoded : (Codec.readGraph codec ctx parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper packet).toOption with
  | none => simp only [decoded, bind, Option.bind]
  | some graph =>
    simp only [decoded, bind, Option.bind]
    cases checked : graph.validate? coeffSign parent context.root.raw.head
      context.root.raw.lower context.root.raw.upper with
    | none => simp only [checked, Option.bind]
    | some memo => simp only [checked, Option.bind]
                   rfl

/-- Check the original inverse operand and candidate with cached graph validation.
The original owner is retained; only checked acceptance proofs are transported. -/
@[expose, macro_inline] def InverseFact.readPacketOperations?
    (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (argument : Element context) (entry : Packing context)
    (candidate : DensePoly E) (same : candidate = argument.inverseCandidate)
    (queries : List (DensePoly E))
    (hq : queries = [argument.polynomial, argument.polynomial * entry.value.polynomial - 1])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    (packet : Codec.Json) : Option (InverseFact context) := do
  let raw := context.root.raw
  let (memo, index) ← Hex.RealClosure.Replay.readPacketMemoOperations?
    operations.one operations.add operations.sub operations.mul operations.natCast
    operations.one_eq operations.add_eq operations.sub_eq operations.mul_eq operations.natCast_eq
    operations.sign coeffSign operations.sign_eq
    codec ctx parent raw.head raw.lower raw.upper packet
  do
    let inverse ← Packing.Inverse.readMemoCandidate? argument entry candidate same queries hq preceding hp memo index
    return ⟨entry, inverse⟩

/-- Equal operations, sign reads and query computations preserve the complete
native result, including malformed input and validation rejection. -/
theorem InverseFact.readPacketOperations_eq
    (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (argument : Element context) (entry : Packing context)
    (candidate : DensePoly E) (same : candidate = argument.inverseCandidate)
    (queries : List (DensePoly E))
    (hq : queries = [argument.polynomial, argument.polynomial * entry.value.polynomial - 1])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    (packet : Codec.Json) :
    InverseFact.readPacketOperations? operations
      codec ctx argument entry candidate same queries hq preceding hp packet =
    InverseFact.readPacket? codec ctx argument entry packet := by
  unfold InverseFact.readPacketOperations?
  simp only [Hex.RealClosure.Replay.readPacketMemoOperations_eq, Packing.Inverse.readMemoCandidate_eq]
  unfold Hex.RealClosure.Replay.readPacketMemo? InverseFact.readPacket?
  cases decoded : (Codec.readGraph codec ctx parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper packet).toOption with
  | none => simp only [decoded, bind, Option.bind]
  | some graph =>
    simp only [decoded, bind, Option.bind]
    cases checked : graph.validate? coeffSign parent context.root.raw.head
      context.root.raw.lower context.root.raw.upper with
    | none => simp only [checked, Option.bind]
    | some memo => simp only [checked, Option.bind]
                   rfl

end Hex.RealClosure.Algebraic
