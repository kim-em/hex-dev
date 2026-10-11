/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RecordPackets
public import HexRealClosure.InversePackets
public import HexRealClosure.RecordOperations
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.InversePacking

public section
namespace Hex.SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Select the original ordered queries with equal supplied arithmetic and
formal-derivative prefixes. Transport is confined to the acceptance proof. -/
@[expose, macro_inline] def SelectedSigns.readQueries? {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) (qs : List (DensePoly E))
    (values : Vector Int qs.length) (queries : List (DensePoly E)) (hq : queries = qs)
    (preceding : List (DensePoly E)) (hp : preceding = d.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked sign context head lower upper)) (index : Nat) :
    Option (SelectedSigns d qs) := do
  let bound ← Dag.bindDomain? sign context memo d.raw.head d.raw.lower d.raw.upper
  let tree ← Dag.select? sign context d.raw.head d.raw.lower d.raw.upper bound index
    (preceding ++ queries)
  if row : tree.val.node.system.tableRows.toList.filter
      (fun entry => decide (entry.1.take preceding.length = d.raw.signs)) =
      [(d.raw.signs ++ values.toList, 1)] then
    return SelectedSigns.ofTable d qs values tree.val
      (by simpa only [hq, hp] using tree.property) (by simpa only [hp] using row)
  else none

/-- Equal query implementations preserve acceptance, rejection and the full
returned evidence, without assuming that the supplied memo is complete. -/
theorem SelectedSigns.readQueries_eq {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) (qs : List (DensePoly E))
    (values : Vector Int qs.length) (queries : List (DensePoly E)) (hq : queries = qs)
    (preceding : List (DensePoly E)) (hp : preceding = d.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked sign context head lower upper)) (index : Nat) :
    SelectedSigns.readQueries? d qs values queries hq preceding hp memo index =
      SelectedSigns.readMemo? d qs values memo index := by
  cases hq
  cases hp
  rfl

end Hex.SignDet

namespace Hex.RealClosure.Algebraic
open SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- Read an original packing record with equal supplied difference arithmetic
and derivative prefixes. The stored packing retains its original owner. -/
@[expose, macro_inline] def Packing.readMemoQueries? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) (p : DensePoly E)
    (queries : List (DensePoly E)) (hq : queries = [reduce p, p - reduce p])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option (Packing context) :=
  match SignFact.find facts (reduce p) with
  | none => none
  | some fact => do
    let signs ← SelectedSigns.readQueries? context.root [reduce p, p - reduce p]
      #v[fact.val, 0] queries hq preceding hp memo index
    Packing.make? reduce hr facts p signs

theorem Packing.readMemoQueries_eq (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) (p : DensePoly E)
    (queries : List (DensePoly E)) (hq : queries = [reduce p, p - reduce p])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Packing.readMemoQueries? reduce hr facts p queries hq preceding hp memo index =
      Packing.readMemo? reduce hr facts p memo index := by
  cases hq
  cases hp
  rfl

/-- Read the exact stored operand with an equal supplied polynomial query. -/
@[expose, macro_inline] def ValueSign.readMemoQueries? (value : Element context)
    (queries : List (DensePoly E)) (hq : queries = [value.polynomial])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option (ValueSign context) := do
  let signs ← SelectedSigns.readQueries? context.root [value.polynomial] #v[value.sign]
    queries hq preceding hp memo index
  ValueSign.make? value signs

theorem ValueSign.readMemoQueries_eq (value : Element context)
    (queries : List (DensePoly E)) (hq : queries = [value.polynomial])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    ValueSign.readMemoQueries? value queries hq preceding hp memo index =
      ValueSign.readMemo? value memo index := by
  cases hq
  cases hp
  rfl

/-- Read the original inverse with equal supplied multiplication/subtraction
queries. The actual native candidate is still checked by the inverse factory. -/
@[expose, macro_inline] def Packing.Inverse.readMemoQueries? (argument : Element context)
    (entry : Packing context) (queries : List (DensePoly E))
    (hq : queries = [argument.polynomial, argument.polynomial * entry.value.polynomial - 1])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option (Packing.Inverse entry) := do
  let signs ← SelectedSigns.readQueries? context.root
    [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]
    #v[argument.sign, 0] queries hq preceding hp memo index
  Packing.Inverse.make? argument entry signs

theorem Packing.Inverse.readMemoQueries_eq (argument : Element context)
    (entry : Packing context) (queries : List (DensePoly E))
    (hq : queries = [argument.polynomial, argument.polynomial * entry.value.polynomial - 1])
    (preceding : List (DensePoly E)) (hp : preceding = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Packing.Inverse.readMemoQueries? argument entry queries hq preceding hp memo index =
      Packing.Inverse.readMemo? argument entry memo index := by
  cases hq
  cases hp
  rfl

end Hex.RealClosure.Algebraic

namespace Hex.RealClosure.Replay
open Hex.SignDet
variable {E Ctx : Type} [zero : Zero E] [dec : DecidableEq E]
variable [ordinaryOne : One E] [ordinaryAdd : Add E] [ordinarySub : Sub E]
variable [ordinaryMul : Mul E] [ordinaryNatCast : NatCast E] [decCtx : DecidableEq Ctx]

/-- Decode and validate a supplied literal graph, retaining its root index and
checked memo for independent original-owner record selection. -/
@[expose, macro_inline] def readPacketMemo? (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (head : DensePoly E) (lower upper : Endpoint E)
    (packet : Codec.Json) : Option (Array (Dag.Checked sign binding head lower upper) × Nat) := do
  let graph ← (Codec.readGraph codec ctx binding head lower upper packet).toOption
  let memo ← graph.validate? sign binding head lower upper
  return (memo, graph.root)

/-- Decode at the original domain, validate with equal supplied operations and
sign reads, then restore only acceptance proofs in the retained literal memo. -/
@[expose, macro_inline] def readPacketMemoOperations?
    (one : One E) (add : Add E) (sub : Sub E) (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign original : E → Int) (same : sign = original)
    (codec : ValueCodec E) (ctx : ValueCodec Ctx) (binding : Ctx)
    (head : DensePoly E) (lower upper : Endpoint E) (packet : Codec.Json) :
    Option (Array (@Dag.Checked E Ctx zero dec ordinaryOne ordinaryAdd ordinarySub ordinaryMul
      ordinaryNatCast decCtx original binding head lower upper) × Nat) :=
  letI := ordinaryOne
  letI := ordinaryAdd
  letI := ordinarySub
  letI := ordinaryMul
  letI := ordinaryNatCast
  do
    let graph ← (Codec.readGraph codec ctx binding head lower upper packet).toOption
    let memo ← validateOperations? one add sub mul natCast ho ha hs hm hn sign original same
      binding head lower upper graph
    return (memo, graph.root)

/-- Equal operations preserve the full decoded memo and root index, including
malformed packets and validation rejection. No inventory completeness is assumed. -/
theorem readPacketMemoOperations_eq
    (one : One E) (add : Add E) (sub : Sub E) (mul : Mul E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hs : sub = ordinarySub)
    (hm : mul = ordinaryMul) (hn : natCast = ordinaryNatCast)
    (sign original : E → Int) (same : sign = original)
    (codec : ValueCodec E) (ctx : ValueCodec Ctx) (binding : Ctx)
    (head : DensePoly E) (lower upper : Endpoint E) (packet : Codec.Json) :
    letI := ordinaryOne
    letI := ordinaryAdd
    letI := ordinarySub
    letI := ordinaryMul
    letI := ordinaryNatCast
    readPacketMemoOperations? one add sub mul natCast ho ha hs hm hn sign original same
      codec ctx binding head lower upper packet =
    readPacketMemo? codec ctx original binding head lower upper packet := by
  cases ho; cases ha; cases hs; cases hm; cases hn; cases same
  unfold readPacketMemoOperations? readPacketMemo?
  simp only [validateOperations_eq]

end Hex.RealClosure.Replay
