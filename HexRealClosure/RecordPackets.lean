/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Packing
public import HexRealClosure.ValueSigns
public import HexSignDet.Codec
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns

public section

namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- Native scalar production exports only a claimed sign and literal graph.
The caller must independently decode and check the graph to obtain a fact. -/
def Context.buildSignPacket (context : Context E Ctx coeffSign parent)
    (value : ValueCodec E) (ctx : ValueCodec Ctx) (p : DensePoly E) :
    Except BuildError (Int × Codec.Json) := do
  let _ : Hashable E := ⟨fun a => hash (value.encode a)⟩
  let _ : Hashable Ctx := ⟨fun _ => 0⟩
  let signs ← context.buildSigns [context.queryPoly p]
  return (signs.value, Codec.graph value ctx (Dag.encode signs.evidence))

/-- Native joint production exports literal data for the original operation,
including its zero difference from the retained remainder. -/
def Context.buildPackingPacket (context : Context E Ctx coeffSign parent)
    (value : ValueCodec E) (ctx : ValueCodec Ctx) (reduce : DensePoly E → DensePoly E)
    (p : DensePoly E) : Except BuildError Codec.Json := do
  let _ : Hashable E := ⟨fun a => hash (value.encode a)⟩
  let _ : Hashable Ctx := ⟨fun _ => 0⟩
  let signs ← context.buildSigns [reduce p, p - reduce p]
  return Codec.graph value ctx (Dag.encode signs.evidence)

/-- Produce literal evidence for the actual stored operand without repacking
its polynomial. The returned graph contains no trusted proof object. -/
def ValueSign.buildPacket (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (value : Element context) : Except BuildError Codec.Json := do
  let _ : Hashable E := ⟨fun a => hash (codec.encode a)⟩
  let _ : Hashable Ctx := ⟨fun _ => 0⟩
  let signs ← context.buildSigns [value.polynomial]
  return Codec.graph codec ctx (Dag.encode signs.evidence)

/-- Decode and validate a supplied joint graph at the actual owner, then bind
its selected signs to the original packing request and its retained remainder.
Missing scalar facts cause rejection, without starting a sign producer. -/
@[expose] def Packing.readPacket? (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = context.reduce)
    (facts : List (SignFact context)) (p : DensePoly E) (packet : Codec.Json) :
    Option (Packing context) := do
  let graph ← (Codec.readGraph value ctx parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper packet).toOption
  let memo ← graph.validate? coeffSign parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  Packing.readMemo? reduce hr facts p memo graph.root

/-- Memo selection preserves the original operation even when its result is
canonical zero or its representative also belongs to another request. -/
theorem Packing.readMemo_bindings (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) (p : DensePoly E)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat)
    {entry : Packing context}
    (accepted : Packing.readMemo? reduce hr facts p memo index = some entry) :
    entry.original = p ∧ entry.representative = reduce p ∧
      entry.value = Element.pack reduce hr facts p := by
  unfold Packing.readMemo? at accepted
  cases found : SignFact.find facts (reduce p) with
  | none => simp [found] at accepted
  | some fact =>
    simp only [found] at accepted
    obtain ⟨signs, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    exact Packing.make?_bindings reduce hr facts p signs accepted

theorem Packing.readPacket_bindings (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = context.reduce)
    (facts : List (SignFact context)) (p : DensePoly E) (packet : Codec.Json)
    {entry : Packing context}
    (accepted : Packing.readPacket? value ctx reduce hr facts p packet = some entry) :
    entry.original = p ∧ entry.representative = reduce p ∧
      entry.value = Element.pack reduce hr facts p := by
  unfold Packing.readPacket? at accepted
  obtain ⟨graph, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨memo, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  exact Packing.readMemo_bindings reduce hr facts p memo graph.root accepted

/-- Reconstruct a cached sign from supplied graph data for the exact stored
operand. Decoding uses the actual predecessor and root domain; selection checks
the stored polynomial and cached tag without repacking the operand. -/
@[expose] def ValueSign.readPacket? (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (value : Element context) (packet : Codec.Json) : Option (ValueSign context) := do
  let graph ← (Codec.readGraph codec ctx parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper packet).toOption
  let memo ← graph.validate? coeffSign parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  ValueSign.readMemo? value memo graph.root

theorem ValueSign.readMemo_value (value : Element context)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat)
    {record : ValueSign context}
    (accepted : ValueSign.readMemo? value memo index = some record) : record.value = value := by
  unfold ValueSign.readMemo? at accepted
  obtain ⟨signs, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  exact ValueSign.make?_value value signs accepted

theorem ValueSign.readPacket_value (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (value : Element context) (packet : Codec.Json) {record : ValueSign context}
    (accepted : ValueSign.readPacket? codec ctx value packet = some record) : record.value = value := by
  unfold ValueSign.readPacket? at accepted
  obtain ⟨graph, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨memo, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  exact ValueSign.readMemo_value value memo graph.root accepted

end Hex.RealClosure.Algebraic
