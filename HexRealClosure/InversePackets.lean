/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.InverseReplay
public import HexRealClosure.RecordPackets
import all HexRealClosure.InversePacking

public section
namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- Export only the literal input-sign and inverse-equation graph. The
independent reader retains the original checked packing and actual operand. -/
def Context.buildInversePacket (context : Context E Ctx coeffSign parent)
    (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (argument result : Element context) : Except BuildError Codec.Json := do
  let _ : Hashable E := ⟨fun a => hash (codec.encode a)⟩
  let _ : Hashable Ctx := ⟨fun _ => 0⟩
  let signs ← context.buildSigns
    [argument.polynomial, argument.polynomial * result.polynomial - 1]
  return Codec.graph codec ctx (Dag.encode signs.evidence)

/-- Decode and validate a supplied graph at the original predecessor and
root domain. The inverse reader checks the exact operand, native candidate
and cached input tag; zero and a same-value alternative candidate reject. -/
@[expose] def InverseFact.readPacket? (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (argument : Element context) (entry : Packing context) (packet : Codec.Json) :
    Option (InverseFact context) := do
  let graph ← (Codec.readGraph codec ctx parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper packet).toOption
  let memo ← graph.validate? coeffSign parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  let inverse ← Packing.Inverse.readMemo? argument entry memo graph.root
  return ⟨entry, inverse⟩

/-- Memo reconstruction retains the literal inverse operand. -/
theorem Packing.Inverse.readMemo_argument (argument : Element context) (entry : Packing context)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat)
    {inverse : Packing.Inverse entry}
    (accepted : Packing.Inverse.readMemo? argument entry memo index = some inverse) :
    inverse.argument = argument := by
  unfold Packing.Inverse.readMemo? at accepted
  obtain ⟨signs, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  exact Packing.Inverse.make?_argument argument entry signs accepted

/-- The checked packet preserves the supplied packing record and operand,
so its inverse law refers to the original operation in its original owner. -/
theorem InverseFact.readPacket_bindings (codec : ValueCodec E) (ctx : ValueCodec Ctx)
    (argument : Element context) (entry : Packing context) (packet : Codec.Json)
    {fact : InverseFact context}
    (accepted : InverseFact.readPacket? codec ctx argument entry packet = some fact) :
    fact.entry = entry ∧ fact.inverse.argument = argument := by
  unfold InverseFact.readPacket? at accepted
  obtain ⟨graph, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨memo, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨inverse, checked, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  cases Option.some.inj accepted
  exact ⟨rfl, Packing.Inverse.readMemo_argument argument entry memo graph.root checked⟩

end Hex.RealClosure.Algebraic
