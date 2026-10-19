/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RecordPackets
public import HexRealClosure.AlgebraicCodec
public import HexSignDet.Codec.Coefficients

public section
namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx UpperCtx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] [DecidableEq UpperCtx]
variable {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable {upperSign : Element context → Int} {upperParent : UpperCtx}

/-- Discover finite literal child keys from supplied graph data through the
native coefficient codec. The result contains only polynomial JSON and cached
tags, and is untrusted producer data. Independent scalar readers must prove
each child key before a strict graph reader restores its coefficients. -/
def Context.childPackets (owner : Context (Element context) UpperCtx upperSign upperParent)
    (codec : ValueCodec E) (ctx : ValueCodec UpperCtx) (packet : Codec.Json) :
    Except String Codec.Json := do
  let graph ← Codec.readGraph (Element.codec codec) ctx upperParent owner.root.raw.head
    owner.root.raw.lower owner.root.raw.upper packet
  let children := (Codec.Coefficients.graph graph).filterMap fun value =>
    if value.sign = 0 then none
    else some (Codec.Json.arr #[Codec.poly codec value.polynomial, Codec.Json.of value.sign])
  return Codec.Json.arr children.eraseDups.toArray

end Hex.RealClosure.Algebraic
