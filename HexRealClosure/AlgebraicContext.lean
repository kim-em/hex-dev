/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosure.Algebraic
public import HexRealClosure.BaseContext
public section

namespace Hex.RealClosure.BaseContext

/-- Adjoin a selected root over this exact staged base. Its storage predicate
is derived from the predecessor; callers supply no cleanliness function. -/
@[expose] def Context.adjoin {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign)
    (root : SignDet.Descriptor (Element context) Signature Element.sign context.signature) :
    Algebraic.Context (Element context) Signature Element.sign context.signature :=
  Algebraic.Context.adjoin root Element.isClean

end Hex.RealClosure.BaseContext

namespace Hex.RealClosure.Algebraic
variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}

/-- Adjoin a selected root over the complete preceding algebraic value type.
The new level derives recursive cleanliness from that predecessor. -/
@[expose] def Context.extend {NextCtx : Type w} [DecidableEq NextCtx] {key : NextCtx}
    (context : Context E Ctx coeffSign parent)
    (root : SignDet.Descriptor (Element context) NextCtx Element.sign key) :
    Context (Element context) NextCtx Element.sign key :=
  Context.adjoin root Element.isClean

end Hex.RealClosure.Algebraic
