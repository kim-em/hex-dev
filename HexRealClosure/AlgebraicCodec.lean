/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Algebraic
public import HexSignDet.Codec.Laws
import all HexSignDet.Codec.Basic
import all Lean.Data.Json.Basic

public section

namespace Hex.RealClosure.Algebraic
open Lean SignDet

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- Exact stored coefficient encoding: `[]` is the unique zero, while a
nonzero is `[polynomial, cachedSign]`. Decoding checks every predecessor
coefficient, rejects trailing zeros, and recomputes the claimed sign. -/
def Element.codec (value : ValueCodec E) : ValueCodec (Element context) where
  encode a := match a.stored with
    | none => .arr #[]
    | some p => .arr #[Codec.poly value p.polynomial, toJson p.sign]
  decode j := do
    let fields ← j.getArr?
    match fields.toList with
    | [] => return 0
    | [p, s] =>
      let polynomial ← Codec.readPoly value p
      let claimed ← fromJson? (α := Int) s
      match Element.restore? polynomial claimed with
      | some a => return a
      | none => throw "stored sign rejected"
    | _ => throw "wrong stored value field count"

/-- This roundtrip is literal, so it also preserves certificate bindings to
noncanonical representatives. It requires no field laws on raw values. -/
theorem Element.codec_lawful (value : ValueCodec E) (h : value.Lawful) :
    (Element.codec (context := context) value).Lawful := by
  intro a
  cases hs : a.stored with
  | none =>
    have ha : a = 0 := Element.ext (hs.trans Element.stored_zero.symm)
    subst a
    simp [Element.codec, Element.stored_zero, Json.getArr?, bind, Except.bind,
      pure, Except.pure]
  | some p =>
    simp [Element.codec, hs, Json.getArr?, bind, Except.bind, pure, Except.pure,
      Codec.read_poly value h, Codec.read_int, Element.restore_stored a p hs]

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Element.codec_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Element.codec_lawful
