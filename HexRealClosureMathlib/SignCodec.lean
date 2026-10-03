/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SignFacts
public import HexRealClosure.AlgebraicCodec
import all HexRealClosure.AlgebraicCodec

public section

namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- Decode exact stored coefficients from previously proved signs. Zero needs
no fact. Nonzero literals need their exact polynomial and claimed sign in the
fixed context; missing facts reject without invoking a sign producer. This
partial codec need not roundtrip values absent from the finite facts. -/
@[expose] def Element.signCodec (value : ValueCodec E) (facts : List (SignFact context)) :
    ValueCodec (Element context) where
  encode := (Element.codec value).encode
  decode j := do
    let fields ← j.getArr?
    match fields.toList with
    | [] => return 0
    | [p, s] =>
      let polynomial ← Codec.readPoly value p
      let claimed ← Codec.Json.decode (α := Int) s
      match SignFact.read facts polynomial claimed with
      | some a => return a
      | none => throw "stored sign fact missing or mismatched"
    | _ => throw "wrong stored value field count"

/-- The encoder preserves the existing wire format exactly. -/
theorem Element.signCodec_encode (value : ValueCodec E) (facts : List (SignFact context))
    (a : Element context) :
    (Element.signCodec value facts).encode a = (Element.codec value).encode a := rfl

/-- Every accepted literal is the same value accepted by the independent
native decoder, without a completeness claim for the finite fact list. -/
theorem Element.signCodec_sound (value : ValueCodec E) (facts : List (SignFact context))
    (j : Codec.Json) (a : Element context)
    (h : (Element.signCodec value facts).decode j = .ok a) :
    (Element.codec value).decode j = .ok a := by
  unfold Element.signCodec at h
  unfold Element.codec
  dsimp only at h ⊢
  cases hf : j.getArr? with
  | error e => simp [hf, bind, Except.bind] at h
  | ok fields =>
    simp only [hf, bind, Except.bind] at h ⊢
    split at h
    · rename_i hs
      simpa only [hs] using h
    · rename_i p s hs
      simp only [hs]
      cases hp : Codec.readPoly value p with
      | error e => simp [hp] at h
      | ok polynomial =>
        simp only [hp] at h ⊢
        cases hc : Codec.Json.decode (α := Int) s with
        | error e => simp [hc] at h
        | ok claimed =>
          simp only [hc] at h ⊢
          cases hr : SignFact.read facts polynomial claimed with
          | none => simp [hr] at h
          | some b =>
            simp only [hr, pure, Except.pure, Except.ok.injEq] at h
            subst b
            rw [SignFact.read_sound facts polynomial claimed a hr]
            rfl
    · simp at h

end Hex.RealClosure.Algebraic
