/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Algebraic
public import HexSignDet.Reencode
public import HexPoly.Interpret

public section

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}

/-- Change the defining polynomial using a checked re-encoding of the same
selected root. The predecessor and its cleanliness predicate remain fixed. -/
@[expose] def Context.reencode (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper) :
    Context E Ctx coeffSign parent :=
  Context.adjoin r.target context.cleanCoeff

/-- The new context uses the checked target descriptor literally. -/
theorem Context.root_reencode (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper) :
    (context.reencode r).root = r.target :=
  Context.root_adjoin r.target context.cleanCoeff

/-- Re-encoding an adjoined root uses the same predecessor cleanliness rule as
adjoining the checked target descriptor directly. -/
theorem Context.reencode_adjoin (d : SignDet.Descriptor E Ctx coeffSign parent)
    (clean : E → Bool) {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding (Context.adjoin d clean).root head lower upper) :
    (Context.adjoin d clean).reencode r = Context.adjoin r.target clean := by
  simp only [Context.reencode, Context.clean_adjoin]

namespace Element

variable {context : Context E Ctx coeffSign parent}

/-- Repack one value under the checked new definition. The old value retains
its original context type. -/
@[expose] def reencode {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper)
    (a : Element context) : Element (context.reencode r) :=
  match a.stored with
  | none => 0
  | some _ => ofPoly a.polynomial

/-- The canonical zero remains canonical without a coefficient-sign query. -/
theorem reencode_zero {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper) :
    reencode r (0 : Element context) = 0 := by
  simp only [reencode, stored_zero]

/-- Convert every coefficient of a dependent polynomial to the new context. -/
@[expose] def reencodePoly {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper)
    (p : DensePoly (Element context)) : DensePoly (Element (context.reencode r)) :=
  DensePoly.ofCoeffs (p.toArray.map (reencode r))

/-- A re-encoding that reflects zero converts every stored
coefficient, including implicit trailing zeros. -/
theorem reencodePoly_coeff {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper)
    (hz : ∀ a : Element context, reencode r a = 0 ↔ a = 0)
    (p : DensePoly (Element context)) (i : Nat) :
    (reencodePoly r p).coeff i = reencode r (p.coeff i) := by
  have h := DensePoly.Interpret.map_ofCoeffs (reencode r) hz p.toArray
  rw [DensePoly.ofCoeffs_toArray] at h
  rw [reencodePoly, ← h]
  exact DensePoly.Interpret.map_coeff (reencode r) hz p i

end Element
end Hex.RealClosure.Algebraic
