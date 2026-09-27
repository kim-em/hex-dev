/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Canonical

public section

namespace Hex.RealClosure

/-- Decide zero by evaluating the polynomial at the selected canonical root. -/
@[expose] def isZero {context : Nat} (d : Root context) (p : DensePoly Rat) : Bool :=
  evalCanonical p d.toCanonical == 0

/-- Rational selected-root storage with a unique zero. Nonzero polynomials may
still represent the same value, so structural equality is not value equality. -/
abbrev Element {context : Nat} (d : Root context) :=
  Option {p : DensePoly Rat // isZero d p = false}

namespace Element

/-- Pack a polynomial after the executable selected-root zero check. -/
@[expose] def ofPoly {context : Nat} {d : Root context} (p : DensePoly Rat) :
    Element d :=
  if h : isZero d p = false then some ⟨p, h⟩ else none

/-- Recover the stored polynomial, using the zero polynomial for the unique
zero representation. -/
@[expose] def polynomial {context : Nat} {d : Root context} (a : Element d) :
    DensePoly Rat :=
  match a with
  | none => 0
  | some v => v.1

@[expose] def toExpression {context : Nat} {d : Root context} (a : Element d) :
    Expression d := ⟨a.polynomial⟩

@[expose] def value {context : Nat} {d : Root context} (a : Element d) :
    Hex.RealAlgebraicNumber :=
  match a with
  | none => 0
  | some v => evalCanonical v.1 d.toCanonical

@[expose] def sign {context : Nat} {d : Root context} (a : Element d) : Int :=
  a.value.sign

@[expose] def add {context : Nat} {d : Root context} (a b : Element d) :
    Element d := ofPoly (a.polynomial + b.polynomial)

@[expose] def neg {context : Nat} {d : Root context} (a : Element d) :
    Element d :=
  match a with
  | none => none
  | some v => ofPoly (-v.1)

@[expose] def sub {context : Nat} {d : Root context} (a b : Element d) :
    Element d := ofPoly (a.polynomial - b.polynomial)

/-- Compare represented values by packing their difference. -/
@[expose] def equal {context : Nat} {d : Root context} (a b : Element d) : Bool :=
  (sub a b).isNone

@[expose] def mul {context : Nat} {d : Root context} (a b : Element d) :
    Element d := ofPoly (a.polynomial * b.polynomial)

/-- Gcd splitting supplies the inverse candidate for a nonzero stored value.
The companion proves that this candidate is an inverse at the selected root. -/
@[expose] def inv {context : Nat} {d : Root context} (a : Element d) :
    Element d :=
  match a with
  | none => none
  | some v => ofPoly (Expression.inverseCandidate (⟨v.1⟩ : Expression d)).polynomial

@[expose] def inverse? {context : Nat} {d : Root context} (a : Element d) :
    Option (Element d) :=
  match a with
  | none => none
  | some _ => some (inv a)

/-- Repack a value under a checked change of the defining polynomial. -/
@[expose] def transport {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper) (a : Element d) :
    Element r.target :=
  match a with
  | none => none
  | some v => ofPoly v.1

/-- Repack a value under a checked context version change. -/
@[expose] def rebind {context version : Nat} {d : Root context}
    (r : Rebinding d version) (a : Element d) :
    Element r.target :=
  match a with
  | none => none
  | some v => ofPoly v.1

/-- Repack a value after a checked factor split and context version change. -/
@[expose] def refine {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version) (a : Element d) :
    Element r.binding.target :=
  match a with
  | none => none
  | some v => ofPoly v.1

instance {context : Nat} {d : Root context} : DecidableEq (Element d) :=
  inferInstance

instance {context : Nat} {d : Root context} : Zero (Element d) := ⟨none⟩
instance {context : Nat} {d : Root context} : One (Element d) := ⟨ofPoly 1⟩
instance {context : Nat} {d : Root context} : Add (Element d) := ⟨add⟩
instance {context : Nat} {d : Root context} : Neg (Element d) := ⟨neg⟩
instance {context : Nat} {d : Root context} : Sub (Element d) := ⟨sub⟩
instance {context : Nat} {d : Root context} : Mul (Element d) := ⟨mul⟩
instance {context : Nat} {d : Root context} : Inv (Element d) := ⟨inv⟩
instance {context : Nat} {d : Root context} : Div (Element d) :=
  ⟨fun a b => a * b⁻¹⟩
instance {context : Nat} {d : Root context} : NatCast (Element d) :=
  ⟨fun n => ofPoly (DensePoly.C n)⟩
instance (priority := 90) {context : Nat} {d : Root context} (n : Nat) :
    OfNat (Element d) (n + 2) :=
  ⟨ofPoly (DensePoly.C (n + 2))⟩

end Element

end Hex.RealClosure
