import HexModArith.Prime
import HexGFqRing.Basic

/-!
Core finite-field wrapper definitions for executable `F_p[x] / (f)`.

This module packages the quotient-ring representation from `HexGFqRing`
into the spec-named `FiniteField` type, keeping the same reduced
representatives and exposing explicit conversions back to the quotient and
polynomial views.
-/
namespace Hex

namespace GFqField

variable {p : Nat} [ZMod64.Bounds p] {hp : Hex.Nat.Prime p}

/-- Executable finite-field elements are a thin wrapper around quotient-ring
residues modulo an irreducible polynomial. -/
structure FiniteField
    (f : FpPoly p) (hf : 0 < FpPoly.degree f)
    (_hp : Hex.Nat.Prime p) (_hirr : FpPoly.Irreducible f) where
  /-- The underlying reduced quotient-ring residue backing this field element. -/
  toQuotient : GFqRing.PolyQuotient f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    DecidableEq (FiniteField f hf hp hirr) := by
  intro x y
  match decEq x.toQuotient y.toQuotient with
  | isTrue h =>
      exact isTrue (by
        cases x
        cases y
        cases h
        rfl)
  | isFalse h =>
      exact isFalse (by
        intro hxy
        apply h
        exact congrArg FiniteField.toQuotient hxy)

/-- Wrap a quotient-ring element as a finite-field element. -/
def ofQuotient {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : GFqRing.PolyQuotient f hf) : FiniteField f hf hp hirr :=
  ⟨x⟩

/-- Reduce a polynomial into the finite field by reusing the quotient-ring
constructor. -/
def ofPoly (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) (g : FpPoly p) : FiniteField f hf hp hirr :=
  ofQuotient (GFqRing.ofPoly f hf g)

/-- Project a finite-field element to its canonical polynomial representative. -/
def repr {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) : FpPoly p :=
  GFqRing.repr x.toQuotient

/-- Projecting a wrapped quotient element returns the original quotient. -/
@[simp, grind =] theorem toQuotient_ofQuotient
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : GFqRing.PolyQuotient f hf) :
    (ofQuotient x : FiniteField f hf hp hirr).toQuotient = x :=
  rfl

/-- Reducing a polynomial into the field projects to the quotient-ring reduction. -/
@[simp, grind =] theorem toQuotient_ofPoly
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) (g : FpPoly p) :
    (ofPoly f hf hp hirr g).toQuotient = GFqRing.ofPoly f hf g :=
  rfl

/-- A wrapped quotient exposes the same canonical polynomial representative. -/
@[simp, grind =] theorem repr_ofQuotient
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : GFqRing.PolyQuotient f hf) :
    repr (ofQuotient x : FiniteField f hf hp hirr) = GFqRing.repr x :=
  rfl

/-- Rewrapping a field element through its quotient projection is the identity. -/
@[simp, grind =] theorem ofQuotient_toQuotient
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    ofQuotient x.toQuotient = x := by
  cases x
  rfl

/-- The representative of a polynomial coerced into the field is its reduced form. -/
@[simp, grind =] theorem repr_ofPoly
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) (g : FpPoly p) :
    repr (ofPoly f hf hp hirr g) = GFqRing.reduceMod f g :=
  rfl

/-- Canonical field representatives are reduced below the modulus degree. -/
@[simp] theorem degree_repr_lt_degree
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    FpPoly.degree (repr x) < FpPoly.degree f := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  exact GFqRing.degree_repr_lt_degree x.toQuotient

/-- Equality of field elements is equality of their quotient representatives. -/
@[grind =] theorem toQuotient_inj
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x y : FiniteField f hf hp hirr} :
    x.toQuotient = y.toQuotient ↔ x = y := by
  constructor
  · intro h
    cases x
    cases y
    cases h
    rfl
  · intro h
    exact congrArg FiniteField.toQuotient h

/-- Extensionality through quotient representatives. -/
@[ext] theorem ext
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x y : FiniteField f hf hp hirr} (h : x.toQuotient = y.toQuotient) :
    x = y := by
  cases x
  cases y
  cases h
  rfl

end GFqField
end Hex
