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

/-- Test zero using the selected canonical root already held by a handle. -/
@[expose] def isZeroWith {context : Nat} {d : Root context}
    (h : Root.Handle d) (p : DensePoly Rat) : Bool :=
  evalCanonical p h.canonical == 0

theorem isZeroWith_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (p : DensePoly Rat) : isZeroWith h p = isZero d p := by
  simp [isZeroWith, isZero, h.canonical_eq]

/-- Rational selected-root storage with a unique zero. Nonzero polynomials may
still represent the same value, so structural equality is not value equality. -/
abbrev Element {context : Nat} (d : Root context) :=
  Option {p : DensePoly Rat // isZero d p = false}

namespace Element

/-- A rational polynomial has integral coefficients exactly when all its
denominators are one. -/
@[expose] def clean (p : DensePoly Rat) : Bool :=
  p.toArray.all (fun c => c.den == 1)

/-- Retain the remainder for a literally monic, clean defining polynomial.
Other definitions keep the original representative. -/
@[expose] def packedPoly {context : Nat} (d : Root context)
    (p : DensePoly Rat) : DensePoly Rat :=
  if d.raw.head.leadingCoeff == 1 && clean d.raw.head then
    p % d.raw.head
  else
    p

/-- The retained remainder has degree below the defining polynomial. -/
theorem packedPoly_degree {context : Nat} (d : Root context)
    (p : DensePoly Rat)
    (h : (d.raw.head.leadingCoeff == 1 && clean d.raw.head) = true) :
    (packedPoly d p).natDegree < d.raw.head.natDegree := by
  simp only [packedPoly, h, ↓reduceIte]
  rw [DensePoly.mod_eq_divMod]
  exact DensePoly.divMod_remainder_degree_lt_of_pos_degree
    p d.raw.head d.head_degree_pos

/-- Retain the permitted remainder, then apply the selected-root zero check. -/
@[expose] def ofPoly {context : Nat} {d : Root context} (p : DensePoly Rat) :
    Element d :=
  let stored := packedPoly d p
  if h : isZero d stored = false then some ⟨stored, h⟩ else none

/-- Pack with a cached selected root, avoiding a new root-list search. -/
@[expose] def ofPolyWith {context : Nat} {d : Root context}
    (h : Root.Handle d) (p : DensePoly Rat) : Element d :=
  let stored := packedPoly d p
  if hz : isZeroWith h stored = false then
    some ⟨stored, by simpa only [isZeroWith_eq] using hz⟩
  else none

theorem ofPolyWith_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (p : DensePoly Rat) : ofPolyWith h p = ofPoly p := by
  unfold ofPolyWith ofPoly
  simp only [isZeroWith_eq]

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

/-- Transport every coefficient through a checked re-encoding. -/
@[expose] def transportPoly {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (p : DensePoly (Element d)) : DensePoly (Element r.target) :=
  DensePoly.ofCoeffs (p.toArray.map (transport r))

/-- Rebind every coefficient to the new context version. -/
@[expose] def rebindPoly {context version : Nat} {d : Root context}
    (r : Rebinding d version)
    (p : DensePoly (Element d)) : DensePoly (Element r.target) :=
  DensePoly.ofCoeffs (p.toArray.map (rebind r))

/-- Refine every coefficient after a checked factor split. -/
@[expose] def refinePoly {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (p : DensePoly (Element d)) : DensePoly (Element r.binding.target) :=
  DensePoly.ofCoeffs (p.toArray.map (refine r))

/-- Transport with one selected-root search shared by all target coefficients. -/
@[expose] def transportWith {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (h : Root.Handle r.target) (a : Element d) : Element r.target :=
  match a with
  | none => none
  | some v => ofPolyWith h v.1

theorem transportWith_eq {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (h : Root.Handle r.target) (a : Element d) :
    transportWith r h a = transport r a := by
  cases a <;> simp [transportWith, transport, ofPolyWith_eq]

/-- Rebind with one selected-root search shared by all target coefficients. -/
@[expose] def rebindWith {context version : Nat} {d : Root context}
    (r : Rebinding d version) (h : Root.Handle r.target)
    (a : Element d) : Element r.target :=
  match a with
  | none => none
  | some v => ofPolyWith h v.1

theorem rebindWith_eq {context version : Nat} {d : Root context}
    (r : Rebinding d version) (h : Root.Handle r.target)
    (a : Element d) : rebindWith r h a = rebind r a := by
  cases a <;> simp [rebindWith, rebind, ofPolyWith_eq]

/-- Refine with one selected-root search shared by all target coefficients. -/
@[expose] def refineWith {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (h : Root.Handle r.binding.target) (a : Element d) :
    Element r.binding.target :=
  match a with
  | none => none
  | some v => ofPolyWith h v.1

theorem refineWith_eq {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (h : Root.Handle r.binding.target) (a : Element d) :
    refineWith r h a = refine r a := by
  cases a <;> simp [refineWith, refine, ofPolyWith_eq]

/-- Transport every coefficient using a single target handle. -/
@[expose] def transportPolyWith {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (h : Root.Handle r.target)
    (p : DensePoly (Element d)) : DensePoly (Element r.target) :=
  DensePoly.ofCoeffs (p.toArray.map (transportWith r h))

theorem transportPolyWith_eq {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (h : Root.Handle r.target) (p : DensePoly (Element d)) :
    transportPolyWith r h p = transportPoly r p := by
  have hf : transportWith r h = transport r := by
    funext a
    exact transportWith_eq r h a
  simp [transportPolyWith, transportPoly, hf]

/-- Rebind every coefficient using a single target handle. -/
@[expose] def rebindPolyWith {context version : Nat} {d : Root context}
    (r : Rebinding d version) (h : Root.Handle r.target)
    (p : DensePoly (Element d)) : DensePoly (Element r.target) :=
  DensePoly.ofCoeffs (p.toArray.map (rebindWith r h))

theorem rebindPolyWith_eq {context version : Nat} {d : Root context}
    (r : Rebinding d version) (h : Root.Handle r.target)
    (p : DensePoly (Element d)) :
    rebindPolyWith r h p = rebindPoly r p := by
  have hf : rebindWith r h = rebind r := by
    funext a
    exact rebindWith_eq r h a
  simp [rebindPolyWith, rebindPoly, hf]

/-- Refine every coefficient using a single target handle. -/
@[expose] def refinePolyWith {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (h : Root.Handle r.binding.target)
    (p : DensePoly (Element d)) : DensePoly (Element r.binding.target) :=
  DensePoly.ofCoeffs (p.toArray.map (refineWith r h))

theorem refinePolyWith_eq {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (h : Root.Handle r.binding.target) (p : DensePoly (Element d)) :
    refinePolyWith r h p = refinePoly r p := by
  have hf : refineWith r h = refine r := by
    funext a
    exact refineWith_eq r h a
  simp [refinePolyWith, refinePoly, hf]

end Element

namespace Root.Handle

/-- Pack a rational polynomial using this handle's cached selected root. -/
@[expose] def pack {context : Nat} {d : Root context}
    (h : Root.Handle d) (p : DensePoly Rat) : Element d :=
  Element.ofPolyWith h p

theorem pack_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (p : DensePoly Rat) :
    h.pack p = Element.ofPoly p := Element.ofPolyWith_eq h p

/-- Evaluate a packed value without searching for the selected root again. -/
@[expose] def value {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) : Hex.RealAlgebraicNumber :=
  match a with
  | none => 0
  | some v => evalCanonical v.1 h.canonical

theorem value_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) : h.value a = a.value := by
  cases a <;> simp [value, Element.value, h.canonical_eq]

@[expose] def sign {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) : Int :=
  (h.value a).sign

theorem sign_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) : h.sign a = a.sign := by
  simp [sign, Element.sign, value_eq]

@[expose] def add {context : Nat} {d : Root context}
    (h : Root.Handle d) (a b : Element d) : Element d :=
  h.pack (a.polynomial + b.polynomial)

theorem add_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (a b : Element d) : h.add a b = a + b := by
  change h.add a b = Element.add a b
  simp [add, pack_eq, Element.add]

@[expose] def neg {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) : Element d :=
  match a with
  | none => none
  | some v => h.pack (-v.1)

theorem neg_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) : h.neg a = -a := by
  change h.neg a = Element.neg a
  cases a <;> simp [neg, pack_eq, Element.neg]

@[expose] def sub {context : Nat} {d : Root context}
    (h : Root.Handle d) (a b : Element d) : Element d :=
  h.pack (a.polynomial - b.polynomial)

theorem sub_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (a b : Element d) : h.sub a b = a - b := by
  change h.sub a b = Element.sub a b
  simp [sub, pack_eq, Element.sub]

@[expose] def mul {context : Nat} {d : Root context}
    (h : Root.Handle d) (a b : Element d) : Element d :=
  h.pack (a.polynomial * b.polynomial)

theorem mul_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (a b : Element d) : h.mul a b = a * b := by
  change h.mul a b = Element.mul a b
  simp [mul, pack_eq, Element.mul]

@[expose] def inv {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) : Element d :=
  match a with
  | none => none
  | some v => h.pack (Expression.inverseCandidate
      (⟨v.1⟩ : Expression d)).polynomial

theorem inv_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) : h.inv a = a⁻¹ := by
  change h.inv a = Element.inv a
  cases a <;> simp [inv, pack_eq, Element.inv]

@[expose] def inverse? {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) : Option (Element d) :=
  match a with
  | none => none
  | some _ => some (h.inv a)

theorem inverse?_eq {context : Nat} {d : Root context}
    (h : Root.Handle d) (a : Element d) :
    h.inverse? a = a.inverse? := by
  change h.inverse? a = Element.inverse? a
  cases a with
  | none => rfl
  | some v =>
    exact congrArg some (inv_eq h (some v))

/-- Packed coefficients sharing one cached selected root. Generic polynomial
algorithms use the ordinary operations below without repeating root search. -/
structure Value {context : Nat} {d : Root context} (h : Root.Handle d) where
  stored : Element d
deriving DecidableEq

namespace Value

@[expose] def ofPoly {context : Nat} {d : Root context}
    (h : Root.Handle d) (p : DensePoly Rat) : Value h :=
  ⟨h.pack p⟩

@[expose] def value {context : Nat} {d : Root context}
    {h : Root.Handle d} (a : Value h) : Hex.RealAlgebraicNumber :=
  h.value a.stored

@[expose] def sign {context : Nat} {d : Root context}
    {h : Root.Handle d} (a : Value h) : Int :=
  h.sign a.stored

instance {context : Nat} {d : Root context} {h : Root.Handle d} :
    Zero (Value h) := ⟨⟨0⟩⟩
instance {context : Nat} {d : Root context} {h : Root.Handle d} :
    One (Value h) := ⟨⟨h.pack 1⟩⟩
instance {context : Nat} {d : Root context} {h : Root.Handle d} :
    Add (Value h) := ⟨fun a b => ⟨h.add a.stored b.stored⟩⟩
instance {context : Nat} {d : Root context} {h : Root.Handle d} :
    Neg (Value h) := ⟨fun a => ⟨h.neg a.stored⟩⟩
instance {context : Nat} {d : Root context} {h : Root.Handle d} :
    Sub (Value h) := ⟨fun a b => ⟨h.sub a.stored b.stored⟩⟩
instance {context : Nat} {d : Root context} {h : Root.Handle d} :
    Mul (Value h) := ⟨fun a b => ⟨h.mul a.stored b.stored⟩⟩
instance {context : Nat} {d : Root context} {h : Root.Handle d} :
    Inv (Value h) := ⟨fun a => ⟨h.inv a.stored⟩⟩
instance {context : Nat} {d : Root context} {h : Root.Handle d} :
    Div (Value h) := ⟨fun a b => a * b⁻¹⟩
instance {context : Nat} {d : Root context} {h : Root.Handle d} :
    NatCast (Value h) := ⟨fun n => ⟨h.pack (DensePoly.C n)⟩⟩
instance (priority := 90) {context : Nat} {d : Root context}
    {h : Root.Handle d} (n : Nat) : OfNat (Value h) (n + 2) :=
  ⟨⟨h.pack (DensePoly.C (n + 2))⟩⟩

@[simp] theorem stored_zero {context : Nat} {d : Root context}
    {h : Root.Handle d} : (0 : Value h).stored = 0 := rfl

theorem stored_eq_zero {context : Nat} {d : Root context}
    {h : Root.Handle d} (a : Value h) : a.stored = 0 ↔ a = 0 := by
  constructor
  · intro hs
    cases a with
    | mk stored =>
      cases hs
      rfl
  · intro ha
    rw [ha]
    rfl

@[simp] theorem stored_ofPoly {context : Nat} {d : Root context}
    (h : Root.Handle d) (p : DensePoly Rat) :
    (ofPoly h p).stored = Element.ofPoly p := h.pack_eq p

@[simp] theorem stored_one {context : Nat} {d : Root context}
    {h : Root.Handle d} : (1 : Value h).stored = 1 := h.pack_eq 1

@[simp] theorem stored_add {context : Nat} {d : Root context}
    {h : Root.Handle d} (a b : Value h) :
    (a + b).stored = a.stored + b.stored := h.add_eq a.stored b.stored

@[simp] theorem stored_neg {context : Nat} {d : Root context}
    {h : Root.Handle d} (a : Value h) :
    (-a).stored = -a.stored := h.neg_eq a.stored

@[simp] theorem stored_sub {context : Nat} {d : Root context}
    {h : Root.Handle d} (a b : Value h) :
    (a - b).stored = a.stored - b.stored := h.sub_eq a.stored b.stored

@[simp] theorem stored_mul {context : Nat} {d : Root context}
    {h : Root.Handle d} (a b : Value h) :
    (a * b).stored = a.stored * b.stored := h.mul_eq a.stored b.stored

@[simp] theorem stored_inv {context : Nat} {d : Root context}
    {h : Root.Handle d} (a : Value h) :
    (a⁻¹).stored = a.stored⁻¹ := h.inv_eq a.stored

@[simp] theorem stored_div {context : Nat} {d : Root context}
    {h : Root.Handle d} (a b : Value h) :
    (a / b).stored = a.stored / b.stored := by
  change (a * b⁻¹).stored = a.stored * b.stored⁻¹
  rw [stored_mul, stored_inv]

theorem value_eq {context : Nat} {d : Root context}
    {h : Root.Handle d} (a : Value h) :
    a.value = a.stored.value := h.value_eq a.stored

theorem sign_eq {context : Nat} {d : Root context}
    {h : Root.Handle d} (a : Value h) :
    a.sign = a.stored.sign := h.sign_eq a.stored

end Value

end Root.Handle

end Hex.RealClosure
