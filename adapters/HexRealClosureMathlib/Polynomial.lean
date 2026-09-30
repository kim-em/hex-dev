/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Element
public import HexPolyMathlib.Interpret

public section

namespace Hex.RealClosure

/-- Coefficientwise interpretation into the lawful selected-root value field.
It preserves degree even though the raw coefficient map is not injective. -/
noncomputable def polyValue {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) : Polynomial (Value d) :=
  HexPolyMathlib.Interpret.interpret Element.toValue
    (fun a => Element.toValue_eq_zero_iff a) p

theorem polyValue_coeff {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) (i : Nat) :
    (polyValue p).coeff i = (p.coeff i).toValue := by
  simp [polyValue]

/-- Interpret every coefficient in the shared canonical real-algebraic field,
so polynomials from different checked contexts have a common target. -/
noncomputable def polyDenote {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) : Polynomial Hex.RealAlgebraicNumber :=
  HexPolyMathlib.Interpret.interpret Element.value
    (fun a => (Element.eq_zero_iff a).symm) p

theorem polyDenote_coeff {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) (i : Nat) :
    (polyDenote p).coeff i = (p.coeff i).value := by
  simp [polyDenote]

theorem polyDenote_eq_map {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) :
    polyDenote p = (polyValue p).map (valueField d).subtype := by
  ext i
  rw [polyDenote_coeff, Polynomial.coeff_map, polyValue_coeff]
  exact congrArg Hex.RealAlgebraicNumber.toAlgebraic
    (Element.toValue_val (p.coeff i)).symm

/-- Forget the cached handle coefficientwise. Its unique stored zero keeps
the dense polynomial's degree and leading coefficient unchanged. -/
def polyStored {context : Nat} {d : Root context} {h : Root.Handle d}
    (p : DensePoly (Root.Handle.Value h)) : DensePoly (Element d) :=
  DensePoly.Interpret.map (fun a => a.stored)
    (fun a => Root.Handle.Value.stored_eq_zero a) p

theorem polyStored_coeff {context : Nat} {d : Root context}
    {h : Root.Handle d} (p : DensePoly (Root.Handle.Value h)) (i : Nat) :
    (polyStored p).coeff i = (p.coeff i).stored := by
  simp [polyStored]

theorem polyStored_divMod {context : Nat} {d : Root context}
    {h : Root.Handle d} (p q : DensePoly (Root.Handle.Value h)) :
    let r := DensePoly.divMod p q
    (polyStored r.1, polyStored r.2) =
      DensePoly.divMod (polyStored p) (polyStored q) := by
  exact DensePoly.Interpret.map_divMod
    (fun a : Root.Handle.Value h => a.stored)
    (fun a => Root.Handle.Value.stored_eq_zero a)
    (fun a b => Root.Handle.Value.stored_sub a b)
    (fun a b => Root.Handle.Value.stored_mul a b)
    (fun a b => Root.Handle.Value.stored_div a b) p q

/-- Interpret cached coefficients in the same lawful selected-root field as
ordinary packed coefficients. -/
noncomputable def polyCachedValue {context : Nat} {d : Root context}
    {h : Root.Handle d} (p : DensePoly (Root.Handle.Value h)) :
    Polynomial (Value d) := polyValue (polyStored p)

theorem polyCachedValue_coeff {context : Nat} {d : Root context}
    {h : Root.Handle d} (p : DensePoly (Root.Handle.Value h)) (i : Nat) :
    (polyCachedValue p).coeff i = (p.coeff i).stored.toValue := by
  rw [polyCachedValue, polyValue_coeff, polyStored_coeff]

theorem polyValue_C {context : Nat} {d : Root context} (a : Element d) :
    polyValue (DensePoly.C a) = Polynomial.C a.toValue := by
  exact HexPolyMathlib.Interpret.interpret_C
    Element.toValue (fun x => Element.toValue_eq_zero_iff x) a

theorem polyValue_one {context : Nat} {d : Root context} :
    polyValue (1 : DensePoly (Element d)) = 1 := by
  exact HexPolyMathlib.Interpret.interpret_one
    Element.toValue (fun x => Element.toValue_eq_zero_iff x)
    (Element.toValue_one (d := d))

theorem polyValue_eq_zero {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) : polyValue p = 0 ↔ p = 0 := by
  exact HexPolyMathlib.Interpret.interpret_eq_zero
    Element.toValue (fun a => Element.toValue_eq_zero_iff a) p

theorem polyValue_degree {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) :
    (polyValue p).natDegree = p.natDegree := by
  exact HexPolyMathlib.Interpret.natDegree_interpret
    Element.toValue (fun a => Element.toValue_eq_zero_iff a) p

theorem polyValue_leading {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) :
    (polyValue p).leadingCoeff = p.leadingCoeff.toValue := by
  exact HexPolyMathlib.Interpret.leadingCoeff_interpret
    Element.toValue (fun a => Element.toValue_eq_zero_iff a) p

theorem polyValue_add {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    polyValue (p + q) = polyValue p + polyValue q := by
  exact HexPolyMathlib.Interpret.interpret_add
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_add a b) p q

theorem polyValue_sub {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    polyValue (p - q) = polyValue p - polyValue q := by
  exact HexPolyMathlib.Interpret.interpret_sub
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_sub a b) p q

theorem polyValue_neg {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) : polyValue (-p) = -polyValue p := by
  exact HexPolyMathlib.Interpret.interpret_neg
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_sub a b) p

theorem polyValue_sub_isZero {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    (p - q).isZero = true ↔ polyValue p = polyValue q := by
  exact HexPolyMathlib.Interpret.sub_isZero
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_sub a b) p q

theorem polyValue_mul {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    polyValue (p * q) = polyValue p * polyValue q := by
  exact HexPolyMathlib.Interpret.interpret_mul
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_add a b)
    (fun a b => Element.toValue_mul a b) p q

theorem polyValue_scale {context : Nat} {d : Root context}
    (c : Element d) (p : DensePoly (Element d)) :
    polyValue (DensePoly.scale c p) =
      Polynomial.C c.toValue * polyValue p := by
  exact HexPolyMathlib.Interpret.interpret_scale
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_mul a b) c p

theorem polyValue_monicize_leading {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) (hp : p ≠ 0) :
    (polyValue (DensePoly.monicize p)).leadingCoeff = 1 := by
  exact HexPolyMathlib.Interpret.monicize_leading
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_mul a b)
    (fun a => Element.toValue_inv a) p hp

theorem polyValue_eval {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) (x : Element d) :
    (polyValue p).eval x.toValue = (p.eval x).toValue := by
  exact HexPolyMathlib.Interpret.eval_interpret
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_add a b)
    (fun a b => Element.toValue_mul a b) p x

theorem polyValue_derivative {context : Nat} {d : Root context}
    (p : DensePoly (Element d)) :
    polyValue p.derivative = (polyValue p).derivative := by
  exact HexPolyMathlib.Interpret.interpret_derivative
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun n => Element.toValue_natCast (d := d) n)
    (fun a b => Element.toValue_mul a b) p

theorem polyValue_divMod {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    (polyValue (DensePoly.divMod p q).1,
      polyValue (DensePoly.divMod p q).2) =
      (polyValue p / polyValue q, polyValue p % polyValue q) := by
  exact HexPolyMathlib.Interpret.interpret_divMod
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_sub a b)
    (fun a b => Element.toValue_mul a b)
    (fun a b => Element.toValue_div a b) p q

theorem polyCachedValue_divMod {context : Nat} {d : Root context}
    {h : Root.Handle d} (p q : DensePoly (Root.Handle.Value h)) :
    (polyCachedValue (DensePoly.divMod p q).1,
      polyCachedValue (DensePoly.divMod p q).2) =
      (polyCachedValue p / polyCachedValue q,
        polyCachedValue p % polyCachedValue q) := by
  have hs := polyStored_divMod p q
  have hv := congrArg
    (fun r : DensePoly (Element d) × DensePoly (Element d) =>
      (polyValue r.1, polyValue r.2)) hs
  simpa only [polyCachedValue] using
    hv.trans (polyValue_divMod (polyStored p) (polyStored q))

theorem polyValue_div {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    polyValue (p / q) = polyValue p / polyValue q := by
  have h := congrArg Prod.fst (polyValue_divMod p q)
  exact h

theorem polyValue_mod {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    polyValue (p % q) = polyValue p % polyValue q := by
  have h := congrArg Prod.snd (polyValue_divMod p q)
  exact h

theorem polyValue_gcd {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    Associated (polyValue (DensePoly.gcd p q))
      (EuclideanDomain.gcd (polyValue p) (polyValue q)) := by
  exact HexPolyMathlib.Interpret.interpret_gcd
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_sub a b)
    (fun a b => Element.toValue_mul a b)
    (fun a b => Element.toValue_div a b) p q

theorem polyValue_xgcd {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    Associated (polyValue (DensePoly.xgcd p q).gcd)
      (EuclideanDomain.gcd (polyValue p) (polyValue q)) := by
  rw [DensePoly.xgcd_gcd_eq_gcd]
  exact polyValue_gcd p q

theorem polyValue_bezout {context : Nat} {d : Root context}
    (p q : DensePoly (Element d)) :
    polyValue (DensePoly.xgcd p q).left * polyValue p +
      polyValue (DensePoly.xgcd p q).right * polyValue q =
        polyValue (DensePoly.xgcd p q).gcd := by
  exact HexPolyMathlib.Interpret.interpret_bezout
    Element.toValue (fun a => Element.toValue_eq_zero_iff a)
    (fun a b => Element.toValue_sub a b)
    (fun a b => Element.toValue_mul a b)
    (fun a b => Element.toValue_div a b)
    (fun a b => Element.toValue_add a b)
    (Element.toValue_one (d := d)) p q

private theorem polyMap_eq {E F : Type*} [Zero E] [DecidableEq E]
    [Zero F] [DecidableEq F] (f : E → F)
    (hz : ∀ a, f a = 0 ↔ a = 0) (p : DensePoly E) :
    DensePoly.ofCoeffs (p.toArray.map f) =
      DensePoly.Interpret.map f hz p := by
  rw [← DensePoly.Interpret.map_ofCoeffs f hz p.toArray,
    DensePoly.ofCoeffs_toArray]

theorem Element.transportPoly_eq_map {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (p : DensePoly (Element d)) :
    transportPoly r p = DensePoly.Interpret.map (transport r)
      (transport_zero_iff r) p :=
  polyMap_eq (transport r) (transport_zero_iff r) p

theorem Element.rebindPoly_eq_map {context version : Nat} {d : Root context}
    (r : Rebinding d version) (p : DensePoly (Element d)) :
    rebindPoly r p = DensePoly.Interpret.map (rebind r)
      (rebind_zero_iff r) p :=
  polyMap_eq (rebind r) (rebind_zero_iff r) p

theorem Element.refinePoly_eq_map {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (p : DensePoly (Element d)) :
    refinePoly r p = DensePoly.Interpret.map (refine r)
      (refine_zero_iff r) p :=
  polyMap_eq (refine r) (refine_zero_iff r) p

theorem Element.transportPoly_eq_zero {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (p : DensePoly (Element d)) :
    transportPoly r p = 0 ↔ p = 0 := by
  rw [transportPoly_eq_map]
  exact DensePoly.Interpret.map_eq_zero (transport r) (transport_zero_iff r) p

theorem Element.rebindPoly_eq_zero {context version : Nat} {d : Root context}
    (r : Rebinding d version) (p : DensePoly (Element d)) :
    rebindPoly r p = 0 ↔ p = 0 := by
  rw [rebindPoly_eq_map]
  exact DensePoly.Interpret.map_eq_zero (rebind r) (rebind_zero_iff r) p

theorem Element.refinePoly_eq_zero {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (p : DensePoly (Element d)) :
    refinePoly r p = 0 ↔ p = 0 := by
  rw [refinePoly_eq_map]
  exact DensePoly.Interpret.map_eq_zero (refine r) (refine_zero_iff r) p

theorem Element.transportPoly_degree {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (p : DensePoly (Element d)) :
    (transportPoly r p).natDegree = p.natDegree := by
  rw [transportPoly_eq_map]
  exact DensePoly.Interpret.map_degree (transport r) (transport_zero_iff r) p

theorem Element.rebindPoly_degree {context version : Nat} {d : Root context}
    (r : Rebinding d version) (p : DensePoly (Element d)) :
    (rebindPoly r p).natDegree = p.natDegree := by
  rw [rebindPoly_eq_map]
  exact DensePoly.Interpret.map_degree (rebind r) (rebind_zero_iff r) p

theorem Element.refinePoly_degree {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (p : DensePoly (Element d)) :
    (refinePoly r p).natDegree = p.natDegree := by
  rw [refinePoly_eq_map]
  exact DensePoly.Interpret.map_degree (refine r) (refine_zero_iff r) p

theorem Element.transportPoly_coeff {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (p : DensePoly (Element d)) (i : Nat) :
    ((transportPoly r p).coeff i).value = (p.coeff i).value := by
  rw [transportPoly_eq_map, DensePoly.Interpret.map_coeff]
  exact value_transport r (p.coeff i)

theorem Element.rebindPoly_coeff {context version : Nat} {d : Root context}
    (r : Rebinding d version) (p : DensePoly (Element d)) (i : Nat) :
    ((rebindPoly r p).coeff i).value = (p.coeff i).value := by
  rw [rebindPoly_eq_map, DensePoly.Interpret.map_coeff]
  exact value_rebind r (p.coeff i)

theorem Element.refinePoly_coeff {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (p : DensePoly (Element d)) (i : Nat) :
    ((refinePoly r p).coeff i).value = (p.coeff i).value := by
  rw [refinePoly_eq_map, DensePoly.Interpret.map_coeff]
  exact value_refine r (p.coeff i)

theorem polyDenote_transport {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper)
    (p : DensePoly (Element d)) :
    polyDenote (Element.transportPoly r p) = polyDenote p := by
  ext i
  rw [polyDenote_coeff, polyDenote_coeff, Element.transportPoly_coeff]

theorem polyDenote_rebind {context version : Nat} {d : Root context}
    (r : Rebinding d version) (p : DensePoly (Element d)) :
    polyDenote (Element.rebindPoly r p) = polyDenote p := by
  ext i
  rw [polyDenote_coeff, polyDenote_coeff, Element.rebindPoly_coeff]

theorem polyDenote_refine {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version)
    (p : DensePoly (Element d)) :
    polyDenote (Element.refinePoly r p) = polyDenote p := by
  ext i
  rw [polyDenote_coeff, polyDenote_coeff, Element.refinePoly_coeff]

end Hex.RealClosure

/-- info: 'Hex.RealClosure.polyValue_divMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.polyValue_divMod
/-- info: 'Hex.RealClosure.polyValue_bezout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.polyValue_bezout
/-- info: 'Hex.RealClosure.polyValue_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.polyValue_derivative
-- Polynomial transport preserves the same axiom boundary.
/-- info: 'Hex.RealClosure.polyDenote_refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.polyDenote_refine
/-- info: 'Hex.RealClosure.polyCachedValue_divMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.polyCachedValue_divMod
