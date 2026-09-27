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

end Hex.RealClosure

/- The inherited `sorryAx` in these guards is the named #10389
`Tarski.check_rootSum` dependency. -/
/-- info: 'Hex.RealClosure.polyValue_divMod' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.polyValue_divMod
/-- info: 'Hex.RealClosure.polyValue_bezout' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.polyValue_bezout
/-- info: 'Hex.RealClosure.polyValue_derivative' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.polyValue_derivative
