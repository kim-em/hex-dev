/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.InverseEquation
public import HexRealClosureMathlib.Packing
public import HexRealClosureMathlib.Algebraic
import all HexRealClosureMathlib.Packing
import all HexRealClosure.InversePacking

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent} {entry : Packing context}
variable [Field K] [DecidableEq K] [LinearOrder K]

/-- A checked inverse equation gives the actual field inverse at the selected
point. The only predecessor arithmetic premises are the reached polynomial
product and subtraction operations, together with zero and unit preservation.
No whole-field embedding, ambient model or closed-domain law is required. -/
theorem Inverse.Equation.eval_inv (record : Inverse.Equation entry) (read : E → K)
    (zero : read 0 = 0) (unit : read 1 = 1) (x : K)
    (product : Transport.Product read record.argument.polynomial entry.value.polynomial)
    (difference : Transport.Difference read
      (record.argument.polynomial * entry.value.polynomial) 1)
    (observed : signsAt (fun y : K => y) (fun _ => Iff.rfl)
      ([record.argument.polynomial,
        record.argument.polynomial * entry.value.polynomial - 1].map
          (Transport.polynomial read)) x = [record.argument.sign, 0]) :
    eval read x entry.value.polynomial = (eval read x record.argument.polynomial)⁻¹ := by
  have signs : (SignType.sign (eval read x record.argument.polynomial) : Int) =
      record.argument.sign ∧
      (SignType.sign (eval read x
        (record.argument.polynomial * entry.value.polynomial - 1)) : Int) = 0 := by
    simpa only [signsAt, List.map_cons, List.map_nil, List.cons.injEq, and_true, eval]
      using observed
  have nonzero : eval read x record.argument.polynomial ≠ 0 := by
    intro vanished
    apply record.nonzero
    rw [← signs.1, vanished]
    simp
  have vanished : eval read x
      (record.argument.polynomial * entry.value.polynomial - 1) = 0 := by
    apply sign_eq_zero_iff.mp
    cases sign : SignType.sign (eval read x
      (record.argument.polynomial * entry.value.polynomial - 1)) <;>
      simp [sign] at signs ⊢
  have multiplied : eval read x record.argument.polynomial *
      eval read x entry.value.polynomial = 1 := by
    unfold eval at vanished ⊢
    rw [Transport.Ring.polynomial_sub read zero _ _ difference.differences,
      Transport.Ring.polynomial_mul read zero _ _ product.products product.sums,
      Transport.polynomial_one read zero unit,
      interpret_sub (fun y : K => y) (fun _ => Iff.rfl) (fun _ _ => rfl),
      interpret_mul (fun y : K => y) (fun _ => Iff.rfl) (fun _ _ => rfl)
        (fun _ _ => rfl),
      interpret_one (fun y : K => y) (fun _ => Iff.rfl) rfl,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one] at vanished
    exact sub_eq_zero.mp vanished
  have reversed : eval read x entry.value.polynomial *
      eval read x record.argument.polynomial = 1 := (mul_comm _ _).trans multiplied
  calc
    eval read x entry.value.polynomial = eval read x entry.value.polynomial *
        (eval read x record.argument.polynomial * (eval read x record.argument.polynomial)⁻¹) := by
      rw [mul_inv_cancel₀ nonzero, mul_one]
    _ = (eval read x entry.value.polynomial * eval read x record.argument.polynomial) *
        (eval read x record.argument.polynomial)⁻¹ := by rw [mul_assoc]
    _ = (eval read x record.argument.polynomial)⁻¹ := by rw [reversed, one_mul]

/-- The supplied equation denotes the field inverse at the descriptor's
selected root under a lawful predecessor interpretation. No equality with a
native inverse candidate is needed. -/
theorem Inverse.Equation.denote_inv [IsStrictOrderedRing K] [IsRealClosed K]
    (record : Inverse.Equation entry)
    (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
    (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (hnat : ∀ n : Nat, f (n : E) = (n : K))
    (hsign : ∀ a, coeffSign a = (SignType.sign (f a) : Int)) :
    entry.value.denote f hz h1 ha hs hm hnat hsign =
      (record.argument.denote f hz h1 ha hs hm hnat hsign)⁻¹ := by
  have observed := (record.signs.values_at_root f hz h1 ha hs hm hnat hsign).symm.trans
    record.observed
  have signs :
      (SignType.sign (record.argument.denote f hz h1 ha hs hm hnat hsign) : Int) =
        record.argument.sign ∧
      (SignType.sign (context.evalPoly f hz h1 ha hs hm hnat hsign
        (record.argument.polynomial * entry.value.polynomial - 1)) : Int) = 0 := by
    simpa only [signsAt, List.map_cons, List.map_nil, List.cons.injEq, and_true,
      Element.denote, Context.evalPoly, Context.rootValue] using observed
  have nonzero : record.argument.denote f hz h1 ha hs hm hnat hsign ≠ 0 := by
    intro vanished
    apply record.nonzero
    rw [← signs.1, vanished]
    simp
  have vanished : context.evalPoly f hz h1 ha hs hm hnat hsign
      (record.argument.polynomial * entry.value.polynomial - 1) = 0 := by
    apply sign_eq_zero_iff.mp
    cases sign : SignType.sign (context.evalPoly f hz h1 ha hs hm hnat hsign
      (record.argument.polynomial * entry.value.polynomial - 1)) <;>
      simp [sign] at signs ⊢
  unfold Context.evalPoly at vanished
  rw [interpret_sub f hz hs, interpret_mul f hz ha hm, interpret_one f hz h1,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one] at vanished
  change record.argument.denote f hz h1 ha hs hm hnat hsign *
    entry.value.denote f hz h1 ha hs hm hnat hsign - 1 = 0 at vanished
  have reversed := (mul_comm _ _).trans (sub_eq_zero.mp vanished)
  calc
    entry.value.denote f hz h1 ha hs hm hnat hsign =
        entry.value.denote f hz h1 ha hs hm hnat hsign *
          (record.argument.denote f hz h1 ha hs hm hnat hsign *
            (record.argument.denote f hz h1 ha hs hm hnat hsign)⁻¹) := by
      rw [mul_inv_cancel₀ nonzero, mul_one]
    _ = (entry.value.denote f hz h1 ha hs hm hnat hsign *
        record.argument.denote f hz h1 ha hs hm hnat hsign) *
        (record.argument.denote f hz h1 ha hs hm hnat hsign)⁻¹ := by rw [mul_assoc]
    _ = (record.argument.denote f hz h1 ha hs hm hnat hsign)⁻¹ := by rw [reversed, one_mul]

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.Equation.eval_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.Equation.eval_inv

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.Equation.denote_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.Equation.denote_inv
