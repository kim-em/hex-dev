/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFnMathlib.Eval
public import Mathlib.Algebra.Field.ZMod

public section

namespace HexRationalFnMathlib.Tests
open Hex
attribute [local instance 2000] Field.toGrindField
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example (f g : RationalFn ℚ) : toRatFunc (f / g) = toRatFunc f / toRatFunc g :=
  toRatFunc_div f g

example (f : RationalFn (ZMod 2)) : HexPolyMathlib.toPolynomial f.den = (toRatFunc f).denom :=
  den_toRatFunc f

example (f : RationalFn ℚ) (n : Nat) : toRatFunc (f ^ n) = toRatFunc f ^ n := toRatFunc_pow f n

-- Both instance paths retain the executable scalar multiplication definition.
example (f : RationalFn ℚ) (n : Nat) :
    (inferInstance : AddMonoid (RationalFn ℚ)).nsmul n f =
      @SMul.smul Nat (RationalFn ℚ) RationalFn.instSMulNat n f := rfl

example (f : RationalFn ℚ) (n : Int) :
    (inferInstance : SubNegMonoid (RationalFn ℚ)).zsmul n f =
      @SMul.smul Int (RationalFn ℚ) RationalFn.instSMulInt n f := rfl

example : RationalFn.eval? (0 : RationalFn ℚ) 0 = some 0 := by decide +kernel

/-- The canonical fraction one over X, constructed without a gcd search. -/
@[expose]
def pole : RationalFn ℚ := RationalFn.ofCoprime 1 (DensePoly.ofList [0, 1])
  (by change (DensePoly.ofList [0, 1] : DensePoly ℚ).leadingCoeff = 1; decide +kernel)
  (DensePoly.Coprime.one_right _).symm

example : RationalFn.eval? pole 0 = none := by decide +kernel

example : RatFunc.eval (RingHom.id ℚ) 0 (toRatFunc pole) = 0 :=
  eval_eq_zero_of_none _ _ (by decide +kernel)

/-- A coprime linear pair with constant Bézout witnesses. -/
@[expose]
def cert : RationalFn.Cert ℚ :=
  ⟨DensePoly.ofList [1, 1], DensePoly.ofList [0, 1], 1, -1⟩

/-- The literal certificate is checked by kernel reduction. -/
theorem replay : RationalFn.check (DensePoly.ofList [1, 2, 1])
    (DensePoly.ofList [0, 1, 1]) cert = true := by decide +kernel

/-- This theorem replays a nontrivial cancellation certificate in the kernel. -/
theorem certified_fraction :
    let f := RationalFn.ofCert (DensePoly.ofList [1, 2, 1]) (DensePoly.ofList [0, 1, 1]) cert replay
    toRatFunc f = embed (DensePoly.ofList [1, 2, 1]) / embed (DensePoly.ofList [0, 1, 1]) ∧
      HexPolyMathlib.toPolynomial cert.num = (toRatFunc f).num ∧
      HexPolyMathlib.toPolynomial cert.den = (toRatFunc f).denom := check_sound _ _ cert replay

example : RationalFn.eval? (RationalFn.normalize (DensePoly.ofList [-1, 0, 1])
    (DensePoly.ofList [-1, 1] : DensePoly ℚ) (by decide +kernel)) 1 = some 2 := by
  let c : RationalFn.Cert ℚ := ⟨DensePoly.ofList [1, 1], 1, 0, 1⟩
  have hc : RationalFn.check (DensePoly.ofList [-1, 0, 1]) (DensePoly.ofList [-1, 1]) c = true :=
    by decide +kernel
  rw [← RationalFn.check_sound _ _ c hc]
  change RationalFn.eval? (RationalFn.ofPoly (DensePoly.ofList [1, 1] : DensePoly ℚ)) 1 = some 2
  decide +kernel

example (f : RationalFn ℚ) (n : Int) : toRatFunc (f ^ n) = toRatFunc f ^ n := map_zpow₀ equiv f n

/-- info: 'HexRationalFnMathlib.Tests.certified_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_fraction
/-- info: 'HexRationalFnMathlib.normalize_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexRationalFnMathlib.normalize_spec
/-- info: 'HexRationalFnMathlib.algEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexRationalFnMathlib.algEquiv

end HexRationalFnMathlib.Tests
