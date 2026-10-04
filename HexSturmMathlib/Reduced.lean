/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm.Reduced
public import HexSturmMathlib.Soundness
public import HexRealRootsMathlib.TarskiMod

public section

namespace HexSturmMathlib

open Hex HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {R : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [Div E]
variable [Field R] [DecidableEq R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable (f : E → R) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : R))
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (hd : ∀ a b, f (a / b) = f a / f b)

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Remainder-only reduction preserves the whole result, including precisely
the original success domain and signed query value. Storage need not carry
field or order instances; its division has an explicit lawful interpretation. -/
theorem queryReduced_eq (p q : DensePoly E) (a b : Endpoint E) :
    Sturm.queryReduced sign p q a b = Sturm.query sign p q a b := by
  rw [Sturm.queryReduced_eq_query]
  apply Option.ext
  intro value
  rw [query_iff f hz h1 ha hs hm hnat sign hsign hn hi,
    query_iff f hz h1 ha hs hm hnat sign hsign hn hi,
    interpret_mod f hz hs hm hd, Tarski.rootSum_mod]

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Prepared reduction returns exactly the original prepared query value. -/
theorem queryReducedPrepared_eq (domain : Sturm.PreparedDomain E)
    (binding : domain.sign = sign) (q : DensePoly E) :
    Sturm.queryReducedPrepared domain q = Sturm.queryPrepared domain q := by
  rw [Sturm.queryReducedPrepared,
    queryPrepared_sound f hz h1 ha hs hm hnat sign hsign hn hi domain binding,
    queryPrepared_sound f hz h1 ha hs hm hnat sign hsign hn hi domain binding,
    interpret_mod f hz hs hm hd, Tarski.rootSum_mod]

/-- info: 'HexSturmMathlib.queryReduced_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queryReduced_eq

/-- info: 'HexSturmMathlib.queryReducedPrepared_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queryReducedPrepared_eq

end HexSturmMathlib
