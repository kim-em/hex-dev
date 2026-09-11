/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDet.Basic
public import HexMvGcd.Divide
public import HexMvGcd.Instances

public section

/-!
The multivariate recipe.

Distributed multivariate polynomials over a coefficient ring with a lawful gcd
divide exactly, by `Hex.MvPoly.instExactDivLaws` from `HexMvGcd.Divide`, so they
select Bareiss through `Hex.exactDiv` and divide by nonconstant pivots exactly.

The coefficient and monomial-order context is the one the division provider
requires; the recipe adds nothing to it.
-/

namespace Hex.Det

universe u

/-- The multivariate recipe: Bareiss over the gcd-based exact quotient. -/
instance instDetOpsMvPoly {k : Nat} {R : Type u} {cmp : Mono k → Mono k → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] [Dvd R] [Hex.GcdOps R] [Hex.IsMonomialOrder cmp]
    [Hex.LawfulGcdOps R] : DetOps (MvPoly k R cmp) where
  policy := quotientPolicy

-- Pin the selected recipe: a missing coefficient instance would silently fall
-- back to the Berkowitz default rather than fail to resolve.
example : (DetOps.policy (R := MvPoly 2 Int Mono.grevlex)).arm = Arm.bareiss := rfl

example : (DetOps.policy (R := MvPoly 2 Rat Mono.grevlex)).arm = Arm.bareiss := rfl

end Hex.Det
