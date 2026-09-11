/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDetMathlib.Berkowitz
public import HexDetMathlib.Field
public import HexDetMathlib.Integer
public import HexDetMathlib.Small
public import HexDet
public import HexPolyFpMathlib

public section

/-!
Carrier laws.

Every recipe `HexDet` installs is proved lawful here, above both the dispatch
chain and the coefficient-structure chain.

Each carrier's Mathlib structure comes from `HexPolyMathlib.commRingOfGrind`,
which keeps the executable operations and whose lightweight reduct is the
instance the carrier computes with. That is what the per-carrier obligations of
[hex-det-mathlib](SPEC/hex-det-mathlib.md) ask for, discharged once
rather than per carrier: the arm theorems above are already stated over
`Lean.Grind.CommRing`, so no carrier needs a structure of its own here.
`HexPolyMathlib.GrindReduct` records the carriers that also have a native
Mathlib structure, which `det_eq_mathlib` needs.
-/

namespace HexDetMathlib

open Hex Hex.Det

universe u

/-! # Native Mathlib structures -/

instance instGrindReductInt : HexPolyMathlib.GrindReduct Int where

instance instGrindReductRat : HexPolyMathlib.GrindReduct Rat where

/-! # Shipped carrier recipes -/

/-- The integer recipe is lawful: its representation maps are the identity. -/
instance instLawfulDetOpsInt : LawfulDetOps Int where
  lawful := lawfulPolicy_integer id id (fun _ => rfl) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- The rational recipe is lawful. -/
instance instLawfulDetOpsRat : LawfulDetOps Rat where
  lawful := lawfulPolicy_fieldPolicy

/-- The prime-residue recipe is lawful. -/
instance instLawfulDetOpsZMod64 {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulDetOps (ZMod64 p) where
  lawful := lawfulPolicy_fieldPolicy

/-- The dense-polynomial recipe is lawful, including at `Hex.ZPoly` and the
executable finite-field polynomials. -/
instance instLawfulDetOpsDensePoly {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R] : LawfulDetOps (DensePoly R) where
  lawful := lawfulPolicy_quotientPolicy

-- The monomial-order context is the one the division provider requires, and the
-- comparator instances the `Hex.MvPoly` type itself needs; neither can be dropped.
set_option linter.overlappingInstances false in
/-- The dense-polynomial recipe at `Hex.FpPoly p` is lawful. -/
instance instLawfulDetOpsFpPoly {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulDetOps (FpPoly p) where
  lawful :=
    lawfulPolicy_bareiss (R := FpPoly p) inferInstance Hex.exactDiv fun a _ hb =>
      @Hex.exactDiv_mul_right (FpPoly p) _ _ _
        (Hex.instExactDivLawsDensePoly (R := ZMod64 p)) a _ hb

-- The monomial-order context is the one the division provider requires, and the
-- comparator instances the `Hex.MvPoly` type itself needs; neither can be dropped.
set_option linter.overlappingInstances false in
/-- The multivariate recipe is lawful. -/
instance instLawfulDetOpsMvPoly {k : Nat} {R : Type u} {cmp : Mono k → Mono k → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] [Dvd R] [Hex.GcdOps R] [Hex.IsMonomialOrder cmp]
    [Hex.LawfulGcdOps R] : LawfulDetOps (MvPoly k R cmp) where
  lawful := lawfulPolicy_quotientPolicy

/-- The generic Berkowitz default is lawful on every commutative ring with
decidable equality, with no quotient, nontriviality or zero-divisor hypothesis. -/
instance instLawfulDetOpsBerkowitz {R : Type u} [inst : Lean.Grind.CommRing R]
    [deq : DecidableEq R] :
    @LawfulDetOps R inst (Hex.Det.instDetOpsBerkowitz) where
  lawful := lawfulPolicy_berkowitz deq

end HexDetMathlib
