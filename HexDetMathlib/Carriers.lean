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
/-- The dense-polynomial recipe at `Hex.FpPoly p` is lawful. The recipe there is
`instDetOpsDensePoly` restated at that type's own coefficient instances, so this
is the dense-polynomial law restated with it, not a second proof that could
drift. -/
instance instLawfulDetOpsFpPoly {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulDetOps (FpPoly p) :=
  instLawfulDetOpsDensePoly (R := ZMod64 p)

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

/-! # Verification

Build-only checks that every carrier resolves both its recipe and that recipe's
law, that the explicit constructors are usable, and that the headline theorems
apply at the shapes the SPEC names. -/

namespace Verification

section Carriers

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

example : LawfulDetOps Int := inferInstance
example : LawfulDetOps Rat := inferInstance
example : LawfulDetOps (ZMod64 p) := inferInstance
example : LawfulDetOps (DensePoly Rat) := inferInstance
example : LawfulDetOps (DensePoly Int) := inferInstance
example : LawfulDetOps (FpPoly p) := inferInstance
example : LawfulDetOps (MvPoly 2 Int Mono.grevlex) := inferInstance
example : LawfulDetOps (MvPoly 2 Rat Mono.grevlex) := inferInstance

/-- The explicit exact-quotient constructor, installed locally rather than as an
instance, with its own quotient law. -/
example : LawfulPolicy (quotientPolicy (R := DensePoly Int)) :=
  lawfulPolicy_quotientPolicy

/-- A custom quotient supplied by the caller, with its law. -/
example : LawfulPolicy (Policy.bareiss (inferInstance : DecidableEq Int) Hex.exactDiv) :=
  lawfulPolicy_bareiss _ _ fun a _ hb => Hex.exactDiv_mul_right a hb

end Carriers

/-- A ring with zero divisors: `2 * 3 = 0` modulo six. It has no exact quotient,
so it takes the Berkowitz default, and the default is lawful there. -/
local instance : ZMod64.Bounds 6 := ⟨by decide, by decide⟩

example : LawfulDetOps (ZMod64 6) := inferInstance

/-- The trivial ring, where `1 = 0`. -/
local instance : ZMod64.Bounds 1 := ⟨by decide, by decide⟩

example : (1 : ZMod64 1) = 0 := by decide

example : LawfulDetOps (ZMod64 1) := inferInstance

/-! The headline theorems at the shapes the SPEC names. `Hex.Matrix.rowSwap`
supplies the row-swapped case and a repeated row the singular one. -/

section Shapes

example (B : Hex.Matrix Int 0 0) : Hex.Det.det B = Hex.Matrix.det B := det_eq B
example (B : Hex.Matrix Int 1 1) : Hex.Det.det B = Hex.Matrix.det B := det_eq B
example (B : Hex.Matrix Int 2 2) : Hex.Det.det B = Hex.Matrix.det B := det_eq B

example (B : Hex.Matrix Int 3 3) :
    Hex.Det.det (Hex.Matrix.rowSwap B 0 1) = Hex.Matrix.det (Hex.Matrix.rowSwap B 0 1) :=
  det_eq _

example (row : Fin 3 → Int) :
    Hex.Det.det (Hex.Matrix.ofFn fun (_ : Fin 3) j => row j) =
      Hex.Matrix.det (Hex.Matrix.ofFn fun (_ : Fin 3) j => row j) :=
  det_eq _

example (B : Hex.Matrix Int 3 3) :
    Hex.Det.det B = Matrix.det (HexMatrixMathlib.matrixEquiv B) :=
  det_eq_mathlib B

example (B : Hex.Matrix Rat 3 3) :
    Hex.Det.det B = Matrix.det (HexMatrixMathlib.matrixEquiv B) :=
  det_eq_mathlib B

/-- A carrier with no global Mathlib structure installs one at the use site.
`HexPolyMathlib.commRingOfGrind` is a definition, not an instance, so the caller
supplies it; `HexPolyMathlib.instGrindReductOfGrind` then discharges the
compatibility hypothesis. -/
example (B : Hex.Matrix (DensePoly Int) 3 3) :
    letI : CommRing (DensePoly Int) := HexPolyMathlib.commRingOfGrind
    Hex.Det.det B = Matrix.det (HexMatrixMathlib.matrixEquiv B) := by
  let _ : CommRing (DensePoly Int) := HexPolyMathlib.commRingOfGrind
  exact det_eq_mathlib B

example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (B : Hex.Matrix (ZMod64 p) 3 3) :
    letI : CommRing (ZMod64 p) := HexPolyMathlib.commRingOfGrind
    Hex.Det.det B = Matrix.det (HexMatrixMathlib.matrixEquiv B) := by
  let _ : CommRing (ZMod64 p) := HexPolyMathlib.commRingOfGrind
  exact det_eq_mathlib B

-- `HexPolyFpMathlib.zmod64CommRing` is that same structure, named where the
-- residue carrier lives.
example {p : Nat} [ZMod64.Bounds p] :
    HexPolyFpMathlib.zmod64CommRing (p := p) = HexPolyMathlib.commRingOfGrind := rfl

end Shapes

/-! Each available non-small arm forced at `n > 2` by an explicit recipe, with
that recipe's route law applied. No arm can fail today, so there is no fallback
transition to force; the modular arm brings the first one. -/

section Forced

variable (A : Hex.Matrix Int 3 3)

example : (runWith (Policy.berkowitz inferInstance) A).value = Hex.Matrix.det A :=
  (lawfulPolicy_berkowitz _).value_eq A

example : ValidRoute (Policy.berkowitz (inferInstance : DecidableEq Int)) A
    (runWith (Policy.berkowitz inferInstance) A) :=
  (lawfulPolicy_berkowitz _).route_sound A

example : (runWith (quotientPolicy (R := Int)) A).value = Hex.Matrix.det A :=
  lawfulPolicy_quotientPolicy.value_eq A

example : ValidRoute (quotientPolicy (R := Int)) A (runWith (quotientPolicy (R := Int)) A) :=
  lawfulPolicy_quotientPolicy.route_sound A

example : (runWith (Policy.integer id id IntArm.bareiss) A).value = Hex.Matrix.det A :=
  (lawfulPolicy_integer id id (fun _ => rfl) rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl)).value_eq A

example (B : Hex.Matrix Rat 3 3) :
    (runWith (fieldPolicy (F := Rat)) B).value = Hex.Matrix.det B :=
  lawfulPolicy_fieldPolicy.value_eq B

end Forced

/-! Tiny closed values, checked by the kernel. At `n ≤ 2` dispatch always runs
the small arm, so the cross-arm comparison calls the lower algorithms directly.
-/

example : Hex.Det.det (Hex.Matrix.ofFn fun (_ : Fin 0) (_ : Fin 0) => (0 : Int)) = 1 := by
  decide

example :
    Hex.Det.det (Hex.Matrix.ofFn fun (_ : Fin 1) (_ : Fin 1) => (7 : Int)) = 7 := by
  decide

example :
    Hex.Det.det (Hex.Matrix.ofFn fun (i : Fin 2) (j : Fin 2) =>
      (i.val * 2 + j.val + 1 : Int)) = -2 := by
  decide

/-- The cross-arm comparison at a tiny size: dispatch runs its small arm there,
so the lower algorithm is called directly. The kernel does not evaluate
`Hex.Matrix.bareiss`, whose integer quotient is native, so this is stated rather
than decided; the executable comparison is a `#guard` in the conformance driver. -/
example (B : Hex.Matrix Int 2 2) : Hex.Matrix.bareiss B = Hex.Det.det B :=
  (HexMatrixMathlib.bareiss_eq_det B).trans (det_eq B).symm

end Verification

end HexDetMathlib
