/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.ExtGcd
public import HexMvGcd.Normalize
public import HexPolyFp.Field
public import HexResultant.ExactDiv

@[expose] public section
set_option backward.proofsInPublic true

/-!
Base coefficient instances for the multivariate gcd kernel.

The field gcd convention is `0` only for the pair `(0, 0)` and `1`
otherwise. `normUnit` is defined at zero as `1`, as required by
`LawfulGcdOps`; the inverse is used only on nonzero inputs.
-/

namespace Hex

/-! # Integers -/

@[reducible] instance instGcdOpsInt : GcdOps Int where
  gcd a b := (Int.gcd a b : Int)
  exactDiv a b := a / b
  isUnit a := decide (a = 1 ∨ a = -1)
  normUnit a := if a < 0 then -1 else 1

instance instBezoutOpsInt : BezoutOps Int where
  gcd := GcdOps.gcd
  exactDiv := GcdOps.exactDiv
  isUnit := GcdOps.isUnit
  normUnit := GcdOps.normUnit
  xgcd a b :=
    let r := HexArith.Int.extGcd a b
    (r.2.1, r.2.2)

instance instLawfulGcdOpsInt : LawfulGcdOps Int := by
  constructor <;> intros <;> sorry

instance instLawfulBezoutOpsInt : LawfulBezoutOps Int := by
  constructor
  intro a b
  simp only [BezoutOps.xgcd, instBezoutOpsInt]
  rw [HexArith.Int.extGcd_bezout_gcd]
  sorry

/-! # Rationals -/

/-- Divisibility in a field, stated in the same multiplication orientation as
the polynomial instances. -/
instance instDvdRat : Dvd Rat where
  dvd a b := ∃ c, b = a * c

def ratXgcd (a b : Rat) : Rat × Rat :=
  if a = 0 then
    if b = 0 then (0, 0) else (0, b⁻¹)
  else
    (a⁻¹, 0)

@[reducible] instance instGcdOpsRat : GcdOps Rat where
  gcd a b := if a = 0 ∧ b = 0 then 0 else 1
  exactDiv a b := a / b
  isUnit a := decide (a ≠ 0)
  normUnit a := if a = 0 then 1 else a⁻¹

instance instBezoutOpsRat : BezoutOps Rat where
  gcd := GcdOps.gcd
  exactDiv := GcdOps.exactDiv
  isUnit := GcdOps.isUnit
  normUnit := GcdOps.normUnit
  xgcd := ratXgcd

instance instLawfulGcdOpsRat : LawfulGcdOps Rat := by
  constructor <;> intros <;> sorry

instance instLawfulBezoutOpsRat : LawfulBezoutOps Rat := by
  constructor
  intro a b
  sorry

/-! # Bounded prime fields -/

namespace ZMod64

variable {p : Nat} [hp : Bounds p] [PrimeModulus p]

def fieldXgcd (a b : @ZMod64 p hp) : @ZMod64 p hp × @ZMod64 p hp :=
  if a = 0 then
    if b = 0 then (0, 0) else (0, b⁻¹)
  else
    (a⁻¹, 0)

end ZMod64

/-- Field divisibility, in multiplication orientation. -/
instance instDvdZMod64 {p : Nat} [hp : ZMod64.Bounds p] :
    Dvd (@ZMod64 p hp) where
  dvd a b := ∃ c, b = a * c

@[reducible] instance instGcdOpsZMod64 {p : Nat} [hp : ZMod64.Bounds p] :
    GcdOps (@ZMod64 p hp) where
  gcd a b := if a = 0 ∧ b = 0 then 0 else 1
  exactDiv a b := a / b
  isUnit a := decide (a ≠ 0)
  normUnit a := if a = 0 then 1 else a⁻¹

instance instBezoutOpsZMod64 {p : Nat} [hp : ZMod64.Bounds p] :
    BezoutOps (@ZMod64 p hp) where
  gcd := GcdOps.gcd
  exactDiv := GcdOps.exactDiv
  isUnit := GcdOps.isUnit
  normUnit := GcdOps.normUnit
  xgcd := ZMod64.fieldXgcd

instance instLawfulGcdOpsZMod64 {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    @LawfulGcdOps (@ZMod64 p hp) _ _ _ _ instDvdZMod64 instGcdOpsZMod64 := by
  sorry

instance instLawfulBezoutOpsZMod64 {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    @LawfulBezoutOps (@ZMod64 p hp) _ _ _ _ instDvdZMod64 instBezoutOpsZMod64
      instLawfulGcdOpsZMod64 := by
  sorry

/-! # Univariate prime-field polynomials -/

namespace FpPoly

variable {p : Nat} [hp : ZMod64.Bounds p] [ZMod64.PrimeModulus p]

/-- Unit which makes the leading coefficient one, with `1` at zero. -/
@[reducible] def normUnit (f : @FpPoly p hp) : @FpPoly p hp :=
  if f = 0 then 1 else DensePoly.C f.leadingCoeff⁻¹

/-- The Euclidean gcd made monic by its leading coefficient. -/
@[reducible] def normalizedGcd (f g : @FpPoly p hp) : @FpPoly p hp :=
  let d := DensePoly.gcd f g
  d * normUnit d

/-- Extended-gcd coefficients scaled by the same unit as the gcd. -/
def normalizedXgcd (f g : @FpPoly p hp) : @FpPoly p hp × @FpPoly p hp :=
  let r := DensePoly.xgcd f g
  let u := normUnit r.gcd
  (r.left * u, r.right * u)

end FpPoly

/-- Canonical dense-polynomial ring instance exposed for `FpPoly`. -/
instance instCommRingFpPoly {p : Nat} [hp : ZMod64.Bounds p] :
    Lean.Grind.CommRing (@FpPoly p hp) :=
  Hex.instGrindCommRingDensePoly

@[reducible] instance instGcdOpsFpPoly {p : Nat} [hp : ZMod64.Bounds p] :
    GcdOps (@FpPoly p hp) where
  gcd := FpPoly.normalizedGcd
  exactDiv f g := f / g
  isUnit f := decide (f.size = 1)
  normUnit := FpPoly.normUnit

instance instBezoutOpsFpPoly {p : Nat} [hp : ZMod64.Bounds p] :
    BezoutOps (@FpPoly p hp) where
  gcd := GcdOps.gcd
  exactDiv := GcdOps.exactDiv
  isUnit := GcdOps.isUnit
  normUnit := GcdOps.normUnit
  xgcd := FpPoly.normalizedXgcd

instance instLawfulGcdOpsFpPoly {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    @LawfulGcdOps (@FpPoly p hp) instCommRingFpPoly _ _ _ _ instGcdOpsFpPoly := by
  sorry

instance instLawfulBezoutOpsFpPoly {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    @LawfulBezoutOps (@FpPoly p hp) instCommRingFpPoly _ _ _ _ instBezoutOpsFpPoly
      instLawfulGcdOpsFpPoly := by
  sorry

/-! Instance-graph checks for every base coefficient family. -/

example : GcdOps Int := inferInstance
example : BezoutOps Int := inferInstance
example : LawfulGcdOps Int := inferInstance
example : GcdOps Rat := inferInstance
example : BezoutOps Rat := inferInstance
example : LawfulGcdOps Rat := inferInstance

example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    GcdOps (ZMod64 p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    GcdOps (FpPoly p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulGcdOps (ZMod64 p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulBezoutOps (ZMod64 p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulGcdOps (FpPoly p) := inferInstance
example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    LawfulBezoutOps (FpPoly p) := inferInstance

end Hex
