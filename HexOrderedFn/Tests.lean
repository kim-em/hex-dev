/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn

@[expose] public section

namespace Hex.OrderedFn.Tests

open Oracle

/-- Test-only requested-width approximation around a rational subject. -/
def window (q δ : Rat) : Bounds :=
  if h : 0 < δ then ⟨q - δ / 2, q + δ / 2, by grind⟩ else .singleton q

def source (q : Rat) : Approximation Rat :=
  .ofConstant (window q)

def exact (q : Rat) : Approximation Rat :=
  .ofConstant (fun _ => .singleton q)

def linearPoly (q : Rat) : DensePoly Rat := DensePoly.ofList [-q, 1]

def linear (q : Rat) : RationalFn Rat := RationalFn.ofPoly (linearPoly q)

def pole : RationalFn Rat := RationalFn.ofCoprime 1 (DensePoly.ofList [-2, 1])
  (by change (DensePoly.ofList [-2, 1] : DensePoly Rat).leadingCoeff = 1; decide +kernel)
  (DensePoly.Coprime.one_right _).symm

def a : Bounds := ⟨-2, 3, by decide +kernel⟩
def b : Bounds := ⟨-5, -1, by decide +kernel⟩

example : a.mul b = ⟨-15, 10, by decide +kernel⟩ := by decide +kernel
example : a.neg = ⟨-3, 2, by decide +kernel⟩ := by decide +kernel
example : Bounds.ofDyadic (.ofIntWithPrec (-3) 2) = .singleton (-3/4) := by decide +kernel
example : a.div? b = some ⟨-3, 2, by decide +kernel⟩ := by decide +kernel
example : b.div? a = none := by decide +kernel
example : a.inter b = some ⟨-2, -1, by decide +kernel⟩ := by decide +kernel
example : (Bounds.singleton 1).inter (.singleton 2) = none := by decide +kernel
example : (Bounds.singleton ((1 : Rat) / 3)).width = 0 := by decide +kernel
example : (Bounds.singleton 0).sign? = none := by decide +kernel
example : (Bounds.singleton 0).exactSign? = some 0 := by decide +kernel
example : (⟨0, 1, by decide +kernel⟩ : Bounds).exactSign? = none := by decide +kernel
example : (⟨-1, 0, by decide +kernel⟩ : Bounds).exactSign? = none := by decide +kernel

-- A nonzero value needs five attempts; the first four touch or straddle zero.
example : Real.attempt (source 2) (linear (31/16)) 0 = none := by decide +kernel
example : Real.attempt (source 2) (linear (31/16)) 1 = none := by decide +kernel
example : Real.attempt (source 2) (linear (31/16)) 2 = none := by decide +kernel
example : Real.attempt (source 2) (linear (31/16)) 3 = none := by decide +kernel
theorem separated : Real.attempt (source 2) (linear (31/16)) 4 = some 1 := by decide +kernel

def totalSign : Int := Real.sign (source 2) (linear (31/16))
  (acc_of_success _ 4 1 separated 0 (by decide))


theorem narrow : Real.approxAttempt (source 2) (linear 1) (1/16) 4 =
    some ⟨31/32, 33/32, by decide +kernel⟩ := by decide +kernel

def totalApprox : Bounds := Real.approx (source 2) (linear 1) (1/16)
  (by
    rw [Real.requestWidth_of_pos (δ := 1/16) (by decide +kernel)]
    exact acc_of_success _ 4 _ narrow 0 (by decide))

def coarseBounds : Bounds := ⟨1/2, 3/2, by decide +kernel⟩

-- Out-of-contract requests still produce a valid coarse enclosure of this value.
def coarseApprox : Bounds := Real.approx (source 2) (linear 1) 0
  (acc_of_success _ 0 coarseBounds (by decide +kernel) 0 (by decide))


-- Algebraic subjects use only finite evaluation, never a universal registration.
example : Real.sign? (source 2) (linear 2) 10 = none := by decide +kernel
example : Real.sign? (exact 2) (linear 2) 1 = some 0 := by decide +kernel
example : Real.sign? (exact 2) pole 3 = none := by decide +kernel
example : Real.sign? (exact 0) pole 1 = some (-1) := by decide +kernel
example : Real.sign? (exact 2) (linear 1) 0 = none := by decide +kernel

-- Both coefficient and constant bounds must refine for this subtraction.
def joint : Approximation Rat := ⟨window, window 2⟩
example : Real.attempt joint (linear (31/16)) 4 = none := by decide +kernel
example : Real.attempt joint (linear (31/16)) 5 = some 1 := by decide +kernel

-- A finite termination witness need not be the first or a persistent success.
def trial (n : Nat) : Option Int := if n = 2 then some (-1) else if n = 5 then some 1 else none
theorem later : trial 5 = some 1 := by decide +kernel
def first : Int := firstSome trial 0 (acc_of_success trial 5 1 later 0 (by decide))
example (h : Acc (Next trial) 2) : firstSome trial 2 h = -1 :=
  firstSome_some _ _ h (by decide +kernel)

/-- info: 'Hex.OrderedFn.firstSome_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms firstSome_spec

end Hex.OrderedFn.Tests
