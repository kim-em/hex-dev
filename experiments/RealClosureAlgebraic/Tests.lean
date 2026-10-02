/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Algebraic
open Hex Algebraic
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

example : valid reducible = true := by decide +kernel
example : valid irreducible = true := by decide +kernel
example : isZero reducible sqrt2 = true := by decide +kernel
example : isZero reducible sqrt3 = false := by decide +kernel
example : (zeroWithCost reducible sqrt2).2.sturmCounts = 1 := by decide +kernel
example : (zeroWithCost reducible sqrt3).2.sturmCounts = 1 := by decide +kernel
example : (invert reducible sqrt3).split = true := by decide +kernel
example : (invert reducible sqrt3).polynomial = sqrt2 := by decide +kernel
example : canonical (invert reducible sqrt3).value = (-1 : QPoly) := by decide +kernel
example : canonical (invert reducible ((DensePoly.monomial 1 1) : QPoly)).value =
    DensePoly.ofCoeffs #[0, (1/2 : Rat)] := by decide +kernel
example : (invert reducible sqrt2).value = 0 := by decide +kernel

def alpha : Element reducible := pack reducible (DensePoly.monomial 1 1)
example : alpha*alpha - ((2 : Nat) : Element reducible) = 0 := by decide +kernel
example : alpha ≠ pack reducible ((DensePoly.monomial 1 1) + reducible.polynomial) := by decide +kernel
example : alpha - pack reducible ((DensePoly.monomial 1 1) + reducible.polynomial) = 0 := by decide +kernel
example : signSqrt2 ((DensePoly.monomial 1 1) - DensePoly.C (7/5)) = 1 := by decide +kernel
example : signSqrt2 ((DensePoly.monomial 1 1) - DensePoly.C (10/7)) = -1 := by decide +kernel

def other : Descriptor := ⟨reducible.polynomial,
  ⟨(Dyadic.ofInt 3) >>> (1 : Int), 2, by decide⟩⟩
example : valid other = true := by decide +kernel
example : isZero other sqrt2 = false := by decide +kernel
example : isZero other sqrt3 = true := by decide +kernel
example : valid ⟨reducible.polynomial, ⟨1,2,by decide⟩⟩ = false := by decide +kernel
example : valid ⟨sqrt2*sqrt2, interval⟩ = false := by decide +kernel

def split := invert reducible sqrt3
def smaller := refine reducible split
example : valid smaller = true := by decide +kernel
example : observe (transport reducible smaller alpha) = observe alpha := by decide +kernel
example : observe (transport reducible smaller (pack reducible sqrt3)) = #[-1] := by
  decide +kernel

/- Generic storage invariant, independent of any semantic model. -/
theorem pack_zero (d : Descriptor) (q : QPoly) :
    pack d q = 0 ↔ isZero d q = true := by
  unfold pack
  by_cases h : isZero d q = false
  · simp [h, show (0 : Element d) = none from rfl]
  · simp [h, show (0 : Element d) = none from rfl]

/-- info: 'pack_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pack_zero
