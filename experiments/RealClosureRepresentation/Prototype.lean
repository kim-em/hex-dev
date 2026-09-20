/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPoly.Euclid.DivGcd
import HexPoly.Instances
import HexPoly.Lcm
import Init.Data.Rat.Lemmas

namespace Prototype

/-- Only zero is canonical; other representations can have equal denotations. -/
def ZeroRep (A : Type) (isZero : A → Bool) := Option {a : A // isZero a = false}

namespace ZeroRep
variable {A : Type} {isZero : A → Bool}
instance : Zero (ZeroRep A isZero) := ⟨none⟩
instance [DecidableEq A] : DecidableEq (ZeroRep A isZero) :=
  inferInstanceAs (DecidableEq (Option {a : A // isZero a = false}))
def ofRaw (a : A) : ZeroRep A isZero :=
  if h : isZero a = false then some ⟨a, h⟩ else none

theorem ofRaw_eq_zero (a : A) : ofRaw (isZero := isZero) a = 0 ↔ isZero a = true := by
  unfold ofRaw
  by_cases h : isZero a = false
  · simp [h, show (0 : ZeroRep A isZero) = none from rfl]
  · simp [h, show (0 : ZeroRep A isZero) = none from rfl]
    cases hval : isZero a <;> simp_all
    rfl
end ZeroRep

-- a+bX interpreted at the selected root +1 of the reducible polynomial X²-1.
def atOne (ab : Rat × Rat) : Rat := ab.1 + ab.2
def testZero (ab : Rat × Rat) : Bool := decide (atOne ab = 0)
abbrev Rep := ZeroRep (Rat × Rat) testZero

def pack (a b : Rat) : Rep := ZeroRep.ofRaw (a, b)
def raw : Rep → Rat × Rat
  | none => (0, 0)
  | some a => a.val
def value (a : Rep) : Rat := atOne (raw a)
instance : One Rep := ⟨pack 1 0⟩
instance : Add Rep := ⟨fun a b => pack ((raw a).1 + (raw b).1) ((raw a).2 + (raw b).2)⟩
instance : Sub Rep := ⟨fun a b => pack ((raw a).1 - (raw b).1) ((raw a).2 - (raw b).2)⟩
instance : Neg Rep := ⟨fun a => pack (-(raw a).1) (-(raw a).2)⟩
instance : Mul Rep := ⟨fun a b =>
  pack ((raw a).1 * (raw b).1 + (raw a).2 * (raw b).2)
       ((raw a).1 * (raw b).2 + (raw a).2 * (raw b).1)⟩
instance : Inv Rep := ⟨fun a => pack (value a)⁻¹ 0⟩
instance : Div Rep := ⟨fun a b => pack (value a / value b) 0⟩

theorem value_pack (a b : Rat) : value (pack a b) = a + b := by
  by_cases h : a + b = 0
  · simp [pack, ZeroRep.ofRaw, testZero, atOne, h, value, raw]
    exact Rat.zero_add 0
  · simp [pack, ZeroRep.ofRaw, testZero, atOne, h, value, raw]

theorem value_zero : value (0 : Rep) = 0 := Rat.zero_add 0

theorem value_eq_zero (a : Rep) : value a = 0 ↔ a = 0 := by
  cases a with
  | none =>
    simp [value, raw, atOne, Rat.zero_add, show (0 : Rep) = none from rfl]
    rfl
  | some a =>
    have hn : atOne a.val ≠ 0 := by simpa [testZero] using a.property
    simp [value, raw, hn, show (0 : Rep) = none from rfl]

theorem value_add (a b : Rep) : value (a+b) = value a + value b := by
  change value (pack _ _) = _
  rw [value_pack]
  unfold value atOne
  grind

theorem value_sub (a b : Rep) : value (a-b) = value a - value b := by
  change value (pack _ _) = _
  rw [value_pack]
  unfold value atOne
  grind

theorem value_mul (a b : Rep) : value (a*b) = value a * value b := by
  change value (pack _ _) = _
  rw [value_pack]
  unfold value atOne
  grind

theorem value_div (a b : Rep) : value (a/b) = value a / value b := by
  change value (pack _ 0) = _
  rw [value_pack]
  grind

-- Same selected-root value, different nonzero representations.
def root : Rep := pack 0 1
example : root ≠ (1 : Rep) := by decide +kernel
example : value root = value (1 : Rep) := by decide +kernel
example : root - 1 = (0 : Rep) := by decide +kernel
example : pack (-1) 1 = (0 : Rep) := by decide +kernel

-- DensePoly's existing zero normalization works without a Field instance.
abbrev Poly := Hex.DensePoly Rep
def p : Poly := Hex.DensePoly.ofCoeffs #[1, root - 1]
example : p.size = 1 := by decide +kernel

def x : Poly := Hex.DensePoly.ofCoeffs #[0, 1]
def a : Poly := x - Hex.DensePoly.C root
def b : Poly := x - Hex.DensePoly.C 1
def product : Poly := a*b
def remainder : Poly := (Hex.DensePoly.divMod product a).2
example : remainder = 0 := by decide +kernel
example : (Hex.DensePoly.gcd product a).natDegree = 1 := by decide +kernel
example : (Hex.DensePoly.xgcd product a).gcd.natDegree = 1 := by decide +kernel

-- Structural polynomial inequality is NOT a semantic identity test.
example : a ≠ b := by decide +kernel
example : a-b = (0 : Poly) := by decide +kernel
example : (a ^ (2 : Nat)).natDegree = 2 := by decide +kernel
example : (Hex.DensePoly.monicize product).natDegree = 2 := by decide +kernel
-- Monicity is semantic on this representation, not literal leadingCoeff = 1.
example : ¬ (Hex.DensePoly.monicize (Hex.DensePoly.C (pack 0 2))).Monic := by
  unfold Hex.DensePoly.Monic
  decide +kernel
example : value (Hex.DensePoly.monicize (Hex.DensePoly.C (pack 0 2))).leadingCoeff = 1 := by
  decide +kernel

theorem cancellation (a c : Rep) (hc : c ≠ 0) : a - (a / c) * c = 0 := by
  apply (value_eq_zero _).mp
  rw [value_sub, value_mul, value_div]
  have hc' : value c ≠ 0 := by simpa [value_eq_zero] using hc
  grind

-- Apply the EXISTING degree theorem; no false Field instance is introduced.
theorem remainder_degree (p q : Poly) (hq : 0 < q.natDegree) :
    (Hex.DensePoly.divMod p q).2.natDegree < q.natDegree := by
  apply Hex.DensePoly.divMod_remainder_degree_lt_of_pos_degree_of_cancel p q hq
  intro a
  apply cancellation a q.leadingCoeff
  apply Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size
  rw [Hex.DensePoly.natDegree_eq_size_sub_one] at hq
  omega

-- Repeat the storage construction over a noncanonical predecessor.
namespace Second
abbrev Raw := Rep × Rep
def testZero (a : Raw) : Bool := decide (a.1 + a.2 = (0 : Rep))
abbrev Coeff := ZeroRep Raw testZero
def pack (a b : Rep) : Coeff := ZeroRep.ofRaw (a,b)
def raw : Coeff → Raw | none => (0,0) | some a => a.val
def lower (a : Coeff) : Rep := (raw a).1 + (raw a).2
instance : One Coeff := ⟨pack 1 0⟩
instance : Add Coeff := ⟨fun a b => pack ((raw a).1 + (raw b).1) ((raw a).2 + (raw b).2)⟩
instance : Sub Coeff := ⟨fun a b => pack ((raw a).1 - (raw b).1) ((raw a).2 - (raw b).2)⟩
instance : Mul Coeff := ⟨fun a b =>
  pack ((raw a).1 * (raw b).1 + (raw a).2 * (raw b).2)
       ((raw a).1 * (raw b).2 + (raw a).2 * (raw b).1)⟩
instance : Div Coeff := ⟨fun a b => pack (lower a / lower b) 0⟩
def root : Coeff := pack 0 1
abbrev Poly := Hex.DensePoly Coeff
def x : Poly := Hex.DensePoly.ofCoeffs #[0,1]
def a : Poly := x - Hex.DensePoly.C root
def b : Poly := x - Hex.DensePoly.C 1
example : a ≠ b := by decide +kernel
example : a-b = (0 : Poly) := by decide +kernel
example : (Hex.DensePoly.divMod (a*b) a).2 = 0 := by decide +kernel
example : (Hex.DensePoly.gcd (a*b) a).natDegree = 1 := by decide +kernel
end Second

#print axioms remainder_degree
#print axioms value_eq_zero
#print axioms value_mul
end Prototype
