/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Presentation

public section

/-!
# The field of canonical algebraic numbers

The executable library supplies canonical rational construction and ordinary
arithmetic.  This module proves those operations lawful by embedding canonical
algebraic numbers injectively into `ℂ`.
-/

namespace Hex.AlgebraicNumber

/-- The executable rational embedding has its expected complex value. -/
@[simp] theorem ofRat_toComplex (q : Rat) :
    (ofRat q).toComplex = (q : ℂ) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
    (AlgebraicPoly.Common.rational?_isSome q)
  unfold ofRat
  rw [ha]
  exact AlgebraicPoly.Common.rational?_sound q ha

/-- Executable one denotes complex one. -/
@[simp] theorem one_toComplex :
    (1 : AlgebraicNumber).toComplex = 1 := by
  change (ofRat 1).toComplex = 1
  simp

/-- Executable rational scalar multiplication preserves interpretation. -/
theorem smul_toComplex (q : Rat) (a : AlgebraicNumber) :
    (q • a).toComplex = (q : ℂ) * a.toComplex := by
  change (smul q a).toComplex = _
  rw [smul, mul_toComplex, ofRat_toComplex]

/-- Executable natural powers preserve interpretation. -/
theorem natPow_toComplex (a : AlgebraicNumber) (n : Nat) :
    (natPow a n).toComplex = a.toComplex ^ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases n with
      | zero => simp [natPow]
      | succ n =>
          have hlt : (n + 1) / 2 < n + 1 :=
            Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)
          rw [natPow]
          by_cases heven : (n + 1) % 2 = 0
          · rw [if_pos heven, mul_toComplex, ih ((n + 1) / 2) hlt,
              ← pow_add]
            have hdecomp := Nat.mod_add_div (n + 1) 2
            congr 1
            omega
          · rw [if_neg heven, mul_toComplex, mul_toComplex,
              ih ((n + 1) / 2) hlt, ← pow_add, ← pow_succ]
            have hdecomp := Nat.mod_add_div (n + 1) 2
            have hmod := Nat.mod_two_eq_zero_or_one (n + 1)
            congr 1
            omega

/-- Executable integer powers preserve interpretation. -/
theorem intPow_toComplex (a : AlgebraicNumber) (n : Int) :
    (intPow a n).toComplex = a.toComplex ^ n := by
  cases n with
  | ofNat n => exact natPow_toComplex a n
  | negSucc n =>
      rw [intPow, inv_toComplex, natPow_toComplex]
      rfl

/-- The law-bearing field whose data fields are the executable canonical
operations. -/
@[expose, reducible]
noncomputable def field : Field AlgebraicNumber := by
  letI : SMul ℚ≥0 AlgebraicNumber :=
    ⟨fun q a => smul (q : Rat) a⟩
  letI : NNRatCast AlgebraicNumber :=
    ⟨fun q => ofRat (q : Rat)⟩
  letI : RatCast AlgebraicNumber := ⟨ofRat⟩
  apply Function.Injective.field toComplex toComplex_injective
  · exact zero_toComplex
  · exact one_toComplex
  · exact add_toComplex
  · exact mul_toComplex
  · exact neg_toComplex
  · exact sub_toComplex
  · exact inv_toComplex
  · exact div_toComplex
  · intro n a
    change (smul (n : Rat) a).toComplex = n • a.toComplex
    rw [smul, mul_toComplex, ofRat_toComplex, nsmul_eq_mul]
    rfl
  · intro n a
    change (smul (n : Rat) a).toComplex = n • a.toComplex
    rw [smul, mul_toComplex, ofRat_toComplex, zsmul_eq_mul]
    rfl
  · intro q a
    change (smul (q : Rat) a).toComplex = q • a.toComplex
    rw [smul, mul_toComplex, ofRat_toComplex, NNRat.smul_def]
    rfl
  · intro q a
    change (smul q a).toComplex = q • a.toComplex
    rw [smul, mul_toComplex, ofRat_toComplex, Rat.smul_def]
  · exact natPow_toComplex
  · exact intPow_toComplex
  · intro n
    change (ofRat (n : Rat)).toComplex = (n : ℂ)
    rw [ofRat_toComplex]
    norm_cast
  · intro n
    change (ofRat (n : Rat)).toComplex = (n : ℂ)
    rw [ofRat_toComplex]
    norm_cast
  · intro q
    change (ofRat (q : Rat)).toComplex = (q : ℂ)
    rw [ofRat_toComplex]
    norm_cast
  · exact ofRat_toComplex

/-- Canonical algebraic numbers form a field without replacing any executable
arithmetic operation. -/
noncomputable instance : Field AlgebraicNumber := field

/--
info: 'Hex.AlgebraicNumber.field' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicNumber.field

/-! Pin the installed field's data fields to the executable definitions. -/

section OperationRegression

variable (a b : AlgebraicNumber) (q : Rat) (n : Nat) (z : Int)

-- Force notation through the installed field dictionary, rather than the
-- standalone executable instances, so these equalities inspect the data
-- fields constructed by `Function.Injective.field`.
attribute [-instance] AlgebraicNumber.instZero AlgebraicNumber.instOne
  AlgebraicNumber.instNatCast AlgebraicNumber.instIntCast
  AlgebraicNumber.instAdd AlgebraicNumber.instSub
  AlgebraicNumber.instMul AlgebraicNumber.instNeg AlgebraicNumber.instInv
  AlgebraicNumber.instDiv AlgebraicNumber.instPowNat
  AlgebraicNumber.instPowInt AlgebraicNumber.instSMulRat
  AlgebraicNumber.instSMulNat AlgebraicNumber.instSMulInt

example : (0 : AlgebraicNumber) = AlgebraicNumber.zero := rfl
example : (1 : AlgebraicNumber) = AlgebraicNumber.ofRat 1 := rfl
example : a + b = AlgebraicNumber.add a b := rfl
example : a - b = AlgebraicNumber.sub a b := rfl
example : a * b = AlgebraicNumber.mul a b := rfl
example : -a = AlgebraicNumber.neg a := rfl
example : a⁻¹ = AlgebraicNumber.inv a := rfl
example : a / b = AlgebraicNumber.div a b := rfl
example : a ^ (3 : Nat) = AlgebraicNumber.natPow a 3 := rfl
example : a ^ (-3 : Int) = AlgebraicNumber.intPow a (-3) := rfl
example : q • a = AlgebraicNumber.smul q a := rfl
example : n • a = AlgebraicNumber.smul (n : Rat) a := rfl
example : z • a = AlgebraicNumber.smul (z : Rat) a := rfl
example : ((2 : Nat) : AlgebraicNumber) = (2 : AlgebraicNumber) := rfl

end OperationRegression

-- With the ordinary instance priorities, Mathlib's generic numeral and the
-- executable natural cast have the same definitional normal form.
example : ((2 : Nat) : AlgebraicNumber) = (2 : AlgebraicNumber) := rfl

-- If Mathlib instance derivation ever takes precedence over the standalone
-- executable operations, this definition becomes noncomputable and fails to
-- elaborate without that annotation.
private def executableCube (a : AlgebraicNumber) : AlgebraicNumber :=
  a ^ (3 : Nat) * a + 1

end Hex.AlgebraicNumber
