/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Interpretation
public import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Tactic.Ring

public section

/-! Ring laws and conjugation for the native Gaussian-integer representation. -/

open scoped ComplexOrder

namespace Hex.PosDefTheory

open Hex.PosDef

namespace Gaussian

@[expose] def nsmul : Nat → PosDef.Gaussian → PosDef.Gaussian
  | 0, _ => 0
  | n + 1, z => nsmul n z + z

@[expose] def power : Nat → PosDef.Gaussian → PosDef.Gaussian
  | 0, _ => 1
  | n + 1, z => power n z * z

instance : NatCast PosDef.Gaussian := ⟨fun n => ⟨(n : Int), 0⟩⟩
instance : IntCast PosDef.Gaussian := ⟨fun z => ⟨z, 0⟩⟩
instance : SMul Nat PosDef.Gaussian := ⟨nsmul⟩
instance : SMul Int PosDef.Gaussian := ⟨fun z x => match z with
  | .ofNat n => nsmul n x
  | .negSucc n => -(nsmul (n + 1) x)⟩
instance : Pow PosDef.Gaussian Nat := ⟨fun z n => power n z⟩

theorem map_zero : toComplex (0 : PosDef.Gaussian) = 0 := gaussianModel.zero
theorem map_one : toComplex (1 : PosDef.Gaussian) = 1 := by
  change toComplex ⟨1, 0⟩ = 1
  apply Complex.ext <;> simp [toComplex]
theorem map_add (x y : PosDef.Gaussian) : toComplex (x + y) = toComplex x + toComplex y :=
  gaussianModel.add x y
theorem map_mul (x y : PosDef.Gaussian) : toComplex (x * y) = toComplex x * toComplex y :=
  gaussianModel.mul x y
theorem map_neg (x : PosDef.Gaussian) : toComplex (-x) = -toComplex x := by
  apply Complex.ext
  · change (((-x.re : Int) : Real)) = -((x.re : Real))
    exact Int.cast_neg x.re
  · change (((-x.im : Int) : Real)) = -((x.im : Real))
    exact Int.cast_neg x.im
theorem map_sub (x y : PosDef.Gaussian) : toComplex (x - y) = toComplex x - toComplex y := by
  change toComplex (x + -y) = _
  rw [map_add, map_neg, sub_eq_add_neg]

theorem map_nsmul (n : Nat) (x : PosDef.Gaussian) :
    toComplex (nsmul n x) = n • toComplex x := by
  induction n with
  | zero => simp [nsmul, map_zero]
  | succ n ih => simp [nsmul, map_add, ih]; ring

theorem map_power (x : PosDef.Gaussian) (n : Nat) :
    toComplex (power n x) = toComplex x ^ n := by
  induction n with
  | zero => simp [power, map_one]
  | succ n ih => simp [power, map_mul, ih, pow_succ]

instance : CommRing PosDef.Gaussian :=
  Function.Injective.commRing toComplex toComplex_injective map_zero map_one map_add map_mul
    map_neg map_sub map_nsmul
    (by
      intro n x
      cases n with
      | ofNat n =>
        change toComplex (nsmul n x) = (Int.ofNat n) • toComplex x
        rw [map_nsmul]
        simp
      | negSucc n =>
        change toComplex (-(nsmul (n + 1) x)) = _
        rw [map_neg, map_nsmul]
        simp
        ring)
    map_power
    (by
      intro n
      change toComplex ⟨(n : Int), 0⟩ = (n : Complex)
      apply Complex.ext <;> simp [toComplex])
    (by
      intro n
      change toComplex ⟨n, 0⟩ = (n : Complex)
      apply Complex.ext <;> simp [toComplex])

instance : Star PosDef.Gaussian := ⟨PosDef.Gaussian.conj⟩
instance : StarRing PosDef.Gaussian :=
  Function.Injective.starRing toComplex toComplex_injective gaussianModel.conj map_add map_mul

instance : Nontrivial PosDef.Gaussian :=
  ⟨⟨0, 1, by intro h; have he := congrArg toComplex h; rw [map_zero, map_one] at he; exact zero_ne_one he⟩⟩

instance : NoZeroDivisors PosDef.Gaussian :=
  Function.Injective.noZeroDivisors toComplex toComplex_injective map_zero map_mul

instance : CharZero PosDef.Gaussian where
  cast_injective n m h := by
    have he := congrArg PosDef.Gaussian.re h
    change (n : Int) = (m : Int) at he
    exact Int.natCast_inj.mp he

/-- A self-adjoint Gaussian integer has zero imaginary component. -/
theorem selfAdjoint_iff (z : PosDef.Gaussian) : star z = z ↔ z.im = 0 := by
  change PosDef.Gaussian.conj z = z ↔ z.im = 0
  cases z
  simp only [PosDef.Gaussian.conj, PosDef.Gaussian.mk.injEq, true_and]
  change -_ = _ ↔ _ = 0
  omega

end Gaussian

end Hex.PosDefTheory
