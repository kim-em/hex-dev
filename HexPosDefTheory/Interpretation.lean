/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Lists
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star

public section

/-! Integer casts and Gaussian-integer interpretation in ordered scalar carriers. -/

open scoped ComplexOrder

namespace Hex.PosDefTheory

open Hex.PosDef

/-- Integer arithmetic is interpreted by casts, including in the standard complex order. -/
@[expose] def intModel (R : Type*) [CommRing R] [PartialOrder R] [StarRing R]
    [IsStrictOrderedRing R] [CharZero R] : Lists.Model (R := R) PosDef.Lists.intArithmetic where
  map := fun z => (z : R)
  injective := Int.cast_injective
  zero := Int.cast_zero
  add := Int.cast_add
  mul := Int.cast_mul
  conj := fun z => (star_intCast z).symm
  eq := fun x y => by simp [PosDef.Lists.intArithmetic]
  positive := fun x h => Int.cast_pos.mpr (of_decide_eq_true h)
  nonpositive := fun x h => Int.cast_nonpos.mpr (of_decide_eq_true h)

/-- Decode both integer components without any equality evaluator on complex numbers. -/
@[expose] def toComplex (z : Gaussian) : Complex := ⟨(z.re : Real), (z.im : Real)⟩

theorem toComplex_injective : Function.Injective toComplex := by
  intro x y h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [toComplex, Int.cast_inj] at hre him
  cases x; cases y
  simp_all

/-- Every Gaussian scalar operation and comparison has its complex meaning. -/
@[expose] def gaussianModel : Lists.Model (R := Complex) PosDef.Lists.gaussianArithmetic where
  map := toComplex
  injective := toComplex_injective
  zero := by apply Complex.ext <;> simp [PosDef.Lists.gaussianArithmetic, toComplex, Gaussian.zero]
  add := by intro x y; apply Complex.ext <;> simp [PosDef.Lists.gaussianArithmetic, toComplex, Gaussian.add]
  mul := by
    intro x y
    apply Complex.ext
    · change (((x.re * y.re - x.im * y.im : Int) : Real)) = _
      push_cast
      simp [toComplex, Complex.mul_re]
    · simp [PosDef.Lists.gaussianArithmetic, toComplex, Gaussian.mul]
  conj := by
    intro x
    apply Complex.ext
    · rfl
    · change (((-x.im : Int) : Real)) = -((x.im : Real))
      exact Int.cast_neg x.im
  eq := by
    intro x y
    cases x; cases y
    simp [PosDef.Lists.gaussianArithmetic, Gaussian.eq, Gaussian.mk.injEq]
  positive := by
    intro x h
    simp only [PosDef.Lists.gaussianArithmetic, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Complex.pos_iff.mpr ⟨Int.cast_pos.mpr h.2, by simp [toComplex, h.1]⟩
  nonpositive := by
    intro x h
    simp only [PosDef.Lists.gaussianArithmetic, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Complex.nonpos_iff.mpr ⟨Int.cast_nonpos.mpr h.2, by simp [toComplex, h.1]⟩

end Hex.PosDefTheory
