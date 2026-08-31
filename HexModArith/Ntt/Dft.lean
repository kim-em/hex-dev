/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ntt.Plan

public section

/-!
# Coefficientwise discrete Fourier transforms

This file contains the allocation-simple mathematical reference transform used
to specify the word-level NTT.  `evalCoeffs x values` evaluates the coefficient
list at `x`; the `k`th DFT coefficient is evaluation at `root^k`.
-/

namespace Hex

namespace ZMod64

namespace Ntt

/-- Evaluate a low-to-high coefficient list by Horner recursion. -/
@[expose] def evalCoeffs {p : Nat} [Bounds p] (x : ZMod64 p) :
    List (ZMod64 p) → ZMod64 p
  | [] => 0
  | value :: values => value + x * evalCoeffs x values

/-- Evaluation of an empty coefficient list is zero. -/
@[simp] theorem evalCoeffs_nil {p : Nat} [Bounds p] (x : ZMod64 p) :
    evalCoeffs x [] = 0 := rfl

/-- Horner equation for a nonempty coefficient list. -/
@[simp] theorem evalCoeffs_cons {p : Nat} [Bounds p] (x value : ZMod64 p)
    (values : List (ZMod64 p)) :
    evalCoeffs x (value :: values) = value + x * evalCoeffs x values := rfl

/-- The coefficientwise DFT value at frequency `k`. -/
@[expose] def dftCoeff {p : Nat} [Bounds p] (root : ZMod64 p)
    (values : List (ZMod64 p)) (k : Nat) : ZMod64 p :=
  evalCoeffs (root ^ k) values

/-- Expose a DFT coefficient as evaluation at the corresponding root power. -/
@[simp] theorem dftCoeff_eq {p : Nat} [Bounds p] (root : ZMod64 p)
    (values : List (ZMod64 p)) (k : Nat) :
    dftCoeff root values k = evalCoeffs (root ^ k) values := rfl

/-- The first `count` coefficientwise DFT values in ordinary frequency order. -/
@[expose] def dft {p : Nat} [Bounds p] (root : ZMod64 p) (count : Nat)
    (values : List (ZMod64 p)) : List (ZMod64 p) :=
  List.ofFn fun k : Fin count => dftCoeff root values k.val

/-- Array wrapper around the coefficientwise DFT reference. -/
@[expose] def dftArray {p : Nat} [Bounds p] (root : ZMod64 p) (count : Nat)
    (values : Array (ZMod64 p)) : Array (ZMod64 p) :=
  (dft root count values.toList).toArray

/-- A coefficientwise DFT has its requested output length. -/
@[simp] theorem length_dft {p : Nat} [Bounds p] (root : ZMod64 p)
    (count : Nat) (values : List (ZMod64 p)) :
    (dft root count values).length = count := by
  simp [dft]

/-- A coefficientwise DFT array has its requested output size. -/
@[simp] theorem size_dftArray {p : Nat} [Bounds p] (root : ZMod64 p)
    (count : Nat) (values : Array (ZMod64 p)) :
    (dftArray root count values).size = count := by
  simp [dftArray]

/-- Lookup exposes the defining coefficient-evaluation formula. -/
@[simp] theorem getElem_dft {p : Nat} [Bounds p] (root : ZMod64 p)
    (count : Nat) (values : List (ZMod64 p)) (k : Nat) (hk : k < count) :
    (dft root count values)[k]'(by simp_all) = dftCoeff root values k := by
  simp [dft]

/-- The one-point DFT of a singleton is that singleton. -/
@[simp] theorem dft_one {p : Nat} [Bounds p] (root value : ZMod64 p) :
    dft root 1 [value] = [value] := by
  simp [dft, dftCoeff, evalCoeffs]

/-- Evaluation of concatenated coefficient blocks shifts the right block by
the length of the left block. -/
theorem evalCoeffs_append {p : Nat} [Bounds p] (x : ZMod64 p)
    (left right : List (ZMod64 p)) :
    evalCoeffs x (left ++ right) =
      evalCoeffs x left + x ^ left.length * evalCoeffs x right := by
  induction left with
  | nil => simp [evalCoeffs]
  | cons value left ih =>
      simp only [List.cons_append, evalCoeffs, List.length_cons]
      rw [ih, ZMod64.pow_succ]
      grind

/-- When the block-shift power is one, concatenated evaluation is the sum of
the two block evaluations. -/
theorem evalCoeffs_append_eq_add {p : Nat} [Bounds p] (x : ZMod64 p)
    (left right : List (ZMod64 p)) (hpow : x ^ left.length = 1) :
    evalCoeffs x (left ++ right) =
      evalCoeffs x left + evalCoeffs x right := by
  rw [evalCoeffs_append, hpow]
  simp

/-- When the block-shift power is minus one, concatenated evaluation is the
difference of the two block evaluations. -/
theorem evalCoeffs_append_eq_sub {p : Nat} [Bounds p] (x : ZMod64 p)
    (left right : List (ZMod64 p)) (hpow : x ^ left.length = 0 - 1) :
    evalCoeffs x (left ++ right) =
      evalCoeffs x left - evalCoeffs x right := by
  rw [evalCoeffs_append, hpow,
    Lean.Grind.Ring.sub_eq_add_neg,
    Lean.Grind.Ring.sub_eq_add_neg]
  grind

/-- Evaluation commutes with multiplication of every coefficient by a common
scalar. -/
theorem evalCoeffs_scale {p : Nat} [Bounds p] (x c : ZMod64 p)
    (values : List (ZMod64 p)) :
    evalCoeffs x (values.map fun value => c * value) =
      c * evalCoeffs x values := by
  induction values with
  | nil => simp [evalCoeffs]
  | cons value values ih =>
      simp only [List.map_cons, evalCoeffs, ih]
      grind

/-- Raising a power and then raising again multiplies the exponents. -/
theorem pow_mul {p : Nat} [Bounds p] (x : ZMod64 p) (a b : Nat) :
    (x ^ a) ^ b = x ^ (a * b) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [ZMod64.pow_succ, ih, Nat.mul_succ,
        Lean.Grind.Semiring.pow_add]

/-- Even powers of minus one are one. -/
theorem negOne_pow_even {p : Nat} [Bounds p] (k : Nat) :
    ((0 - 1 : ZMod64 p) ^ (2 * k)) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, Lean.Grind.Semiring.pow_add, ih]
      simp only [Lean.Grind.Semiring.pow_two]
      rw [Lean.Grind.Ring.sub_eq_add_neg]
      grind

/-- Odd powers of minus one are minus one. -/
theorem negOne_pow_odd {p : Nat} [Bounds p] (k : Nat) :
    ((0 - 1 : ZMod64 p) ^ (2 * k + 1)) = 0 - 1 := by
  rw [Lean.Grind.Semiring.pow_add, negOne_pow_even, ZMod64.pow_one]
  simp

/-- A root whose `n`th power is one has periodic powers modulo positive `n`. -/
theorem pow_mod {p n : Nat} [Bounds p] (root : ZMod64 p)
    (hroot : root ^ n = 1) (e : Nat) :
    root ^ (e % n) = root ^ e := by
  symm
  calc
    root ^ e = root ^ (e % n + n * (e / n)) :=
      congrArg (fun exponent : Nat => root ^ exponent)
        (Nat.mod_add_div e n).symm
    _ = root ^ (e % n) * root ^ (n * (e / n)) := by
      rw [Lean.Grind.Semiring.pow_add]
    _ = root ^ (e % n) * (root ^ n) ^ (e / n) := by
      rw [pow_mul]
    _ = root ^ (e % n) := by rw [hroot]; simp

end Ntt

end ZMod64

end Hex
