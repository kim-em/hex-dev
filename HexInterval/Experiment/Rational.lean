/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Data.Rat

@[expose] public section

/-!
# D2 rational-replay experiment

Core rational arithmetic is exact and Mathlib-free, but the ordinary
`Rat.add`, `Rat.sub`, `Rat.mul`, and `Rat.inv` implementations are marked
irreducible.  This module records two provisional replay encodings:

* exposed wrappers around Core's normalization formulae;
* a plain numerator/denominator certificate checked by integer
  cross-products.

These declarations are experiment inputs, not a choice of the production
working-endpoint representation.
-/

namespace Hex.Interval.Experiment.Rational

/-! ## Exposed Core rational operations -/

/-- Kernel-reducible rational addition using Core's normalization formula. -/
def add (a b : Rat) : Rat :=
  Rat.normalize (a.num * b.den + b.num * a.den) (a.den * b.den)
    (Nat.mul_ne_zero a.den_nz b.den_nz)

/-- Kernel-reducible rational subtraction using Core's normalization formula. -/
def sub (a b : Rat) : Rat :=
  Rat.normalize (a.num * b.den - b.num * a.den) (a.den * b.den)
    (Nat.mul_ne_zero a.den_nz b.den_nz)

/-- Kernel-reducible rational multiplication using Core's normalization formula. -/
def mul (a b : Rat) : Rat :=
  Rat.normalize (a.num * b.num) (a.den * b.den)
    (Nat.mul_ne_zero a.den_nz b.den_nz)

/-- Kernel-reducible rational inversion, including Core's convention `0⁻¹ = 0`. -/
def inv (a : Rat) : Rat := Rat.divInt a.den a.num

/-- The exposed addition wrapper computes Core rational addition. -/
theorem add_eq (a b : Rat) : add a b = a + b := (Rat.add_def a b).symm

/-- The exposed subtraction wrapper computes Core rational subtraction. -/
theorem sub_eq (a b : Rat) : sub a b = a - b := (Rat.sub_def a b).symm

/-- The exposed multiplication wrapper computes Core rational multiplication. -/
theorem mul_eq (a b : Rat) : mul a b = a * b := (Rat.mul_def a b).symm

/-- The exposed inversion wrapper computes Core rational inversion. -/
theorem inv_eq (a : Rat) : inv a = a⁻¹ := (Rat.inv_def a).symm

/-! ## Cross-product certificates -/

/-- An untrusted rational certificate.  `den` is signed so that interpretation
is exactly Core's `Rat.divInt`; validity rejects its zero-denominator fallback. -/
structure Raw where
  num : Int
  den : Int
  deriving DecidableEq, Repr

namespace Raw

/-- Interpret a raw certificate as a Core rational. -/
def value (q : Raw) : Rat := Rat.divInt q.num q.den

/-- A raw certificate has a genuine denominator. -/
def valid (q : Raw) : Bool := decide (q.den ≠ 0)

/-- Check a proposed addition result by cross multiplication. -/
def addOk (a b c : Raw) : Bool :=
  a.valid && b.valid && c.valid &&
    decide ((a.num * b.den + b.num * a.den) * c.den = c.num * (a.den * b.den))

/-- Check a proposed subtraction result by cross multiplication. -/
def subOk (a b c : Raw) : Bool :=
  a.valid && b.valid && c.valid &&
    decide ((a.num * b.den - b.num * a.den) * c.den = c.num * (a.den * b.den))

/-- Check a proposed multiplication result by cross multiplication. -/
def mulOk (a b c : Raw) : Bool :=
  a.valid && b.valid && c.valid &&
    decide ((a.num * b.num) * c.den = c.num * (a.den * b.den))

/-- Check a proposed inverse.  The zero branch follows Core's convention
`0⁻¹ = 0`; otherwise equality is one cross-product. -/
def invOk (a c : Raw) : Bool :=
  a.valid && c.valid &&
    if a.num = 0 then decide (c.num = 0)
    else decide (a.den * c.den = c.num * a.num)

/-- A successful cross-product addition check is sound in `Rat`. -/
theorem add_sound {a b c : Raw} (h : addOk a b c = true) :
    a.value + b.value = c.value := by
  simp only [addOk, Bool.and_eq_true, valid, decide_eq_true_eq] at h
  change Rat.divInt a.num a.den + Rat.divInt b.num b.den = Rat.divInt c.num c.den
  rw [Rat.divInt_add_divInt _ _ h.1.1.1 h.1.1.2]
  exact
    (Rat.divInt_eq_divInt_iff (Int.mul_ne_zero h.1.1.1 h.1.1.2) h.1.2).2 h.2

/-- A successful cross-product subtraction check is sound in `Rat`. -/
theorem sub_sound {a b c : Raw} (h : subOk a b c = true) :
    a.value - b.value = c.value := by
  simp only [subOk, Bool.and_eq_true, valid, decide_eq_true_eq] at h
  change Rat.divInt a.num a.den - Rat.divInt b.num b.den = Rat.divInt c.num c.den
  rw [Rat.divInt_sub_divInt _ _ h.1.1.1 h.1.1.2]
  exact
    (Rat.divInt_eq_divInt_iff (Int.mul_ne_zero h.1.1.1 h.1.1.2) h.1.2).2 h.2

/-- A successful cross-product multiplication check is sound in `Rat`. -/
theorem mul_sound {a b c : Raw} (h : mulOk a b c = true) :
    a.value * b.value = c.value := by
  simp only [mulOk, Bool.and_eq_true, valid, decide_eq_true_eq] at h
  change Rat.divInt a.num a.den * Rat.divInt b.num b.den = Rat.divInt c.num c.den
  rw [Rat.divInt_mul_divInt]
  exact
    (Rat.divInt_eq_divInt_iff (Int.mul_ne_zero h.1.1.1 h.1.1.2) h.1.2).2 h.2

/-- A successful cross-product inverse check is sound in `Rat`, including at zero. -/
theorem inv_sound {a c : Raw} (h : invOk a c = true) : a.value⁻¹ = c.value := by
  change (Rat.divInt a.num a.den)⁻¹ = Rat.divInt c.num c.den
  rw [Rat.inv_divInt]
  simp only [invOk, Bool.and_eq_true, valid, decide_eq_true_eq] at h
  by_cases hn : a.num = 0
  · simp only [if_pos hn, decide_eq_true_eq] at h
    rw [hn, Rat.divInt_zero, h.2, Rat.zero_divInt]
  · simp only [if_neg hn, decide_eq_true_eq] at h
    exact (Rat.divInt_eq_divInt_iff hn h.1.2).2 h.2

end Raw

/-! ## Rational replay microprobes -/

/-- The exposed-wrapper operand for the BKLNW-sized addition fold. -/
def directStep : Rat := Rat.divInt 1 433

/-- Repeated exposed rational addition, normalizing each result. -/
def directFold : Nat → Rat
  | 0 => 0
  | n + 1 => add (directFold n) directStep

/-- A certificate-only replay for the same mathematical sequence of additions.

Unlike `directFold`, this does not construct the proposed output literals: it
checks a trace in which the planner has already supplied them.  The benchmark
therefore isolates verifier replay, not end-to-end certificate production. -/
def checkedFold : Nat → Bool
  | 0 => true
  | n + 1 =>
      checkedFold n && Raw.addOk ⟨n, 433⟩ ⟨1, 433⟩ ⟨n + 1, 433⟩

/-- Successful certificate replay composes to the value computed by the
exposed Core-rational fold. -/
theorem checkedFold_sound {n : Nat} (h : checkedFold n = true) :
    Raw.value ⟨n, 433⟩ = directFold n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [checkedFold, Bool.and_eq_true] at h
      rw [directFold, add_eq, ← ih h.1]
      exact (Raw.add_sound h.2).symm

end Hex.Interval.Experiment.Rational
