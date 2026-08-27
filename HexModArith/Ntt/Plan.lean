/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Prime

public section

/-!
Reusable plans for radix-two number-theoretic transforms.

Plan construction validates the transform length and root once, and stores
both forward and inverse powers together with their Shoup preconditioners.
Transform execution therefore performs no root search or table construction.
-/
namespace Hex

namespace ZMod64

/-- Executable characterization of a nonzero power of two. -/
@[expose] def IsPowTwo (n : Nat) : Prop :=
  n ≠ 0 ∧ n = 2 ^ n.log2

instance (n : Nat) : Decidable (IsPowTwo n) :=
  inferInstanceAs (Decidable (n ≠ 0 ∧ n = 2 ^ n.log2))

/-- Exact-order certificate specialized to a power-of-two order.  For a
power-of-two `n`, an `n`th root has exact order `n` precisely when it is not
already an `(n / 2)`th root (with the order-one case separated). -/
@[expose] def ExactOrder {p : Nat} [Bounds p] (root : ZMod64 p) (n : Nat) : Prop :=
  root ^ n = 1 ∧ (n = 1 ∨ root ^ (n / 2) ≠ 1)

instance {p : Nat} [Bounds p] (root : ZMod64 p) (n : Nat) :
    Decidable (ExactOrder root n) :=
  inferInstanceAs (Decidable (root ^ n = 1 ∧ (n = 1 ∨ root ^ (n / 2) ≠ 1)))

/-- An exact-order certificate includes the root-of-unity equation. -/
theorem ExactOrder.pow_eq_one {p n : Nat} [Bounds p] {root : ZMod64 p}
    (h : ExactOrder root n) : root ^ n = 1 :=
  h.1

/-- The nontrivial half-order clause of a power-of-two exact-order
certificate. -/
theorem ExactOrder.half {p n : Nat} [Bounds p] {root : ZMod64 p}
    (h : ExactOrder root n) : n = 1 ∨ root ^ (n / 2) ≠ 1 :=
  h.2

/-- A transform twiddle and the quotient preconditioner
`floor(value * 2^64 / p)` used by Shoup multiplication. -/
structure NttTwiddle (p : Nat) [Bounds p] where
  /-- Canonical twiddle value. -/
  value : ZMod64 p
  /-- Shoup quotient preconditioner. -/
  precon : UInt64
  /-- The preconditioner stores the exact one-word quotient. -/
  precon_eq : precon.toNat = value.toNat * UInt64.word / p

namespace NttTwiddle

/-- Build a twiddle and its Shoup preconditioner. -/
def ofValue {p : Nat} [Bounds p] (value : ZMod64 p) : NttTwiddle p :=
  { value
    precon := UInt64.ofNat (value.toNat * UInt64.word / p)
    precon_eq := by
      have hproduct : value.toNat * UInt64.word < p * UInt64.word :=
        (Nat.mul_lt_mul_right (by decide : 0 < UInt64.word)).mpr value.toNat_lt
      have hquot : value.toNat * UInt64.word / p < UInt64.word :=
        Nat.div_lt_of_lt_mul hproduct
      exact UInt64.toNat_ofNat_of_lt' (by
        simpa [UInt64.word, UInt64.size] using hquot) }

/-- The Shoup quotient fits in one word and is stored without wraparound. -/
@[simp] theorem precon_toNat {p : Nat} [Bounds p] (value : ZMod64 p) :
    (ofValue value).precon.toNat = value.toNat * UInt64.word / p := by
  exact (ofValue value).precon_eq

end NttTwiddle

/-- A reusable radix-two NTT plan. -/
structure NttPlan (p n : Nat) [Bounds p] [PrimeModulus p] where
  /-- The requested transform length is a power of two. -/
  length_pow_two : ∃ k, n = 2 ^ k
  /-- The transform length divides the order of the prime field's unit group. -/
  length_dvd : n ∣ p - 1
  /-- Primitive transform root. -/
  root : ZMod64 p
  /-- The root has exact power-of-two order `n`. -/
  root_order : ExactOrder root n
  /-- Inverse transform root. -/
  invRoot : ZMod64 p
  /-- The stored inverse root is the multiplicative inverse of `root`. -/
  invRoot_eq : invRoot = root⁻¹
  /-- Inverse of the transform length modulo `p`. -/
  invLength : ZMod64 p
  /-- The stored length inverse is the inverse of the natural cast of `n`. -/
  invLength_eq : invLength = (n : ZMod64 p)⁻¹
  /-- Reusable forward root powers and Shoup preconditioners. -/
  forwardTwiddles : Array (NttTwiddle p)
  /-- There is one forward power for every exponent below `n`. -/
  forward_size : forwardTwiddles.size = n
  /-- Every stored forward twiddle is the corresponding root power. -/
  forward_value : ∀ (i : Nat) (hi : i < n),
    (forwardTwiddles[i]'(by simpa [forward_size] using hi)).value = root ^ i
  /-- Reusable inverse-root powers and Shoup preconditioners. -/
  inverseTwiddles : Array (NttTwiddle p)
  /-- There is one inverse power for every exponent below `n`. -/
  inverse_size : inverseTwiddles.size = n
  /-- Every stored inverse twiddle is the corresponding inverse-root power. -/
  inverse_value : ∀ (i : Nat) (hi : i < n),
    (inverseTwiddles[i]'(by simpa [inverse_size] using hi)).value = invRoot ^ i

namespace NttPlan

/-- Everything checked by NTT plan construction. -/
@[expose] def Valid {p : Nat} [Bounds p] (n : Nat) (root : ZMod64 p) : Prop :=
  IsPowTwo n ∧ n ∣ p - 1 ∧ ExactOrder root n

instance {p n : Nat} [Bounds p] (root : ZMod64 p) : Decidable (Valid n root) :=
  inferInstanceAs
    (Decidable (IsPowTwo n ∧ n ∣ p - 1 ∧ ExactOrder root n))

/-- Table of the first `n` powers of a root, with Shoup preconditioners. -/
def twiddles {p : Nat} [Bounds p] (root : ZMod64 p) (n : Nat) :
    Array (NttTwiddle p) :=
  Array.ofFn fun i : Fin n => NttTwiddle.ofValue (root ^ i.val)

/-- The twiddle table has the requested length. -/
@[simp] theorem twiddles_size {p : Nat} [Bounds p]
    (root : ZMod64 p) (n : Nat) :
    (twiddles root n).size = n := by
  simp [twiddles]

/-- Looking up a twiddle exposes the corresponding root power. -/
@[simp] theorem twiddles_value {p : Nat} [Bounds p]
    (root : ZMod64 p) (n : Nat) (i : Nat) (hi : i < n) :
    ((twiddles root n)[i]'(by simpa using hi)).value = root ^ i := by
  simp [twiddles, NttTwiddle.ofValue]

/-- Validate a requested root and build all reusable transform data. -/
def build? {p n : Nat} [Bounds p] [PrimeModulus p]
    (root : ZMod64 p) : Option (NttPlan p n) :=
  if h : Valid n root then
    let invRoot := root⁻¹
    some
      { length_pow_two := ⟨n.log2, h.1.2⟩
        length_dvd := h.2.1
        root
        root_order := h.2.2
        invRoot
        invRoot_eq := rfl
        invLength := (n : ZMod64 p)⁻¹
        invLength_eq := rfl
        forwardTwiddles := twiddles root n
        forward_size := twiddles_size root n
        forward_value := twiddles_value root n
        inverseTwiddles := twiddles invRoot n
        inverse_size := twiddles_size invRoot n
        inverse_value := twiddles_value invRoot n }
  else
    none

/-- Plan construction succeeds exactly when the requested length and root
pass all validation checks. -/
theorem build?_isSome {p n : Nat} [Bounds p] [PrimeModulus p]
    (root : ZMod64 p) :
    (build? (n := n) root).isSome = decide (Valid n root) := by
  unfold build?
  split <;> simp_all

/-- A successful plan records the supplied root. -/
theorem build?_root {p n : Nat} [Bounds p] [PrimeModulus p]
    {root : ZMod64 p} {plan : NttPlan p n}
    (h : build? (n := n) root = some plan) :
    plan.root = root := by
  unfold build? at h
  split at h <;> try contradiction
  cases h
  rfl

/-- A successful plan exposes the validated inverse root. -/
theorem invRoot_mul_root {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (hroot : plan.root ≠ 0) :
    plan.invRoot * plan.root = 1 := by
  rw [plan.invRoot_eq]
  exact inv_mul_eq_one_of_ne_zero hroot

end NttPlan

end ZMod64

end Hex
