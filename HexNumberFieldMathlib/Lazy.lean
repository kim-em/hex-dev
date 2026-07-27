/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Exact

public section

/-!
# Semantics of lazy and canonical arithmetic

Each checked lazy operation has a soundness theorem and a bounded-search
completeness theorem.  The total headline then follows for the executable
fallback wrapper, and exactification transfers it to canonical algebraic
numbers.
-/

namespace Hex

namespace AlgebraicRoot

/-- Reflection computes complex negation. -/
theorem neg_toComplex (a : AlgebraicRoot) :
    a.neg.toComplex = -a.toComplex := by
  sorry

/-- A certified lazy sum denotes the sum of its inputs. -/
theorem add?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.add? b = some c) :
    c.toComplex = a.toComplex + b.toComplex := by
  sorry

/-- The bounded lazy addition search always finds its certificate. -/
theorem add?_isSome (a b : AlgebraicRoot) :
    (a.add? b).isSome := by
  sorry

/-- Total lazy addition computes complex addition. -/
theorem add_toComplex (a b : AlgebraicRoot) :
    (a.add b).toComplex = a.toComplex + b.toComplex := by
  cases h : a.add? b with
  | none =>
      have hsome := add?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.add, h] using add?_sound a b h

/-- A certified lazy difference denotes the difference of its inputs. -/
theorem sub?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.sub? b = some c) :
    c.toComplex = a.toComplex - b.toComplex := by
  have hsum : c.toComplex = a.toComplex + b.neg.toComplex :=
    add?_sound a b.neg h
  rw [neg_toComplex] at hsum
  exact hsum

/-- The bounded lazy subtraction search always finds its certificate. -/
theorem sub?_isSome (a b : AlgebraicRoot) :
    (a.sub? b).isSome := by
  exact add?_isSome a b.neg

/-- Total lazy subtraction computes complex subtraction. -/
theorem sub_toComplex (a b : AlgebraicRoot) :
    (a.sub b).toComplex = a.toComplex - b.toComplex := by
  cases h : a.sub? b with
  | none =>
      have hsome := sub?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.sub, h] using sub?_sound a b h

/-- A certified lazy product denotes the product of its inputs. -/
theorem mul?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.mul? b = some c) :
    c.toComplex = a.toComplex * b.toComplex := by
  sorry

/-- The bounded lazy multiplication search always finds its certificate. -/
theorem mul?_isSome (a b : AlgebraicRoot) :
    (a.mul? b).isSome := by
  sorry

/-- Total lazy multiplication computes complex multiplication. -/
theorem mul_toComplex (a b : AlgebraicRoot) :
    (a.mul b).toComplex = a.toComplex * b.toComplex := by
  cases h : a.mul? b with
  | none =>
      have hsome := mul?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.mul, h] using mul?_sound a b h

/-- A certified lazy inverse denotes the reciprocal of its input, including
the executable convention `0⁻¹ = 0`. -/
theorem inv?_sound (a : AlgebraicRoot) {b : AlgebraicRoot}
    (h : a.inv? = some b) :
    b.toComplex = a.toComplex⁻¹ := by
  sorry

/-- The bounded lazy inverse search always finds its certificate. -/
theorem inv?_isSome (a : AlgebraicRoot) :
    a.inv?.isSome := by
  sorry

/-- Total lazy inversion computes complex inversion. -/
theorem inv_toComplex (a : AlgebraicRoot) :
    a.inv.toComplex = a.toComplex⁻¹ := by
  cases h : a.inv? with
  | none =>
      have hsome := inv?_isSome a
      simp [h] at hsome
  | some b =>
      simpa [AlgebraicRoot.inv, h] using inv?_sound a h

/-- A certified lazy quotient denotes the quotient of its inputs. -/
theorem div?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.div? b = some c) :
    c.toComplex = a.toComplex / b.toComplex := by
  cases hb : b.inv? with
  | none => simp [AlgebraicRoot.div?, hb] at h
  | some bInv =>
      have hmul : a.mul? bInv = some c := by
        simpa [AlgebraicRoot.div?, hb] using h
      rw [mul?_sound a bInv hmul, inv?_sound b hb]
      rfl

/-- The bounded lazy division search always finds its certificate. -/
theorem div?_isSome (a b : AlgebraicRoot) :
    (a.div? b).isSome := by
  cases hb : b.inv? with
  | none =>
      have hsome := inv?_isSome b
      simp [hb] at hsome
  | some bInv =>
      simpa [AlgebraicRoot.div?, hb] using mul?_isSome a bInv

/-- Total lazy division computes complex division. -/
theorem div_toComplex (a b : AlgebraicRoot) :
    (a.div b).toComplex = a.toComplex / b.toComplex := by
  cases h : a.div? b with
  | none =>
      have hsome := div?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.div, h] using div?_sound a b h

end AlgebraicRoot

namespace AlgebraicNumber

/-- Canonical zero denotes complex zero. -/
theorem zero_toComplex : (0 : AlgebraicNumber).toComplex = 0 := by
  sorry

/-- Canonical addition computes complex addition. -/
theorem add_toComplex (a b : AlgebraicNumber) :
    (a + b).toComplex = a.toComplex + b.toComplex := by
  change (a.toRoot.add b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.add_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical subtraction computes complex subtraction. -/
theorem sub_toComplex (a b : AlgebraicNumber) :
    (a - b).toComplex = a.toComplex - b.toComplex := by
  change (a.toRoot.sub b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.sub_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical multiplication computes complex multiplication. -/
theorem mul_toComplex (a b : AlgebraicNumber) :
    (a * b).toComplex = a.toComplex * b.toComplex := by
  change (a.toRoot.mul b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.mul_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical negation computes complex negation. -/
theorem neg_toComplex (a : AlgebraicNumber) :
    (-a).toComplex = -a.toComplex := by
  change a.toRoot.neg.exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.neg_toComplex,
    AlgebraicNumber.toRoot_toComplex]

/-- Canonical inversion computes complex inversion. -/
theorem inv_toComplex (a : AlgebraicNumber) :
    a⁻¹.toComplex = a.toComplex⁻¹ := by
  change a.toRoot.inv.exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.inv_toComplex,
    AlgebraicNumber.toRoot_toComplex]

/-- Canonical division computes complex division. -/
theorem div_toComplex (a b : AlgebraicNumber) :
    (a / b).toComplex = a.toComplex / b.toComplex := by
  change (a.toRoot.div b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.div_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

end AlgebraicNumber

end Hex
