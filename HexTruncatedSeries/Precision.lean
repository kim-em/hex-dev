/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Classes

public section

/-!
Precision-changing operations for fixed-length truncated series.

Truncation and the two genuine precision losses (`divXPow?` and `deriv`)
record their output precision in the type.  Zero extension is deliberately
only a coefficient operation: it is not multiplicative.  `derivPad` retains
the input precision for Newton reversion while explicitly zeroing the
unavailable top derivative coefficient.
-/

namespace Hex.TSeries

universe u

attribute [local instance] Lean.Grind.Semiring.natCast

variable {R : Type u} {n m : Nat}

/-- Discard coefficients at index `m` and above. -/
@[expose]
def truncate [Zero R] (a : TSeries R n) (m : Nat) (_h : m ≤ n) : TSeries R m :=
  ofFn a.coeff

/-- Pad a series with zero coefficients to a larger precision. -/
@[expose]
def extend [Zero R] (a : TSeries R n) (m : Nat) (_h : n ≤ m) : TSeries R m :=
  ofFn a.coeff

/-- Multiply by `x^k`, discarding coefficients shifted beyond the precision. -/
@[expose]
def mulXPow [Zero R] (a : TSeries R n) (k : Nat) : TSeries R n :=
  ofFn fun i => if k ≤ i then a.coeff (i - k) else 0

/-- Whether every coefficient below `m` is zero. -/
@[expose]
def allZeroBelow [Zero R] [DecidableEq R] (a : TSeries R n) (m : Nat) : Bool :=
  (List.range m).all fun i => decide (a.coeff i = 0)

/-- Divide by `x^k` when every discarded low coefficient is zero. -/
@[expose]
def divXPow? [Zero R] [DecidableEq R] (a : TSeries R n) (k : Nat) :
    Option (TSeries R (n - k)) :=
  if allZeroBelow a (min k n) then
    some (ofFn fun i => a.coeff (i + k))
  else
    none

/-- The first represented nonzero coefficient, if one exists. -/
@[expose]
def valuation? [Zero R] [DecidableEq R] (a : TSeries R n) : Option Nat :=
  (List.range n).find? fun i => decide (a.coeff i ≠ 0)

/-- The formal derivative, losing one coefficient of precision. -/
@[expose]
def deriv [Lean.Grind.CommRing R] (a : TSeries R n) : TSeries R (n - 1) :=
  ofFn fun i => ((i + 1 : Nat) : R) * a.coeff (i + 1)

/-- The derivative retained at the input precision, with the unavailable top
coefficient set to zero. -/
@[expose]
def derivPad [Lean.Grind.CommRing R] (a : TSeries R n) : TSeries R n :=
  ofFn fun i =>
    if i + 1 < n then ((i + 1 : Nat) : R) * a.coeff (i + 1) else 0

/-- Formal integration with zero constant coefficient. -/
@[expose]
def integrate [Lean.Grind.CommRing R] [NatInverses R n]
    (a : TSeries R n) : TSeries R (n + 1) :=
  ofFn fun i =>
    if i = 0 then 0 else
      NatInverses.invNat (R := R) (m := n) i * a.coeff (i - 1)

@[simp, grind =]
theorem coeff_truncate [Lean.Grind.CommRing R] (a : TSeries R n)
    (h : m ≤ n) (i : Nat) (hi : i < m) :
    (a.truncate m h).coeff i = a.coeff i :=
  coeff_ofFn _ i hi

@[simp, grind =]
theorem coeff_extend [Lean.Grind.CommRing R] (a : TSeries R n)
    (h : n ≤ m) (i : Nat) (hi : i < m) :
    (a.extend m h).coeff i = a.coeff i :=
  coeff_ofFn _ i hi

/-- Truncating a zero extension back to its source precision is the identity. -/
@[simp]
theorem truncate_extend [Lean.Grind.CommRing R] (a : TSeries R n)
    (h : n ≤ m) : (a.extend m h).truncate n h = a := by
  apply ext
  intro i hi
  rw [coeff_truncate _ h i hi, coeff_extend a h i (by omega)]

@[simp, grind =]
theorem coeff_mulXPow [Lean.Grind.CommRing R] (a : TSeries R n)
    (k i : Nat) (hi : i < n) :
    (a.mulXPow k).coeff i = if k ≤ i then a.coeff (i - k) else 0 :=
  coeff_ofFn _ i hi

/-- A successful division by `x^k` exposes the shifted coefficients. -/
theorem coeff_divXPow?_eq_some [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) (k : Nat) {b : TSeries R (n - k)}
    (h : divXPow? a k = some b) (i : Nat) (hi : i < n - k) :
    b.coeff i = a.coeff (i + k) := by
  unfold divXPow? at h
  split at h
  · injection h with hb
    subst b
    exact coeff_ofFn _ i hi
  · simp at h

@[simp, grind =]
theorem coeff_deriv [Lean.Grind.CommRing R] (a : TSeries R n)
    (i : Nat) (hi : i < n - 1) :
    a.deriv.coeff i = ((i + 1 : Nat) : R) * a.coeff (i + 1) :=
  coeff_ofFn _ i hi

@[simp, grind =]
theorem coeff_derivPad [Lean.Grind.CommRing R] (a : TSeries R n)
    (i : Nat) (hi : i < n) :
    a.derivPad.coeff i =
      if i + 1 < n then ((i + 1 : Nat) : R) * a.coeff (i + 1) else 0 :=
  coeff_ofFn _ i hi

@[simp, grind =]
theorem coeff_integrate [Lean.Grind.CommRing R] [NatInverses R n]
    (a : TSeries R n) (i : Nat) (hi : i < n + 1) :
    (integrate a).coeff i =
      if i = 0 then 0 else
        NatInverses.invNat (R := R) (m := n) i * a.coeff (i - 1) :=
  coeff_ofFn _ i hi

/-- Integration is independent of which lawful natural-inverse dictionary is
in scope. -/
theorem integrate_congr [Lean.Grind.CommRing R] (a : TSeries R n)
    (h₁ h₂ : NatInverses R n) :
    @integrate R n _ h₁ a = @integrate R n _ h₂ a := by
  apply ext
  intro i hi
  rw [@coeff_integrate R n _ h₁ a i hi,
    @coeff_integrate R n _ h₂ a i hi]
  by_cases hi0 : i = 0
  · simp [hi0]
  · rw [if_neg hi0, if_neg hi0,
      NatInverses.invNat_unique h₁ h₂ i (by omega) (by omega)]

/-- Differentiation cancels zero-constant integration at every represented
coefficient. -/
@[simp]
theorem deriv_integrate [Lean.Grind.CommRing R] [NatInverses R n]
    (a : TSeries R n) : (integrate a).deriv = a := by
  apply ext
  intro i hi
  rw [coeff_deriv (integrate a) i (by omega),
    coeff_integrate a (i + 1) (by omega)]
  simp only [show i + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
  have hinv := NatInverses.invNat_eq (R := R) (m := n) (i + 1)
    (by omega) (by omega)
  rw [Lean.Grind.Semiring.natCast_succ] at hinv
  rw [Lean.Grind.Semiring.natCast_succ, ← Lean.Grind.Semiring.mul_assoc,
    hinv, Lean.Grind.Semiring.one_mul]

private theorem foldRange_succ [Lean.Grind.CommRing R]
    (A : Nat → R) (m : Nat) :
    (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl (fun acc i => acc + A i) 0 + A m := by
  rw [List.range_succ, List.foldl_append]
  simp

private theorem weightedFold_aux [Lean.Grind.CommRing R]
    (A : Nat → R) (m : Nat) :
    ((m : Nat) : R) *
        (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl
          (fun acc i => acc + ((i + 1 : Nat) : R) * A (i + 1)) 0 +
        (List.range m).foldl
          (fun acc i => acc + ((m - i : Nat) : R) * A i) 0 := by
  induction m with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      rw [Lean.Grind.Semiring.natCast_zero]
      grind
  | succ m ih =>
      rw [foldRange_succ A (m + 1)]
      have hsplit :
          (((m + 1 : Nat) : R) *
              ((List.range (m + 1)).foldl (fun acc i => acc + A i) 0 + A (m + 1))) =
            ((m : Nat) : R) *
                (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              ((m + 1 : Nat) : R) * A (m + 1) := by
        rw [Lean.Grind.Semiring.natCast_succ]
        grind
      rw [hsplit, ih]
      rw [foldRange_succ
        (fun i => ((i + 1 : Nat) : R) * A (i + 1)) m]
      rw [foldRange_succ
        (fun i => ((m + 1 - i : Nat) : R) * A i) m]
      rw [foldRange_succ A m]
      have htail : ((m + 1 - m : Nat) : R) * A m = A m := by
        have hsub : m + 1 - m = 1 := by omega
        rw [hsub, Lean.Grind.Semiring.natCast_one]
        grind
      rw [htail]
      have hcoeff :
          (List.range m).foldl
              (fun acc i => acc + ((m - i : Nat) : R) * A i) 0 +
            (List.range m).foldl (fun acc i => acc + A i) 0 =
          (List.range m).foldl
              (fun acc i => acc + ((m + 1 - i : Nat) : R) * A i) 0 := by
        rw [← List.foldl_add_add]
        apply List.foldl_add_congr
        intro i hi
        have hi' : i < m := List.mem_range.mp hi
        have hnat : ((m + 1 - i : Nat) : R) =
            ((m - i : Nat) : R) + 1 := by
          have h : m + 1 - i = m - i + 1 := by omega
          rw [h, Lean.Grind.Semiring.natCast_succ]
        rw [hnat]
        grind
      rw [← hcoeff]
      grind

private theorem weightedFold [Lean.Grind.CommRing R]
    (A : Nat → R) (q : Nat) :
    ((q + 1 : Nat) : R) *
        (List.range (q + 2)).foldl (fun acc i => acc + A i) 0 =
      (List.range (q + 1)).foldl
          (fun acc i => acc + ((i + 1 : Nat) : R) * A (i + 1)) 0 +
        (List.range (q + 1)).foldl
          (fun acc i => acc + ((q - i + 1 : Nat) : R) * A i) 0 := by
  have h := weightedFold_aux A (q + 1)
  rw [show q + 1 + 1 = q + 2 by omega] at h
  exact h.trans (by
    congr 1
    apply List.foldl_add_congr
    intro i hi
    have hi' : i < q + 1 := List.mem_range.mp hi
    have hidx : q + 1 - i = q - i + 1 := by omega
    rw [hidx])

/-- Formal differentiation obeys the product rule after both undifferentiated
factors are truncated to the derivative's precision. -/
theorem deriv_mul [Lean.Grind.CommRing R] (a b : TSeries R n) :
    (a * b).deriv =
      a.deriv * b.truncate (n - 1) (Nat.sub_le n 1) +
        a.truncate (n - 1) (Nat.sub_le n 1) * b.deriv := by
  apply ext
  intro i hi
  rw [coeff_deriv (a * b) i hi, coeff_mul a b (i + 1) (by omega),
    coeff_add _ _ i hi, coeff_mul _ _ i hi, coeff_mul _ _ i hi]
  unfold convCoeff
  rw [weightedFold (fun j => a.coeff j * b.coeff (i + 1 - j)) i]
  congr 1
  · apply List.foldl_add_congr
    intro j hj
    have hj' : j < i + 1 := List.mem_range.mp hj
    rw [coeff_deriv a j (by omega),
      coeff_truncate b (Nat.sub_le n 1) (i - j) (by omega)]
    have hidx : i + 1 - (j + 1) = i - j := by omega
    rw [hidx]
    grind
  · apply List.foldl_add_congr
    intro j hj
    have hj' : j < i + 1 := List.mem_range.mp hj
    rw [coeff_truncate a (Nat.sub_le n 1) j (by omega),
      coeff_deriv b (i - j) (by omega)]
    have hidx : i - j + 1 = i + 1 - j := by omega
    rw [hidx]
    grind

/-- Two truncated series with the same constant coefficient and derivative
are equal when all represented positive naturals are invertible. -/
theorem eq_of_deriv [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    {a b : TSeries R n} (h0 : a.coeff 0 = b.coeff 0)
    (hderiv : a.deriv = b.deriv) : a = b := by
  apply ext
  intro i hi
  cases i with
  | zero => exact h0
  | succ i =>
      have hin : i < n - 1 := by omega
      have hd := congrArg (fun z : TSeries R (n - 1) => z.coeff i) hderiv
      rw [coeff_deriv a i hin, coeff_deriv b i hin] at hd
      have hu := NatInverses.invNat_eq (R := R) (m := n - 1) (i + 1)
        (by omega) (by omega)
      calc
        a.coeff (i + 1) = 1 * a.coeff (i + 1) := by grind
        _ = (((i + 1 : Nat) : R) *
              NatInverses.invNat (R := R) (m := n - 1) (i + 1)) *
              a.coeff (i + 1) := by rw [hu]
        _ = NatInverses.invNat (R := R) (m := n - 1) (i + 1) *
              (((i + 1 : Nat) : R) * a.coeff (i + 1)) := by grind
        _ = NatInverses.invNat (R := R) (m := n - 1) (i + 1) *
              (((i + 1 : Nat) : R) * b.coeff (i + 1)) := by rw [hd]
        _ = (((i + 1 : Nat) : R) *
              NatInverses.invNat (R := R) (m := n - 1) (i + 1)) *
              b.coeff (i + 1) := by grind
        _ = b.coeff (i + 1) := by rw [hu]; grind

/-- Truncation preserves multiplication. -/
theorem truncate_mul [Lean.Grind.CommRing R] (a b : TSeries R n)
    (h : m ≤ n) :
    (a * b).truncate m h = a.truncate m h * b.truncate m h := by
  apply ext
  intro i hi
  rw [coeff_truncate _ h i hi, coeff_mul a b i (by omega),
    coeff_mul (a.truncate m h) (b.truncate m h) i hi]
  unfold convCoeff
  apply List.foldl_add_congr
  intro j hj
  have hj' : j ≤ i := by
    have := List.mem_range.mp hj
    omega
  rw [coeff_truncate a h j (by omega), coeff_truncate b h (i - j) (by omega)]

/-! Prefix agreement packages the precision-local reasoning used by all
bounded algorithms. -/

/-- Two series have the same represented coefficients below `p`. -/
@[expose]
def Agree [Zero R] (p : Nat) (a b : TSeries R n) : Prop :=
  ∀ i, i < n → i < p → a.coeff i = b.coeff i

namespace Agree

theorem refl [Zero R] (p : Nat) (a : TSeries R n) : Agree p a a := by
  intro _ _ _
  rfl

theorem symm [Zero R] {p : Nat} {a b : TSeries R n}
    (h : Agree p a b) : Agree p b a := by
  intro i hi hip
  exact (h i hi hip).symm

theorem trans [Zero R] {p : Nat} {a b c : TSeries R n}
    (hab : Agree p a b) (hbc : Agree p b c) : Agree p a c := by
  intro i hi hip
  exact (hab i hi hip).trans (hbc i hi hip)

theorem mono [Zero R] {p q : Nat} {a b : TSeries R n}
    (h : Agree p a b) (hpq : q ≤ p) : Agree q a b := by
  intro i hi hiq
  exact h i hi (Nat.lt_of_lt_of_le hiq hpq)

theorem full [Zero R] {p : Nat} {a b : TSeries R n}
    (h : Agree p a b) (hnp : n ≤ p) : a = b := by
  apply ext
  intro i hi
  exact h i hi (Nat.lt_of_lt_of_le hi hnp)

theorem add [Lean.Grind.CommRing R] {p : Nat} {a a' b b' : TSeries R n}
    (ha : Agree p a a') (hb : Agree p b b') : Agree p (a + b) (a' + b') := by
  intro i hi hip
  rw [coeff_add a b i hi, coeff_add a' b' i hi, ha i hi hip, hb i hi hip]

theorem neg [Lean.Grind.CommRing R] {p : Nat} {a a' : TSeries R n}
    (ha : Agree p a a') : Agree p (-a) (-a') := by
  intro i hi hip
  rw [coeff_neg a i hi, coeff_neg a' i hi, ha i hi hip]

theorem sub [Lean.Grind.CommRing R] {p : Nat} {a a' b b' : TSeries R n}
    (ha : Agree p a a') (hb : Agree p b b') : Agree p (a - b) (a' - b') := by
  intro i hi hip
  rw [coeff_sub a b i hi, coeff_sub a' b' i hi, ha i hi hip, hb i hi hip]

theorem ofSub [Lean.Grind.CommRing R] {p : Nat} {a b : TSeries R n}
    (h : Agree p (a - b) 0) : Agree p a b := by
  intro i hi hip
  have hz := h i hi hip
  rw [coeff_sub a b i hi, coeff_zero] at hz
  grind

theorem mul [Lean.Grind.CommRing R] {p : Nat} {a a' b b' : TSeries R n}
    (ha : Agree p a a') (hb : Agree p b b') : Agree p (a * b) (a' * b') := by
  intro i hi hip
  rw [coeff_mul a b i hi, coeff_mul a' b' i hi]
  unfold convCoeff
  apply List.foldl_add_congr
  intro j hj
  have hj' : j ≤ i := by
    have := List.mem_range.mp hj
    omega
  rw [ha j (by omega) (by omega), hb (i - j) (by omega) (by omega)]

theorem pow [Lean.Grind.CommRing R] {p : Nat} {a b : TSeries R n}
    (h : Agree p a b) (k : Nat) : Agree p (a ^ k) (b ^ k) := by
  induction k with
  | zero =>
      rw [Hex.TSeries.pow_zero, Hex.TSeries.pow_zero]
      exact refl p (1 : TSeries R n)
  | succ k ih =>
      rw [Hex.TSeries.pow_succ, Hex.TSeries.pow_succ]
      exact mul ih h

/-- A bounded product agrees with the ordinary product throughout its work
prefix. -/
theorem mulUpTo [Lean.Grind.CommRing R] (p : Nat) (a b : TSeries R n) :
    Agree p (Hex.TSeries.mulUpTo p a b) (a * b) := by
  intro i hi hip
  rw [coeff_mulUpTo p a b i hi, if_pos hip]

@[simp]
theorem mulUpTo_full [Lean.Grind.CommRing R] (a b : TSeries R n) :
    Hex.TSeries.mulUpTo n a b = a * b :=
  full (mulUpTo n a b) (Nat.le_refl n)

/-- Orders add under multiplication: a product of two vanishing prefixes
vanishes through the sum of their lengths. -/
theorem zeroMul [Lean.Grind.CommRing R] {p q : Nat} {a b : TSeries R n}
    (ha : Agree p a 0) (hb : Agree q b 0) : Agree (p + q) (a * b) 0 := by
  intro i hi hipq
  rw [coeff_mul a b i hi, coeff_zero]
  unfold convCoeff
  apply List.foldl_add_eq_self
  intro j hj
  have hj' : j ≤ i := by
    have := List.mem_range.mp hj
    omega
  by_cases hjp : j < p
  · rw [ha j (by omega) hjp, coeff_zero]
    grind
  · have hiq : i - j < q := by omega
    rw [hb (i - j) (by omega) hiq, coeff_zero]
    grind

end Agree

end Hex.TSeries
