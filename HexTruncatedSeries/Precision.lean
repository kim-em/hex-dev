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

/-- Truncation preserves every coefficient in the retained prefix. -/
@[simp, grind =]
theorem coeff_truncate [Lean.Grind.CommRing R] (a : TSeries R n)
    (h : m ≤ n) (i : Nat) (hi : i < m) :
    (a.truncate m h).coeff i = a.coeff i :=
  coeff_ofFn _ i hi

/-- Zero extension preserves represented coefficients and reads zero above
the source precision through total coefficient access. -/
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

/-- Truncation preserves zero. -/
@[simp]
theorem truncate_zero [Lean.Grind.CommRing R] (h : m ≤ n) :
    (0 : TSeries R n).truncate m h = 0 := by
  apply ext
  intro i hi
  rw [coeff_truncate _ h i hi, coeff_zero, coeff_zero]

/-- Truncation preserves one. -/
@[simp]
theorem truncate_one [Lean.Grind.CommRing R] (h : m ≤ n) :
    (1 : TSeries R n).truncate m h = 1 := by
  apply ext
  intro i hi
  rw [coeff_truncate _ h i hi, coeff_one i (by omega), coeff_one i hi]

/-- Truncation preserves addition. -/
@[simp]
theorem truncate_add [Lean.Grind.CommRing R] (a b : TSeries R n)
    (h : m ≤ n) :
    (a + b).truncate m h = a.truncate m h + b.truncate m h := by
  apply ext
  intro i hi
  rw [coeff_truncate _ h i hi, coeff_add a b i (by omega),
    coeff_add _ _ i hi, coeff_truncate a h i hi, coeff_truncate b h i hi]

/-- Truncation preserves negation. -/
@[simp]
theorem truncate_neg [Lean.Grind.CommRing R] (a : TSeries R n)
    (h : m ≤ n) :
    (-a).truncate m h = -(a.truncate m h) := by
  apply ext
  intro i hi
  rw [coeff_truncate _ h i hi, coeff_neg a i (by omega),
    coeff_neg _ i hi, coeff_truncate a h i hi]

/-- Truncation preserves subtraction. -/
@[simp]
theorem truncate_sub [Lean.Grind.CommRing R] (a b : TSeries R n)
    (h : m ≤ n) :
    (a - b).truncate m h = a.truncate m h - b.truncate m h := by
  apply ext
  intro i hi
  rw [coeff_truncate _ h i hi, coeff_sub a b i (by omega),
    coeff_sub _ _ i hi, coeff_truncate a h i hi, coeff_truncate b h i hi]

/-- Multiplication by `x^k` shifts coefficients upward by `k`. -/
@[simp, grind =]
theorem coeff_mulXPow [Lean.Grind.CommRing R] (a : TSeries R n)
    (k i : Nat) (hi : i < n) :
    (a.mulXPow k).coeff i = if k ≤ i then a.coeff (i - k) else 0 :=
  coeff_ofFn _ i hi

/-- The zero-prefix test succeeds exactly when every tested coefficient
vanishes. -/
theorem allZeroBelow_eq_true [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) (m : Nat) :
    allZeroBelow a m = true ↔ ∀ i, i < m → a.coeff i = 0 := by
  simp [allZeroBelow]

/-- The zero-prefix test fails exactly when it encounters a nonzero
coefficient. -/
theorem allZeroBelow_eq_false [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) (m : Nat) :
    allZeroBelow a m = false ↔ ∃ i, i < m ∧ a.coeff i ≠ 0 := by
  simp [allZeroBelow]

/-- Division by `x^k` succeeds exactly when every discarded represented
coefficient is zero. -/
theorem divXPow?_isSome_iff [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) (k : Nat) :
    (divXPow? a k).isSome = true ↔
      ∀ i, i < min k n → a.coeff i = 0 := by
  unfold divXPow?
  split <;> rename_i h
  · exact ⟨fun _ => (allZeroBelow_eq_true a (min k n)).mp h,
      fun _ => rfl⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro hz
    exact h ((allZeroBelow_eq_true a (min k n)).mpr hz)

/-- Division by `x^k` fails exactly when a discarded represented coefficient
is nonzero. -/
theorem divXPow?_eq_none_iff [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) (k : Nat) :
    divXPow? a k = none ↔
      ∃ i, i < min k n ∧ a.coeff i ≠ 0 := by
  unfold divXPow?
  split <;> rename_i h
  · simp only [reduceCtorEq, false_iff]
    rintro ⟨i, hi, hne⟩
    exact hne ((allZeroBelow_eq_true a (min k n)).mp h i hi)
  · simp only [true_iff]
    have hf : allZeroBelow a (min k n) = false := by simpa using h
    exact (allZeroBelow_eq_false a (min k n)).mp hf

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

/-- The complete characterization of a successful division by `x^k`. -/
theorem divXPow?_eq_some_iff [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) (k : Nat) (b : TSeries R (n - k)) :
    divXPow? a k = some b ↔
      (∀ i, i < min k n → a.coeff i = 0) ∧
        ∀ i, i < n - k → b.coeff i = a.coeff (i + k) := by
  constructor
  · intro h
    have hsome : (divXPow? a k).isSome = true := by simp [h]
    exact ⟨(divXPow?_isSome_iff a k).mp hsome,
      coeff_divXPow?_eq_some a k h⟩
  · rintro ⟨hz, hc⟩
    unfold divXPow?
    rw [ite_eq_left ((allZeroBelow_eq_true a (min k n)).mpr hz)]
    congr 1
    apply ext
    intro i hi
    rw [coeff_ofFn _ i hi]
    exact (hc i hi).symm

/-- Multiplying by `x^k` and then dividing recovers the represented prefix of
the input. -/
@[simp]
theorem divXPow?_mulXPow [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) (k : Nat) :
    divXPow? (a.mulXPow k) k =
      some (a.truncate (n - k) (Nat.sub_le n k)) := by
  apply (divXPow?_eq_some_iff _ _ _).mpr
  constructor
  · intro i hi
    by_cases hin : i < n
    · rw [coeff_mulXPow a k i hin, ite_eq_right (by omega)]
    · rw [coeff]
      split <;> simp_all
  · intro i hi
    rw [coeff_truncate a (Nat.sub_le n k) i hi,
      coeff_mulXPow a k (i + k) (by omega), ite_eq_left (by omega)]
    congr 1
    omega

/-- Extending a successful quotient and multiplying back by `x^k` recovers
the dividend. -/
theorem mulXPow_extend_divXPow?_eq [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) (k : Nat) (b : TSeries R (n - k))
    (h : divXPow? a k = some b) :
    (b.extend n (Nat.sub_le n k)).mulXPow k = a := by
  apply ext
  intro i hi
  rw [coeff_mulXPow _ k i hi]
  by_cases hki : k ≤ i
  · rw [ite_eq_left hki, coeff_extend b (Nat.sub_le n k) (i - k) (by omega),
      coeff_divXPow?_eq_some a k h (i - k) (by omega)]
    congr 1
    omega
  · rw [ite_eq_right hki]
    have hz := (divXPow?_eq_some_iff a k b).mp h |>.1 i (by omega)
    exact hz.symm

/-- A successful valuation search identifies a represented nonzero
coefficient and proves every earlier coefficient zero. -/
theorem valuation?_eq_some_iff [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) (k : Nat) :
    valuation? a = some k ↔
      k < n ∧ a.coeff k ≠ 0 ∧ ∀ i, i < k → a.coeff i = 0 := by
  simp [valuation?, and_left_comm]

/-- A failed valuation search means that every represented coefficient is
zero. -/
theorem valuation?_eq_none_iff [Lean.Grind.CommRing R] [DecidableEq R]
    (a : TSeries R n) :
    valuation? a = none ↔ ∀ i, i < n → a.coeff i = 0 := by
  simp [valuation?]

/-- The valuation search fails exactly on the zero truncated series. -/
@[simp]
theorem valuation?_eq_none_iff_eq_zero [Lean.Grind.CommRing R]
    [DecidableEq R] (a : TSeries R n) :
    valuation? a = none ↔ a = 0 := by
  rw [valuation?_eq_none_iff]
  constructor
  · intro h
    apply ext
    intro i hi
    rw [h i hi, coeff_zero]
  · rintro rfl
    simp

/-- The coefficient selected by a successful valuation search is nonzero. -/
theorem coeff_ne_zero_of_valuation?_eq_some [Lean.Grind.CommRing R]
    [DecidableEq R] (a : TSeries R n) (k : Nat)
    (h : valuation? a = some k) : a.coeff k ≠ 0 :=
  ((valuation?_eq_some_iff a k).mp h).2.1

/-- Every coefficient below a successful valuation is zero. -/
theorem coeff_eq_zero_of_lt_valuation [Lean.Grind.CommRing R]
    [DecidableEq R] (a : TSeries R n) (k i : Nat)
    (h : valuation? a = some k) (hi : i < k) : a.coeff i = 0 :=
  ((valuation?_eq_some_iff a k).mp h).2.2 i hi

/-- Coefficients of the precision-losing formal derivative. -/
@[simp, grind =]
theorem coeff_deriv [Lean.Grind.CommRing R] (a : TSeries R n)
    (i : Nat) (hi : i < n - 1) :
    a.deriv.coeff i = ((i + 1 : Nat) : R) * a.coeff (i + 1) :=
  coeff_ofFn _ i hi

/-- Coefficients of the precision-preserving padded derivative. -/
@[simp, grind =]
theorem coeff_derivPad [Lean.Grind.CommRing R] (a : TSeries R n)
    (i : Nat) (hi : i < n) :
    a.derivPad.coeff i =
      if i + 1 < n then ((i + 1 : Nat) : R) * a.coeff (i + 1) else 0 :=
  coeff_ofFn _ i hi

/-- Coefficients of zero-constant formal integration. -/
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
  · rw [ite_eq_right hi0, ite_eq_right hi0,
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
  simp only [show i + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
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

/-- The precision-preserving derivative is additive. -/
@[simp]
theorem derivPad_add [Lean.Grind.CommRing R] (a b : TSeries R n) :
    (a + b).derivPad = a.derivPad + b.derivPad := by
  apply ext
  intro i hi
  rw [coeff_derivPad (a + b) i hi, coeff_add _ _ i hi,
    coeff_derivPad a i hi, coeff_derivPad b i hi]
  by_cases hnext : i + 1 < n
  · rw [ite_eq_left hnext, ite_eq_left hnext, ite_eq_left hnext,
      coeff_add a b (i + 1) hnext]
    grind
  · rw [ite_eq_right hnext, ite_eq_right hnext, ite_eq_right hnext]
    grind

/-- The precision-preserving derivative kills constant series. -/
@[simp]
theorem derivPad_C [Lean.Grind.CommRing R] (c : R) :
    (C c : TSeries R n).derivPad = 0 := by
  apply ext
  intro i hi
  rw [coeff_derivPad (C c) i hi, coeff_zero]
  by_cases hnext : i + 1 < n
  · rw [ite_eq_left hnext, coeff_C c (i + 1) hnext, ite_eq_right (by omega)]
    grind
  · rw [ite_eq_right hnext]

/-- The precision-preserving derivative kills zero. -/
@[simp]
theorem derivPad_zero [Lean.Grind.CommRing R] :
    (0 : TSeries R n).derivPad = 0 := by
  calc
    (0 : TSeries R n).derivPad = (C (0 : R) : TSeries R n).derivPad := by
      rw [C_zero]
    _ = 0 := derivPad_C (0 : R)

/-- The precision-preserving derivative kills one. -/
@[simp]
theorem derivPad_one [Lean.Grind.CommRing R] :
    (1 : TSeries R n).derivPad = 0 := by
  rw [← C_one]
  exact derivPad_C 1

/-- A constant scalar factors through the precision-preserving derivative. -/
@[simp]
theorem derivPad_C_mul [Lean.Grind.CommRing R] (c : R) (a : TSeries R n) :
    (C c * a).derivPad = C c * a.derivPad := by
  apply ext
  intro i hi
  rw [coeff_derivPad (C c * a) i hi, coeff_C_mul c a.derivPad i hi,
    coeff_derivPad a i hi]
  by_cases hnext : i + 1 < n
  · rw [ite_eq_left hnext, ite_eq_left hnext, coeff_C_mul c a (i + 1) hnext]
    grind
  · rw [ite_eq_right hnext, ite_eq_right hnext]
    grind

/-- The precision-preserving derivative commutes with an additive fold. -/
theorem derivPad_foldl_add [Lean.Grind.CommRing R] {α : Type}
    (xs : List α) (f : α → TSeries R n) (z : TSeries R n) :
    (xs.foldl (fun acc x => acc + f x) z).derivPad =
      xs.foldl (fun acc x => acc + (f x).derivPad) z.derivPad := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, List.foldl_cons, ih, derivPad_add]

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

/-- The product rule for `derivPad` holds through the last coefficient whose
successor is represented. -/
theorem derivPad_mul_agree [Lean.Grind.CommRing R] (a b : TSeries R n) :
    Agree (n - 1) (a * b).derivPad
      (a.derivPad * b + a * b.derivPad) := by
  intro i hi hip
  rw [coeff_derivPad (a * b) i hi, ite_eq_left (by omega),
    coeff_mul a b (i + 1) (by omega), coeff_add _ _ i hi,
    coeff_mul _ _ i hi, coeff_mul _ _ i hi]
  unfold convCoeff
  rw [weightedFold (fun j => a.coeff j * b.coeff (i + 1 - j)) i]
  congr 1
  · apply List.foldl_add_congr
    intro j hj
    have hj' : j < i + 1 := List.mem_range.mp hj
    rw [coeff_derivPad a j (by omega), ite_eq_left (by omega)]
    have hidx : i + 1 - (j + 1) = i - j := by omega
    rw [hidx]
    grind
  · apply List.foldl_add_congr
    intro j hj
    have hj' : j < i + 1 := List.mem_range.mp hj
    rw [coeff_derivPad b (i - j) (by omega), ite_eq_left (by omega)]
    have hidx : i - j + 1 = i + 1 - j := by omega
    rw [hidx]
    grind

/-- The padded derivative of `X` is one throughout the honest derivative
prefix. -/
theorem derivPad_X_agree [Lean.Grind.CommRing R] :
    Agree (n - 1) (derivPad (X : TSeries R n)) 1 := by
  intro i hi hip
  rw [coeff_derivPad X i hi, ite_eq_left (by omega), coeff_X (i + 1) (by omega),
    coeff_one i hi]
  by_cases hi0 : i = 0
  · subst i
    grind
  · simp [hi0]
    grind

namespace Agree

/-- Every series agrees with itself at every precision. -/
theorem refl [Zero R] (p : Nat) (a : TSeries R n) : Agree p a a := by
  intro _ _ _
  rfl

/-- Prefix agreement is symmetric. -/
theorem symm [Zero R] {p : Nat} {a b : TSeries R n}
    (h : Agree p a b) : Agree p b a := by
  intro i hi hip
  exact (h i hi hip).symm

/-- Prefix agreement is transitive. -/
theorem trans [Zero R] {p : Nat} {a b c : TSeries R n}
    (hab : Agree p a b) (hbc : Agree p b c) : Agree p a c := by
  intro i hi hip
  exact (hab i hi hip).trans (hbc i hi hip)

/-- Agreement through a precision implies agreement through every smaller
precision. -/
theorem mono [Zero R] {p q : Nat} {a b : TSeries R n}
    (h : Agree p a b) (hpq : q ≤ p) : Agree q a b := by
  intro i hi hiq
  exact h i hi (Nat.lt_of_lt_of_le hiq hpq)

/-- Agreement through the represented precision implies series equality. -/
theorem full [Zero R] {p : Nat} {a b : TSeries R n}
    (h : Agree p a b) (hnp : n ≤ p) : a = b := by
  apply ext
  intro i hi
  exact h i hi (Nat.lt_of_lt_of_le hi hnp)

/-- Prefix agreement is preserved by addition. -/
theorem add [Lean.Grind.CommRing R] {p : Nat} {a a' b b' : TSeries R n}
    (ha : Agree p a a') (hb : Agree p b b') : Agree p (a + b) (a' + b') := by
  intro i hi hip
  rw [coeff_add a b i hi, coeff_add a' b' i hi, ha i hi hip, hb i hi hip]

/-- Pointwise agreement of summands is preserved by an additive fold. -/
theorem foldl_add [Lean.Grind.CommRing R] {α : Type} {p : Nat}
    (xs : List α) (f g : α → TSeries R n)
    (h : ∀ x, x ∈ xs → Agree p (f x) (g x)) :
    Agree p (xs.foldl (fun acc x => acc + f x) 0)
      (xs.foldl (fun acc x => acc + g x) 0) := by
  induction xs with
  | nil => exact refl p 0
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have htail : ∀ y, y ∈ xs → Agree p (f y) (g y) := by
        intro y hy
        exact h y (List.mem_cons_of_mem x hy)
      have hhead := h x (List.mem_cons_self)
      have go (ys : List α) (z z' : TSeries R n) (hz : Agree p z z')
          (hs : ∀ y, y ∈ ys → Agree p (f y) (g y)) :
          Agree p (ys.foldl (fun acc y => acc + f y) z)
            (ys.foldl (fun acc y => acc + g y) z') := by
        induction ys generalizing z z' with
        | nil => exact hz
        | cons y ys ih =>
            simp only [List.foldl_cons]
            exact ih _ _ (add hz (hs y (List.mem_cons_self)))
              (fun t ht => hs t (List.mem_cons_of_mem y ht))
      exact go xs (0 + f x) (0 + g x) (add (refl p 0) hhead) htail

/-- Prefix agreement is preserved by negation. -/
theorem neg [Lean.Grind.CommRing R] {p : Nat} {a a' : TSeries R n}
    (ha : Agree p a a') : Agree p (-a) (-a') := by
  intro i hi hip
  rw [coeff_neg a i hi, coeff_neg a' i hi, ha i hi hip]

/-- Prefix agreement is preserved by subtraction. -/
theorem sub [Lean.Grind.CommRing R] {p : Nat} {a a' b b' : TSeries R n}
    (ha : Agree p a a') (hb : Agree p b b') : Agree p (a - b) (a' - b') := by
  intro i hi hip
  rw [coeff_sub a b i hi, coeff_sub a' b' i hi, ha i hi hip, hb i hi hip]

/-- If a difference vanishes through a prefix, its terms agree there. -/
theorem ofSub [Lean.Grind.CommRing R] {p : Nat} {a b : TSeries R n}
    (h : Agree p (a - b) 0) : Agree p a b := by
  intro i hi hip
  have hz := h i hi hip
  rw [coeff_sub a b i hi, coeff_zero] at hz
  grind

/-- Prefix agreement is preserved by multiplication. -/
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

/-- Prefix agreement is preserved by natural powers. -/
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
  rw [coeff_mulUpTo p a b i hi, ite_eq_left hip]

/-- Multiplication bounded at the represented precision is ordinary
multiplication. -/
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

/-- The power rule for `derivPad` holds throughout its honest prefix. -/
theorem derivPad_pow_agree [Lean.Grind.CommRing R] (a : TSeries R n)
    (k : Nat) : Agree (n - 1) (a ^ k).derivPad
      (C (((k : Nat) : R)) * a ^ (k - 1) * a.derivPad) := by
  induction k with
  | zero =>
      rw [pow_zero, derivPad_one, Lean.Grind.Semiring.natCast_zero,
        C_zero, zero_mul]
      simp only [zero_mul]
      exact Agree.refl (R := R) (n := n) (n - 1) (0 : TSeries R n)
  | succ k ih =>
      rw [pow_succ]
      have hprod := derivPad_mul_agree (a ^ k) a
      have hrule := Agree.add
        (Agree.mul ih (Agree.refl (n - 1) a))
        (Agree.refl (n - 1) (a ^ k * a.derivPad))
      have halg :
          (C (((k : Nat) : R)) * a ^ (k - 1) * a.derivPad) * a +
              a ^ k * a.derivPad =
            C ((((k + 1 : Nat) : R))) * a ^ (k + 1 - 1) * a.derivPad := by
        cases k with
        | zero =>
            rw [Lean.Grind.Semiring.natCast_zero,
              Lean.Grind.Semiring.natCast_one, C_zero, C_one]
            rw [show (1 : Nat) - 1 = 0 by decide, pow_zero]
            simp only [zero_mul, one_mul]
            grind
        | succ k =>
            have hcast : ((((k + 2 : Nat) : R))) =
                (((k + 1 : Nat) : R)) + 1 := by
              rw [show k + 2 = (k + 1) + 1 by omega,
                Lean.Grind.Semiring.natCast_succ]
            have hC : (C ((((k + 2 : Nat) : R))) : TSeries R n) =
                C ((((k + 1 : Nat) : R))) + 1 := by
              rw [hcast, C_add, C_one]
            rw [Nat.add_sub_cancel, Nat.succ_sub_one, hC, pow_succ]
            grind
      rw [halg] at hrule
      exact hprod.trans hrule

end Hex.TSeries
