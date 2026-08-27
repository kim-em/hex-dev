/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Plan

public section

/-!
# Cyclic and negacyclic products

The reference kernels fold an ordinary planned product by congruence classes
of exponents. They allocate exactly the requested `n` coefficient slots and
therefore also serve as independent comparators for transform-based plans.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

private def addCyclicCoeff (n : Nat) (p : DensePoly R)
    (acc : Array R) (i : Nat) : Array R :=
  let k := i % n
  acc.set! k (acc.getD k 0 + p.coeff i)

/-- Fold every coefficient into its exponent class modulo `n`, using one
preallocated `n`-slot accumulator. -/
def cyclicCoeffs (n : Nat) (p : DensePoly R) : Array R :=
  (List.range p.size).foldl (addCyclicCoeff n p)
    (Array.replicate n 0)

private def addNegacyclicCoeff (n : Nat) (p : DensePoly R)
    (acc : Array R) (i : Nat) : Array R :=
  let k := i % n
  let value := acc.getD k 0
  if (i / n) % 2 = 0 then
    acc.set! k (value + p.coeff i)
  else
    acc.set! k (value - p.coeff i)

/-- Fold every coefficient modulo `x^n + 1`, alternating the sign after each
block of `n` exponents. -/
def negacyclicCoeffs (n : Nat) (p : DensePoly R) : Array R :=
  (List.range p.size).foldl (addNegacyclicCoeff n p)
    (Array.replicate n 0)

/-- Sum coefficients of `p` whose exponents are congruent to `k` modulo `n`. -/
def cyclicCoeff (n k : Nat) (p : DensePoly R) : R :=
  (cyclicCoeffs n p).getD k 0

/-- Alternating sum of coefficients in one congruence class, implementing
reduction by `x^n = -1`. -/
def negacyclicCoeff (n k : Nat) (p : DensePoly R) : R :=
  (negacyclicCoeffs n p).getD k 0

theorem size_cyclicCoeffs (n : Nat) (p : DensePoly R) :
    (cyclicCoeffs n p).size = n := by
  have aux : ∀ (xs : List Nat) (acc : Array R),
      (xs.foldl (addCyclicCoeff n p) acc).size = acc.size := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        rw [List.foldl_cons, ih]
        simp [addCyclicCoeff]
  unfold cyclicCoeffs
  rw [aux]
  simp

theorem size_negacyclicCoeffs (n : Nat) (p : DensePoly R) :
    (negacyclicCoeffs n p).size = n := by
  have aux : ∀ (xs : List Nat) (acc : Array R),
      (xs.foldl (addNegacyclicCoeff n p) acc).size = acc.size := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        rw [List.foldl_cons, ih]
        by_cases h : (i / n) % 2 = 0
        · simp [addNegacyclicCoeff, h]
        · simp [addNegacyclicCoeff, h]
  unfold negacyclicCoeffs
  rw [aux]
  simp

/-- Cyclic convolution of positive length `n`. -/
@[expose]
def mulCyclic (plan : MulPlan R) (n : Nat) (_hn : 0 < n)
    (a b : DensePoly R) : DensePoly R :=
  ofCoeffs (cyclicCoeffs n (mulWith plan a b))

/-- Negacyclic convolution of positive length `n`. -/
@[expose]
def mulNegacyclic (plan : MulPlan R) (n : Nat) (_hn : 0 < n)
    (a b : DensePoly R) : DensePoly R :=
  ofCoeffs (negacyclicCoeffs n (mulWith plan a b))

/-- Checked cyclic convolution; length zero has no quotient-ring meaning. -/
def mulCyclic? (plan : MulPlan R) (n : Nat) (a b : DensePoly R) :
    Option (DensePoly R) :=
  if hn : 0 < n then some (mulCyclic plan n hn a b) else none

/-- Checked negacyclic convolution; length zero has no quotient-ring meaning. -/
def mulNegacyclic? (plan : MulPlan R) (n : Nat) (a b : DensePoly R) :
    Option (DensePoly R) :=
  if hn : 0 < n then some (mulNegacyclic plan n hn a b) else none

/-- Cyclic products contain at most `n` stored coefficients. -/
theorem size_mulCyclic_le (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (a b : DensePoly R) : (mulCyclic plan n hn a b).size ≤ n := by
  unfold mulCyclic
  exact Nat.le_trans (size_ofCoeffs_le _) (by rw [size_cyclicCoeffs]; exact Nat.le_refl n)

/-- Negacyclic products contain at most `n` stored coefficients. -/
theorem size_mulNegacyclic_le (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (a b : DensePoly R) : (mulNegacyclic plan n hn a b).size ≤ n := by
  unfold mulNegacyclic
  exact Nat.le_trans (size_ofCoeffs_le _)
    (by rw [size_negacyclicCoeffs]; exact Nat.le_refl n)

/-- Coefficient description of cyclic folding. -/
theorem coeff_mulCyclic (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (a b : DensePoly R) (i : Nat) :
    (mulCyclic plan n hn a b).coeff i =
      if i < n then cyclicCoeff n i (a * b) else 0 := by
  unfold mulCyclic
  rw [coeff_ofCoeffs]
  unfold cyclicCoeff
  rw [mulWith_eq]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  by_cases hi : i < n
  · rw [_root_.ite_eq_left hi]
  · rw [_root_.ite_eq_right hi]
    unfold Array.getD
    rw [HexPoly.dite_eq_right]
    simpa [size_cyclicCoeffs] using hi

/-- Coefficient description of negacyclic folding. -/
theorem coeff_mulNegacyclic (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (a b : DensePoly R) (i : Nat) :
    (mulNegacyclic plan n hn a b).coeff i =
      if i < n then negacyclicCoeff n i (a * b) else 0 := by
  unfold mulNegacyclic
  rw [coeff_ofCoeffs]
  unfold negacyclicCoeff
  rw [mulWith_eq]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  by_cases hi : i < n
  · rw [_root_.ite_eq_left hi]
  · rw [_root_.ite_eq_right hi]
    unfold Array.getD
    rw [HexPoly.dite_eq_right]
    simpa [size_negacyclicCoeffs] using hi

private theorem ofCoeffs_set_add (coeffs : Array R) (k : Nat) (c : R)
    (hk : k < coeffs.size) :
    (ofCoeffs (coeffs.set! k (coeffs.getD k 0 + c)) : DensePoly R) =
      ofCoeffs coeffs + monomial k c := by
  apply ext_coeff
  intro i
  have hzero_add : (Zero.zero : R) + (Zero.zero : R) = (Zero.zero : R) := by
    change (0 : R) + 0 = 0
    grind
  rw [coeff_ofCoeffs, coeff_add _ _ _ hzero_add, coeff_ofCoeffs,
    coeff_monomial]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  by_cases hi : i = k
  · subst i
    simp [Array.getD, hk]
  · have hki : k ≠ i := fun h => hi h.symm
    by_cases hib : i < coeffs.size
    · unfold Array.getD
      simp [Array.set!_eq_setIfInBounds, hib, hki, hi,
        Lean.Grind.Semiring.add_zero]
    · unfold Array.getD
      simp [Array.set!_eq_setIfInBounds, hib, hi,
        Lean.Grind.Semiring.add_zero]

private theorem foldl_cyclic_poly (n : Nat) (hn : 0 < n) (p : DensePoly R)
    (xs : List Nat) (acc : Array R) (hsize : acc.size = n) :
    (ofCoeffs (xs.foldl (addCyclicCoeff n p) acc) : DensePoly R) =
      xs.foldl (fun q i => q + monomial (i % n) (p.coeff i))
        (ofCoeffs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      have hmod : i % n < n := Nat.mod_lt i hn
      have hstep :
          (ofCoeffs (addCyclicCoeff n p acc i) : DensePoly R) =
            ofCoeffs acc + monomial (i % n) (p.coeff i) := by
        unfold addCyclicCoeff
        exact ofCoeffs_set_add acc (i % n) (p.coeff i) (by simpa [hsize] using hmod)
      rw [← hstep]
      apply ih
      simp [addCyclicCoeff, hsize]

theorem ofCoeffs_cyclicCoeffs (n : Nat) (hn : 0 < n) (p : DensePoly R) :
    (ofCoeffs (cyclicCoeffs n p) : DensePoly R) =
      (List.range p.size).foldl
        (fun q i => q + monomial (i % n) (p.coeff i)) 0 := by
  unfold cyclicCoeffs
  rw [foldl_cyclic_poly n hn p]
  · have hrep : (ofCoeffs (Array.replicate n (0 : R)) : DensePoly R) = 0 := by
      change (ofCoeffs (Array.replicate n (Zero.zero : R)) : DensePoly R) = 0
      exact ofCoeffs_replicate_zero n
    rw [hrep]
  · simp

/-- The signed monomial contributed by coefficient `i` when reducing modulo
`x^n + 1`. -/
@[expose]
def negacyclicTerm (n : Nat) (p : DensePoly R) (i : Nat) : DensePoly R :=
  if (i / n) % 2 = 0 then
    monomial (i % n) (p.coeff i)
  else
    monomial (i % n) (0 - p.coeff i)

private theorem ofCoeffs_set_sub (coeffs : Array R) (k : Nat) (c : R)
    (hk : k < coeffs.size) :
    (ofCoeffs (coeffs.set! k (coeffs.getD k 0 - c)) : DensePoly R) =
      ofCoeffs coeffs + monomial k (0 - c) := by
  apply ext_coeff
  intro i
  have hzero_add : (Zero.zero : R) + (Zero.zero : R) = (Zero.zero : R) := by
    change (0 : R) + 0 = 0
    grind
  rw [coeff_ofCoeffs, coeff_add _ _ _ hzero_add, coeff_ofCoeffs,
    coeff_monomial]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  by_cases hi : i = k
  · subst i
    simp [Array.getD, hk]
    grind
  · have hki : k ≠ i := fun h => hi h.symm
    by_cases hib : i < coeffs.size
    · unfold Array.getD
      simp [Array.set!_eq_setIfInBounds, hib, hki, hi,
        Lean.Grind.Semiring.add_zero]
    · unfold Array.getD
      simp [Array.set!_eq_setIfInBounds, hib, hi,
        Lean.Grind.Semiring.add_zero]

private theorem foldl_negacyclic_poly (n : Nat) (hn : 0 < n) (p : DensePoly R)
    (xs : List Nat) (acc : Array R) (hsize : acc.size = n) :
    (ofCoeffs (xs.foldl (addNegacyclicCoeff n p) acc) : DensePoly R) =
      xs.foldl (fun q i => q + negacyclicTerm n p i) (ofCoeffs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      have hmod : i % n < n := Nat.mod_lt i hn
      have hk : i % n < acc.size := by simpa [hsize] using hmod
      have hstep :
          (ofCoeffs (addNegacyclicCoeff n p acc i) : DensePoly R) =
            ofCoeffs acc + negacyclicTerm n p i := by
        unfold addNegacyclicCoeff negacyclicTerm
        by_cases hparity : (i / n) % 2 = 0
        · rw [HexPoly.ite_eq_left hparity, HexPoly.ite_eq_left hparity]
          exact ofCoeffs_set_add acc (i % n) (p.coeff i) hk
        · rw [HexPoly.ite_eq_right hparity, HexPoly.ite_eq_right hparity]
          exact ofCoeffs_set_sub acc (i % n) (p.coeff i) hk
      rw [← hstep]
      apply ih
      by_cases hparity : (i / n) % 2 = 0
      · simp [addNegacyclicCoeff, hparity, hsize]
      · simp [addNegacyclicCoeff, hparity, hsize]

theorem ofCoeffs_negacyclicCoeffs (n : Nat) (hn : 0 < n) (p : DensePoly R) :
    (ofCoeffs (negacyclicCoeffs n p) : DensePoly R) =
      (List.range p.size).foldl (fun q i => q + negacyclicTerm n p i) 0 := by
  unfold negacyclicCoeffs
  rw [foldl_negacyclic_poly n hn p]
  · have hrep : (ofCoeffs (Array.replicate n (0 : R)) : DensePoly R) = 0 := by
      change (ofCoeffs (Array.replicate n (Zero.zero : R)) : DensePoly R) = 0
      exact ofCoeffs_replicate_zero n
    rw [hrep]
  · simp

end Hex.DensePoly
