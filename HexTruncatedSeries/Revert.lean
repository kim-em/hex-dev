/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Comp

public section

/-!
Compositional reversion of fixed-precision truncated series.

The primary route is Newton iteration and needs only an inverse of the linear
coefficient.  It composes the zero-padded derivative, inverts that denominator
with the same witness, and applies a bounded correction.  A direct Lagrange
formula is also provided under `NatInverses`; it is an independent conformance
route rather than the primary algorithm because its explicit `1/k` divisions
exclude valid integral reversions.
-/

namespace Hex.TSeries

universe u

variable {R : Type u} {n : Nat}

attribute [local instance] Lean.Grind.Semiring.natCast

/-- One bounded Newton reversion update. -/
def revStep [Lean.Grind.CommRing R] (b : TSeries R n) (v : R)
    (y : TSeries R n) (m : Nat) : TSeries R n :=
  let numerator := compUpTo m b y - X
  let denominator := compUpTo m b.derivPad y
  let correction := mulUpTo m numerator (invUpTo m denominator v)
  let next := y - correction
  ofFn fun i => if i < m then next.coeff i else 0

/-- Revert through coefficient `m - 1`, zeroing all later coefficients. -/
def revUpTo [Lean.Grind.CommRing R] (m : Nat)
    (b : TSeries R n) (v : R) : TSeries R n :=
  let init := mulUpTo m (C v) X
  let y := newton (revStep b v) init (steps (min m n))
  ofFn fun i => if i < m then y.coeff i else 0

/-- The compositional inverse of `b`, given an inverse of its linear
coefficient. -/
def revOfUnit [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) : TSeries R n :=
  revUpTo n b v

/-- Check the constant coefficient and look up the linear inverse when that
coefficient is represented. -/
def rev? [Lean.Grind.CommRing R] [DecidableEq R] [UnitOps R]
    (b : TSeries R n) : Option (TSeries R n) :=
  if b.coeff 0 ≠ 0 then
    none
  else if n ≤ 1 then
    some 0
  else
    match UnitOps.inv? (R := R) (b.coeff 1) with
    | some v => some (revOfUnit b v)
    | none => none

private def shiftQuotient [Zero R] (b : TSeries R n) : TSeries R n :=
  ofFn fun i => b.coeff (i + 1)

@[simp]
private theorem coeff_shiftQuotient [Zero R] (b : TSeries R n)
    (i : Nat) (hi : i < n) :
    (shiftQuotient b).coeff i = b.coeff (i + 1) :=
  coeff_ofFn _ i hi

private theorem X_mul_shiftQuotient [Lean.Grind.CommRing R]
    (b : TSeries R n) (h0 : b.coeff 0 = 0) :
    (X : TSeries R n) * shiftQuotient b = b := by
  apply ext
  intro i hi
  rw [mul_comm X (shiftQuotient b), coeff_mul_X (shiftQuotient b) i hi]
  by_cases hi0 : i = 0
  · subst i
    rw [ite_eq_left rfl, h0]
  · rw [ite_eq_right hi0, coeff_shiftQuotient b (i - 1) (by omega)]
    congr 1
    omega

private def lagrangeStep [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (p : TSeries R n)
    (state : TSeries R n × TSeries R n) (k : Nat) :
    TSeries R n × TSeries R n :=
  if k = 0 then
    state
  else
    let power := mulUpTo n state.1 p
    let c := NatInverses.invNat (R := R) (m := n - 1) k *
      power.coeff (k - 1)
    (power, ⟨state.2.coeffs.modify k fun _ => c⟩)

private def lagrangeState [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (p : TSeries R n) (m : Nat) :
    TSeries R n × TSeries R n :=
  (List.range m).foldl (lagrangeStep p) (1, 0)

/-- Direct Lagrange inversion.  This deliberately performs the explicit
division by `k` and therefore carries `NatInverses R (n-1)`.  Consecutive
powers are carried through the fold, so the schoolbook route performs `n`
full multiplications and costs `O(n³)` rather than recomputing each power by
square-and-multiply.  When `b.coeff 0 = 0`, `b = X * shiftQuotient b`
exactly; the unavailable top coefficient of the quotient is harmless because
truncated multiplication is lower triangular. -/
def revLagrange [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (b : TSeries R n) (v : R) : TSeries R n :=
  let xOverB := invOfUnit (shiftQuotient b) v
  (lagrangeState xOverB n).2

private theorem lagrangeState_power [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (p : TSeries R n) (m : Nat) :
    (lagrangeState p m).1 = p ^ (m - 1) := by
  induction m with
  | zero =>
      simp [lagrangeState, pow_zero]
  | succ m ih =>
      rw [lagrangeState, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, ← lagrangeState]
      unfold lagrangeStep
      by_cases hm : m = 0
      · subst m
        simpa [pow_zero] using ih
      · rw [ite_eq_right hm]
        rw [show m + 1 - 1 = m by omega]
        change mulUpTo n (lagrangeState p m).1 p = p ^ m
        have hpow : p ^ (m - 1) * p = p ^ m := by
          calc
            p ^ (m - 1) * p = p ^ ((m - 1) + 1) := (pow_succ _ _).symm
            _ = p ^ m := by rw [show m - 1 + 1 = m by omega]
        rw [Agree.mulUpTo_full, ih, hpow]

private theorem lagrangeState_coeff [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (p : TSeries R n) (m i : Nat)
    (hm : m ≤ n) (hi : i < n) :
    (lagrangeState p m).2.coeff i =
      if 0 < i ∧ i < m then
        NatInverses.invNat (R := R) (m := n - 1) i *
          (p ^ i).coeff (i - 1)
      else 0 := by
  induction m with
  | zero =>
      simp [lagrangeState, coeff_zero]
  | succ m ih =>
      have hmn : m ≤ n := by omega
      rw [lagrangeState, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, ← lagrangeState]
      unfold lagrangeStep
      by_cases hm0 : m = 0
      · subst m
        change (lagrangeState p 0).2.coeff i = _
        rw [lagrangeState]
        change (0 : TSeries R n).coeff i = _
        rw [coeff_zero, ite_eq_right (by omega)]
      · rw [ite_eq_right hm0]
        change
          (⟨(lagrangeState p m).2.coeffs.modify m fun _ =>
            NatInverses.invNat (R := R) (m := n - 1) m *
              (mulUpTo n (lagrangeState p m).1 p).coeff (m - 1)⟩ :
              TSeries R n).coeff i = _
        rw [coeff_modify (lagrangeState p m).2 m i _ hi]
        by_cases hmi : m = i
        · subst i
          rw [ite_eq_left rfl, ite_eq_left (by omega), Agree.mulUpTo_full,
            lagrangeState_power]
          rw [← pow_succ, show m - 1 + 1 = m by omega]
        · rw [ite_eq_right hmi, ih hmn]
          by_cases hii : 0 < i ∧ i < m
          · rw [ite_eq_left hii, ite_eq_left (by omega)]
          · rw [ite_eq_right hii]
            have hnot : ¬(0 < i ∧ i < m + 1) := by
              intro h
              apply hmi
              omega
            rw [ite_eq_right hnot]

/-- Coefficients produced by direct Lagrange inversion have the advertised
closed form. -/
private theorem coeff_revLagrange [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (b : TSeries R n) (v : R)
    (i : Nat) (hi : i < n) :
    (revLagrange b v).coeff i =
      if i = 0 then 0 else
        NatInverses.invNat (R := R) (m := n - 1) i *
          ((invOfUnit (shiftQuotient b) v) ^ i).coeff (i - 1) := by
  unfold revLagrange
  rw [lagrangeState_coeff _ n i (Nat.le_refl n) hi]
  by_cases hi0 : i = 0
  · subst i
    simp
  · rw [ite_eq_right hi0, ite_eq_left (by omega)]

private theorem shiftQuotient_mul_inv [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (hv : b.coeff 1 * v = 1)
    (hn : 0 < n) :
    shiftQuotient b * invOfUnit (shiftQuotient b) v = 1 := by
  apply invOfUnit_mul
  rw [coeff_shiftQuotient b 0 hn]
  exact hv

private theorem pow_mul_pow_cancel [Lean.Grind.CommRing R]
    (p q : TSeries R n) (hpq : p * q = 1)
    (k j : Nat) (hjk : j ≤ k) :
    p ^ k * q ^ j = p ^ (k - j) := by
  have hpowers : p ^ j * q ^ j = 1 := by
    induction j with
    | zero =>
        rw [pow_zero, pow_zero]
        grind
    | succ j ih =>
        rw [pow_succ, pow_succ]
        calc
          p ^ j * p * (q ^ j * q) = (p ^ j * q ^ j) * (p * q) := by grind
          _ = 1 := by rw [ih (by omega), hpq]; grind
  calc
    p ^ k * q ^ j = (p ^ (k - j) * p ^ j) * q ^ j := by
      rw [← pow_add, show k - j + j = k by omega]
    _ = p ^ (k - j) * (p ^ j * q ^ j) := by grind
    _ = p ^ (k - j) := by rw [hpowers]; grind

private theorem coeff_pow_mul_derivPad [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (b : TSeries R n) (v : R)
    (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1)
    (r : Nat) (hr : 0 < r) (hrn : r < n) :
    ((invOfUnit (shiftQuotient b) v) ^ r * b.derivPad).coeff (r - 1) =
      if r = 1 then 1 else 0 := by
  let q := shiftQuotient b
  let p := invOfUnit q v
  have hqp : q * p = 1 := shiftQuotient_mul_inv b v hv (by omega)
  have hpq : p * q = 1 := by rw [mul_comm]; exact hqp
  have hb : (X : TSeries R n) * q = b := X_mul_shiftQuotient b h0
  have hderiv : Agree (n - 1) b.derivPad (q + X * q.derivPad) := by
    rw [← hb]
    apply Agree.trans (derivPad_mul_agree X q)
    have hxq := Agree.mul (derivPad_X_agree (R := R) (n := n))
      (Agree.refl (n - 1) q)
    have hsum := Agree.add hxq
      (Agree.refl (n - 1) (X * q.derivPad))
    simpa only [one_mul] using hsum
  have hmain := Agree.mul (Agree.refl (n - 1) (p ^ r)) hderiv
  have hmainCoeff := hmain (r - 1) (by omega) (by omega)
  change (p ^ r * b.derivPad).coeff (r - 1) = _
  by_cases hr1 : r = 1
  · subst r
    rw [ite_eq_left rfl]
    have halg : p ^ 1 * (q + X * q.derivPad) =
        1 + X * (p * q.derivPad) := by
      rw [pow_one, Lean.Grind.Semiring.left_distrib, hpq]
      grind
    rw [hmainCoeff, halg, coeff_add _ _ 0 (by omega),
      coeff_one 0 (by omega), coeff_mul_zero _ _ (by omega)]
    rw [X_coeff_zero]
    grind
  · rw [ite_eq_right hr1]
    have hr2 : 1 < r := by omega
    have hcancel : p ^ r * q = p ^ (r - 1) := by
      simpa only [pow_one] using pow_mul_pow_cancel p q hpq r 1 (by omega)
    have halg : p ^ r * (q + X * q.derivPad) =
        p ^ (r - 1) + X * (p ^ r * q.derivPad) := by
      rw [Lean.Grind.Semiring.left_distrib, hcancel]
      grind
    rw [hmainCoeff, halg, coeff_add _ _ (r - 1) (by omega),
      mul_comm X (p ^ r * q.derivPad),
      coeff_mul_X (p ^ r * q.derivPad) (r - 1) (by omega),
      ite_eq_right (by omega)]
    have hinvDeriv : Agree (n - 1)
        (p ^ r * q.derivPad + p ^ (r - 2) * p.derivPad) 0 := by
      have hprod := derivPad_mul_agree q p
      rw [hqp, derivPad_one] at hprod
      have hzero := Agree.symm hprod
      have hmul := Agree.mul (Agree.refl (n - 1) (p ^ (r - 1))) hzero
      have hcancel' : p ^ (r - 1) * q = p ^ (r - 2) := by
        have h := pow_mul_pow_cancel p q hpq (r - 1) 1 (by omega)
        rw [pow_one, show r - 1 - 1 = r - 2 by omega] at h
        exact h
      have hpowsucc : p ^ (r - 1) * p = p ^ r := by
        calc
          p ^ (r - 1) * p = p ^ ((r - 1) + 1) := (pow_succ _ _).symm
          _ = p ^ r := by rw [show r - 1 + 1 = r by omega]
      have halg' :
          p ^ (r - 1) * (q.derivPad * p + q * p.derivPad) =
            p ^ r * q.derivPad + p ^ (r - 2) * p.derivPad := by
        rw [Lean.Grind.Semiring.left_distrib]
        calc
          p ^ (r - 1) * (q.derivPad * p) +
                p ^ (r - 1) * (q * p.derivPad) =
              (p ^ (r - 1) * p) * q.derivPad +
                (p ^ (r - 1) * q) * p.derivPad := by grind
          _ = p ^ r * q.derivPad + p ^ (r - 2) * p.derivPad := by
            rw [hpowsucc, hcancel']
      rw [halg'] at hmul
      simpa only [mul_zero] using hmul
    have hinvCoeff := hinvDeriv (r - 2) (by omega) (by omega)
    rw [coeff_add _ _ (r - 2) (by omega), coeff_zero] at hinvCoeff
    have hpow := derivPad_pow_agree p (r - 1)
    have hpowCoeff := hpow (r - 2) (by omega) (by omega)
    rw [coeff_derivPad (p ^ (r - 1)) (r - 2) (by omega),
      ite_eq_left (by omega), show r - 2 + 1 = r - 1 by omega] at hpowCoeff
    have hright :
        (C (((r - 1 : Nat) : R)) * p ^ (r - 1 - 1) * p.derivPad).coeff
            (r - 2) =
          (((r - 1 : Nat) : R)) *
            (p ^ (r - 2) * p.derivPad).coeff (r - 2) := by
      rw [show r - 1 - 1 = r - 2 by omega, mul_assoc,
        coeff_C_mul _ _ _ (by omega)]
    rw [hright] at hpowCoeff
    have heq :
        (p ^ (r - 1)).coeff (r - 1) =
          (p ^ (r - 2) * p.derivPad).coeff (r - 2) := by
      let u := NatInverses.invNat (R := R) (m := n - 1) (r - 1)
      have hu := NatInverses.invNat_eq (R := R) (m := n - 1)
        (r - 1) (by omega) (by omega)
      calc
        (p ^ (r - 1)).coeff (r - 1) =
            1 * (p ^ (r - 1)).coeff (r - 1) := by grind
        _ = (((r - 1 : Nat) : R) * u) *
            (p ^ (r - 1)).coeff (r - 1) := by rw [hu]
        _ = u * (((r - 1 : Nat) : R) *
            (p ^ (r - 1)).coeff (r - 1)) := by grind
        _ = u * (((r - 1 : Nat) : R) *
            (p ^ (r - 2) * p.derivPad).coeff (r - 2)) := by rw [hpowCoeff]
        _ = (((r - 1 : Nat) : R) * u) *
            (p ^ (r - 2) * p.derivPad).coeff (r - 2) := by grind
        _ = (p ^ (r - 2) * p.derivPad).coeff (r - 2) := by rw [hu]; grind
    rw [← heq] at hinvCoeff
    rw [show r - 1 - 1 = r - 2 by omega]
    grind

private theorem mul_pow_comm [Lean.Grind.CommRing R]
    (a b : TSeries R n) (k : Nat) :
    (a * b) ^ k = a ^ k * b ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, pow_zero]
      grind
  | succ k ih =>
      rw [pow_succ, pow_succ, pow_succ, ih]
      grind

private theorem coeff_lagrange_term [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (b : TSeries R n) (v : R)
    (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1)
    (k j : Nat) (hk : 0 < k) (hkn : k < n) :
    ((invOfUnit (shiftQuotient b) v) ^ k * b ^ j * b.derivPad).coeff
        (k - 1) =
      if j + 1 = k then 1 else 0 := by
  let q := shiftQuotient b
  let p := invOfUnit q v
  change (p ^ k * b ^ j * b.derivPad).coeff (k - 1) = _
  by_cases hjk : j < k
  · have hpq : p * q = 1 := by
      rw [mul_comm]
      exact shiftQuotient_mul_inv b v hv (by omega)
    have hcancel := pow_mul_pow_cancel p q hpq k j (by omega)
    have hb : (X : TSeries R n) * q = b := X_mul_shiftQuotient b h0
    have hbpow : b ^ j = (X : TSeries R n) ^ j * q ^ j := by
      rw [← hb, mul_pow_comm]
    have halg : p ^ k * b ^ j * b.derivPad =
        X ^ j * (p ^ (k - j) * b.derivPad) := by
      calc
        p ^ k * b ^ j * b.derivPad =
            p ^ k * (X ^ j * q ^ j) * b.derivPad := by rw [hbpow]
        _ = X ^ j * ((p ^ k * q ^ j) * b.derivPad) := by grind
        _ = X ^ j * (p ^ (k - j) * b.derivPad) := by rw [hcancel]
    rw [halg, coeff_X_pow_mul (p ^ (k - j) * b.derivPad) j (k - 1)
      (by omega), ite_eq_left (by omega)]
    rw [show k - 1 - j = k - j - 1 by omega,
      coeff_pow_mul_derivPad b v h0 hv (k - j) (by omega) (by omega)]
    by_cases hj : j + 1 = k
    · rw [ite_eq_left hj, ite_eq_left (by omega)]
    · rw [ite_eq_right hj, ite_eq_right (by omega)]
  · have hz := pow_vanish b h0 j
    have hmul := Agree.mul
      (Agree.mul (Agree.refl j (p ^ k)) hz)
      (Agree.refl j b.derivPad)
    have hzero : Agree j (p ^ k * b ^ j * b.derivPad) 0 := by
      simpa only [mul_zero, zero_mul] using hmul
    rw [ite_eq_right (by omega)]
    have hc := hzero (k - 1) (by omega) (by omega)
    rw [coeff_zero] at hc
    exact hc

private def tangent [Lean.Grind.CommRing R]
    (y d : TSeries R n) (k : Nat) : TSeries R n :=
  if k = 0 then 0 else C ((k : Nat) : R) * y ^ (k - 1) * d

private theorem tangent_vanish [Lean.Grind.CommRing R]
    (y d : TSeries R n) (p k : Nat) (hd : Agree p d 0) :
    Agree p (tangent y d k) 0 := by
  unfold tangent
  split
  · exact Agree.refl p 0
  · have hm := Agree.mul
        (Agree.mul (Agree.refl p (C ((k : Nat) : R)))
          (Agree.refl p (y ^ (k - 1)))) hd
    simpa only [mul_zero] using hm

private theorem pow_taylor [Lean.Grind.CommRing R]
    (y d : TSeries R n) (p k : Nat) (hd : Agree p d 0) :
    Agree (p + p) ((y + d) ^ k) (y ^ k + tangent y d k) := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero]
      unfold tangent
      rw [ite_eq_left rfl, add_zero]
      exact Agree.refl (p + p) (1 : TSeries R n)
  | succ k ih =>
      rw [pow_succ]
      have hmul := Agree.mul ih (Agree.refl (p + p) (y + d))
      have halg :
          (y ^ k + tangent y d k) * (y + d) =
            (y ^ (k + 1) + tangent y d (k + 1)) + tangent y d k * d := by
        cases k with
        | zero =>
            simp [tangent, pow_zero, pow_succ,
              Lean.Grind.Semiring.natCast_one]
            grind
        | succ k =>
            unfold tangent
            simp only [Nat.add_sub_cancel]
            have hcast1 : (((k + 1 : Nat) : R)) = ((k : Nat) : R) + 1 := by
              rw [Lean.Grind.Semiring.natCast_succ]
            have hcast2 : (((k + 2 : Nat) : R)) = ((k : Nat) : R) + 1 + 1 := by
              rw [show k + 2 = (k + 1) + 1 by omega,
                Lean.Grind.Semiring.natCast_succ, hcast1]
            have hpow2 : y ^ (k + 2) = y ^ k * y * y := by
              rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, pow_succ]
            rw [hcast1, hcast2, hpow2, pow_succ]
            simp only [C_add, C_one]
            grind
      apply Agree.trans hmul
      rw [halg]
      have hquad := Agree.zeroMul (tangent_vanish y d p k hd) hd
      simpa only [add_zero] using
        Agree.add (Agree.refl (p + p) (y ^ (k + 1) + tangent y d (k + 1))) hquad

private theorem tangent_sum [Lean.Grind.CommRing R]
    (b y d : TSeries R n) (hy : y.coeff 0 = 0) :
    (List.range n).foldl
        (fun acc k => acc + C (b.coeff k) * tangent y d k) 0 =
      comp b.derivPad y * d := by
  cases n with
  | zero =>
      apply ext
      intro i hi
      omega
  | succ q =>
      rw [comp_spec b.derivPad y hy]
      have hright :
          (List.range (q + 1)).foldl
              (fun acc j => acc + C (b.derivPad.coeff j) * y ^ j) 0 =
            (List.range q).foldl
              (fun acc j => acc +
                C ((((j + 1 : Nat) : R)) * b.coeff (j + 1)) * y ^ j) 0 := by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hpref :
            (List.range q).foldl
                (fun acc j => acc + C (b.derivPad.coeff j) * y ^ j) 0 =
              (List.range q).foldl
                (fun acc j => acc +
                  C ((((j + 1 : Nat) : R)) * b.coeff (j + 1)) * y ^ j) 0 := by
          apply List.foldl_add_congr
          intro j hj
          have hjq : j < q := List.mem_range.mp hj
          rw [coeff_derivPad b j (by omega), ite_eq_left (by omega)]
        rw [hpref, coeff_derivPad b q (Nat.lt_succ_self q),
          ite_eq_right (Nat.lt_irrefl (q + 1)),
          C_zero, zero_mul, add_zero]
      change
        (List.range (q + 1)).foldl
            (fun acc k => acc + C (b.coeff k) * tangent y d k) 0 =
          (List.range (q + 1)).foldl
            (fun acc k => acc + C (b.derivPad.coeff k) * y ^ k) 0 * d
      rw [hright, ← List.foldl_add_mul_right_zero]
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have hzero : C (b.coeff 0) * tangent y d 0 = 0 := by
        rw [show tangent y d 0 = 0 by simp [tangent], mul_zero]
      rw [hzero, add_zero]
      apply List.foldl_add_congr
      intro j hj
      unfold tangent
      rw [ite_eq_right (by omega), Nat.succ_sub_one]
      have hc :
          C (b.coeff (j + 1)) *
              (C (((j + 1 : Nat) : R)) : TSeries R (q + 1)) =
            C ((((j + 1 : Nat) : R)) * b.coeff (j + 1)) := by
        rw [← C_mul]
        congr 1
        grind
      grind

private theorem derivPad_comp_agree [Lean.Grind.CommRing R]
    (a b : TSeries R n) (h0 : b.coeff 0 = 0) :
    Agree (n - 1) (comp a b).derivPad
      (comp a.derivPad b * b.derivPad) := by
  rw [comp_spec a b h0, derivPad_foldl_add, derivPad_zero]
  have hfold : Agree (n - 1)
      ((List.range n).foldl
        (fun acc k => acc + (C (a.coeff k) * b ^ k).derivPad) 0)
      ((List.range n).foldl
        (fun acc k => acc + C (a.coeff k) * tangent b b.derivPad k) 0) := by
    apply Agree.foldl_add
    intro k hk
    rw [derivPad_C_mul]
    have hpow := derivPad_pow_agree b k
    have hmul := Agree.mul (Agree.refl (n - 1) (C (a.coeff k))) hpow
    unfold tangent
    by_cases hk0 : k = 0
    · subst k
      rw [ite_eq_left rfl, pow_zero, derivPad_one, mul_zero]
      exact Agree.refl (n - 1) 0
    · rw [ite_eq_right hk0]
      exact hmul
  apply Agree.trans hfold
  rw [tangent_sum a b b.derivPad h0]
  exact Agree.refl (n - 1) (comp a.derivPad b * b.derivPad)

private theorem comp_taylor [Lean.Grind.CommRing R]
    (b y d : TSeries R n) (p : Nat) (hy : y.coeff 0 = 0)
    (hd0 : d.coeff 0 = 0) (hd : Agree p d 0) :
    Agree (p + p) (comp b (y + d))
      (comp b y + comp b.derivPad y * d) := by
  have hyd : (y + d).coeff 0 = 0 := by
    by_cases hn : 0 < n
    · rw [coeff_add y d 0 hn, hy, hd0]
      grind
    · unfold coeff
      rw [dite_eq_right hn]
  rw [comp_spec b (y + d) hyd, comp_spec b y hy]
  have hfold :
      Agree (p + p)
        ((List.range n).foldl
          (fun acc k => acc + C (b.coeff k) * (y + d) ^ k) 0)
        ((List.range n).foldl
          (fun acc k => acc + C (b.coeff k) *
            (y ^ k + tangent y d k)) 0) := by
    have go (xs : List Nat) (z z' : TSeries R n)
        (hz : Agree (p + p) z z') :
        Agree (p + p)
          (xs.foldl (fun acc k => acc + C (b.coeff k) * (y + d) ^ k) z)
          (xs.foldl (fun acc k => acc + C (b.coeff k) *
            (y ^ k + tangent y d k)) z') := by
      induction xs generalizing z z' with
      | nil => exact hz
      | cons k ks ih =>
          simp only [List.foldl_cons]
          exact ih _ _ (Agree.add hz
            (Agree.mul (Agree.refl (p + p) (C (b.coeff k)))
              (pow_taylor y d p k hd)))
    exact go (List.range n) 0 0 (Agree.refl (p + p) 0)
  apply Agree.trans hfold
  have hsplit :
      (List.range n).foldl
          (fun acc k => acc + C (b.coeff k) *
            (y ^ k + tangent y d k)) 0 =
        (List.range n).foldl
            (fun acc k => acc + C (b.coeff k) * y ^ k) 0 +
          (List.range n).foldl
            (fun acc k => acc + C (b.coeff k) * tangent y d k) 0 := by
    calc
      _ = (List.range n).foldl
          (fun acc k => acc +
            (C (b.coeff k) * y ^ k + C (b.coeff k) * tangent y d k)) 0 := by
              apply List.foldl_add_congr
              intro k hk
              rw [left_distrib]
      _ = _ := List.foldl_add_add _ _ _
  rw [hsplit, tangent_sum b y d hy]
  exact Agree.refl (p + p) _

private theorem derivPad_coeff_zero_mul [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (hv : b.coeff 1 * v = 1) :
    b.derivPad.coeff 0 * v = 1 := by
  by_cases hn : 0 < n
  · rw [coeff_derivPad b 0 hn]
    simp only [Nat.zero_add]
    by_cases h1 : 1 < n
    · rw [ite_eq_left h1, Lean.Grind.Semiring.natCast_one]
      calc
        1 * b.coeff 1 * v = b.coeff 1 * v := by grind
        _ = 1 := hv
    · rw [ite_eq_right h1]
      have hb : b.coeff 1 = 0 := by
        unfold coeff
        rw [dite_eq_right h1]
      rw [hb] at hv
      simpa only [zero_mul] using hv
  · have hd : b.derivPad.coeff 0 = 0 := by
      unfold coeff
      rw [dite_eq_right hn]
    have hb : b.coeff 1 = 0 := by
      unfold coeff
      rw [dite_eq_right (by omega)]
    rw [hd]
    calc
      0 * v = b.coeff 1 * v := by rw [hb]
      _ = 1 := hv

private theorem revStep_correct [Lean.Grind.CommRing R]
    (b y : TSeries R n) (v : R) (p : Nat) (hp : 0 < p)
    (hy : y.coeff 0 = 0) (hv : b.coeff 1 * v = 1)
    (herr : Agree p (comp b y - X) 0) :
    (revStep b v y (p + p)).coeff 0 = 0 ∧
      Agree (p + p) (comp b (revStep b v y (p + p)) - X) 0 := by
  let m := p + p
  let numerator := compUpTo m b y - X
  let denominator := compUpTo m b.derivPad y
  let inverse := invUpTo m denominator v
  let correction := mulUpTo m numerator inverse
  let derivative := comp b.derivPad y
  have hnum : Agree m numerator (comp b y - X) := by
    dsimp only [numerator]
    exact Agree.sub (Agree.compUpTo m b y hy) (Agree.refl m X)
  have hden : Agree m denominator derivative := by
    dsimp only [denominator, derivative]
    exact Agree.compUpTo m b.derivPad y hy
  have hden0 : denominator.coeff 0 * v = 1 := by
    by_cases hn : 0 < n
    · calc
        denominator.coeff 0 * v = derivative.coeff 0 * v := by
          rw [hden 0 hn (by dsimp only [m]; omega)]
        _ = b.derivPad.coeff 0 * v := by
          rw [coeff_comp_zero b.derivPad y hy]
        _ = 1 := derivPad_coeff_zero_mul b v hv
    · have hd : denominator.coeff 0 = 0 := by
        unfold coeff
        rw [dite_eq_right hn]
      have hb : b.coeff 1 = 0 := by
        unfold coeff
        rw [dite_eq_right (by omega)]
      rw [hd]
      calc
        0 * v = b.coeff 1 * v := by rw [hb]
        _ = 1 := hv
  have hinv : Agree m inverse (invOfUnit denominator v) := by
    intro i hi him
    dsimp only [inverse]
    rw [coeff_invUpTo m denominator v hden0 i hi, ite_eq_left him]
  have hdeninv : Agree m (denominator * inverse) 1 := by
    have hmul := Agree.mul (Agree.refl m denominator) hinv
    rw [invOfUnit_mul denominator v hden0] at hmul
    exact hmul
  have hcorrection : Agree m correction (numerator * inverse) := by
    dsimp only [correction]
    exact Agree.mulUpTo m numerator inverse
  have hcancel : Agree m (derivative * correction) (comp b y - X) := by
    have hleft := Agree.mul hden.symm hcorrection
    have halg : denominator * (numerator * inverse) =
        numerator * (denominator * inverse) := by
      grind
    rw [halg] at hleft
    have hright := Agree.mul (Agree.refl m numerator) hdeninv
    rw [mul_one] at hright
    exact hleft.trans (hright.trans hnum)
  have hnumSmall : Agree p numerator 0 :=
    (hnum.mono (by dsimp only [m]; omega)).trans herr
  have hcorrectionSmall : Agree p correction 0 := by
    have hprod := Agree.mul hnumSmall (Agree.refl p inverse)
    rw [zero_mul] at hprod
    exact (hcorrection.mono (by dsimp only [m]; omega)).trans hprod
  have hnegSmall : Agree p (-correction) 0 := by
    have hneg := Agree.neg hcorrectionSmall
    have hz : -(0 : TSeries R n) = 0 := by grind
    rw [hz] at hneg
    exact hneg
  have hneg0 : (-correction).coeff 0 = 0 := by
    by_cases hn : 0 < n
    · rw [coeff_neg correction 0 hn,
        hcorrectionSmall 0 hn hp, coeff_zero]
      grind
    · unfold coeff
      rw [dite_eq_right hn]
  have hyc0 : (y - correction).coeff 0 = 0 := by
    by_cases hn : 0 < n
    · rw [coeff_sub y correction 0 hn, hy,
        hcorrectionSmall 0 hn hp, coeff_zero]
      grind
    · unfold coeff
      rw [dite_eq_right hn]
  have htaylor : Agree m (comp b (y - correction))
      (comp b y - derivative * correction) := by
    have ht := comp_taylor b y (-correction) p hy hneg0 hnegSmall
    have hleft : y + -correction = y - correction := by grind
    have hright : comp b y + derivative * -correction =
        comp b y - derivative * correction := by grind
    rw [hleft, hright] at ht
    dsimp only [m, derivative]
    exact ht
  have hlinear : Agree m ((comp b y - derivative * correction) - X) 0 := by
    have hs := Agree.sub
      (Agree.sub (Agree.refl m (comp b y)) hcancel) (Agree.refl m X)
    have halg : (comp b y - (comp b y - X)) - X = 0 := by
      grind
    rw [halg] at hs
    exact hs
  have hideal : Agree m (comp b (y - correction) - X) 0 :=
    (Agree.sub htaylor (Agree.refl m X)).trans hlinear
  have hstep : Agree m (revStep b v y m) (y - correction) := by
    intro i hi him
    unfold revStep
    rw [coeff_ofFn _ i hi, ite_eq_left him]
  have hstep0 : (revStep b v y m).coeff 0 = 0 := by
    by_cases hn : 0 < n
    · exact (hstep 0 hn (by dsimp only [m]; omega)).trans hyc0
    · unfold coeff
      rw [dite_eq_right hn]
  have hcomp := Agree.comp_inner b (revStep b v y m) (y - correction)
    hstep hstep0 hyc0
  have hresult := (Agree.sub hcomp (Agree.refl m X)).trans hideal
  dsimp only [m] at hstep0 hresult
  exact ⟨hstep0, hresult⟩

private theorem coeff_mul_right_lead [Lean.Grind.CommRing R]
    (a d : TSeries R n) (p : Nat) (hp : p < n) (hd : Agree p d 0) :
    (a * d).coeff p = a.coeff 0 * d.coeff p := by
  rw [coeff_mul a d p hp]
  unfold convCoeff
  calc
    (List.range (p + 1)).foldl
        (fun acc j => acc + a.coeff j * d.coeff (p - j)) 0 =
      (List.range (p + 1)).foldl
        (fun acc j => acc + if j = 0 then a.coeff 0 * d.coeff p else 0) 0 := by
          apply List.foldl_add_congr
          intro j hj
          have hjp : j < p + 1 := List.mem_range.mp hj
          by_cases hj0 : j = 0
          · subst j
            rw [ite_eq_left rfl, Nat.sub_zero]
          · rw [ite_eq_right hj0, hd (p - j) (by omega) (by omega), coeff_zero]
            grind
    _ = 0 + a.coeff 0 * d.coeff p :=
      List.foldl_add_single _ _ _ _ (List.mem_range.mpr (by omega)) List.nodup_range
    _ = a.coeff 0 * d.coeff p := by grind

private theorem comp_left_cancel_agree [Lean.Grind.CommRing R]
    (b y z : TSeries R n) (hy : y.coeff 0 = 0) (hz : z.coeff 0 = 0)
    (v : R) (hv : b.coeff 1 * v = 1) (p : Nat)
    (hcomp : Agree p (comp b y) (comp b z)) : Agree p y z := by
  have go (q : Nat) (hqp : q ≤ p) : Agree q y z := by
    induction q with
    | zero =>
        intro i hi hip
        omega
    | succ q ih =>
        intro i hi hip
        by_cases hil : i < q
        · exact ih (by omega) i hi hil
        · have hip' : i = q := by omega
          subst i
          by_cases hq0 : q = 0
          · subst q
            exact hy.trans hz.symm
          · let d := y - z
            have hd : Agree q d 0 := by
              have hs := Agree.sub (ih (by omega)) (Agree.refl q z)
              have hzz : z - z = 0 := by grind
              rw [hzz] at hs
              exact hs
            have hd0 : d.coeff 0 = 0 := by
              dsimp only [d]
              rw [coeff_sub y z 0 (by omega), hy, hz]
              grind
            have ht := comp_taylor b z d q hz hd0 hd
            have hyd : z + d = y := by
              dsimp only [d]
              grind
            have htp := ht q hi (by omega)
            rw [hyd, coeff_add _ _ q hi] at htp
            rw [hcomp q hi (by omega)] at htp
            have hmul : (comp b.derivPad z * d).coeff q = 0 := by
              grind
            rw [coeff_mul_right_lead (comp b.derivPad z) d q hi hd] at hmul
            have hunit : (comp b.derivPad z).coeff 0 * v = 1 := by
              rw [coeff_comp_zero b.derivPad z hz]
              exact derivPad_coeff_zero_mul b v hv
            have hdp : d.coeff q = 0 := by
              calc
                d.coeff q = 1 * d.coeff q := by grind
                _ = ((comp b.derivPad z).coeff 0 * v) * d.coeff q := by rw [hunit]
                _ = v * ((comp b.derivPad z).coeff 0 * d.coeff q) := by grind
                _ = 0 := by rw [hmul]; grind
            dsimp only [d] at hdp
            rw [coeff_sub y z q hi] at hdp
            grind
  exact go p (Nat.le_refl p)

private theorem comp_left_cancel [Lean.Grind.CommRing R]
    (b y z : TSeries R n) (hy : y.coeff 0 = 0) (hz : z.coeff 0 = 0)
    (v : R) (hv : b.coeff 1 * v = 1) (hcomp : comp b y = comp b z) :
    y = z := by
  apply Agree.full (p := n) _ (Nat.le_refl n)
  apply comp_left_cancel_agree b y z hy hz v hv n
  rw [hcomp]
  exact Agree.refl n (comp b z)

private theorem revInit_zero [Lean.Grind.CommRing R] (m : Nat) (v : R) :
    (mulUpTo m (C v) X : TSeries R n).coeff 0 = 0 := by
  by_cases hn : 0 < n
  · rw [coeff_mulUpTo m (C v) X 0 hn]
    by_cases hm : 0 < m
    · rw [ite_eq_left hm, coeff_mul_zero (C v) X hn,
        coeff_C v 0 hn, X_coeff_zero]
      grind
    · rw [ite_eq_right hm]
  · unfold coeff
    rw [dite_eq_right hn]

private theorem revNewton_correctAt [Lean.Grind.CommRing R]
    (m : Nat) (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) (j : Nat) :
    (newton (revStep b v) (mulUpTo m (C v) X) j).coeff 0 = 0 ∧
      Agree (2 ^ j)
        (comp b (newton (revStep b v) (mulUpTo m (C v) X) j) - X) 0 := by
  induction j with
  | zero =>
      rw [newton]
      refine ⟨revInit_zero m v, ?_⟩
      intro i hi hip
      have hi0 : i = 0 := by omega
      subst i
      rw [coeff_sub _ X 0 hi, coeff_comp_zero b _ (revInit_zero m v),
        h0, coeff_X 0 hi, coeff_zero]
      grind
  | succ j ih =>
      rw [newton]
      have hs := revStep_correct b
        (newton (revStep b v) (mulUpTo m (C v) X) j) v (2 ^ j)
        (Nat.two_pow_pos j) ih.1 hv ih.2
      have hp : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
        rw [Nat.pow_succ]
        omega
      simpa only [hp] using hs

private theorem revNewton_correct [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) (j : Nat) :
    (newton (revStep b v) (mulUpTo n (C v) X) j).coeff 0 = 0 ∧
      Agree (2 ^ j)
        (comp b (newton (revStep b v) (mulUpTo n (C v) X) j) - X) 0 :=
  revNewton_correctAt n b v h0 hv j

private theorem revOfUnit_eq [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) :
    revOfUnit b v =
      newton (revStep b v) (mulUpTo n (C v) X) (steps n) := by
  apply ext
  intro i hi
  unfold revOfUnit revUpTo
  rw [coeff_ofFn _ i hi, ite_eq_left hi, Nat.min_self]

/-- Bounded Newton reversion agrees with the full compositional inverse
throughout the requested prefix. -/
theorem revUpTo_agree [Lean.Grind.CommRing R]
    (m : Nat) (b : TSeries R n) (v : R)
    (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1) :
    Agree m (revUpTo m b v) (revOfUnit b v) := by
  let q := min m n
  let short := newton (revStep b v) (mulUpTo m (C v) X) (steps q)
  let full := newton (revStep b v) (mulUpTo n (C v) X) (steps n)
  have hs := revNewton_correctAt m b v h0 hv (steps q)
  have hf := revNewton_correct b v h0 hv (steps n)
  have hsComp : Agree q (comp b short) X := by
    exact (Agree.ofSub hs.2).mono (two_pow_steps_ge q)
  have hfComp : Agree q (comp b full) X := by
    exact (Agree.ofSub hf.2).mono
      (Nat.le_trans (Nat.min_le_right m n) (two_pow_steps_ge n))
  have hiter : Agree q short full :=
    comp_left_cancel_agree b short full hs.1 hf.1 v hv q
      (hsComp.trans hfComp.symm)
  intro i hi him
  have hiq : i < q := by dsimp only [q]; omega
  unfold revOfUnit revUpTo
  rw [coeff_ofFn _ i hi, ite_eq_left him, coeff_ofFn _ i hi, ite_eq_left hi,
    Nat.min_self]
  exact hiter i hi hiq

private theorem coeff_comp_one [Lean.Grind.CommRing R]
    (b y : TSeries R n) (hy : y.coeff 0 = 0) (h : 1 < n) :
    (comp b y).coeff 1 = b.coeff 1 * y.coeff 1 := by
  have hyAgree : Agree 1 y 0 := by
    intro i hi hi1
    have hi0 : i = 0 := by omega
    subst i
    rw [hy, coeff_zero]
  have ht := comp_taylor b 0 y 1 (coeff_zero 0) hy hyAgree
  have hzy : (0 : TSeries R n) + y = y := by grind
  rw [hzy] at ht
  have hc := ht 1 h (by omega)
  rw [coeff_add _ _ 1 h, comp_zero_right,
    coeff_C (b.coeff 0) 1 h, ite_eq_right (by omega),
    coeff_mul_right_lead (comp b.derivPad 0) y 1 h hyAgree,
    coeff_comp_zero b.derivPad 0 (coeff_zero 0),
    coeff_derivPad b 0 (by omega), ite_eq_left h,
    Lean.Grind.Semiring.natCast_one] at hc
  grind

/-- Newton reversion is both a left and right compositional inverse. -/
theorem revOfUnit_comp [Lean.Grind.CommRing R] (b : TSeries R n) (v : R)
    (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1) :
    comp b (revOfUnit b v) = X ∧ comp (revOfUnit b v) b = X := by
  let y := newton (revStep b v) (mulUpTo n (C v) X) (steps n)
  have hy0 : y.coeff 0 = 0 := (revNewton_correct b v h0 hv (steps n)).1
  have hyerr : Agree (2 ^ steps n) (comp b y - X) 0 :=
    (revNewton_correct b v h0 hv (steps n)).2
  have hleftY : comp b y = X := by
    apply Agree.full (Agree.ofSub hyerr) (two_pow_steps_ge n)
  have hrev : revOfUnit b v = y := revOfUnit_eq b v
  have hleft : comp b (revOfUnit b v) = X := by
    rw [hrev]
    exact hleftY
  have hrev0 : (revOfUnit b v).coeff 0 = 0 := by
    rw [hrev]
    exact hy0
  have hright0 : (comp (revOfUnit b v) b).coeff 0 = 0 := by
    rw [coeff_comp_zero (revOfUnit b v) b h0, hrev0]
  have hcomp : comp b (comp (revOfUnit b v) b) = comp b X := by
    calc
      comp b (comp (revOfUnit b v) b) =
          comp (comp b (revOfUnit b v)) b :=
        (comp_assoc b (revOfUnit b v) b hrev0 h0).symm
      _ = comp X b := by rw [hleft]
      _ = b := comp_X_left b h0
      _ = comp b X := (comp_X_right b).symm
  exact ⟨hleft, comp_left_cancel b (comp (revOfUnit b v) b) X
    hright0 X_coeff_zero v hv hcomp⟩

private theorem revOfUnit_chain [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) :
    Agree (n - 1)
      (comp (revOfUnit b v).derivPad b * b.derivPad) 1 := by
  have hchain := derivPad_comp_agree (revOfUnit b v) b h0
  have hcomp := (revOfUnit_comp b v h0 hv).2
  rw [hcomp] at hchain
  exact Agree.trans (Agree.symm hchain)
    (derivPad_X_agree (R := R) (n := n))

private theorem lagrange_coeff [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (b : TSeries R n) (v : R)
    (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1)
    (k : Nat) (hk : 0 < k) (hkn : k < n) :
    (((k : Nat) : R) * (revOfUnit b v).coeff k) =
      ((invOfUnit (shiftQuotient b) v) ^ k).coeff (k - 1) := by
  let g := revOfUnit b v
  let p := invOfUnit (shiftQuotient b) v
  have hchain := revOfUnit_chain b v h0 hv
  have hmul := Agree.mul (Agree.refl (n - 1) (p ^ k)) hchain
  have hcoeff := hmul (k - 1) (by omega) (by omega)
  change
    (p ^ k * (comp g.derivPad b * b.derivPad)).coeff (k - 1) =
      (p ^ k * 1).coeff (k - 1) at hcoeff
  rw [comp_spec g.derivPad b h0] at hcoeff
  change
    (p ^ k *
      ((List.range n).foldl
        (fun acc j => acc + C (g.derivPad.coeff j) * b ^ j) 0 *
        b.derivPad)).coeff (k - 1) =
      (p ^ k * 1).coeff (k - 1) at hcoeff
  have hfold :
      p ^ k *
          ((List.range n).foldl
            (fun acc j => acc + C (g.derivPad.coeff j) * b ^ j) 0 *
            b.derivPad) =
        (List.range n).foldl
          (fun acc j => acc +
            p ^ k * (C (g.derivPad.coeff j) * b ^ j) * b.derivPad) 0 := by
    calc
      p ^ k *
          ((List.range n).foldl
            (fun acc j => acc + C (g.derivPad.coeff j) * b ^ j) 0 *
            b.derivPad) =
          (p ^ k * (List.range n).foldl
            (fun acc j => acc + C (g.derivPad.coeff j) * b ^ j) 0) *
            b.derivPad := by grind
      _ = (List.range n).foldl
          (fun acc j => acc + p ^ k * (C (g.derivPad.coeff j) * b ^ j)) 0 *
            b.derivPad := by
          rw [List.foldl_add_mul_left_zero]
      _ = (List.range n).foldl
          (fun acc j => acc +
            p ^ k * (C (g.derivPad.coeff j) * b ^ j) * b.derivPad) 0 := by
          rw [List.foldl_add_mul_right_zero]
  rw [hfold, coeff_foldl_add (List.range n)
    (fun j => p ^ k * (C (g.derivPad.coeff j) * b ^ j) * b.derivPad)
    0 (k - 1) (by omega), coeff_zero, mul_one] at hcoeff
  have hterms :
      (List.range n).foldl
          (fun acc j => acc +
            (p ^ k * (C (g.derivPad.coeff j) * b ^ j) * b.derivPad).coeff
              (k - 1)) 0 =
        (((k : Nat) : R) * g.coeff k) := by
    calc
      (List.range n).foldl
          (fun acc j => acc +
            (p ^ k * (C (g.derivPad.coeff j) * b ^ j) * b.derivPad).coeff
              (k - 1)) 0 =
        (List.range n).foldl
          (fun acc j => acc + if j = k - 1 then
            (((k : Nat) : R) * g.coeff k) else 0) 0 := by
              apply List.foldl_add_congr
              intro j hj
              have hjn : j < n := List.mem_range.mp hj
              have halg :
                  p ^ k * (C (g.derivPad.coeff j) * b ^ j) * b.derivPad =
                    C (g.derivPad.coeff j) *
                      (p ^ k * b ^ j * b.derivPad) := by grind
              rw [halg, coeff_C_mul _ _ _ (by omega),
                coeff_lagrange_term b v h0 hv k j hk hkn]
              by_cases hjk : j = k - 1
              · subst j
                rw [ite_eq_left rfl, ite_eq_left (by omega),
                  coeff_derivPad g (k - 1) (by omega),
                  show k - 1 + 1 = k by omega, ite_eq_left hkn]
                grind
              · rw [ite_eq_right hjk, ite_eq_right (by omega)]
                grind
      _ = 0 + (((k : Nat) : R) * g.coeff k) :=
        List.foldl_add_single _ _ _ _ (List.mem_range.mpr (by omega))
          List.nodup_range
      _ = (((k : Nat) : R) * g.coeff k) := by grind
  rw [hterms] at hcoeff
  exact hcoeff

/-- A Newton reversion has zero constant coefficient. -/
theorem revOfUnit_coeff_zero [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) : (revOfUnit b v).coeff 0 = 0 := by
  rw [revOfUnit_eq b v]
  exact (revNewton_correct b v h0 hv (steps n)).1

/-- Direct Lagrange inversion agrees with Newton reversion whenever its
explicit natural-number divisions are available. -/
theorem revLagrange_eq [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (b : TSeries R n) (v : R)
    (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1) :
    revLagrange b v = revOfUnit b v := by
  apply ext
  intro i hi
  rw [coeff_revLagrange b v i hi]
  by_cases hi0 : i = 0
  · subst i
    rw [ite_eq_left rfl, revOfUnit_coeff_zero b v h0 hv]
  · rw [ite_eq_right hi0]
    have hlag := lagrange_coeff b v h0 hv i (by omega) hi
    have hinv := NatInverses.invNat_eq (R := R) (m := n - 1)
      i (by omega) (by omega)
    calc
      NatInverses.invNat (R := R) (m := n - 1) i *
          ((invOfUnit (shiftQuotient b) v) ^ i).coeff (i - 1) =
        NatInverses.invNat (R := R) (m := n - 1) i *
          (((i : Nat) : R) * (revOfUnit b v).coeff i) := by rw [hlag]
      _ = (((i : Nat) : R) *
          NatInverses.invNat (R := R) (m := n - 1) i) *
            (revOfUnit b v).coeff i := by grind
      _ = (revOfUnit b v).coeff i := by rw [hinv]; grind

/-- The compositional inverse retains the supplied inverse linear
coefficient. -/
theorem revOfUnit_coeff_one [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) (h : 1 < n) :
    (revOfUnit b v).coeff 1 = v := by
  have hleft := (revOfUnit_comp b v h0 hv).1
  have hrev0 : (revOfUnit b v).coeff 0 = 0 := by
    rw [revOfUnit_eq b v]
    exact (revNewton_correct b v h0 hv (steps n)).1
  have hc := coeff_comp_one b (revOfUnit b v) hrev0 h
  rw [hleft, coeff_X 1 h, ite_eq_left rfl] at hc
  calc
    (revOfUnit b v).coeff 1 = 1 * (revOfUnit b v).coeff 1 := by grind
    _ = (b.coeff 1 * v) * (revOfUnit b v).coeff 1 := by rw [hv]
    _ = v * (b.coeff 1 * (revOfUnit b v).coeff 1) := by grind
    _ = v := by rw [← hc]; grind

/-- At precision at most one, every zero-constant series reverts to zero. -/
theorem rev_le_one [Lean.Grind.CommRing R] (b : TSeries R n)
    (hn : n ≤ 1) (h0 : b.coeff 0 = 0) :
    comp b 0 = X ∧ comp 0 b = X := by
  have hb : b = 0 := by
    apply ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    rw [h0, coeff_zero]
  have hX : (X : TSeries R n) = 0 := by
    apply ext
    intro i hi
    rw [coeff_X i hi, coeff_zero]
    have hi0 : i = 0 := by omega
    simp [hi0]
  subst b
  rw [hX]
  exact ⟨comp_zero 0 (coeff_zero 0), comp_zero 0 (coeff_zero 0)⟩

/-- The bounded Newton implementation itself returns zero when no linear
coefficient is represented. -/
theorem revOfUnit_le_one [Lean.Grind.CommRing R] (b : TSeries R n) (v : R)
    (hn : n ≤ 1) : revOfUnit b v = 0 := by
  apply ext
  intro i hi
  have hn1 : n = 1 := by omega
  subst n
  have hi0 : i = 0 := by omega
  subst i
  unfold revOfUnit revUpTo steps
  simp only [Nat.min_self, ite_eq_left (by omega : 1 ≤ 1), newton]
  grind

/-- The Newton numerator vanishes throughout the precision already established
by an iterate. -/
theorem rev_numerator_valuation [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) (j i : Nat)
    (hi : i < min n (2 ^ j)) :
    (comp b (newton (revStep b v) (mulUpTo n (C v) X) j) - X).coeff i = 0 := by
  have h := (revNewton_correct b v h0 hv j).2 i (by omega) (by omega)
  rw [coeff_zero] at h
  exact h

/-- Optional reversion keeps the constant test at precision one while dropping
the nonexistent linear test. -/
theorem rev?_isSome_iff [Lean.Grind.CommRing R] [DecidableEq R]
    [UnitOps R] [LawfulUnitOps R] (b : TSeries R n) :
    (rev? b).isSome = true ↔
      b.coeff 0 = 0 ∧ (n ≤ 1 ∨ ∃ v, b.coeff 1 * v = 1) := by
  by_cases h0 : b.coeff 0 = 0
  · by_cases hn : n ≤ 1
    · simp [rev?, h0, hn]
    · rw [show rev? b =
        match UnitOps.inv? (R := R) (b.coeff 1) with
        | some v => some (revOfUnit b v)
        | none => none by simp [rev?, h0, hn]]
      cases hq : UnitOps.inv? (R := R) (b.coeff 1) with
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff, h0,
            true_and, hn, false_or]
          intro hunit
          have hsome := LawfulUnitOps.inv?_isSome (R := R) (b.coeff 1) hunit
          simp [hq] at hsome
      | some v =>
          simp only [Option.isSome_some, h0, true_and, hn, false_or, true_iff]
          exact ⟨v, LawfulUnitOps.inv?_eq (R := R) (b.coeff 1) v hq⟩
  · simp [rev?, h0]

end Hex.TSeries
