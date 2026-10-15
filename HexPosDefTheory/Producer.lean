/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Augmented
public import HexMatrixTheory.Algebra
public import HexPosDef.Producer
import all HexPosDef.Producer
import all HexPosDefTheory.Augmented

public section

/-! Invariants for the native no-swap recurrence and exact division by real pivots. -/

namespace Hex.PosDefTheory.Producer

open Hex.PosDef
open HexMatrixTheory

variable {R : Type} [CommRing R]

/-- A proof-only extension of division by real pivots to a total exact
quotient. It agrees with native division whenever the denominator is real. -/
noncomputable def quotient (a : PosDef.Producer.Arithmetic R) (x y : R) : R := by
  classical
  exact match a.real y with
  | some p => a.div x p
  | none => if h : ∃ q, q * y = x then Classical.choose h else 0

theorem quotient_mul [NoZeroDivisors R] (a : PosDef.Producer.Arithmetic R)
    (hreal : ∀ z p, a.real z = some p ↔ z = (p : R))
    (hdiv : ∀ (q : R) (p : Int), p ≠ 0 → a.div (q * (p : R)) p = q)
    (q y : R) (hy : y ≠ 0) : quotient a (q * y) y = q := by
  unfold quotient
  cases he : a.real y with
  | none =>
    simp only
    rw [dite_eq_left (show ∃ q', q' * y = q * y from ⟨q, rfl⟩)]
    exact mul_right_cancel₀ hy (Classical.choose_spec (show ∃ q', q' * y = q * y from ⟨q, rfl⟩))
  | some p =>
    simp only
    have hy' := (hreal y p).mp he
    have hp : p ≠ 0 := by intro hp; simp [hp] at hy'; exact hy hy'
    rw [hy']
    exact hdiv q p hp

theorem quotient_real (a : PosDef.Producer.Arithmetic R)
    (hreal : ∀ z p, a.real z = some p ↔ z = (p : R)) (x : R) (p : Int) :
    quotient a x (p : R) = a.div x p := by
  simp only [quotient, (hreal (p : R) p).mpr rfl]

/-- The two native blocks interpreted as a state of the existing square
Bareiss recurrence. -/
def state (k : Nat) (s : PosDef.Producer.State R n) : Hex.Matrix.BareissState R (n + n) :=
  { step := k
    matrix := augment s.left s.right
    prevPivot := (s.previous : R)
    rowSwaps := 0
    singularStep := none }

/-- The elimination invariant records the augmented minors, transform
equation, triangular support, and frozen positive pivots. -/
structure Invariant (B : Hex.Matrix R n n) (k : Nat) (s : PosDef.Producer.State R n) : Prop where
  step_le : k ≤ n
  previous_pos : 0 < s.previous
  minors : BareissNoPivotInvariant (augment B (Hex.Matrix.identity n)) (state k s)
  product : matrixEquiv s.left = matrixEquiv s.right * matrixEquiv B
  lower : (matrixEquiv s.right).IsLowerTriangular
  zeros : ∀ (i j : Fin n), j.val < k → j.val < i.val → s.left[i][j] = 0
  diagonal : ∀ (i : Fin n), k ≤ i.val → s.right[i][i] = (s.previous : R)
  frozen : ∀ (i : Fin n), i.val < k → ∃ p l : Int,
    0 < p ∧ 0 < l ∧ s.left[i][i] = (p : R) ∧ s.right[i][i] = (l : R)

theorem initial_invariant [Nontrivial R] (a : PosDef.Producer.Arithmetic R)
    (hz : a.zero = 0) (ho : a.one = 1) (B : Hex.Matrix R n n) :
    Invariant B 0 (PosDef.Producer.initial a B) := by
  have hl : (PosDef.Producer.initial a B).left = B := rfl
  have hp : (PosDef.Producer.initial a B).previous = 1 := rfl
  have hr : (PosDef.Producer.initial a B).right = (1 : Hex.Matrix R n n) := by
    apply matrixEquiv.injective
    rw [matrixEquiv_one]
    ext i j
    rw [matrixEquiv_apply]
    change (Hex.Matrix.ofFn (fun i j : Fin n => if i = j then a.one else a.zero))[i][j] = _
    rw [Hex.Matrix.getElem_ofFn, Matrix.one_apply]
    simp only [hz, ho]
  have hs : state 0 (PosDef.Producer.initial a B) =
      Hex.Matrix.noPivotInitialState (augment B (Hex.Matrix.identity n)) := by
    simp only [state, hl, hr, hp, Int.cast_one, Hex.Matrix.noPivotInitialState]
    rfl
  refine ⟨by omega, by rw [hp]; decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]
    exact bareissNoPivotInvariant_initialWith _ one_ne_zero
  · rw [hl, hr, matrixEquiv_one, one_mul]
  · rw [hr, matrixEquiv_one]
    intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    simp [hne]
  · intro i j hj _
    omega
  · intro i _
    rw [hr, ← matrixEquiv_apply, matrixEquiv_one, Matrix.one_apply]
    simp [hp]
  · intro i hi
    omega

theorem augment_step [NoZeroDivisors R] [CharZero R]
    (a : PosDef.Producer.Arithmetic R)
    (hmul : ∀ x y, a.mul x y = x * y) (hsub : ∀ x y, a.sub x y = x - y)
    (hreal : ∀ z p, a.real z = some p ↔ z = (p : R))
    (hdiv : ∀ (q : R) (p : Int), p ≠ 0 → a.div (q * (p : R)) p = q)
    (s : PosDef.Producer.State R n) (k : Fin n) (p : Int) (hp : s.previous ≠ 0)
    (hzeros : ∀ (i j : Fin n), j.val < k.val → j.val < i.val → s.left[i][j] = 0) :
    augment (PosDef.Producer.step a s k p).left (PosDef.Producer.step a s k p).right =
      Hex.Matrix.stepMatrixWith (quotient a) (augment s.left s.right) k.val
        s.left[k][k] (s.previous : R) := by
  have hd (x : R) : a.div x s.previous = quotient a x (s.previous : R) :=
    (quotient_real a hreal x s.previous).symm
  have hq0 : quotient a 0 (s.previous : R) = 0 := by
    simpa only [zero_mul] using quotient_mul a hreal hdiv 0 (s.previous : R)
      (Int.cast_ne_zero.mpr hp)
  apply Hex.Matrix.ext_getElem
  intro i j
  rw [Hex.Matrix.stepMatrixWith_eq_ofFn, Hex.Matrix.getElem_ofFn]
  by_cases hi : i.val < n
  · by_cases hj : j.val < n
    · let ii : Fin n := ⟨i.val, hi⟩
      let jj : Fin n := ⟨j.val, hj⟩
      by_cases hki : k.val < i.val
      · by_cases hkj : k.val < j.val
        · simp only [augment, PosDef.Producer.step, Hex.Matrix.getElem_pair_eq_nested,
            Hex.Matrix.getElem_ofFn, Fin.eta,      hi, hj, hki, hkj, k.isLt, dite_eq_left,
            ite_eq_left, hmul, hsub, hd, and_self]
        · by_cases he : j.val = k.val
          · have hjk : jj = k := Fin.ext he
            have hcancel : s.left[k][k] * s.left[ii][k] - s.left[ii][k] * s.left[k][k] = 0 :=
              sub_eq_zero.mpr (mul_comm _ _)
            simp only [augment, PosDef.Producer.step, Hex.Matrix.getElem_pair_eq_nested,
              Hex.Matrix.getElem_ofFn, Fin.eta, dite_false, lt_self_iff_false, hi, hki, he,
              k.isLt, dite_eq_left, ite_eq_left, and_true, and_false, hmul, hsub, hd]
            change quotient a (s.left[k][k] * s.left[ii][k] - s.left[ii][k] * s.left[k][k])
              (s.previous : R) = 0
            rw [hcancel, hq0]
          · have hjk : j.val < k.val := by omega
            have hij := hzeros ii jj hjk (by dsimp [ii, jj]; omega)
            have hkj' := hzeros k jj hjk hjk
            simp only [augment, PosDef.Producer.step, Hex.Matrix.getElem_pair_eq_nested,
              Hex.Matrix.getElem_ofFn, Fin.eta, dite_false, ite_false, hi, hj, hki, hkj, he,
              k.isLt, dite_eq_left, ite_eq_left, and_false, hmul, hsub, hd,]
            change quotient a (s.left[k][k] * s.left[ii][jj] - s.left[ii][k] * s.left[k][jj])
              (s.previous : R) = s.left[ii][jj]
            rw [hij, hkj']
            simp [hq0]
      · simp only [augment, PosDef.Producer.step, Hex.Matrix.getElem_pair_eq_nested,
          Hex.Matrix.getElem_ofFn, Fin.eta, dite_false, ite_false,    hi, hj, hki, k.isLt, dite_eq_left,
          false_and]
    · have hkj : k.val < j.val := by omega
      by_cases hki : k.val < i.val <;>
        simp only [augment, PosDef.Producer.step, Hex.Matrix.getElem_pair_eq_nested,
          Hex.Matrix.getElem_ofFn, Fin.eta, dite_false, ite_false, hi, hj, hki, hkj, k.isLt,
          dite_eq_left, ite_eq_left, true_and, false_and, hmul, hsub, hd]
  · simp only [augment, Hex.Matrix.getElem_ofFn, Fin.eta, dite_false,     Hex.Matrix.getElem_pair_eq_nested,
      hi]
    split_ifs <;> simp [         hq0]

theorem left_divisible (B : Hex.Matrix R n n) (s : PosDef.Producer.State R n) (k : Fin n)
    (h : Invariant B k.val s) (i j : Fin n) (hi : k.val < i.val) :
    ∃ q : R, s.left[k][k] * s.left[i][j] - s.left[i][k] * s.left[k][j] = q * (s.previous : R) := by
  classical
  by_cases hj : k.val < j.val
  · have he := trailing_divisible (augment B (Hex.Matrix.identity n)) (state k.val s)
      h.minors (i.castAdd n) (j.castAdd n) hi hj
    change ∃ q : R,
      (augment s.left s.right)[k.castAdd n][k.castAdd n] *
          (augment s.left s.right)[i.castAdd n][j.castAdd n] -
        (augment s.left s.right)[i.castAdd n][k.castAdd n] *
          (augment s.left s.right)[k.castAdd n][j.castAdd n] = q * (s.previous : R) at he
    simpa only [augment_left] using he
  · refine ⟨0, ?_⟩
    by_cases hjk : j = k
    · subst j
      rw [mul_comm s.left[k][k], sub_self, zero_mul]
    · have hjk' : j.val < k.val := by omega
      rw [h.zeros i j hjk' (by omega), h.zeros k j hjk' hjk', mul_zero, mul_zero,
        sub_self, zero_mul]

theorem right_divisible (B : Hex.Matrix R n n) (s : PosDef.Producer.State R n) (k : Fin n)
    (h : Invariant B k.val s) (i j : Fin n) (hi : k.val < i.val) :
    ∃ q : R, s.left[k][k] * s.right[i][j] - s.left[i][k] * s.right[k][j] = q * (s.previous : R) := by
  classical
  have he := Hex.PosDefTheory.right_divisible B (Hex.Matrix.identity n) (state k.val s)
    h.minors i j hi
  change ∃ q : R,
    (augment s.left s.right)[k.castAdd n][k.castAdd n] *
        (augment s.left s.right)[i.castAdd n][j.natAdd n] -
      (augment s.left s.right)[i.castAdd n][k.castAdd n] *
        (augment s.left s.right)[k.castAdd n][j.natAdd n] = q * (s.previous : R) at he
  simpa only [augment_left, augment_right] using he

theorem step_left (a : PosDef.Producer.Arithmetic R)
    (hmul : ∀ x y, a.mul x y = x * y) (hsub : ∀ x y, a.sub x y = x - y)
    (s : PosDef.Producer.State R n) (k : Fin n) (p : Int) (i j : Fin n) :
    (PosDef.Producer.step a s k p).left[i][j] =
      if k.val < i.val then
        a.div (s.left[k][k] * s.left[i][j] - s.left[i][k] * s.left[k][j]) s.previous
      else s.left[i][j] := by
  change (Hex.Matrix.ofFn (n := n) (m := n) _)[i][j] = _
  rw [Hex.Matrix.getElem_ofFn]
  simp only [Hex.Matrix.getElem_pair_eq_nested, hmul, hsub]

theorem step_right (a : PosDef.Producer.Arithmetic R)
    (hmul : ∀ x y, a.mul x y = x * y) (hsub : ∀ x y, a.sub x y = x - y)
    (s : PosDef.Producer.State R n) (k : Fin n) (p : Int) (i j : Fin n) :
    (PosDef.Producer.step a s k p).right[i][j] =
      if k.val < i.val then
        a.div (s.left[k][k] * s.right[i][j] - s.left[i][k] * s.right[k][j]) s.previous
      else s.right[i][j] := by
  change (Hex.Matrix.ofFn (n := n) (m := n) _)[i][j] = _
  rw [Hex.Matrix.getElem_ofFn]
  simp only [Hex.Matrix.getElem_pair_eq_nested, hmul, hsub]

theorem minors_next [NoZeroDivisors R] [CharZero R]
    (a : PosDef.Producer.Arithmetic R)
    (hmul : ∀ x y, a.mul x y = x * y) (hsub : ∀ x y, a.sub x y = x - y)
    (hreal : ∀ z p, a.real z = some p ↔ z = (p : R))
    (hdiv : ∀ (q : R) (p : Int), p ≠ 0 → a.div (q * (p : R)) p = q)
    (B : Hex.Matrix R n n) (s : PosDef.Producer.State R n) (k : Fin n)
    (h : Invariant B k.val s) (p : Int) (hp : 0 < p)
    (hpivot : a.real s.left[k][k] = some p) :
    BareissNoPivotInvariant (augment B (Hex.Matrix.identity n))
      (state (k.val + 1) (PosDef.Producer.step a s k p)) := by
  classical
  have he : s.left[k][k] = (p : R) := (hreal _ _).mp hpivot
  have hn : s.left[k][k] ≠ 0 := he ▸ Int.cast_ne_zero.mpr hp.ne'
  have ha : (state k.val s).matrix[(⟨k.val, by omega⟩ : Fin (n + n))][
      (⟨k.val, by omega⟩ : Fin (n + n))] = s.left[k][k] := by
    change (augment s.left s.right)[k.castAdd n][k.castAdd n] = _
    exact augment_left _ _ k k
  have haNat : (augment s.left s.right)[k.val][k.val] = s.left[k][k] := by
    simpa only [state, Hex.Matrix.getElem_nat_eq_getRow, Hex.Matrix.getElem_eq_getRow,
      Fin.getElem_fin] using ha
  have hh := bareissPivotInvariant_regular_no_swap (quotient a)
    (quotient_mul a hreal hdiv) (augment B (Hex.Matrix.identity n)) (state k.val s)
    h.minors (by change k.val + 1 < n + n; omega) (by
      change (augment s.left s.right)[k.val][k.val] ≠ 0
      rw [haNat]
      exact hn)
  change BareissNoPivotInvariant (augment B (Hex.Matrix.identity n))
    { step := k.val + 1
      matrix := augment (PosDef.Producer.step a s k p).left (PosDef.Producer.step a s k p).right
      prevPivot := (p : R)
      rowSwaps := 0
      singularStep := none }
  rw [augment_step a hmul hsub hreal hdiv s k p h.previous_pos.ne' h.zeros, ← he]
  simpa only [state, haNat] using hh

omit [CommRing R] in
theorem entry_eq (M : Hex.Matrix R n n) (i j : Fin n) : matrixEquiv M i j = M[i][j] := by
  rw [matrixEquiv_apply]

theorem next_invariant [NoZeroDivisors R] [CharZero R]
    (a : PosDef.Producer.Arithmetic R)
    (hmul : ∀ x y, a.mul x y = x * y) (hsub : ∀ x y, a.sub x y = x - y)
    (hreal : ∀ z p, a.real z = some p ↔ z = (p : R))
    (hdiv : ∀ (q : R) (p : Int), p ≠ 0 → a.div (q * (p : R)) p = q)
    (B : Hex.Matrix R n n) (s : PosDef.Producer.State R n) (k : Fin n)
    (h : Invariant B k.val s) (p : Int) (hp : 0 < p)
    (hpivot : a.real s.left[k][k] = some p) :
    Invariant B (k.val + 1) (PosDef.Producer.step a s k p) := by
  classical
  let next := PosDef.Producer.step a s k p
  have hprev : s.previous ≠ 0 := h.previous_pos.ne'
  have hzero : a.div 0 s.previous = 0 := by simpa only [zero_mul] using hdiv 0 s.previous hprev
  have hP : s.left[k][k] = (p : R) := (hreal _ _).mp hpivot
  have lower (i j : Fin n) (hij : i < j) : s.right[i][j] = 0 := by
    simpa only [entry_eq] using h.lower hij
  have exact_div (x : R) (hx : ∃ q : R, x = q * (s.previous : R)) :
      a.div x s.previous * (s.previous : R) = x := by
    obtain ⟨q, hq⟩ := hx
    rw [hq, hdiv q s.previous hprev]
  have hL (i j : Fin n) (hi : k.val < i.val) :
      next.left[i][j] * (s.previous : R) =
        s.left[k][k] * s.left[i][j] - s.left[i][k] * s.left[k][j] := by
    rw [step_left a hmul hsub, ite_eq_left hi]
    exact exact_div _ (left_divisible B s k h i j hi)
  have hT (i j : Fin n) (hi : k.val < i.val) :
      next.right[i][j] * (s.previous : R) =
        s.left[k][k] * s.right[i][j] - s.left[i][k] * s.right[k][j] := by
    rw [step_right a hmul hsub, ite_eq_left hi]
    exact exact_div _ (right_divisible B s k h i j hi)
  refine ⟨by omega, hp, minors_next a hmul hsub hreal hdiv B s k h p hp hpivot,
    ?_, ?_, ?_, ?_, ?_⟩
  · apply transform_step (matrixEquiv B) (matrixEquiv s.left) (matrixEquiv s.right)
      (matrixEquiv next.left) (matrixEquiv next.right) k s.left[k][k] (s.previous : R)
      (Int.cast_ne_zero.mpr hprev) h.product (fun i => k.val < i.val)
    · intro i j hi; simpa only [entry_eq] using hL i j hi
    · intro i j hi; simpa only [entry_eq] using hT i j hi
    · intro i j hi
      simp only [entry_eq, next, step_left a hmul hsub, ite_eq_right hi]
    · intro i j hi
      simp only [entry_eq, next, step_right a hmul hsub, ite_eq_right hi]
  · intro i j hij
    change matrixEquiv next.right i j = 0
    rw [entry_eq, step_right a hmul hsub]
    have hij' : i.val < j.val := hij
    split
    next hi =>
      rw [lower i j hij, lower k j (by show k.val < j.val; omega)]
      simp [hzero]
    next => exact lower i j hij
  · intro i j hj hji
    rw [step_left a hmul hsub]
    split
    next hi =>
      by_cases hjk : j.val < k.val
      · rw [h.zeros i j hjk hji, h.zeros k j hjk hjk]
        simp [hzero]
      · have hjk : j = k := Fin.ext (by omega)
        subst j
        have he : s.left[k][k] * s.left[i][k] - s.left[i][k] * s.left[k][k] = 0 := by ring
        rw [he, hzero]
    next hi => exact h.zeros i j (by omega) hji
  · intro i hi
    change next.right[i][i] = (p : R)
    rw [step_right a hmul hsub, ite_eq_left (by omega), h.diagonal i (by omega),
      lower k i (by show k.val < i.val; omega), mul_zero, sub_zero,
      hdiv _ s.previous hprev, hP]
  · intro i hi
    by_cases hik : i.val < k.val
    · obtain ⟨q, l, hq, hl, hli, hri⟩ := h.frozen i hik
      refine ⟨q, l, hq, hl, ?_, ?_⟩
      · rw [step_left a hmul hsub, ite_eq_right (by omega), hli]
      · rw [step_right a hmul hsub, ite_eq_right (by omega), hri]
    · have hik : i = k := Fin.ext (by omega)
      subst i
      refine ⟨p, s.previous, hp, h.previous_pos, ?_, ?_⟩
      · rw [step_left a hmul hsub, ite_eq_right (by omega), hP]
      · rw [step_right a hmul hsub, ite_eq_right (by omega), h.diagonal k (by omega)]

/-- Native Gaussian pivot recognition agrees with integer scalar inclusion. -/
theorem gaussian_real (z : PosDef.Gaussian) (p : Int) :
    PosDef.Producer.gaussianArithmetic.real z = some p ↔ z = (p : PosDef.Gaussian) := by
  change (if z.im = 0 then some z.re else none) = some p ↔ z = ⟨p, 0⟩
  cases z with
  | mk re im =>
    by_cases hi : im = 0 <;> simp [hi, PosDef.Gaussian.mk.injEq]

/-- Division by a preceding real nonzero pivot cancels multiplication exactly
in both native Gaussian components. -/
theorem gaussian_div_mul (q : PosDef.Gaussian) (p : Int) (hp : p ≠ 0) :
    PosDef.Producer.gaussianArithmetic.div (q * (p : PosDef.Gaussian)) p = q := by
  cases q with
  | mk re im =>
    change (⟨HexArith.Int.exactDiv (re * p - im * 0) p,
      HexArith.Int.exactDiv (re * 0 + im * p) p⟩ : PosDef.Gaussian) = ⟨re, im⟩
    simp [HexArith.Int.exactDiv, hp]

end Hex.PosDefTheory.Producer
