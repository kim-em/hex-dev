/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Sylvester
public import Mathlib.FieldTheory.Separable

public section

/-!
Agreement of the executable discriminant with Mathlib.
-/
namespace Hex.DensePoly

universe u

variable {R : Type u}

/-- The executable and Mathlib discriminants agree under dense-polynomial
correspondence. -/
theorem toPolynomial_disc [CommRing R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R] (f : DensePoly R) :
    disc f = Polynomial.discr (HexPolyMathlib.toPolynomial f) := by
  let F := HexPolyMathlib.toPolynomial f
  by_cases hsmall : f.size ≤ 1
  · unfold disc
    rw [ite_eq_left hsmall]
    have hdeg : F.natDegree = 0 := by
      rw [show F.natDegree = f.degree?.getD 0 by
        simpa only [F] using HexPolyMathlib.natDegree_toPolynomial f]
      by_cases hf : f = 0
      · subst f
        simp
      · have hfpos : 0 < f.size := by
          by_contra h
          apply hf
          exact (size_eq_zero_iff f).mp (by omega)
        rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
        omega
    change 1 = Polynomial.discr F
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    exact (Polynomial.discr_C _).symm
  · let n := f.size - 1
    let d := f.derivative
    let D := HexPolyMathlib.toPolynomial d
    let k := d.degree?.getD 0
    let gap := n - 1 - k
    have hfpos : 0 < f.size := by omega
    have hn : 0 < n := by
      dsimp only [n]
      omega
    have hFn : F.natDegree = n := by
      rw [show F.natDegree = f.degree?.getD 0 by
        simpa only [F] using HexPolyMathlib.natDegree_toPolynomial f]
      rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
    have hD : D = F.derivative := by
      simpa only [D, d, F] using HexPolyMathlib.toPolynomial_derivative f
    have hDk : D.natDegree = k := by
      simpa only [D, k] using HexPolyMathlib.natDegree_toPolynomial d
    have hk : k ≤ n - 1 := by
      rw [← hDk, hD, ← hFn]
      exact Polynomial.natDegree_derivative_le F
    have hkgap : k + gap = n - 1 := by
      dsimp only [gap]
      omega
    have hlc : F.leadingCoeff = f.leadingCoeff := by
      simpa only [F] using HexPolyMathlib.leadingCoeff_toPolynomial f
    have hactual :
        resultant f d = Polynomial.resultant F D n k := by
      rw [toPolynomial_resultant]
      rw [show f.degree?.getD 0 = n by
        rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]]
    have hpromote :
        powNat f.leadingCoeff gap * resultant f d =
          Polynomial.resultant F F.derivative n (n - 1) := by
      have hadd := Polynomial.resultant_add_right_deg F D n k gap
        (by rw [hDk])
      rw [hkgap, hD] at hadd
      have hcoeff : F.coeff n = F.leadingCoeff := by
        rw [← hFn]
        exact Polynomial.coeff_natDegree
      rw [powNat_eq_pow, hactual, ← hlc, hD, ← hcoeff]
      exact hadd.symm
    have hdegree : 0 < F.degree := by
      rw [← Polynomial.natDegree_pos_iff_degree_pos, hFn]
      exact hn
    have hformal := Polynomial.resultant_deriv (f := F) hdegree
    rw [hFn] at hformal
    rw [hlc] at hformal
    unfold disc
    rw [ite_eq_right hsmall]
    change
      negOnePow (R := R) (n * (n - 1) / 2) *
          exactDiv (powNat f.leadingCoeff gap * resultant f d)
            f.leadingCoeff =
        Polynomial.discr F
    rw [show powNat f.leadingCoeff (n - 1 - k) * resultant f d =
        Polynomial.resultant F F.derivative n (n - 1) by
      simpa only [gap] using hpromote]
    rw [hformal]
    rw [negOnePow_eq_sign,
      Hex.SubresultantMinor.sign_eq_pow]
    have hflc : f.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero_of_pos_size f hfpos
    have hdiv :
        exactDiv
            ((-1 : R) ^ (n * (n - 1) / 2) * f.leadingCoeff *
              Polynomial.discr F)
            f.leadingCoeff =
          (-1 : R) ^ (n * (n - 1) / 2) * Polynomial.discr F := by
      rw [show
          (-1 : R) ^ (n * (n - 1) / 2) * f.leadingCoeff *
              Polynomial.discr F =
            ((-1 : R) ^ (n * (n - 1) / 2) * Polynomial.discr F) *
              f.leadingCoeff by ring]
      exact Hex.exactDiv_mul_right _ hflc
    rw [hdiv]
    have hsign :
        (-1 : R) ^ (n * (n - 1) / 2) *
            (-1 : R) ^ (n * (n - 1) / 2) = 1 := by
      simpa only [← Hex.SubresultantMinor.sign_eq_pow] using
        (Hex.SubresultantMinor.sign_mul_self (R := R)
          (n * (n - 1) / 2))
    rw [← mul_assoc, hsign, one_mul]

/-- Mathlib's discriminant of a positive-degree product is the product of the
factor discriminants times the squared cross-resultant. The proof runs both
resultant multiplicativity laws through `resultant_deriv` and cancels the
common sign and leading-coefficient factors. -/
private theorem discr_mul [CommRing R] [IsDomain R]
    [IsAddTorsionFree R] (f g : Polynomial R)
    (hf : 0 < f.natDegree) (hg : 0 < g.natDegree) :
    Polynomial.discr (f * g) =
      Polynomial.discr f * Polynomial.discr g *
        Polynomial.resultant f g ^ 2 := by
  let m := f.natDegree
  let n := g.natDegree
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hf
    omega
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hg
    omega
  have hdf0 : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt hf)
  have hdg0 : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt hg)
  have hdf : f.derivative.natDegree = m - 1 := by
    simpa only [m] using Polynomial.natDegree_derivative f
  have hdg : g.derivative.natDegree = n - 1 := by
    simpa only [n] using Polynomial.natDegree_derivative g
  have hfg : (f * g).natDegree = m + n := by
    simpa only [m, n] using Polynomial.natDegree_mul hf0 hg0
  have hdfg : (f.derivative * g).natDegree = m - 1 + n := by
    rw [Polynomial.natDegree_mul hdf0 hg0, hdf]
  have hfdg : (f * g.derivative).natDegree = m + (n - 1) := by
    rw [Polynomial.natDegree_mul hf0 hdg0, hdg]
  have hresF :
      Polynomial.resultant f (f.derivative * g + f * g.derivative)
          m (m + n - 1) =
        Polynomial.resultant f f.derivative m (m - 1) *
          Polynomial.resultant f g m n := by
    calc
      Polynomial.resultant f (f.derivative * g + f * g.derivative)
            m (m + n - 1) =
          Polynomial.resultant f (f.derivative * g) m (m + n - 1) := by
            apply Polynomial.resultant_add_mul_right
            · rw [hdg]
              omega
            · exact le_rfl
      _ = Polynomial.resultant f f.derivative m (m - 1) *
            Polynomial.resultant f g m n := by
            have h := Polynomial.resultant_mul_right
              f f.derivative g m (by exact le_rfl)
            change
              Polynomial.resultant f (f.derivative * g) m
                  (f.derivative.natDegree + g.natDegree) =
                Polynomial.resultant f f.derivative m
                    f.derivative.natDegree *
                  Polynomial.resultant f g m g.natDegree at h
            rw [hdf] at h
            change
              Polynomial.resultant f (f.derivative * g) m (m - 1 + n) =
                Polynomial.resultant f f.derivative m (m - 1) *
                  Polynomial.resultant f g m n at h
            rw [show m + n - 1 = m - 1 + n by omega]
            exact h
  have hresG :
      Polynomial.resultant g (f.derivative * g + f * g.derivative)
          n (m + n - 1) =
        Polynomial.resultant g f n m *
          Polynomial.resultant g g.derivative n (n - 1) := by
    rw [show f.derivative * g + f * g.derivative =
        f * g.derivative + g * f.derivative by ring]
    calc
      Polynomial.resultant g (f * g.derivative + g * f.derivative)
            n (m + n - 1) =
          Polynomial.resultant g (f * g.derivative) n (m + n - 1) := by
            apply Polynomial.resultant_add_mul_right
            · rw [hdf]
              omega
            · exact le_rfl
      _ = Polynomial.resultant g f n m *
            Polynomial.resultant g g.derivative n (n - 1) := by
            have h := Polynomial.resultant_mul_right
              g f g.derivative n (by exact le_rfl)
            change
              Polynomial.resultant g (f * g.derivative) n
                  (f.natDegree + g.derivative.natDegree) =
                Polynomial.resultant g f n f.natDegree *
                  Polynomial.resultant g g.derivative n
                    g.derivative.natDegree at h
            rw [hdg] at h
            change
              Polynomial.resultant g (f * g.derivative) n (m + (n - 1)) =
                Polynomial.resultant g f n m *
                  Polynomial.resultant g g.derivative n (n - 1) at h
            rw [show m + n - 1 = m + (n - 1) by omega]
            exact h
  have hresMul :
      Polynomial.resultant (f * g) (f * g).derivative
          (m + n) (m + n - 1) =
        (Polynomial.resultant f f.derivative m (m - 1) *
            Polynomial.resultant f g m n) *
          (Polynomial.resultant g f n m *
            Polynomial.resultant g g.derivative n (n - 1)) := by
    rw [Polynomial.derivative_mul]
    have hderiv :
        (f.derivative * g + f * g.derivative).natDegree ≤
          m + n - 1 := by
      rw [← Polynomial.derivative_mul]
      calc
        (f * g).derivative.natDegree ≤ (f * g).natDegree - 1 :=
          Polynomial.natDegree_derivative_le (f * g)
        _ = m + n - 1 := by rw [hfg]
    have h := Polynomial.resultant_mul_left f g
      (f.derivative * g + f * g.derivative) (m + n - 1)
      hderiv
    rw [hresF, hresG] at h
    simpa only [m, n] using h
  have hdegF : 0 < f.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    exact hf
  have hdegG : 0 < g.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    exact hg
  have hdegMul : 0 < (f * g).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hfg]
    omega
  have hdiscF := Polynomial.resultant_deriv (f := f) hdegF
  have hdiscG := Polynomial.resultant_deriv (f := g) hdegG
  have hdiscMul := Polynomial.resultant_deriv (f := f * g) hdegMul
  rw [hfg] at hdiscMul
  have hcomm := Polynomial.resultant_comm g f n m
  have htri :
      (m + n) * (m + n - 1) / 2 =
        m * (m - 1) / 2 + n * (n - 1) / 2 + m * n := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Nat.succ_add, Nat.triangle_succ, Nat.triangle_succ, ih]
        ring
  rw [hdiscMul, hdiscF, hdiscG, hcomm,
    Nat.mul_comm n m] at hresMul
  rw [htri, pow_add, pow_add] at hresMul
  rw [Polynomial.leadingCoeff_mul] at hresMul
  have hlcf : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
  have hlcg : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
  let s : R :=
    (-1 : R) ^ (m * (m - 1) / 2) *
      (-1 : R) ^ (n * (n - 1) / 2) * (-1 : R) ^ (m * n)
  have hpow (k : Nat) : (-1 : R) ^ k ≠ 0 := by
    rw [← Hex.SubresultantMinor.sign_eq_pow]
    exact Hex.SubresultantMinor.sign_ne_zero one_ne_zero k
  have hs0 : s ≠ 0 := by
    dsimp only [s]
    exact mul_ne_zero (mul_ne_zero (hpow _) (hpow _)) (hpow _)
  have hcancelSign :
      f.leadingCoeff * g.leadingCoeff * Polynomial.discr (f * g) =
        f.leadingCoeff * g.leadingCoeff *
          (Polynomial.discr f * Polynomial.discr g *
            Polynomial.resultant f g ^ 2) := by
    apply mul_left_cancel₀ hs0
    calc
      s * (f.leadingCoeff * g.leadingCoeff * Polynomial.discr (f * g)) =
          (-1 : R) ^ (m * (m - 1) / 2) *
              (-1 : R) ^ (n * (n - 1) / 2) * (-1 : R) ^ (m * n) *
            (f.leadingCoeff * g.leadingCoeff) * Polynomial.discr (f * g) := by
        dsimp only [s]
        ring
      _ = (-1 : R) ^ (m * (m - 1) / 2) * f.leadingCoeff *
            Polynomial.discr f * Polynomial.resultant f g m n *
          ((-1 : R) ^ (m * n) * Polynomial.resultant f g m n *
            ((-1 : R) ^ (n * (n - 1) / 2) * g.leadingCoeff *
              Polynomial.discr g)) := hresMul
      _ = s * (f.leadingCoeff * g.leadingCoeff *
            (Polynomial.discr f * Polynomial.discr g *
              Polynomial.resultant f g ^ 2)) := by
        ring
  apply mul_left_cancel₀ (mul_ne_zero hlcf hlcg)
  exact hcancelSign

/-- Discriminants multiply with the square of the cross-resultant.

The positive-degree hypotheses are essential: Mathlib and the executable API
assign discriminant one to constants, while multiplying by a nonunit constant
scales the other discriminant. -/
theorem disc_mul [CommRing R] [IsDomain R] [IsAddTorsionFree R]
    [DecidableEq R] [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly R) (hf : 0 < f.degree?.getD 0)
    (hg : 0 < g.degree?.getD 0) :
    disc (f * g) = disc f * disc g * resultant f g ^ 2 := by
  have hf' : 0 < (HexPolyMathlib.toPolynomial f).natDegree := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    exact hf
  have hg' : 0 < (HexPolyMathlib.toPolynomial g).natDegree := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    exact hg
  rw [toPolynomial_disc, toPolynomial_disc, toPolynomial_disc,
    HexPolyMathlib.toPolynomial_mul, toPolynomial_resultant]
  simpa only [HexPolyMathlib.natDegree_toPolynomial] using
    discr_mul _ _ hf' hg'

/-- A positive-degree polynomial over a characteristic-zero field has
nonzero executable discriminant exactly when it is separable. -/
theorem disc_ne_zero_iff_separable [Field R] [IsAddTorsionFree R]
    [DecidableEq R] [Hex.ExactDivLaws R]
    (f : DensePoly R) (hf : 0 < f.degree?.getD 0) :
    disc f ≠ 0 ↔ (HexPolyMathlib.toPolynomial f).Separable := by
  let F := HexPolyMathlib.toPolynomial f
  have hFn : F.natDegree = f.degree?.getD 0 := by
    simpa only [F] using HexPolyMathlib.natDegree_toPolynomial f
  have hFpos : 0 < F.natDegree := by rw [hFn]; exact hf
  have hF0 : F ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hFpos
    omega
  have hdegree : 0 < F.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    exact hFpos
  have hderiv : F.derivative.natDegree = F.natDegree - 1 :=
    Polynomial.natDegree_derivative F
  have hres := Polynomial.resultant_deriv (f := F) hdegree
  rw [← hderiv] at hres
  have hlc : F.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hF0
  have hsign :
      (-1 : R) ^ (F.natDegree * F.derivative.natDegree / 2) ≠ 0 := by
    rw [← Hex.SubresultantMinor.sign_eq_pow]
    exact Hex.SubresultantMinor.sign_ne_zero one_ne_zero _
  have hresultantZero :
      Polynomial.resultant F F.derivative = 0 ↔ F.discr = 0 := by
    rw [hres]
    simp only [mul_eq_zero, hsign, hlc, false_or]
  have hcoprimeZero :
      Polynomial.resultant F F.derivative = 0 ↔
        ¬ IsCoprime F F.derivative := by
    simpa [hF0] using
      (Polynomial.resultant_eq_zero_iff
        (f := F) (g := F.derivative))
  have hzero : F.discr = 0 ↔ ¬ IsCoprime F F.derivative := by
    exact hresultantZero.symm.trans hcoprimeZero
  rw [toPolynomial_disc, Polynomial.separable_def]
  change F.discr ≠ 0 ↔ IsCoprime F F.derivative
  constructor
  · intro hdisc
    by_contra hnot
    exact hdisc (hzero.mpr hnot)
  · intro hcoprime hdisc
    exact (hzero.mp hdisc) hcoprime

/-! Trust-surface regression checks for the headline discriminant contracts. -/

/--
info: 'Hex.DensePoly.toPolynomial_disc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toPolynomial_disc

/--
info: 'Hex.DensePoly.disc_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms disc_mul

/--
info: 'Hex.DensePoly.disc_ne_zero_iff_separable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms disc_ne_zero_iff_separable

end Hex.DensePoly
