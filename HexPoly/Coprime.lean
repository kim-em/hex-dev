/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly.Field

public section

namespace Hex.DensePoly

universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]

/-- A Bézout identity witnesses coprimality without storing a gcd. -/
@[expose]
def Coprime (p q : DensePoly K) : Prop :=
  ∃ s t, s * p + t * q = 1

/-- The constant polynomial one is monic. -/
theorem monic_one : (1 : DensePoly K).Monic := leadingCoeff_one

/-- Multiplication by a nonzero polynomial is injective. -/
theorem mul_right_cancel {a b c : DensePoly K} (hc : c ≠ 0)
    (h : a * c = b * c) : a = b := by
  have h' := congrArg (fun p => (divMod p c).1) h
  simpa only [divMod_mul_field _ _ hc] using h'

/-- A product of nonzero polynomials over a field is nonzero. -/
theorem mul_ne_zero {p q : DensePoly K} (hp : p ≠ 0) (hq : q ≠ 0) :
    p * q ≠ 0 := by
  intro h
  exact hp (mul_right_cancel hq (by grind))

/-- A nonzero polynomial has a nonzero leading coefficient. -/
theorem leadingCoeff_ne_zero {p : DensePoly K} (hp : p ≠ 0) :
    p.leadingCoeff ≠ 0 :=
  leadingCoeff_ne_zero_of_pos_size p
    (Nat.pos_of_ne_zero (fun h => hp ((size_eq_zero_iff p).mp h)))

/-- Scaling by one leaves a polynomial unchanged. -/
theorem scale_one (p : DensePoly K) : scale (1 : K) p = p := by
  apply ext_coeff
  intro i
  rw [coeff_scale_semiring]
  grind

/-- Scaling is multiplication by the corresponding constant polynomial. -/
theorem scale_eq_C_mul (a : K) (p : DensePoly K) : scale a p = C a * p := by
  have h : scale a (1 : DensePoly K) = C a := by
    apply ext_coeff
    intro i
    rw [coeff_scale_semiring]
    change a * (C 1).coeff i = (C a).coeff i
    simp only [coeff_C]
    split
    · exact Lean.Grind.Semiring.mul_one a
    · exact Lean.Grind.Semiring.mul_zero a
  rw [← h, ← scale_mul]
  congr 1
  grind

/-- Monic normalization is scalar multiplication, including at zero. -/
theorem monicize_eq_scale (p : DensePoly K) :
    monicize p = scale p.leadingCoeff⁻¹ p := by
  by_cases hp : p = 0
  · subst p
    apply ext_coeff
    intro i
    rw [monicize_zero, coeff_scale_semiring, coeff_zero]
    exact (Lean.Grind.Semiring.mul_zero _).symm
  · exact (scale_inv_eq_monicize hp).symm

/-- The monic gcd admits Bézout coefficients. -/
theorem bezout_monicize_gcd (p q : DensePoly K) :
    ∃ s t, s * p + t * q = monicize (gcd p q) := by
  let r := xgcd p q
  refine ⟨scale (gcd p q).leadingCoeff⁻¹ r.left,
    scale (gcd p q).leadingCoeff⁻¹ r.right, ?_⟩
  rw [← scale_mul, ← scale_mul, ← scale_add, monicize_eq_scale]
  congr 1
  exact (xgcd_bezout p q).trans (xgcd_gcd_eq_gcd p q)

/-- A gcd with a nonzero right input is nonzero. -/
theorem gcd_ne_zero_right (p q : DensePoly K) (hq : q ≠ 0) : gcd p q ≠ 0 := by
  intro h
  rcases gcd_dvd_right p q with ⟨r, hr⟩
  apply hq
  rw [hr, h, zero_mul]

/-- Coprimality is equivalent to the canonical gcd being one. -/
theorem coprime_iff (p q : DensePoly K) :
    Coprime p q ↔ monicize (gcd p q) = 1 := by
  constructor
  · rintro ⟨s, t, h⟩
    have hd : gcd p q ∣ (1 : DensePoly K) := by
      rw [← h]
      exact dvd_add_poly (dvd_mul_left_poly s (gcd_dvd_left p q))
        (dvd_mul_left_poly t (gcd_dvd_right p q))
    have hg : gcd p q ≠ 0 := by
      intro hg
      rcases hd with ⟨r, hr⟩
      have hz : (1 : DensePoly K) = 0 := by rw [hr, hg, zero_mul]
      exact monic_ne_zero monic_one hz
    exact monic_dvd_antisymm (monicize_monic hg) monic_one
      (monicize_dvd_of_dvd hg hd) ⟨monicize (gcd p q), by grind⟩
  · intro h
    rcases bezout_monicize_gcd p q with ⟨s, t, hst⟩
    exact ⟨s, t, hst.trans h⟩

/-- Every polynomial is coprime to one. -/
theorem Coprime.one_right (p : DensePoly K) : Coprime p 1 :=
  ⟨0, 1, by grind⟩

/-- Coprimality is symmetric. -/
theorem Coprime.symm {p q : DensePoly K} (h : Coprime p q) : Coprime q p := by
  rcases h with ⟨s, t, h⟩
  exact ⟨t, s, by grind⟩

/-- A common divisor of coprime polynomials divides one. -/
theorem Coprime.dvd_one {p q d : DensePoly K} (h : Coprime p q)
    (hp : d ∣ p) (hq : d ∣ q) : d ∣ (1 : DensePoly K) := by
  rcases h with ⟨s, t, h⟩
  rw [← h]
  exact dvd_add_poly (dvd_mul_left_poly s hp) (dvd_mul_left_poly t hq)

/-- A factor coprime to a divisor can be cancelled from a divisibility claim. -/
theorem Coprime.dvd_of_dvd_mul {p q r : DensePoly K} (h : Coprime p q)
    (hd : q ∣ p * r) : q ∣ r := by
  rcases h with ⟨s, t, h⟩
  rcases hd with ⟨a, ha⟩
  exact ⟨s * a + t * r, by grind⟩

/-- Coprimality passes to a divisor of the right operand. -/
theorem Coprime.of_dvd_right {p q d : DensePoly K} (h : Coprime p q)
    (hd : d ∣ q) : Coprime p d := by
  rcases h with ⟨s, t, h⟩
  rcases hd with ⟨a, ha⟩
  exact ⟨s, t * a, by grind⟩

/-- Coprimality is preserved by products in the right operand. -/
theorem Coprime.mul_right {p q r : DensePoly K} (hq : Coprime p q)
    (hr : Coprime p r) : Coprime p (q * r) := by
  rcases hq with ⟨s, t, hs⟩
  rcases hr with ⟨u, v, hu⟩
  exact ⟨s * u * p + s * v * r + t * q * u, t * v, by grind⟩

/-- Adding a multiple of the right operand preserves coprimality. -/
theorem Coprime.add_mul {p q r : DensePoly K} (h : Coprime p q) :
    Coprime (p + r * q) q := by
  rcases h with ⟨s, t, h⟩
  exact ⟨s, t - s * r, by grind⟩

/-- Scaling either operand by a nonzero field scalar preserves coprimality. -/
theorem Coprime.scale_left {p q : DensePoly K} (h : Coprime p q)
    {a : K} (ha : a ≠ 0) : Coprime (scale a p) q := by
  rcases h with ⟨s, t, h⟩
  refine ⟨scale a⁻¹ s, t, ?_⟩
  rw [← scale_mul, mul_scale, scale_scale, Lean.Grind.Field.inv_mul_cancel ha,
    scale_one]
  exact h

/-- Cancelling a common factor from its Bézout identity yields coprime cofactors. -/
theorem coprime_cofactors {p q d a b : DensePoly K} (hd : d ≠ 0)
    (hp : p = d * a) (hq : q = d * b)
    (hbez : ∃ s t, s * p + t * q = d) : Coprime a b := by
  rcases hbez with ⟨s, t, h⟩
  refine ⟨s, t, mul_right_cancel hd ?_⟩
  grind

/-- A monic factor of a monic product has a monic cofactor. -/
theorem monic_of_mul {p q : DensePoly K} (hp : p.Monic) (hpq : (p * q).Monic) :
    q.Monic := by
  have hq : q ≠ 0 := by
    intro h
    apply monic_ne_zero hpq
    rw [h]
    grind
  have hl := leadingCoeff_mul p q
    (Nat.pos_of_ne_zero (fun h => monic_ne_zero hp ((size_eq_zero_iff p).mp h)))
    (Nat.pos_of_ne_zero (fun h => hq ((size_eq_zero_iff q).mp h)))
    (by rw [hp, Lean.Grind.Semiring.one_mul]; exact leadingCoeff_ne_zero hq)
  rw [hpq, hp, Lean.Grind.Semiring.one_mul] at hl
  exact hl.symm

/-- Divisibility is transitive. -/
theorem dvd_trans {p q r : DensePoly K} (hpq : p ∣ q) (hqr : q ∣ r) : p ∣ r := by
  rcases hpq with ⟨a, ha⟩
  rcases hqr with ⟨b, hb⟩
  exact ⟨a * b, by grind⟩

/-- Coprimality passes to divisors in both operands. -/
theorem Coprime.of_dvd {p q a b : DensePoly K} (h : Coprime p q)
    (ha : a ∣ p) (hb : b ∣ q) : Coprime a b :=
  ((h.of_dvd_right hb).symm.of_dvd_right ha).symm

/-- Two products are coprime when each pair of factors is coprime. -/
theorem Coprime.mul {a b c d : DensePoly K} (hac : Coprime a c)
    (had : Coprime a d) (hbc : Coprime b c) (hbd : Coprime b d) :
    Coprime (a * b) (c * d) :=
  ((hac.mul_right had).symm.mul_right (hbc.mul_right hbd).symm).symm

/-- Powers of monic polynomials remain monic. -/
theorem monic_pow {p : DensePoly K} (hp : p.Monic) (n : Nat) : (p ^ n).Monic := by
  induction n with
  | zero => simpa only [Lean.Grind.Semiring.pow_zero] using monic_one (K := K)
  | succ n ih => rw [Lean.Grind.Semiring.pow_succ]; exact mul_monic ih hp

/-- Coprimality is preserved under powers of the right operand. -/
theorem Coprime.pow_right {p q : DensePoly K} (h : Coprime p q) (n : Nat) :
    Coprime p (q ^ n) := by
  induction n with
  | zero => rw [Lean.Grind.Semiring.pow_zero]; exact .one_right p
  | succ n ih => rw [Lean.Grind.Semiring.pow_succ]; exact ih.mul_right h

/-- Powers of coprime polynomials are coprime. -/
theorem Coprime.pow {p q : DensePoly K} (h : Coprime p q) (m n : Nat) :
    Coprime (p ^ m) (q ^ n) := ((h.pow_right n).symm.pow_right m).symm

end Hex.DensePoly
