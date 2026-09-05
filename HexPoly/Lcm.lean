/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly.Euclid

public section

/-!
Monic normalization and least common multiples for dense polynomials over a
field.  The executable Euclidean gcd is only determined up to a unit, so every
public least common multiple is normalized before it is returned.
-/

namespace Hex.DensePoly

universe u

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F]

/-- Normalize a nonzero polynomial to leading coefficient `1`; keep `0` fixed. -/
@[expose]
def monicize (p : DensePoly F) : DensePoly F :=
  if p.isZero then 0 else scale p.leadingCoeff⁻¹ p

@[simp, grind =]
theorem monicize_zero : monicize (0 : DensePoly F) = 0 := by
  simp [monicize]

/-- Normalization preserves the stored size. -/
theorem size_monicize (p : DensePoly F) : (monicize p).size = p.size := by
  by_cases hp : p = 0
  · subst p
    rw [monicize_zero]
  · have hpPos : 0 < p.size := by
      by_cases h : 0 < p.size
      · exact h
      · exfalso
        apply hp
        exact (size_eq_zero_iff p).mp (Nat.eq_zero_of_not_pos h)
    have hisZero : p.isZero = false := by
      rw [← Bool.not_eq_true]
      intro h
      exact hp ((size_eq_zero_iff p).mp ((isZero_eq_true_iff p).mp h))
    rw [monicize, ite_eq_right (by simp [hisZero])]
    apply Nat.le_antisymm
    · rw [scale_eq_scaleImpl]
      exact size_scaleImpl_le _ _
    · apply Nat.le_of_not_gt
      intro hlt
      have hle : (scale p.leadingCoeff⁻¹ p).size ≤ p.size - 1 := by omega
      have hz := coeff_eq_zero_of_size_le
        (scale p.leadingCoeff⁻¹ p) hle
      rw [coeff_scale_semiring] at hz
      have hlc : p.leadingCoeff = p.coeff (p.size - 1) :=
        leadingCoeff_eq_coeff_last p hpPos
      rw [← hlc] at hz
      have hlcNe : p.leadingCoeff ≠ (0 : F) :=
        leadingCoeff_ne_zero_of_pos_size p hpPos
      have hone : p.leadingCoeff⁻¹ * p.leadingCoeff = 1 :=
        Lean.Grind.Field.inv_mul_cancel hlcNe
      rw [hone] at hz
      exact Lean.Grind.Field.zero_ne_one hz.symm

/-- Normalizing a nonzero polynomial produces a monic polynomial. -/
theorem monicize_monic {p : DensePoly F} (hp : p ≠ 0) : (monicize p).Monic := by
  have hpPos : 0 < p.size := by
    by_cases h : 0 < p.size
    · exact h
    · exfalso
      apply hp
      exact (size_eq_zero_iff p).mp (Nat.eq_zero_of_not_pos h)
  have hisZero : p.isZero = false := by
    rw [← Bool.not_eq_true]
    intro h
    exact hp ((size_eq_zero_iff p).mp ((isZero_eq_true_iff p).mp h))
  rw [monic_iff_leadingCoeff_eq_one,
    leadingCoeff_eq_coeff_last _ (by rw [size_monicize]; exact hpPos),
    size_monicize, monicize, ite_eq_right (by simp [hisZero]),
    coeff_scale_semiring, ← leadingCoeff_eq_coeff_last p hpPos]
  exact Lean.Grind.Field.inv_mul_cancel
    (leadingCoeff_ne_zero_of_pos_size p hpPos)

/-- Normalization of a nonzero polynomial is nonzero. -/
theorem monicize_ne_zero {p : DensePoly F} (hp : p ≠ 0) : monicize p ≠ 0 := by
  intro hz
  have hsize := size_monicize p
  rw [hz, size_zero] at hsize
  exact hp ((size_eq_zero_iff p).mp hsize.symm)

private theorem field_cancel_lead (q : DensePoly F) (hq : q.isZero = false) :
    ∀ a : F, a - (a / q.leadingCoeff) * q.leadingCoeff = (0 : F) := by
  have hqPos : 0 < q.size := by
    by_cases h : 0 < q.size
    · exact h
    · have hz : q.size = 0 := Nat.eq_zero_of_not_pos h
      have hi : q.isZero = true := (isZero_eq_true_iff q).2 hz
      rw [hi] at hq
      cases hq
  have hlead : q.leadingCoeff ≠ (0 : F) :=
    leadingCoeff_ne_zero_of_pos_size q hqPos
  intro a
  rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
    Lean.Grind.Field.inv_mul_cancel hlead, Lean.Grind.Semiring.mul_one]
  grind

private theorem field_reconstruct (p q : DensePoly F) (hq : q.isZero = false) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  exact divMod_reconstruction p q (field_cancel_lead q hq)

private theorem field_remainder_degree (p q : DensePoly F) (hq : q.isZero = false)
    (hdegree : 0 < q.degree?.getD 0) :
    (divMod p q).2.degree?.getD 0 < q.degree?.getD 0 := by
  exact divMod_remainder_degree_lt_of_pos_degree_of_cancel p q hdegree
    (field_cancel_lead q hq)

private theorem field_small_remainder (p q : DensePoly F) (hq : q.isZero = false)
    (hdegree : ¬ 0 < q.degree?.getD 0) :
    (divMod p q).2 = 0 := by
  have hqPos : 0 < q.size := by
    by_cases h : 0 < q.size
    · exact h
    · have hz : q.size = 0 := Nat.eq_zero_of_not_pos h
      have hi : q.isZero = true := (isZero_eq_true_iff q).2 hz
      rw [hi] at hq
      cases hq
  have hqSize : q.size = 1 := by
    have hdeg : q.degree?.getD 0 = q.size - 1 := by
      rw [degree?_eq_some_of_pos_size q hqPos, Option.getD_some]
    rw [hdeg] at hdegree
    omega
  exact divMod_remainder_eq_zero_of_degree_zero_of_cancel p q hqSize
    (field_cancel_lead q hq)

theorem xgcd_bezout_field (p q : DensePoly F) :
    let r := xgcd p q
    r.left * p + r.right * q = r.gcd := by
  exact xgcd_bezout_of_reconstruction field_reconstruct p q

theorem gcd_dvd_inputs_field (p q : DensePoly F) :
    gcd p q ∣ p ∧ gcd p q ∣ q := by
  exact gcd_dvd_inputs_of_reconstruction field_reconstruct field_remainder_degree
    field_small_remainder p q

private theorem scale_one_poly (p : DensePoly F) : scale (1 : F) p = p := by
  apply ext_coeff
  intro i
  rw [coeff_scale_semiring]
  grind

private theorem poly_mul_right_cancel {a b q : DensePoly F} (hq : q ≠ 0)
    (h : a * q = b * q) : a = b := by
  have hqPos : 0 < q.size := by
    by_cases hp : 0 < q.size
    · exact hp
    · exact False.elim (hq ((size_eq_zero_iff q).mp (Nat.eq_zero_of_not_pos hp)))
  have hlc := leadingCoeff_ne_zero_of_pos_size q hqPos
  have hexact (x : F) : (x * q.leadingCoeff) / q.leadingCoeff = x := by
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hlc, Lean.Grind.Semiring.mul_one]
  have htop (x : F) (hx : x ≠ 0) : x * q.leadingCoeff ≠ 0 := by
    intro hz
    have hz' := congrArg (fun y : F => y * q.leadingCoeff⁻¹) hz
    rw [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hlc, Lean.Grind.Semiring.mul_one] at hz'
    exact hx hz'
  have ha := divMod_eq_of_polynomial_mul (a * q) q a hq hexact htop rfl
  have hb := divMod_eq_of_polynomial_mul (b * q) q b hq hexact htop rfl
  have hd := congrArg (fun p : DensePoly F => (divMod p q).1) h
  rw [ha, hb] at hd
  exact hd

private theorem poly_mul_left_comm (a b q : DensePoly F) :
    a * (b * q) = b * (a * q) := by
  rw [← mul_assoc_poly, mul_comm_poly a b, mul_assoc_poly]

theorem monicize_dvd_of_dvd {g p : DensePoly F} (hg : g ≠ 0)
    (hgp : g ∣ p) : monicize g ∣ p := by
  rcases hgp with ⟨r, hr⟩
  have hgPos : 0 < g.size := by
    by_cases h : 0 < g.size
    · exact h
    · exact False.elim (hg ((size_eq_zero_iff g).mp (Nat.eq_zero_of_not_pos h)))
  have hlc : g.leadingCoeff ≠ (0 : F) := leadingCoeff_ne_zero_of_pos_size g hgPos
  have hisZero : g.isZero = false := by
    rw [← Bool.not_eq_true]
    intro h
    exact hg ((size_eq_zero_iff g).mp ((isZero_eq_true_iff g).mp h))
  refine ⟨scale g.leadingCoeff r, ?_⟩
  calc
    p = g * r := hr
    _ = scale (1 : F) (g * r) := (scale_one_poly (g * r)).symm
    _ = scale (g.leadingCoeff⁻¹ * g.leadingCoeff) (g * r) := by
      rw [Lean.Grind.Field.inv_mul_cancel hlc]
    _ = scale g.leadingCoeff⁻¹ (scale g.leadingCoeff (g * r)) := by
      rw [scale_scale]
    _ = scale g.leadingCoeff⁻¹ (g * scale g.leadingCoeff r) := by
      rw [mul_scale]
    _ = scale g.leadingCoeff⁻¹ g * scale g.leadingCoeff r := by
      rw [scale_mul]
    _ = monicize g * scale g.leadingCoeff r := by
      rw [monicize, ite_eq_right (by
        intro h
        rw [h] at hisZero
        cases hisZero)]

theorem divMod_mul_field (a q : DensePoly F) (hq : q ≠ 0) :
    (divMod (a * q) q).1 = a := by
  have hqPos : 0 < q.size := by
    by_cases h : 0 < q.size
    · exact h
    · exact False.elim (hq ((size_eq_zero_iff q).mp (Nat.eq_zero_of_not_pos h)))
  have hlc := leadingCoeff_ne_zero_of_pos_size q hqPos
  have hexact (x : F) : (x * q.leadingCoeff) / q.leadingCoeff = x := by
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hlc, Lean.Grind.Semiring.mul_one]
  have htop (x : F) (hx : x ≠ 0) : x * q.leadingCoeff ≠ 0 := by
    intro hz
    have hz' := congrArg (fun y : F => y * q.leadingCoeff⁻¹) hz
    rw [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hlc, Lean.Grind.Semiring.mul_one] at hz'
    exact hx hz'
  have h := divMod_eq_of_polynomial_mul (a * q) q a hq hexact htop rfl
  exact congrArg Prod.fst h

private theorem poly_mul_ne_zero {p q : DensePoly F} (hp : p ≠ 0) (hq : q ≠ 0) :
    p * q ≠ 0 := by
  intro h
  have h' : p * q = (0 : DensePoly F) * q := by rw [h, zero_mul]
  exact hp (poly_mul_right_cancel hq h')

omit [DecidableEq F] in
private theorem field_mul_ne_zero {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  have h' := congrArg (fun x : F => x * b⁻¹) h
  rw [Lean.Grind.Semiring.mul_assoc, Lean.Grind.Field.mul_inv_cancel hb,
    Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.zero_mul] at h'
  exact ha h'

/-- A monic polynomial over a nontrivial field is nonzero. -/
theorem monic_ne_zero {p : DensePoly F} (hp : p.Monic) : p ≠ 0 := by
  intro h
  rw [h, monic_iff_leadingCoeff_eq_one, leadingCoeff_zero] at hp
  exact Lean.Grind.Field.zero_ne_one hp

/-- The product of two monic polynomials is monic. -/
theorem mul_monic {p q : DensePoly F} (hp : p.Monic) (hq : q.Monic) :
    (p * q).Monic := by
  have hpNe := monic_ne_zero hp
  have hqNe := monic_ne_zero hq
  have hpPos : 0 < p.size := by
    by_cases h : 0 < p.size
    · exact h
    · exact False.elim (hpNe ((size_eq_zero_iff p).mp (Nat.eq_zero_of_not_pos h)))
  have hqPos : 0 < q.size := by
    by_cases h : 0 < q.size
    · exact h
    · exact False.elim (hqNe ((size_eq_zero_iff q).mp (Nat.eq_zero_of_not_pos h)))
  rw [monic_iff_leadingCoeff_eq_one]
  rw [leadingCoeff_mul p q hpPos hqPos
    (field_mul_ne_zero (leadingCoeff_ne_zero_of_pos_size p hpPos)
      (leadingCoeff_ne_zero_of_pos_size q hqPos)), hp, hq]
  grind

private theorem size_mul_field {p q : DensePoly F} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).size = p.size + q.size - 1 := by
  have hpPos : 0 < p.size := by
    by_cases h : 0 < p.size
    · exact h
    · exact False.elim (hp ((size_eq_zero_iff p).mp (Nat.eq_zero_of_not_pos h)))
  have hqPos : 0 < q.size := by
    by_cases h : 0 < q.size
    · exact h
    · exact False.elim (hq ((size_eq_zero_iff q).mp (Nat.eq_zero_of_not_pos h)))
  exact size_mul_of_top_ne p q hpPos hqPos
    (field_mul_ne_zero
      (leadingCoeff_ne_zero_of_pos_size p hpPos)
      (leadingCoeff_ne_zero_of_pos_size q hqPos))

/-- Two monic polynomials dividing one another are equal. -/
theorem monic_dvd_antisymm {p q : DensePoly F} (hp : p.Monic) (hq : q.Monic)
    (hpq : p ∣ q) (hqp : q ∣ p) : p = q := by
  have hpNe : p ≠ 0 := by
    intro h
    rw [h, monic_iff_leadingCoeff_eq_one, leadingCoeff_zero] at hp
    exact Lean.Grind.Field.zero_ne_one hp
  have hqNe : q ≠ 0 := by
    intro h
    rw [h, monic_iff_leadingCoeff_eq_one, leadingCoeff_zero] at hq
    exact Lean.Grind.Field.zero_ne_one hq
  rcases hpq with ⟨r, hr⟩
  rcases hqp with ⟨s, hs⟩
  have hrNe : r ≠ 0 := by
    intro h
    apply hqNe
    rw [hr, h, mul_comm_poly, zero_mul]
  have hsNe : s ≠ 0 := by
    intro h
    apply hpNe
    rw [hs, h, mul_comm_poly, zero_mul]
  have hsizeR := size_mul_field hpNe hrNe
  have hsizeS := size_mul_field hqNe hsNe
  rw [← hr] at hsizeR
  rw [← hs] at hsizeS
  have hqPos : 0 < q.size := by
    by_cases h : 0 < q.size
    · exact h
    · exact False.elim (hqNe ((size_eq_zero_iff q).mp (Nat.eq_zero_of_not_pos h)))
  have hsPos : 0 < s.size := by
    by_cases h : 0 < s.size
    · exact h
    · exact False.elim (hsNe ((size_eq_zero_iff s).mp (Nat.eq_zero_of_not_pos h)))
  have hsumR : 1 ≤ p.size + r.size := by omega
  have hsumS : 1 ≤ q.size + s.size := by omega
  have hsizeR' : q.size + 1 = p.size + r.size := by
    rw [hsizeR]
    exact Nat.sub_add_cancel hsumR
  have hsizeS' : p.size + 1 = q.size + s.size := by
    rw [hsizeS]
    exact Nat.sub_add_cancel hsumS
  have hqle : q.size ≤ p.size := by
    clear hsizeR hsizeS hsizeR'
    omega
  have hrle : r.size ≤ 1 := by
    clear hsizeR hsizeS hsizeS'
    omega
  have hrPos : 0 < r.size := by
    by_cases h : 0 < r.size
    · exact h
    · exact False.elim (hrNe ((size_eq_zero_iff r).mp (Nat.eq_zero_of_not_pos h)))
  have hrSize : r.size = 1 := by
    clear hsizeR hsizeS
    omega
  have hpPos : 0 < p.size := by
    by_cases h : 0 < p.size
    · exact h
    · exact False.elim (hpNe ((size_eq_zero_iff p).mp (Nat.eq_zero_of_not_pos h)))
  have hlcProd := leadingCoeff_mul p r hpPos hrPos
    (field_mul_ne_zero (leadingCoeff_ne_zero_of_pos_size p hpPos)
      (leadingCoeff_ne_zero_of_pos_size r hrPos))
  have hrMonic : r.Monic := by
    rw [monic_iff_leadingCoeff_eq_one]
    rw [← hr, hp, hq] at hlcProd
    rw [Lean.Grind.Semiring.one_mul] at hlcProd
    exact hlcProd.symm
  have hrOne : r = 1 := by
    apply ext_coeff
    intro i
    by_cases hi : i = 0
    · subst i
      have hlcr : r.leadingCoeff = r.coeff 0 := by
        simpa [hrSize] using leadingCoeff_eq_coeff_last r hrPos
      rw [← hlcr, hrMonic]
      change (1 : F) = (C 1).coeff 0
      rw [coeff_C]
      simp
    · rw [coeff_eq_zero_of_size_le r (by omega)]
      change (0 : F) = (C 1).coeff i
      rw [coeff_C]
      simp [hi]
      rfl
  rw [hr, hrOne, mul_one_right_poly]

private theorem dvd_monicize_of_dvd {p r : DensePoly F} (hr : r ≠ 0)
    (hpr : p ∣ r) : p ∣ monicize r := by
  rcases hpr with ⟨q, hq⟩
  have hrPos : 0 < r.size := by
    by_cases h : 0 < r.size
    · exact h
    · exact False.elim (hr ((size_eq_zero_iff r).mp (Nat.eq_zero_of_not_pos h)))
  have hisZero : r.isZero = false := (isZero_eq_false_iff r).2 hrPos
  refine ⟨scale r.leadingCoeff⁻¹ q, ?_⟩
  rw [monicize, ite_eq_right (by simp [hisZero]), hq, mul_scale]

private theorem monicize_eq_self_of_monic {p : DensePoly F} (hp : p.Monic) :
    monicize p = p := by
  have hpNe : p ≠ 0 := by
    intro h
    rw [h, monic_iff_leadingCoeff_eq_one, leadingCoeff_zero] at hp
    exact Lean.Grind.Field.zero_ne_one hp
  have hpPos : 0 < p.size := by
    by_cases h : 0 < p.size
    · exact h
    · exact False.elim (hpNe ((size_eq_zero_iff p).mp (Nat.eq_zero_of_not_pos h)))
  have hisZero : p.isZero = false := (isZero_eq_false_iff p).2 hpPos
  rw [monicize, ite_eq_right (by simp [hisZero]), hp, Lean.Grind.Field.inv_one,
    scale_one_poly]

@[simp, grind =]
theorem monicize_monicize (p : DensePoly F) : monicize (monicize p) = monicize p := by
  by_cases hp : p = 0
  · subst p
    rw [monicize_zero, monicize_zero]
  · exact monicize_eq_self_of_monic (monicize_monic hp)

/-- A Bézout-certified product of coprime cofactors divides every common
multiple of the two inputs. -/
theorem commonProduct_dvd
    (running incoming common left right bezoutLeft bezoutRight result r : DensePoly F)
    (hincomingNe : incoming ≠ 0)
    (hrunning : running = common * left)
    (hincoming : incoming = common * right)
    (hbezout : bezoutLeft * running + bezoutRight * incoming = common)
    (hresult : result = left * incoming)
    (hrunDvd : running ∣ r) (hinDvd : incoming ∣ r) : result ∣ r := by
  have hcommonNe : common ≠ 0 := by
    intro hc
    apply hincomingNe
    rw [hincoming, hc, zero_mul]
  have hunit : bezoutLeft * left + bezoutRight * right = 1 := by
    apply poly_mul_right_cancel hcommonNe
    calc
      (bezoutLeft * left + bezoutRight * right) * common =
          bezoutLeft * (common * left) + bezoutRight * (common * right) := by
        rw [mul_add_left_poly]
        congr 1
        · rw [mul_assoc_poly, mul_comm_poly left common]
        · rw [mul_assoc_poly, mul_comm_poly right common]
      _ = common := by rw [← hrunning, ← hincoming, hbezout]
      _ = 1 * common := by rw [mul_comm_poly, mul_one_right_poly]
  rcases hrunDvd with ⟨a, ha⟩
  rcases hinDvd with ⟨b, hb⟩
  refine ⟨bezoutLeft * b + bezoutRight * a, ?_⟩
  rw [hresult]
  calc
    r = 1 * r := by rw [mul_comm_poly, mul_one_right_poly]
    _ = (bezoutLeft * left + bezoutRight * right) * r := by rw [hunit]
    _ = (bezoutLeft * left) * r + (bezoutRight * right) * r := by
      rw [mul_add_left_poly]
    _ = (left * incoming) * (bezoutLeft * b + bezoutRight * a) := by
      rw [mul_add_right_poly]
      congr 1
      · rw [hb]
        simp only [mul_assoc_poly, poly_mul_left_comm]
      · rw [ha, hrunning, hincoming]
        simp only [mul_assoc_poly, poly_mul_left_comm]

/-- The monic least common multiple of `p` and `q`, and `0` if either input is
zero. -/
@[expose]
def lcm (p q : DensePoly F) : DensePoly F :=
  if p.isZero || q.isZero then
    0
  else
    let common := monicize (gcd p q)
    monicize (p * (divMod q common).1)

private theorem lcm_nonzero_spec (p q : DensePoly F) (hp : p ≠ 0) (hq : q ≠ 0) :
    p ∣ lcm p q ∧ q ∣ lcm p q ∧
      ∀ r, p ∣ r → q ∣ r → lcm p q ∣ r := by
  have hpPos : 0 < p.size := by
    by_cases h : 0 < p.size
    · exact h
    · exact False.elim (hp ((size_eq_zero_iff p).mp (Nat.eq_zero_of_not_pos h)))
  have hqPos : 0 < q.size := by
    by_cases h : 0 < q.size
    · exact h
    · exact False.elim (hq ((size_eq_zero_iff q).mp (Nat.eq_zero_of_not_pos h)))
  have hpZero : p.isZero = false := (isZero_eq_false_iff p).2 hpPos
  have hqZero : q.isZero = false := (isZero_eq_false_iff q).2 hqPos
  let g := gcd p q
  have hgDvd : g ∣ p ∧ g ∣ q := gcd_dvd_inputs_field p q
  have hgNe : g ≠ 0 := by
    rcases hgDvd.1 with ⟨a, ha⟩
    intro hg
    apply hp
    rw [ha, hg, zero_mul]
  have hgPos : 0 < g.size := by
    by_cases h : 0 < g.size
    · exact h
    · exact False.elim (hgNe ((size_eq_zero_iff g).mp (Nat.eq_zero_of_not_pos h)))
  have hgZero : g.isZero = false := (isZero_eq_false_iff g).2 hgPos
  let common := monicize g
  have hcommonNe : common ≠ 0 := monicize_ne_zero hgNe
  have hcDvdP : common ∣ p := monicize_dvd_of_dvd hgNe hgDvd.1
  have hcDvdQ : common ∣ q := monicize_dvd_of_dvd hgNe hgDvd.2
  rcases hcDvdP with ⟨left, hpFactor⟩
  rcases hcDvdQ with ⟨right, hqFactor⟩
  have hrightNe : right ≠ 0 := by
    intro hr
    apply hq
    rw [hqFactor, hr, mul_comm_poly, zero_mul]
  have hquot : (divMod q common).1 = right := by
    rw [hqFactor, mul_comm_poly common right, divMod_mul_field right common hcommonNe]
  let raw := p * right
  have hrawNe : raw ≠ 0 := poly_mul_ne_zero hp hrightNe
  have hlcm : lcm p q = monicize raw := by
    rw [lcm, hpZero, hqZero]
    simp only [Bool.false_or]
    change monicize (p * (divMod q common).1) = monicize raw
    rw [hquot]
  have hpRaw : p ∣ raw := ⟨right, rfl⟩
  have hqRaw : q ∣ raw := by
    refine ⟨left, ?_⟩
    change raw = q * left
    rw [show raw = p * right by rfl, hpFactor, hqFactor]
    calc
      (common * left) * right = common * (left * right) := mul_assoc_poly _ _ _
      _ = common * (right * left) := by rw [mul_comm_poly left right]
      _ = (common * right) * left := (mul_assoc_poly _ _ _).symm
  have hpLcm : p ∣ lcm p q := by
    rw [hlcm]
    exact dvd_monicize_of_dvd hrawNe hpRaw
  have hqLcm : q ∣ lcm p q := by
    rw [hlcm]
    exact dvd_monicize_of_dvd hrawNe hqRaw
  refine ⟨hpLcm, hqLcm, ?_⟩
  intro r hpr hqr
  let x := xgcd p q
  let u := g.leadingCoeff⁻¹
  let bezoutLeft := scale u x.left
  let bezoutRight := scale u x.right
  have hbezout : bezoutLeft * p + bezoutRight * q = common := by
    change scale u x.left * p + scale u x.right * q = common
    rw [← scale_mul, ← scale_mul, ← scale_add]
    change scale u (x.left * p + x.right * q) = common
    rw [xgcd_bezout_field p q, xgcd_gcd_eq_gcd]
    change scale g.leadingCoeff⁻¹ g = monicize g
    rw [monicize, ite_eq_right (by simp [hgZero])]
  have hrawResult : raw = left * q := by
    rw [show raw = p * right by rfl, hpFactor, hqFactor]
    exact (mul_assoc_poly common left right).trans
      (poly_mul_left_comm left common right).symm
  have hrawDvd : raw ∣ r := commonProduct_dvd p q common left right
    bezoutLeft bezoutRight raw r hq hpFactor hqFactor hbezout hrawResult hpr hqr
  rw [hlcm]
  exact monicize_dvd_of_dvd hrawNe hrawDvd

@[simp, grind =]
theorem lcm_zero_left (q : DensePoly F) : lcm 0 q = 0 := by
  have hz : (0 : DensePoly F).isZero = true :=
    (isZero_eq_true_iff 0).2 (by simp)
  simp [lcm, hz]

@[simp, grind =]
theorem lcm_zero_right (p : DensePoly F) : lcm p 0 = 0 := by
  have hz : (0 : DensePoly F).isZero = true :=
    (isZero_eq_true_iff 0).2 (by simp)
  simp [lcm, hz]

@[simp, grind =]
theorem lcm_zero_zero : lcm (0 : DensePoly F) 0 = 0 := by
  simp

/-- The left input divides the least common multiple. -/
theorem dvd_lcm_left (p q : DensePoly F) : p ∣ lcm p q := by
  by_cases hp : p = 0
  · subst p
    refine ⟨0, ?_⟩
    rw [lcm_zero_left, zero_mul]
  · by_cases hq : q = 0
    · subst q
      refine ⟨0, ?_⟩
      rw [lcm_zero_right, mul_comm_poly, zero_mul]
    · exact (lcm_nonzero_spec p q hp hq).1

/-- The right input divides the least common multiple. -/
theorem dvd_lcm_right (p q : DensePoly F) : q ∣ lcm p q := by
  by_cases hp : p = 0
  · subst p
    refine ⟨0, ?_⟩
    rw [lcm_zero_left, mul_comm_poly, zero_mul]
  · by_cases hq : q = 0
    · subst q
      refine ⟨0, ?_⟩
      rw [lcm_zero_right, zero_mul]
    · exact (lcm_nonzero_spec p q hp hq).2.1

/-- The executable `lcm` divides every common multiple. -/
theorem lcm_dvd (p q r : DensePoly F) (hp : p ∣ r) (hq : q ∣ r) :
    lcm p q ∣ r := by
  by_cases hp0 : p = 0
  · subst p
    rcases hp with ⟨a, ha⟩
    rw [zero_mul] at ha
    subst r
    refine ⟨0, ?_⟩
    rw [lcm_zero_left, zero_mul]
  · by_cases hq0 : q = 0
    · subst q
      rcases hq with ⟨a, ha⟩
      rw [zero_mul] at ha
      subst r
      refine ⟨0, ?_⟩
      rw [lcm_zero_right, zero_mul]
    · exact (lcm_nonzero_spec p q hp0 hq0).2.2 r hp hq

/-- Least common multiples are normalized, including the zero cases. -/
theorem lcm_normalized (p q : DensePoly F) : monicize (lcm p q) = lcm p q := by
  unfold lcm
  split
  · rw [monicize_zero]
  · exact monicize_monicize _

/-- An `lcm` of nonzero polynomials is nonzero. -/
theorem lcm_ne_zero {p q : DensePoly F} (hp : p ≠ 0) (hq : q ≠ 0) :
    lcm p q ≠ 0 := by
  have hpqNe : p * q ≠ 0 := poly_mul_ne_zero hp hq
  have hpDvd : p ∣ p * q := ⟨q, rfl⟩
  have hqDvd : q ∣ p * q := by
    refine ⟨p, ?_⟩
    rw [mul_comm_poly]
  rcases lcm_dvd p q (p * q) hpDvd hqDvd with ⟨r, hr⟩
  intro hl
  apply hpqNe
  rw [hr, hl, zero_mul]

/-- An `lcm` of nonzero polynomials is monic. -/
theorem lcm_monic {p q : DensePoly F} (hp : p ≠ 0) (hq : q ≠ 0) :
    (lcm p q).Monic := by
  have h := monicize_monic (lcm_ne_zero hp hq)
  rw [lcm_normalized] at h
  exact h

/-- Fold least common multiples, using `1` for the empty family. -/
@[expose]
def lcmList : List (DensePoly F) → DensePoly F :=
  List.foldl lcm 1

@[simp, grind =] theorem lcmList_nil : lcmList ([] : List (DensePoly F)) = 1 := rfl

private theorem one_poly_ne_zero : (1 : DensePoly F) ≠ 0 := by
  intro h
  have hlc := congrArg DensePoly.leadingCoeff h
  rw [leadingCoeff_one, leadingCoeff_zero] at hlc
  exact Lean.Grind.Field.zero_ne_one hlc.symm

private theorem foldl_lcm_ne_zero (acc : DensePoly F) (xs : List (DensePoly F))
    (hacc : acc ≠ 0) (hxs : ∀ p ∈ xs, p ≠ 0) :
    xs.foldl lcm acc ≠ 0 := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons p xs ih =>
      simp only [List.foldl_cons]
      exact ih (lcm acc p) (lcm_ne_zero hacc (hxs p (by simp)))
        (by
          intro q hq
          exact hxs q (List.mem_cons_of_mem p hq))

private theorem foldl_lcm_monic (acc : DensePoly F) (xs : List (DensePoly F))
    (haccNe : acc ≠ 0) (hacc : acc.Monic) (hxs : ∀ p ∈ xs, p ≠ 0) :
    (xs.foldl lcm acc).Monic := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons p xs ih =>
      simp only [List.foldl_cons]
      have hp := hxs p (by simp)
      exact ih (lcm acc p) (lcm_ne_zero haccNe hp) (lcm_monic haccNe hp)
        (by
          intro q hq
          exact hxs q (List.mem_cons_of_mem p hq))

private theorem foldl_dvd_lcm (acc : DensePoly F) (xs : List (DensePoly F)) :
    acc ∣ xs.foldl lcm acc := by
  induction xs generalizing acc with
  | nil =>
      refine ⟨1, ?_⟩
      change acc = acc * 1
      rw [mul_one_right_poly]
  | cons p xs ih =>
      simp only [List.foldl_cons]
      rcases dvd_lcm_left acc p with ⟨a, ha⟩
      rcases ih (lcm acc p) with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      rw [hb, ha, mul_assoc_poly]

private theorem dvd_foldl_lcm_of_mem (acc p : DensePoly F) (xs : List (DensePoly F))
    (hp : p ∈ xs) : p ∣ xs.foldl lcm acc := by
  induction xs generalizing acc with
  | nil => cases hp
  | cons q xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hp with hp | hp
      · subst q
        rcases dvd_lcm_right acc p with ⟨a, ha⟩
        rcases foldl_dvd_lcm (lcm acc p) xs with ⟨b, hb⟩
        refine ⟨a * b, ?_⟩
        rw [hb, ha, mul_assoc_poly]
      · exact ih (lcm acc q) hp

private theorem foldl_lcm_dvd (acc : DensePoly F) (xs : List (DensePoly F))
    (r : DensePoly F) (hacc : acc ∣ r) (hxs : ∀ p ∈ xs, p ∣ r) :
    xs.foldl lcm acc ∣ r := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons p xs ih =>
      simp only [List.foldl_cons]
      exact ih (lcm acc p) (lcm_dvd acc p r hacc (hxs p (by simp)))
        (by
          intro q hq
          exact hxs q (List.mem_cons_of_mem p hq))

/-- A member of a list divides its folded least common multiple. -/
theorem dvd_lcmList_of_mem {p : DensePoly F} {xs : List (DensePoly F)}
    (hp : p ∈ xs) : p ∣ lcmList xs :=
  dvd_foldl_lcm_of_mem 1 p xs hp

/-- The folded LCM divides every common multiple of the list. -/
theorem lcmList_dvd (xs : List (DensePoly F)) (r : DensePoly F)
    (h : ∀ p ∈ xs, p ∣ r) : lcmList xs ∣ r := by
  apply foldl_lcm_dvd 1 xs r
  · refine ⟨r, ?_⟩
    rw [mul_comm_poly, mul_one_right_poly]
  · exact h

/-- A list of nonzero polynomials has a monic folded LCM. -/
theorem lcmList_monic (xs : List (DensePoly F)) (h : ∀ p ∈ xs, p ≠ 0) :
    (lcmList xs).Monic := by
  apply foldl_lcm_monic 1 xs one_poly_ne_zero
  · rw [monic_iff_leadingCoeff_eq_one, leadingCoeff_one]
  · exact h

end Hex.DensePoly
