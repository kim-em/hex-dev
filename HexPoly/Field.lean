/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly.Euclid
public import HexPoly.Instances
public import HexPoly.Monic

public section

/-!
Lawfulness of dense-polynomial Euclidean operations over every lightweight
field.
-/

namespace Hex

universe u

namespace DensePoly

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F]

omit [DecidableEq F] in
private theorem field_div_cancel (a b : F) (hb : b ≠ 0) :
    a - (a / b) * b = 0 := by
  rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
    Lean.Grind.Field.inv_mul_cancel hb, Lean.Grind.Semiring.mul_one]
  grind

omit [DecidableEq F] in
private theorem field_mul_div_cancel (a b : F) (hb : b ≠ 0) :
    (a * b) / b = a := by
  rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
    Lean.Grind.Field.mul_inv_cancel hb, Lean.Grind.Semiring.mul_one]

omit [DecidableEq F] in
private theorem field_mul_ne_zero (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro h
  rcases Lean.Grind.Field.of_mul_eq_zero h with h | h
  · exact ha h
  · exact hb h

private theorem field_divMod_spec (p q : DensePoly F) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  by_cases hq : q.size = 0
  · have hrem := divMod_remainder_eq_self_of_size_zero p q hq
    have hqzero : q = 0 := (size_eq_zero_iff q).mp hq
    change (divMod p q).1 * q + (divMod p q).2 = p
    rw [hrem, hqzero, mul_comm_poly, zero_mul, zero_add]
  · exact divMod_reconstruction p q fun a =>
      field_div_cancel a q.leadingCoeff
        (leadingCoeff_ne_zero_of_pos_size q (Nat.pos_of_ne_zero hq))

private theorem field_divMod_remainder_degree_lt (p q : DensePoly F)
    (hdegree : 0 < q.degree?.getD 0) :
    (divMod p q).2.degree?.getD 0 < q.degree?.getD 0 := by
  apply divMod_remainder_degree_lt_of_pos_degree_of_cancel p q hdegree
  intro a
  apply field_div_cancel
  apply leadingCoeff_ne_zero_of_pos_size
  by_cases hq : q.size = 0
  · simp [degree?, hq] at hdegree
  · exact Nat.pos_of_ne_zero hq

private theorem field_divMod_remainder_eq_zero_of_not_pos_degree
    (p q : DensePoly F) (hqfalse : q.isZero = false)
    (hdegree : ¬ 0 < q.degree?.getD 0) :
    (divMod p q).2 = 0 := by
  have hqsizeNe : q.size ≠ 0 := by
    intro hsize
    have hzero : q.isZero = true := by
      simpa [isZero, size, Array.isEmpty_iff_size_eq_zero] using hsize
    rw [hzero] at hqfalse
    contradiction
  have hqsize : q.size = 1 := by
    have hdeg : q.degree?.getD 0 = q.size - 1 := by
      simp [degree?, hqsizeNe]
    rw [hdeg] at hdegree
    omega
  exact divMod_remainder_eq_zero_of_degree_zero_of_cancel p q hqsize
    (fun a => field_div_cancel a q.leadingCoeff
      (leadingCoeff_ne_zero_of_pos_size q (by omega)))

private theorem field_divMod_exact (p q : DensePoly F) (hdiv : q ∣ p) :
    (divMod p q).2 = 0 := by
  rcases hdiv with ⟨r, hr⟩
  by_cases hq : q = 0
  · subst q
    have hp : p = 0 := by
      rw [zero_mul] at hr
      exact hr
    subst p
    rfl
  · have hqPos : 0 < q.size := by
      apply Nat.pos_of_ne_zero
      intro hsize
      exact hq ((size_eq_zero_iff q).mp hsize)
    have hlc := leadingCoeff_ne_zero_of_pos_size q hqPos
    have hpair : divMod p q = (r, 0) :=
      divMod_eq_of_polynomial_mul p q r hq
        (fun a => field_mul_div_cancel a q.leadingCoeff hlc)
        (fun a ha => field_mul_ne_zero a q.leadingCoeff ha hlc)
        (by rw [hr, mul_comm_poly])
    exact congrArg Prod.snd hpair

private theorem field_congr_mod (p m : DensePoly F) :
    m ∣ (p % m) - p := by
  refine ⟨0 - p / m, ?_⟩
  have hrec := field_divMod_spec p m
  change (divMod p m).2 - p = m * (0 - (divMod p m).1)
  grind

private theorem field_mod_eq_mod_of_congr_pos_degree
    (p q m : DensePoly F) (hdegree : 0 < m.degree?.getD 0)
    (hcongr : m ∣ (p - q)) :
    p % m = q % m := by
  rcases hcongr with ⟨k, hk⟩
  have hqrec := field_divMod_spec q m
  have hrec : (q / m + k) * m + q % m = p := by
    change ((divMod q m).1 + k) * m + (divMod q m).2 = p
    grind
  have hlc : m.leadingCoeff ≠ 0 := by
    apply leadingCoeff_ne_zero_of_pos_size
    by_cases hm : m.size = 0
    · simp [degree?, hm] at hdegree
    · exact Nat.pos_of_ne_zero hm
  have hpair := divMod_eq_of_reconstruction p m (q / m + k) (q % m)
    hdegree
    (fun a => field_div_cancel a m.leadingCoeff hlc)
    (fun a => field_mul_div_cancel a m.leadingCoeff hlc)
    (fun a ha => field_mul_ne_zero a m.leadingCoeff ha hlc)
    hrec (field_divMod_remainder_degree_lt q m hdegree)
  have hsnd := congrArg (fun z : DensePoly F × DensePoly F => z.2) hpair
  exact hsnd

private theorem field_mod_eq_mod_of_congr_not_pos_degree
    (p q m : DensePoly F) (hdegree : ¬ 0 < m.degree?.getD 0)
    (hcongr : m ∣ (p - q)) :
    p % m = q % m := by
  by_cases hm : m.size = 0
  · have hm0 : m = 0 := (size_eq_zero_iff m).mp hm
    have hpq : p - q = 0 := by
      rcases hcongr with ⟨k, hk⟩
      rw [hm0, zero_mul] at hk
      exact hk
    have heq : p = q := by grind
    rw [heq]
  · have hmSize : m.size = 1 := by
      have hdeg : m.degree?.getD 0 = m.size - 1 := by simp [degree?, hm]
      rw [hdeg] at hdegree
      omega
    have hmFalse : m.isZero = false := (isZero_eq_false_iff m).mpr (by omega)
    rw [mod_eq_divMod, mod_eq_divMod,
      field_divMod_remainder_eq_zero_of_not_pos_degree p m hmFalse hdegree,
      field_divMod_remainder_eq_zero_of_not_pos_degree q m hmFalse hdegree]

private theorem field_mod_eq_mod_of_congr (p q m : DensePoly F)
    (hcongr : m ∣ (p - q)) :
    p % m = q % m := by
  by_cases hdegree : 0 < m.degree?.getD 0
  · exact field_mod_eq_mod_of_congr_pos_degree p q m hdegree hcongr
  · exact field_mod_eq_mod_of_congr_not_pos_degree p q m hdegree hcongr

/-- Executable long division is lawful over every lightweight field. -/
instance (priority := 50) instDivModLawsField : DivModLaws F where
  divMod_spec := field_divMod_spec
  divMod_remainder_degree_lt_of_pos_degree := field_divMod_remainder_degree_lt
  divModMonic_eq_divMod_of_monic := by
    intro p q hmonic
    by_cases hlt : p.degree?.getD 0 < q.degree?.getD 0
    · rw [divMod_eq_zero_self_of_degree_lt p q hlt]
      unfold divModMonic
      exact divModArray_eq_zero_self_of_degree_lt p q id hlt
    · apply divModMonic_eq_divMod_of_monic_of_scale p q hmonic hlt
      intro a
      rw [hmonic, Lean.Grind.Field.div_eq_mul_inv,
        Lean.Grind.Field.inv_one, Lean.Grind.Semiring.mul_one]
  mod_self_eq_zero := by
    intro p
    exact field_divMod_exact p p (dvd_refl_poly p)
  mod_eq_zero_of_dvd := field_divMod_exact
  mod_mod_of_not_pos_degree := by
    intro p m _
    exact field_mod_eq_mod_of_congr (p % m) p m (field_congr_mod p m)
  mod_eq_mod_of_congr := field_mod_eq_mod_of_congr
  mod_add_mod := by
    intro p q m
    apply field_mod_eq_mod_of_congr
    refine ⟨p / m + q / m, ?_⟩
    have hp := field_divMod_spec p m
    have hq := field_divMod_spec q m
    change p + q - ((divMod p m).2 + (divMod q m).2) =
      m * ((divMod p m).1 + (divMod q m).1)
    grind
  mod_mul_mod := by
    intro p q m
    apply field_mod_eq_mod_of_congr
    refine ⟨(p / m) * (q / m) * m + (p / m) * (q % m) +
      (q / m) * (p % m), ?_⟩
    have hp := field_divMod_spec p m
    have hq := field_divMod_spec q m
    change p * q - (divMod p m).2 * (divMod q m).2 =
      m * ((divMod p m).1 * (divMod q m).1 * m +
        (divMod p m).1 * (divMod q m).2 +
        (divMod q m).1 * (divMod p m).2)
    grind

/-- Executable gcd and extended gcd are lawful over every lightweight field. -/
instance (priority := 50) instGcdLawsField : GcdLaws F where
  gcd_dvd_left := by
    intro p q
    exact gcd_dvd_left_of_divModLaws
      field_divMod_remainder_eq_zero_of_not_pos_degree p q
  gcd_dvd_right := by
    intro p q
    exact gcd_dvd_right_of_divModLaws
      field_divMod_remainder_eq_zero_of_not_pos_degree p q
  dvd_gcd := dvd_gcd_of_divModLaws
  xgcd_bezout := xgcd_bezout_of_divModLaws

/-- A polynomial admitting a multiplicative inverse has degree zero. -/
theorem size_eq_one_of_mul_eq_one (p q : DensePoly F) (h : p * q = 1) :
    p.size = 1 := by
  have hOneSize : (1 : DensePoly F).size = 1 :=
    size_one (Lean.Grind.Field.zero_ne_one (α := F)).symm
  have hOne : (1 : DensePoly F) ≠ 0 := by
    intro hz
    have hs := congrArg DensePoly.size hz
    rw [hOneSize, size_zero] at hs
    exact Nat.one_ne_zero hs
  have hp : p ≠ 0 := by
    intro hp
    rw [hp, DensePoly.zero_mul] at h
    exact hOne h.symm
  have hpPos : 0 < p.size := by
    apply Nat.pos_of_ne_zero
    intro hs
    exact hp ((size_eq_zero_iff p).mp hs)
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hsize
    have hdegOne : ((1 : DensePoly F).degree?).getD 0 = 0 := by
      simp [degree?, hOneSize]
    have hdegP : p.degree?.getD 0 = p.size - 1 := by
      simp [degree?, Nat.ne_of_gt hpPos]
    have hlt : ((1 : DensePoly F).degree?).getD 0 < p.degree?.getD 0 := by
      rw [hdegOne, hdegP]
      omega
    have hdvd : p ∣ (1 : DensePoly F) := ⟨q, h.symm⟩
    have hzero := mod_eq_zero_of_dvd (1 : DensePoly F) p hdvd
    have hself := mod_eq_self_of_degree_lt (1 : DensePoly F) p hlt
    rw [hself] at hzero
    exact hOne hzero
  · exact hpPos

/-- Vanishing remainder supplies the quotient witness for divisibility. -/
theorem dvd_of_mod_eq_zero (p q : DensePoly F) (hmod : p % q = 0) :
    q ∣ p := by
  refine ⟨p / q, ?_⟩
  have hrec := div_mul_add_mod p q
  rw [hmod] at hrec
  rw [mul_comm_poly]
  grind

/-- Over a field, nonzero polynomial products have the expected stored size. -/
theorem size_mul_field (p q : DensePoly F) (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).size = p.size + q.size - 1 := by
  have hpPos : 0 < p.size := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hp ((size_eq_zero_iff p).mp h)
  have hqPos : 0 < q.size := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hq ((size_eq_zero_iff q).mp h)
  have htop :
      (p * q).coeff (p.size - 1 + (q.size - 1)) =
        p.leadingCoeff * q.leadingCoeff := by
    rw [coeff_mul_top p q hpPos hqPos,
      ← leadingCoeff_eq_coeff_last p hpPos,
      ← leadingCoeff_eq_coeff_last q hqPos]
  have htopNe :
      (p * q).coeff (p.size - 1 + (q.size - 1)) ≠ 0 := by
    rw [htop]
    exact field_mul_ne_zero _ _
      (leadingCoeff_ne_zero_of_pos_size p hpPos)
      (leadingCoeff_ne_zero_of_pos_size q hqPos)
  apply Nat.le_antisymm (size_mul_le p q)
  apply Nat.le_of_not_gt
  intro hlt
  apply htopNe
  apply coeff_eq_zero_of_size_le
  omega

/-- Multiplication of constant dense polynomials. -/
theorem C_mul_C (a b : F) : C a * C b = C (a * b) := by
  have ha : C a = monomial 0 a := by
    apply ext_coeff
    intro n
    rw [coeff_C, coeff_monomial]
  have hb : C b = monomial 0 b := by
    apply ext_coeff
    intro n
    rw [coeff_C, coeff_monomial]
  rw [ha, hb, monomial_mul_monomial]
  apply ext_coeff
  intro n
  rw [coeff_monomial, coeff_C]

/-- A proper polynomial divisor has strictly smaller stored size. -/
theorem size_lt_of_dvd_not_dvd {g p : DensePoly F} (hg : g ≠ 0) (hp : p ≠ 0)
    (hgp : g ∣ p) (hpg : ¬p ∣ g) : g.size < p.size := by
  rcases hgp with ⟨q, hq⟩
  have hqNe : q ≠ 0 := by
    intro hz
    apply hp
    calc
      p = g * q := hq
      _ = 0 := by rw [hz]; grind
  have hqSize : 1 < q.size := by
    have hqPos : 0 < q.size := by
      apply Nat.pos_of_ne_zero
      intro h
      exact hqNe ((size_eq_zero_iff q).mp h)
    apply Nat.lt_of_le_of_ne (by omega)
    intro hle
    have hsize : q.size = 1 := by omega
    have hqC := eq_C_leadingCoeff_of_size_one hsize
    let c := q.leadingCoeff
    have hc : c ≠ 0 := by
      apply leadingCoeff_ne_zero_of_pos_size
      omega
    apply hpg
    refine ⟨C (1 / c), ?_⟩
    have hcunit : c * (1 / c) = 1 := by
      rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.one_mul,
        Lean.Grind.Field.mul_inv_cancel hc]
    calc
      g = g * 1 := (mul_one_right_poly g).symm
      _ = g * C (c * (1 / c)) := by rw [hcunit]; rfl
      _ = g * (C c * C (1 / c)) := by rw [C_mul_C]
      _ = (g * C c) * C (1 / c) := by rw [mul_assoc_poly]
      _ = p * C (1 / c) := by rw [← hqC, hq]
  have hsize := size_mul_field g q hg hqNe
  rw [hq]
  omega

/-- The monic gcd is a strict divisor of a nonzero left input whenever the
left input does not divide the right input. -/
theorem monicize_gcd_size_lt_left (p q : DensePoly F) (hp : p ≠ 0)
    (hpdq : ¬p ∣ q) : (monicize (gcd p q)).size < p.size := by
  have hgDiv : gcd p q ∣ p := gcd_dvd_left p q
  have hg : gcd p q ≠ 0 := by
    intro hzero
    rcases hgDiv with ⟨r, hr⟩
    rw [hzero, zero_mul] at hr
    exact hp hr
  have hnot : ¬p ∣ gcd p q := by
    intro h
    rcases h with ⟨a, ha⟩
    rcases gcd_dvd_right p q with ⟨b, hb⟩
    apply hpdq
    refine ⟨a * b, ?_⟩
    calc
      q = gcd p q * b := hb
      _ = (p * a) * b := by rw [ha]
      _ = p * (a * b) := mul_assoc_poly p a b
  have hlt := size_lt_of_dvd_not_dvd hg hp hgDiv hnot
  rw [size_monicize]
  exact hlt

end DensePoly

end Hex
