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

private theorem scale_one (p : DensePoly F) : scale (1 : F) p = p := by
  apply ext_coeff
  intro n
  rw [coeff_scale_semiring]
  grind

omit [DecidableEq F] in
private theorem one_div_ne_zero (a : F) (ha : a ≠ 0) : 1 / a ≠ 0 := by
  intro h
  have hcancel : (1 / a) * a = 1 := by
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.one_mul,
      Lean.Grind.Field.inv_mul_cancel ha]
  rw [h, Lean.Grind.Semiring.zero_mul] at hcancel
  exact Lean.Grind.Field.zero_ne_one hcancel

private theorem degree_lt_fuel (p : DensePoly F) :
    p.degree?.getD 0 < p.size + 1 := by
  by_cases hsize : p.size = 0
  · simp [degree?, hsize]
  · have hdeg : p.degree?.getD 0 = p.size - 1 := by
      simp [degree?, hsize]
    omega

private theorem scale_inv_cancel (p : DensePoly F) (hp : p ≠ 0) :
    scale p.leadingCoeff (scale (1 / p.leadingCoeff) p) = p := by
  have hpPos : 0 < p.size := by
    by_cases h : 0 < p.size
    · exact h
    · exact False.elim (hp ((size_eq_zero_iff p).mp (Nat.eq_zero_of_not_pos h)))
  have hlc := leadingCoeff_ne_zero_of_pos_size p hpPos
  rw [scale_scale]
  have hcancel : p.leadingCoeff * (1 / p.leadingCoeff) = 1 := by
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.one_mul,
      Lean.Grind.Field.mul_inv_cancel hlc]
  rw [hcancel, scale_one]

private theorem dvd_scale_field {d p : DensePoly F} (c : F) (h : d ∣ p) :
    d ∣ scale c p := by
  rcases h with ⟨q, hq⟩
  refine ⟨scale c q, ?_⟩
  rw [hq, mul_scale]

private theorem xgcdLeftMonicAux_stop
    (r₀ s₀ r₁ s₁ : DensePoly F) (fuel : Nat) (hr₁ : r₁ = 0) :
    (xgcdLeftMonicAux r₀ s₀ r₁ s₁ fuel).gcd = r₀ := by
  cases fuel with
  | zero => simp [xgcdLeftMonicAux]
  | succ fuel =>
      subst r₁
      rfl

private theorem xgcdLeftMonicAux_dvd
    (r₀ s₀ r₁ s₁ : DensePoly F) (fuel : Nat)
    (hfuel : r₁.degree?.getD 0 < fuel) :
    (xgcdLeftMonicAux r₀ s₀ r₁ s₁ fuel).gcd ∣ r₀ ∧
      (xgcdLeftMonicAux r₀ s₀ r₁ s₁ fuel).gcd ∣ r₁ := by
  induction fuel generalizing r₀ s₀ r₁ s₁ with
  | zero => omega
  | succ fuel ih =>
      unfold xgcdLeftMonicAux
      by_cases hr₁zero : r₁.isZero
      · simp only [hr₁zero, ↓reduceDIte]
        exact ⟨dvd_refl_poly r₀, by
          rw [(size_eq_zero_iff r₁).mp ((isZero_eq_true_iff r₁).mp hr₁zero)]
          exact dvd_zero_poly r₀⟩
      · simp only [hr₁zero]
        let c := 1 / r₁.leadingCoeff
        let r₁' := scale c r₁
        let s₁' := scale c s₁
        let qr := divMod r₀ r₁'
        let rem := qr.2
        have hr₁ne : r₁ ≠ 0 := by
          intro h
          apply hr₁zero
          subst r₁
          rfl
        have hr₁Pos : 0 < r₁.size := by
          exact Nat.pos_of_ne_zero (fun h => hr₁ne ((size_eq_zero_iff r₁).mp h))
        have hc : c ≠ 0 := by
          apply one_div_ne_zero
          exact leadingCoeff_ne_zero_of_pos_size r₁ hr₁Pos
        have hr₁size : r₁'.size = r₁.size := by
          exact size_scale_field hc r₁
        have hr₁degree : r₁'.degree?.getD 0 = r₁.degree?.getD 0 := by
          simp [degree?, hr₁size]
        change (xgcdLeftMonicAux r₁' s₁' rem
            (s₀ - qr.1 * s₁') fuel).gcd ∣ r₀ ∧
          (xgcdLeftMonicAux r₁' s₁' rem
            (s₀ - qr.1 * s₁') fuel).gcd ∣ r₁
        have hr₁recover : scale r₁.leadingCoeff r₁' = r₁ := by
          exact scale_inv_cancel r₁ hr₁ne
        by_cases hpos : 0 < r₁'.degree?.getD 0
        · have hremDegree : rem.degree?.getD 0 < r₁'.degree?.getD 0 := by
            simpa [qr, rem] using field_divMod_remainder_degree_lt r₀ r₁' hpos
          have hrec := ih r₁' s₁' rem (s₀ - qr.1 * s₁') (by
            rw [hr₁degree] at hremDegree
            omega)
          have hgRight := hrec.1
          have hgRem := hrec.2
          constructor
          · have hspec : qr.1 * r₁' + rem = r₀ := by
              simpa [qr, rem] using field_divMod_spec r₀ r₁'
            rw [← hspec]
            exact dvd_add_poly (dvd_mul_left_poly qr.1 hgRight) hgRem
          · rw [← hr₁recover]
            exact dvd_scale_field r₁.leadingCoeff hgRight
        · have hr₁false : r₁'.isZero = false := by
            rw [isZero_eq_false_iff]
            omega
          have hremZero : rem = 0 := by
            simpa [qr, rem] using
              field_divMod_remainder_eq_zero_of_not_pos_degree
                r₀ r₁' hr₁false hpos
          have hgEq : (xgcdLeftMonicAux r₁' s₁' rem
              (s₀ - qr.1 * s₁') fuel).gcd = r₁' := by
            exact xgcdLeftMonicAux_stop
              r₁' s₁' rem (s₀ - qr.1 * s₁') fuel hremZero
          constructor
          · rw [hgEq]
            have hspec : qr.1 * r₁' + rem = r₀ := by
              simpa [qr, rem] using field_divMod_spec r₀ r₁'
            rw [hremZero, add_zero_poly] at hspec
            rw [← hspec]
            exact dvd_mul_left_poly qr.1 (dvd_refl_poly r₁')
          · rw [hgEq, ← hr₁recover]
            exact dvd_scale_field r₁.leadingCoeff (dvd_refl_poly r₁')

/-- The monic one-sided extended gcd's returned representative divides both
inputs over a field. -/
theorem xgcdLeftMonic_dvd (p q : DensePoly F) :
    (xgcdLeftMonic p q).gcd ∣ p ∧ (xgcdLeftMonic p q).gcd ∣ q := by
  unfold xgcdLeftMonic
  apply xgcdLeftMonicAux_dvd
  have hq := degree_lt_fuel q
  omega

private theorem xgcdLeftMonic_step
    (a s₀ t₀ s₁ t₁ p q : DensePoly F) :
    (s₀ - a * s₁) * p + (t₀ - a * t₁) * q =
      (s₀ * p + t₀ * q) - a * (s₁ * p + t₁ * q) := by
  rw [sub_eq_add_neg_poly s₀ (a * s₁), sub_eq_add_neg_poly t₀ (a * t₁),
    mul_add_left_poly, mul_add_left_poly, neg_mul_right_poly, neg_mul_right_poly,
    mul_assoc_poly a s₁ p, mul_assoc_poly a t₁ q, mul_add_right_poly]
  apply ext_coeff
  intro n
  have hzeroAdd : (0 : F) + (0 : F) = 0 := by grind
  have hzeroSub : (0 : F) - (0 : F) = 0 := by grind
  rw [coeff_add (s₀ * p + (0 - a * (s₁ * p)))
      (t₀ * q + (0 - a * (t₁ * q))) n hzeroAdd]
  rw [coeff_add (s₀ * p) (0 - a * (s₁ * p)) n hzeroAdd,
    coeff_sub 0 (a * (s₁ * p)) n hzeroSub, coeff_zero,
    coeff_add (t₀ * q) (0 - a * (t₁ * q)) n hzeroAdd,
    coeff_sub 0 (a * (t₁ * q)) n hzeroSub, coeff_zero,
    coeff_sub (s₀ * p + t₀ * q) (a * (s₁ * p) + a * (t₁ * q)) n hzeroSub,
    coeff_add (s₀ * p) (t₀ * q) n hzeroAdd,
    coeff_add (a * (s₁ * p)) (a * (t₁ * q)) n hzeroAdd]
  grind

private theorem xgcdLeftMonicAux_bezout
    (p q r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly F) (fuel : Nat)
    (hr₀ : s₀ * p + t₀ * q = r₀)
    (hr₁ : s₁ * p + t₁ * q = r₁) :
    ∃ t, (xgcdLeftMonicAux r₀ s₀ r₁ s₁ fuel).left * p + t * q =
      (xgcdLeftMonicAux r₀ s₀ r₁ s₁ fuel).gcd := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      exact ⟨t₀, by simpa [xgcdLeftMonicAux] using hr₀⟩
  | succ fuel ih =>
      unfold xgcdLeftMonicAux
      by_cases hr₁zero : r₁.isZero
      · exact ⟨t₀, by simpa [hr₁zero] using hr₀⟩
      · simp only [hr₁zero]
        let c := 1 / r₁.leadingCoeff
        let r₁' := scale c r₁
        let s₁' := scale c s₁
        let t₁' := scale c t₁
        let qr := divMod r₀ r₁'
        let rem := qr.2
        let s := s₀ - qr.1 * s₁'
        let t := t₀ - qr.1 * t₁'
        have hr₁scaled : s₁' * p + t₁' * q = r₁' := by
          calc
            s₁' * p + t₁' * q =
                scale c (s₁ * p) + scale c (t₁ * q) := by
                  rw [scale_mul, scale_mul]
            _ = scale c (s₁ * p + t₁ * q) := by rw [scale_add]
            _ = r₁' := by rw [hr₁]
        apply ih r₁' s₁' t₁' rem s t
        · exact hr₁scaled
        · have hspec : qr.1 * r₁' + rem = r₀ := by
            simpa [qr, rem] using field_divMod_spec r₀ r₁'
          calc
            s * p + t * q =
                (s₀ * p + t₀ * q) - qr.1 *
                  (s₁' * p + t₁' * q) := by
                    exact xgcdLeftMonic_step qr.1 s₀ t₀ s₁' t₁' p q
            _ = r₀ - qr.1 * r₁' := by rw [hr₀, hr₁scaled]
            _ = rem := by
              rw [← hspec]
              apply ext_coeff
              intro n
              simp only [coeff_sub_ring, coeff_add_semiring]
              grind

/-- The monic one-sided extended gcd preserves a Bezout identity, with the
untracked right coefficient supplied existentially. -/
theorem xgcdLeftMonic_bezout (p q : DensePoly F) :
    ∃ t, (xgcdLeftMonic p q).left * p + t * q = (xgcdLeftMonic p q).gcd := by
  unfold xgcdLeftMonic
  apply xgcdLeftMonicAux_bezout p q
  · rw [mul_comm_poly (1 : DensePoly F) p, mul_one_right_poly, zero_mul,
      add_zero_poly]
  · rw [zero_mul, mul_comm_poly (1 : DensePoly F) q, mul_one_right_poly,
      zero_add]

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
