/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Grind.Ring.Basic
public import Init.Data.List.Lemmas
public import HexPoly.Operations
public import HexPoly.Euclid.MulRing
import all HexPoly.Euclid.DivGcd
import all HexPoly.Euclid.MulRing

public section
set_option backward.proofsInPublic true

/-!
Division-reconstruction identities, divisibility lemmas, the concrete
extended-gcd/gcd correctness proofs, and division uniqueness
(`divMod_eq_of_polynomial_mul`) for `DensePoly`.
-/
namespace Hex

universe u

namespace DensePoly
/-- Multiplication by a unit-coefficient monomial shifts coefficients upward. -/
theorem monomial_one_mul_poly_eq_shift {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (shift : Nat) (q : DensePoly S) :
    monomial shift 1 * q = DensePoly.shift shift q := by
  apply ext_coeff
  intro n
  rw [coeff_mul, mulCoeffSum_eq_diagonal, diagonalSum_eq_degree_bound, coeff_shift]
  have hterm : ∀ i,
      diagonalMulCoeffTerm (monomial shift 1) q n i =
        if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0 := by
    intro i
    unfold diagonalMulCoeffTerm
    rw [coeff_monomial]
    by_cases hni : n < i
    · have hcond : ¬(i = shift ∧ shift ≤ n) := by
        intro h
        omega
      simp [hni, hcond]
    · have hile : i ≤ n := by omega
      by_cases hishift : i = shift
      · subst i
        simp [hni, hile]
        grind
      · simp [hni, hishift]
        exact Lean.Grind.Semiring.zero_mul _
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i =>
          acc + diagonalMulCoeffTerm (monomial shift 1) q n i) acc =
        xs.foldl (fun acc i =>
          acc + if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [hterm i]
        exact ih _
  rw [hfold (List.range (n + 1)) 0]
  by_cases hshift : shift ≤ n
  · rw [if_neg (by omega : ¬n < shift)]
    have hsimp : ∀ i,
        (if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) =
          if i = shift then q.coeff (n - shift) else 0 := by
      intro i
      simp [hshift]
    have hfold2 : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i =>
            acc + if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) acc =
          xs.foldl (fun acc i =>
            acc + if i = shift then q.coeff (n - shift) else 0) acc := by
      intro xs
      induction xs with
      | nil =>
          intro acc
          rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          rw [hsimp i]
          exact ih _
    rw [hfold2 (List.range (n + 1)) 0, fold_single_index, if_pos (by omega : shift < n + 1)]
  · rw [if_pos (by omega : n < shift)]
    have hzero_fold : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i =>
            acc + if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) acc = acc := by
      intro xs
      induction xs with
      | nil =>
          intro acc
          rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          have hzero :
              (if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) = 0 := by
            simp [hshift]
          rw [hzero, show acc + (0 : S) = acc by grind]
          exact ih _
    rw [hzero_fold]
    rfl

/-- Negation passes through the left multiplicand: `(0 - p) * q = 0 - p * q`.
A `grind` normalization lemma that lets sign manipulations in the extended-gcd
recursion move the negation out to the product. -/
@[grind =] theorem neg_mul_right_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    (0 - p) * q = 0 - p * q := by
  rw [mul_comm_poly (0 - p) q, mul_sub_zero_comm q p]

/-- Telescoping identity for an extended-Euclid update step:
`(p + t) * q + (r - t * q) = p * q + r`. -/
theorem add_mul_sub_cancel_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p t q r : DensePoly S) :
    (p + t) * q + (r - t * q) = p * q + r := by
  rw [mul_add_left_poly]
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_add (p * q + t * q) (r - t * q) n hzero_add, coeff_add (p * q) (t * q) n hzero_add,
    coeff_sub r (t * q) n hzero_sub, coeff_add (p * q) r n hzero_add]
  grind

/-- One long-division reconstruction step preserves the accumulated identity
`quot * q + rem`. -/
theorem divMod_reconstruction_step {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (quot term q rem : DensePoly S) :
    (quot + term) * q + (rem - term * q) = quot * q + rem := by
  exact add_mul_sub_cancel_right quot term q rem

/-- The polynomial-level reading of one step of the array-based long-division
remainder update: subtracting `coeff * q * x^shift` from `rem`, in coefficient
form, matches the in-place `subtractScaledShift` array update whenever the
update window stays within `rem`. -/
private theorem ofCoeffs_subtractScaledShift_eq_sub_monomial_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (rem q : Array S) (shift : Nat) (coeff : S)
    (hbound : ∀ j, j < q.size → shift + j < rem.size) :
    ofCoeffs (subtractScaledShift rem q shift coeff) =
      ofCoeffs rem - monomial shift coeff * ofCoeffs q := by
  apply ext_coeff
  intro n
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_ofCoeffs, coeff_sub (ofCoeffs rem) (monomial shift coeff * ofCoeffs q) n hzero_sub,
    coeff_ofCoeffs, coeff_mul, mulCoeffSum_eq_diagonal, diagonalSum_eq_degree_bound,
    subtractScaledShift_getD rem q shift coeff n hbound]
  -- Compute each diagonal term using the monomial's coefficient law.
  have hterm : ∀ i,
      diagonalMulCoeffTerm (monomial shift coeff) (ofCoeffs q) n i =
        if i = shift ∧ shift ≤ n
          then coeff * q.getD (n - shift) (Zero.zero : S)
          else 0 := by
    intro i
    unfold diagonalMulCoeffTerm
    rw [coeff_monomial, coeff_ofCoeffs]
    by_cases hni : n < i
    · by_cases hieq : i = shift
      · subst i
        have hshift_gt : ¬ shift ≤ n := by omega
        simp [hni, hshift_gt]
      · simp [hni, hieq]
    · have hile : i ≤ n := by omega
      by_cases hieq : i = shift
      · subst i
        simp [hni, hile]
      · simp [hni, hieq]
        exact Lean.Grind.Semiring.zero_mul _
  -- Lift the term-by-term rewrite to the foldl.
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i =>
          acc + diagonalMulCoeffTerm (monomial shift coeff) (ofCoeffs q) n i) acc =
        xs.foldl (fun acc i =>
          acc + if i = shift ∧ shift ≤ n
            then coeff * q.getD (n - shift) (Zero.zero : S)
            else 0) acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [hterm i]
        exact ih _
  rw [hfold (List.range (n + 1)) 0]
  by_cases hshift : shift ≤ n
  · -- Collapse the conjunction `i = shift ∧ shift ≤ n` to `i = shift`.
    have hsimp : ∀ i,
        (if i = shift ∧ shift ≤ n
            then coeff * q.getD (n - shift) (Zero.zero : S)
            else 0) =
        (if i = shift
            then coeff * q.getD (n - shift) (Zero.zero : S)
            else 0) := by
      intro i
      simp [hshift]
    have hfold2 : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i =>
            acc + if i = shift ∧ shift ≤ n
              then coeff * q.getD (n - shift) (Zero.zero : S)
              else 0) acc =
          xs.foldl (fun acc i =>
            acc + if i = shift
              then coeff * q.getD (n - shift) (Zero.zero : S)
              else 0) acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          rw [hsimp i]
          exact ih _
    rw [hfold2 (List.range (n + 1)) 0, fold_single_index]
    have hshift_lt : shift < n + 1 := by omega
    rw [if_pos hshift_lt]
    by_cases hsize : n - shift < q.size
    · rw [if_pos ⟨hshift, hsize⟩]
    · have hand : ¬ (shift ≤ n ∧ n - shift < q.size) := fun ⟨_, h⟩ => hsize h
      rw [if_neg hand]
      have hq0 : q.getD (n - shift) (Zero.zero : S) = (0 : S) := by
        unfold Array.getD
        rw [dif_neg (Nat.not_lt.mpr (Nat.le_of_not_lt hsize))]
        rfl
      rw [hq0]
      grind
  · -- All terms are zero; the fold yields zero.
    have hzero_fold : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i =>
            acc + if i = shift ∧ shift ≤ n
              then coeff * q.getD (n - shift) (Zero.zero : S)
              else 0) acc = acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          have h0 : (if i = shift ∧ shift ≤ n
              then coeff * q.getD (n - shift) (Zero.zero : S)
              else (0 : S)) = 0 := by
            simp [hshift]
          rw [h0, show acc + (0 : S) = acc by grind]
          exact ih _
    rw [hzero_fold (List.range (n + 1)) 0]
    have hand : ¬ (shift ≤ n ∧ n - shift < q.size) := fun ⟨h, _⟩ => hshift h
    rw [if_neg hand]
    grind

/-- Left absorption for polynomial multiplication: `0 * p = 0`. A `grind`
normalization lemma so that products with a vanished factor collapse during
the division and gcd proofs. -/
@[grind =] theorem zero_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    (0 : DensePoly S) * p = 0 := by
  apply ext_coeff
  intro n
  rw [coeff_mul]
  simp [mulCoeffSum]
  rfl

/-- Left identity for polynomial addition over a commutative ring: `0 + p = p`.
A `grind` normalization lemma so downstream proofs cancel leading zero summands. -/
@[grind =] theorem zero_add {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    (0 : DensePoly S) + p = p := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add 0 p n hzero_add, coeff_zero]
  grind

private theorem eq_zero_of_isZero_true {S : Type _} [Zero S] [DecidableEq S]
    (p : DensePoly S) (h : p.isZero = true) :
    p = 0 := by
  apply ext_coeff
  intro n
  have hsize : p.size = 0 := by
    simpa [isZero, size, Array.isEmpty_iff_size_eq_zero] using h
  rw [coeff_zero]
  exact coeff_eq_zero_of_size_le p (by omega)

private theorem isZero_zero {S : Type _} [Zero S] [DecidableEq S] :
    (0 : DensePoly S).isZero = true := by
  rfl

private theorem degree_getD_lt_size_add_one {S : Type _} [Zero S] [DecidableEq S]
    (p : DensePoly S) :
    p.degree?.getD 0 < p.size + 1 := by
  by_cases hsize : p.size = 0
  · simp [degree?, hsize]
  · have hdeg : p.degree?.getD 0 = p.size - 1 := by
      simp [degree?, hsize]
    omega

/-- Reflexivity of `DensePoly` divisibility (the Mathlib-free `dvd_refl`). -/
theorem dvd_refl_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p ∣ p := by
  exact ⟨1, (mul_one_right_poly p).symm⟩

/-- Every `DensePoly` divides `0` (the Mathlib-free `dvd_zero`). -/
theorem dvd_zero_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p ∣ 0 := by
  exact ⟨0, by rw [mul_comm_poly p 0, zero_mul]⟩

/-- Divisibility is preserved by multiplication on the left: `d ∣ p → d ∣ q * p`. -/
theorem dvd_mul_left_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {d p : DensePoly S} (q : DensePoly S) :
    d ∣ p → d ∣ q * p := by
  intro h
  rcases h with ⟨a, ha⟩
  refine ⟨q * a, ?_⟩
  rw [ha, ← mul_assoc_poly q d a, mul_comm_poly q d, mul_assoc_poly d q a]

/-- A common divisor of two `DensePoly`s divides their sum. -/
theorem dvd_add_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {d p q : DensePoly S} :
    d ∣ p → d ∣ q → d ∣ p + q := by
  intro hp hq
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [ha, hb, mul_add_right_poly]

/-- A common divisor of two `DensePoly`s divides their (zero-based) difference. -/
theorem dvd_sub_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {d p q : DensePoly S} :
    d ∣ p → d ∣ q → d ∣ p - q := by
  intro hp hq
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  refine ⟨a + (0 - b), ?_⟩
  rw [sub_eq_add_neg_poly, ha, hb, mul_add_right_poly, mul_sub_zero_comm, mul_comm_poly b d]

/-- `xgcdAux` base case: when the right input `r₁` is zero, the returned gcd
equals the left input `r₀`. -/
private theorem xgcdAux_gcd_eq_left_of_right_zero {S : Type _}
    [Zero S] [DecidableEq S] [One S] [Add S] [Sub S] [Mul S] [Div S]
    (r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly S) (fuel : Nat) (hr₁ : r₁ = 0) :
    (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd = r₀ := by
  cases fuel with
  | zero =>
      simp [xgcdAux]
  | succ fuel =>
      simp [xgcdAux, hr₁, isZero_zero]

/-- `xgcd_bezout_step` is the single recursion step of the Bezout coefficients:
pairing `(s₀ - a * s₁, t₀ - a * t₁)` with `p, q` equals
`(s₀ * p + t₀ * q) - a * (s₁ * p + t₁ * q)`. -/
private theorem xgcd_bezout_step {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (a s₀ t₀ s₁ t₁ p q : DensePoly S) :
    (s₀ - a * s₁) * p + (t₀ - a * t₁) * q =
      (s₀ * p + t₀ * q) - a * (s₁ * p + t₁ * q) := by
  rw [sub_eq_add_neg_poly s₀ (a * s₁), sub_eq_add_neg_poly t₀ (a * t₁),
    mul_add_left_poly, mul_add_left_poly, neg_mul_right_poly, neg_mul_right_poly,
    mul_assoc_poly a s₁ p, mul_assoc_poly a t₁ q, mul_add_right_poly]
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_add (s₀ * p + (0 - a * (s₁ * p))) (t₀ * q + (0 - a * (t₁ * q))) n
    hzero_add]
  rw [coeff_add (s₀ * p) (0 - a * (s₁ * p)) n hzero_add,
    coeff_sub 0 (a * (s₁ * p)) n hzero_sub, coeff_zero,
    coeff_add (t₀ * q) (0 - a * (t₁ * q)) n hzero_add,
    coeff_sub 0 (a * (t₁ * q)) n hzero_sub, coeff_zero,
    coeff_sub (s₀ * p + t₀ * q) (a * (s₁ * p) + a * (t₁ * q)) n hzero_sub,
    coeff_add (s₀ * p) (t₀ * q) n hzero_add, coeff_add (a * (s₁ * p)) (a * (t₁ * q)) n hzero_add]
  grind

/-- `xgcdAux` satisfies the Bezout identity: the returned `left * p + right * q`
equals the returned `gcd`. -/
private theorem xgcdAux_bezout {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (p q r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly S) (fuel : Nat)
    (hr₀ : s₀ * p + t₀ * q = r₀)
    (hr₁ : s₁ * p + t₁ * q = r₁) :
    let r := xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel
    r.left * p + r.right * q = r.gcd := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      simpa [xgcdAux] using hr₀
  | succ fuel ih =>
      unfold xgcdAux
      by_cases hr₁zero : r₁.isZero
      · simp [hr₁zero, hr₀]
      · simp [hr₁zero]
        let qr := divMod r₀ r₁
        let r := qr.2
        let s := s₀ - qr.1 * s₁
        let t := t₀ - qr.1 * t₁
        apply ih r₁ s₁ t₁ r s t
        · exact hr₁
        · have hspec : qr.1 * r₁ + qr.2 = r₀ := by
            simpa [qr] using DivModLaws.divMod_spec r₀ r₁
          calc
            s * p + t * q
                = (s₀ * p + t₀ * q) - qr.1 * (s₁ * p + t₁ * q) := by
                  exact xgcd_bezout_step qr.1 s₀ t₀ s₁ t₁ p q
            _ = r₀ - qr.1 * r₁ := by rw [hr₀, hr₁]
            _ = qr.2 := by
              have h : r₀ = qr.1 * r₁ + qr.2 := hspec.symm
              rw [h]
              apply ext_coeff
              intro n
              have hzero_add : (0 : S) + (0 : S) = 0 := by grind
              have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
              rw [coeff_sub]
              · rw [coeff_add]
                · grind
                · exact hzero_add
              · exact hzero_sub

/-- Bezout identity for `xgcd`, proved from `DivModLaws` for use when building
the corresponding `GcdLaws` instance. -/
theorem xgcd_bezout_of_divModLaws {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (p q : DensePoly S) :
    let r := xgcd p q
    r.left * p + r.right * q = r.gcd := by
  unfold xgcd
  apply xgcdAux_bezout p q
  · rw [mul_comm_poly (1 : DensePoly S) p, mul_one_right_poly, zero_mul, add_zero_poly]
  · rw [zero_mul, mul_comm_poly (1 : DensePoly S) q, mul_one_right_poly, zero_add]

/-- Common-divisor direction: any `d` dividing both `r₀` and `r₁` divides the
gcd returned by `xgcdAux`. -/
private theorem xgcdAux_common_dvd_gcd {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (d r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly S) (fuel : Nat)
    (hr₀ : d ∣ r₀) (hr₁ : d ∣ r₁) :
    d ∣ (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      simpa [xgcdAux] using hr₀
  | succ fuel ih =>
      unfold xgcdAux
      by_cases hr₁zero : r₁.isZero
      · simp [hr₁zero, hr₀]
      · simp [hr₁zero]
        let qr := divMod r₀ r₁
        let rem := qr.2
        apply ih
        · exact hr₁
        · have hspec : qr.1 * r₁ + rem = r₀ := by
            simpa [qr, rem] using DivModLaws.divMod_spec r₀ r₁
          have hrem : rem = r₀ - qr.1 * r₁ := by
            rw [← hspec]
            apply ext_coeff
            intro n
            have hzero_add : (0 : S) + (0 : S) = 0 := by grind
            have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
            rw [coeff_sub]
            · rw [coeff_add]
              · grind
              · exact hzero_add
            · exact hzero_sub
          change d ∣ rem
          rw [hrem]
          exact dvd_sub_poly hr₀ (dvd_mul_left_poly qr.1 hr₁)

/-- gcd-divides-inputs direction: the gcd returned by `xgcdAux` divides both
inputs `r₀` and `r₁`. -/
private theorem xgcdAux_gcd_dvd_inputs {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (hsmall :
      ∀ p q : DensePoly S,
        q.isZero = false → ¬ 0 < q.degree?.getD 0 → (divMod p q).2 = 0)
    (r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly S) (fuel : Nat)
    (hfuel : r₁.degree?.getD 0 < fuel) :
    (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd ∣ r₀ ∧
      (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd ∣ r₁ := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      omega
  | succ fuel ih =>
      unfold xgcdAux
      by_cases hr₁zero : r₁.isZero
      · simp only [hr₁zero, ↓reduceDIte]
        exact ⟨dvd_refl_poly r₀, by
          rw [eq_zero_of_isZero_true r₁ hr₁zero]
          exact dvd_zero_poly r₀⟩
      · simp only [hr₁zero]
        let qr := divMod r₀ r₁
        let rem := qr.2
        have hr₁false : r₁.isZero = false := by
          cases h : r₁.isZero <;> simp [h] at hr₁zero ⊢
        change (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁) (t₀ - qr.1 * t₁) fuel).gcd ∣ r₀ ∧
          (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁) (t₀ - qr.1 * t₁) fuel).gcd ∣ r₁
        by_cases hpos : 0 < r₁.degree?.getD 0
        · have hrem_degree : rem.degree?.getD 0 < r₁.degree?.getD 0 := by
            simpa [qr, rem] using
              DivModLaws.divMod_remainder_degree_lt_of_pos_degree r₀ r₁ hpos
          have hrem_fuel : rem.degree?.getD 0 < fuel := by omega
          have hrec := ih r₁ s₁ t₁ rem (s₀ - qr.1 * s₁) (t₀ - qr.1 * t₁) hrem_fuel
          have hg_r₁ : (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁)
              (t₀ - qr.1 * t₁) fuel).gcd ∣ r₁ := hrec.1
          have hg_rem : (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁)
              (t₀ - qr.1 * t₁) fuel).gcd ∣ rem := hrec.2
          constructor
          · have hspec : qr.1 * r₁ + rem = r₀ := by
              simpa [qr, rem] using DivModLaws.divMod_spec r₀ r₁
            rw [← hspec]
            exact dvd_add_poly (dvd_mul_left_poly qr.1 hg_r₁) hg_rem
          · exact hg_r₁
        · have hrem_zero : rem = 0 := by
            simpa [qr, rem] using hsmall r₀ r₁ hr₁false hpos
          have hg_eq : (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁)
              (t₀ - qr.1 * t₁) fuel).gcd = r₁ := by
            exact xgcdAux_gcd_eq_left_of_right_zero r₁ s₁ t₁ rem
              (s₀ - qr.1 * s₁) (t₀ - qr.1 * t₁) fuel hrem_zero
          constructor
          · rw [hg_eq]
            have hspec : qr.1 * r₁ + rem = r₀ := by
              simpa [qr, rem] using DivModLaws.divMod_spec r₀ r₁
            rw [hrem_zero, add_zero_poly] at hspec
            rw [← hspec]
            exact dvd_mul_left_poly qr.1 (dvd_refl_poly r₁)
          · rw [hg_eq]
            exact dvd_refl_poly r₁

/-- The gcd returned by `xgcd` divides the left input, assuming `DivModLaws`
and the one-off `hsmall` fact for nonzero divisors of degree zero. This is
intended for `GcdLaws` instance construction. -/
theorem gcd_dvd_left_of_divModLaws {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (hsmall :
      ∀ p q : DensePoly S,
        q.isZero = false → ¬ 0 < q.degree?.getD 0 → (divMod p q).2 = 0)
    (p q : DensePoly S) :
    gcd p q ∣ p := by
  rw [gcd_eq_xgcd_gcd]
  unfold xgcd
  exact (xgcdAux_gcd_dvd_inputs hsmall p 1 0 q 0 1 (p.size + q.size + 1)
    (by
      have hq := degree_getD_lt_size_add_one q
      omega)).1

/-- The gcd returned by `xgcd` divides the right input, assuming `DivModLaws`
and the one-off `hsmall` fact for nonzero divisors of degree zero. This is
intended for `GcdLaws` instance construction. -/
theorem gcd_dvd_right_of_divModLaws {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (hsmall :
      ∀ p q : DensePoly S,
        q.isZero = false → ¬ 0 < q.degree?.getD 0 → (divMod p q).2 = 0)
    (p q : DensePoly S) :
    gcd p q ∣ q := by
  rw [gcd_eq_xgcd_gcd]
  unfold xgcd
  exact (xgcdAux_gcd_dvd_inputs hsmall p 1 0 q 0 1 (p.size + q.size + 1)
    (by
      have hq := degree_getD_lt_size_add_one q
      omega)).2

/-- Any common divisor divides the gcd returned by `xgcd`; this packages the
`DivModLaws` proof needed by `GcdLaws` instance construction. -/
theorem dvd_gcd_of_divModLaws {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (d p q : DensePoly S) :
    d ∣ p → d ∣ q → d ∣ gcd p q := by
  intro hdp hdq
  rw [gcd_eq_xgcd_gcd]
  unfold xgcd
  exact xgcdAux_common_dvd_gcd d p 1 0 q 0 1 (p.size + q.size + 1) hdp hdq

/-- Recursive reconstruction invariant for the array-backed long-division loop.
Under the cancellation hypothesis for the leading-coefficient scaling function
together with sparsity bounds on `quot` and `rem`, each step of `divModArrayAux`
preserves the polynomial-level identity `quot * q + rem`. The bound parameter `B`
is chosen freshly per recursive call so that strict descent of the loop's pivot
position keeps the slot of `quot` about to be written zero. -/
private theorem divModArrayAux_reconstruction {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (q : Array S) (qDegree : Nat) (scaleLead : S → S)
    (fuel : Nat) (quot rem : Array S) (B : Nat)
    (hsize_q : q.size = qDegree + 1)
    (hcancel :
      ∀ a : S, a - scaleLead a * q.getD qDegree (Zero.zero : S) = (Zero.zero : S))
    (hzero_rem :
      ∀ i, qDegree + B ≤ i → rem.getD i (Zero.zero : S) = (Zero.zero : S))
    (hzero_quot :
      ∀ i, i < B → quot.getD i (Zero.zero : S) = (Zero.zero : S))
    (hsize_match : rem.size ≤ qDegree + quot.size) :
    (ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot rem).1 : DensePoly S) *
        ofCoeffs q +
      ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot rem).2 =
      ofCoeffs quot * ofCoeffs q + ofCoeffs rem := by
  induction fuel generalizing quot rem B with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold divModArrayAux
      cases hdeg : arrayDegree? rem with
      | none => rfl
      | some rd =>
          by_cases hrd_lt : rd < qDegree
          · simp [hrd_lt]
          · simp [hrd_lt]
            simp only [← Array.set!_eq_setIfInBounds, ← Array.getD_eq_getD_getElem?]
            have hrd_nonzero : rem.getD rd (Zero.zero : S) ≠ (Zero.zero : S) :=
              arrayDegree?_some_coeff_ne_zero hdeg
            have hrd_lt_size : rd < rem.size := arrayDegree?_some_lt hdeg
            have hrd_ge : qDegree ≤ rd := Nat.le_of_not_lt hrd_lt
            have hrd_lt_B : rd < qDegree + B := by
              rcases Nat.lt_or_ge rd (qDegree + B) with hlt | hge
              · exact hlt
              · exact absurd (hzero_rem rd hge) hrd_nonzero
            have hshift_eq : (rd - qDegree) + qDegree = rd := by omega
            have hshift_lt_B : rd - qDegree < B := by omega
            have hshift_lt_quot : rd - qDegree < quot.size := by
              have h1 : rd < qDegree + quot.size :=
                Nat.lt_of_lt_of_le hrd_lt_size hsize_match
              omega
            have hquot_shift_zero :
                quot.getD (rd - qDegree) (Zero.zero : S) = (Zero.zero : S) :=
              hzero_quot _ hshift_lt_B
            have hbound_rem :
                ∀ j, j < q.size → rd - qDegree + j < rem.size := by
              intro j hj
              have hj_le : j ≤ qDegree := by omega
              calc rd - qDegree + j
                  ≤ rd - qDegree + qDegree := Nat.add_le_add_left hj_le _
                _ = rd := hshift_eq
                _ < rem.size := hrd_lt_size
            have hzero_rem_new : ∀ i, qDegree + (rd - qDegree) ≤ i →
                (subtractScaledShift rem q (rd - qDegree)
                    (scaleLead (rem.getD rd (Zero.zero : S)))).getD i
                  (Zero.zero : S) = (Zero.zero : S) := by
              intro i hi
              have hi_ge_rd : rd ≤ i := by omega
              rcases Nat.lt_or_eq_of_le hi_ge_rd with hgt | heq
              · rw [subtractScaledShift_getD_above_last rem q (rd - qDegree) qDegree
                  (scaleLead (rem.getD rd (Zero.zero : S))) i hsize_q
                  (by rw [hshift_eq]; exact hgt)]
                exact arrayDegree?_some_above_eq_zero hdeg hgt
              · have hi_eq : i = (rd - qDegree) + qDegree := by omega
                rw [hi_eq]
                apply subtractScaledShift_getD_last_cancel rem q (rd - qDegree) qDegree
                  (scaleLead (rem.getD rd (Zero.zero : S))) hsize_q
                · rw [hshift_eq]; exact hrd_lt_size
                · rw [hshift_eq]
                  exact hcancel (rem.getD rd (Zero.zero : S))
            have hzero_quot_new : ∀ i, i < rd - qDegree →
                (quot.set! (rd - qDegree)
                    (scaleLead (rem.getD rd (Zero.zero : S)))).getD i
                  (Zero.zero : S) = (Zero.zero : S) := by
              intro i hi
              rw [array_getD_set!_ne quot i (rd - qDegree) _ (by omega)]
              exact hzero_quot i (Nat.lt_trans hi hshift_lt_B)
            have hsize_match_new :
                (subtractScaledShift rem q (rd - qDegree)
                    (scaleLead (rem.getD rd (Zero.zero : S)))).size ≤
                  qDegree + (quot.set! (rd - qDegree)
                    (scaleLead (rem.getD rd (Zero.zero : S)))).size := by
              have hrem_size : (subtractScaledShift rem q (rd - qDegree)
                  (scaleLead (rem.getD rd (Zero.zero : S)))).size = rem.size := by
                unfold subtractScaledShift
                exact subtractScaledShift_fold_size rem q (rd - qDegree) _
                  (List.range q.size)
              have hquot_size : (quot.set! (rd - qDegree)
                  (scaleLead (rem.getD rd (Zero.zero : S)))).size = quot.size := by
                simp [Array.set!_eq_setIfInBounds]
              rw [hrem_size, hquot_size]
              exact hsize_match
            have ih_result := ih
              (quot := quot.set! (rd - qDegree)
                (scaleLead (rem.getD rd (Zero.zero : S))))
              (rem := subtractScaledShift rem q (rd - qDegree)
                (scaleLead (rem.getD rd (Zero.zero : S))))
              (B := rd - qDegree)
              hzero_rem_new hzero_quot_new hsize_match_new
            rw [ih_result]
            rw [ofCoeffs_set!_eq_add_monomial quot (rd - qDegree)
              (scaleLead (rem.getD rd (Zero.zero : S))) hshift_lt_quot
              hquot_shift_zero]
            rw [ofCoeffs_subtractScaledShift_eq_sub_monomial_mul rem q (rd - qDegree)
              (scaleLead (rem.getD rd (Zero.zero : S))) hbound_rem]
            exact divMod_reconstruction_step (ofCoeffs quot)
              (monomial (rd - qDegree)
                (scaleLead (rem.getD rd (Zero.zero : S))))
              (ofCoeffs q) (ofCoeffs rem)

/-- Reconstruction identity for array-backed long division: under the cancellation
hypothesis for `scaleLead` against the divisor's leading coefficient, the
quotient/remainder pair returned by `divModArray p q scaleLead` satisfies
`q' * q + r' = p`. -/
theorem divModArray_reconstruction {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (scaleLead : S → S)
    (hcancel : ∀ a : S, a - scaleLead a * q.leadingCoeff = (Zero.zero : S)) :
    (divModArray p q scaleLead).1 * q + (divModArray p q scaleLead).2 = p := by
  unfold divModArray
  by_cases hqzero : q.isZero
  · simp [hqzero]
    rw [zero_mul, zero_add]
  · rw [if_neg hqzero]
    have hqpos : 0 < q.size := by
      have hcoeffs : q.coeffs.size ≠ 0 := by
        simpa [isZero, Array.isEmpty_iff_size_eq_zero] using hqzero
      simpa [size, Nat.pos_iff_ne_zero] using hcoeffs
    have hqsize : q.toArray.size = (q.size - 1) + 1 := by
      have hraw : q.coeffs.size = (q.coeffs.size - 1) + 1 := by
        have hcoeffpos : 0 < q.coeffs.size := by simpa [size] using hqpos
        omega
      simpa [toArray, size] using hraw
    have hlead : q.toArray.getD (q.size - 1) (Zero.zero : S) = q.leadingCoeff := by
      unfold leadingCoeff toArray
      simp [size]
    have hcancel_array :
        ∀ a, a - scaleLead a * q.toArray.getD (q.size - 1) (Zero.zero : S) =
          (Zero.zero : S) := by
      intro a
      rw [hlead]
      exact hcancel a
    have hzero_rem : ∀ i, (q.size - 1) + p.size ≤ i →
        p.toArray.getD i (Zero.zero : S) = (Zero.zero : S) := by
      intro i hi
      unfold toArray Array.getD
      have hle : p.coeffs.size ≤ i := by
        simpa [size] using (by omega : p.size ≤ i)
      rw [dif_neg (Nat.not_lt.mpr hle)]
    have hzero_quot : ∀ i, i < p.size →
        (Array.replicate (p.size - (q.size - 1)) (Zero.zero : S)).getD i
          (Zero.zero : S) = (Zero.zero : S) := by
      intro i _
      simp [Array.getD]
    have hsize_match : p.toArray.size ≤
        (q.size - 1) + (Array.replicate (p.size - (q.size - 1))
          (Zero.zero : S)).size := by
      have hpsize : p.toArray.size = p.size := by simp [toArray, size]
      have hqsize_replicate :
          (Array.replicate (p.size - (q.size - 1)) (Zero.zero : S)).size =
            p.size - (q.size - 1) := Array.size_replicate
      rw [hpsize, hqsize_replicate]
      omega
    have hreconstr := divModArrayAux_reconstruction
      q.toArray (q.size - 1) scaleLead p.size
      (Array.replicate (p.size - (q.size - 1)) (Zero.zero : S))
      p.toArray p.size hqsize hcancel_array hzero_rem hzero_quot hsize_match
    -- Convert array-level identity to the polynomial-level conclusion.
    have hofq : (ofCoeffs q.toArray : DensePoly S) = q := ofCoeffs_toArray q
    have hofp : (ofCoeffs p.toArray : DensePoly S) = p := ofCoeffs_toArray p
    have hofquot : (ofCoeffs (Array.replicate (p.size - (q.size - 1))
        (Zero.zero : S)) : DensePoly S) = 0 :=
      ofCoeffs_replicate_zero _
    rw [hofq, hofp, hofquot, zero_mul, zero_add] at hreconstr
    exact hreconstr

/-- Reconstruction identity for the executable long division wrapper. -/
theorem divMod_reconstruction {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    (p q : DensePoly S)
    (hcancel : ∀ a : S, a - (a / q.leadingCoeff) * q.leadingCoeff = (Zero.zero : S)) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  unfold divMod
  by_cases hdeg : p.degree?.getD 0 < q.degree?.getD 0
  · simp [hdeg]
    rw [zero_mul, zero_add]
  · simp [hdeg]
    exact divModArray_reconstruction p q (fun coeff => coeff / q.leadingCoeff) hcancel

private theorem foldl_add_general_eq_last_of_below_zero {S : Type _}
    [Lean.Grind.CommRing S]
    (g : Nat → S) (k : Nat)
    (h : ∀ i, i < k → g i = 0) :
    (List.range (k + 1)).foldl (fun acc i => acc + g i) 0 = g k := by
  have hzero : ∀ m, m ≤ k →
      (List.range m).foldl (fun acc i => acc + g i) 0 = 0 := by
    intro m hm
    induction m with
    | zero => simp
    | succ m' ih =>
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih (Nat.le_of_succ_le hm)]
        have hg : g m' = 0 := h m' (Nat.lt_of_succ_le hm)
        rw [hg]
        grind
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hzero k (Nat.le_refl k)]
  grind

private theorem foldl_add_general_eq_at_predecessor {S : Type _}
    [Lean.Grind.CommRing S]
    (g : Nat → S) (psize : Nat) (hpsize : 0 < psize)
    (h : ∀ i, i < psize - 1 → g i = 0) :
    (List.range psize).foldl (fun acc i => acc + g i) 0 = g (psize - 1) := by
  have hpsize_eq : psize - 1 + 1 = psize := by omega
  rw [← hpsize_eq]
  exact foldl_add_general_eq_last_of_below_zero g (psize - 1) h

private theorem foldl_add_general_eq_zero_of_forall_zero {S : Type _}
    [Lean.Grind.CommRing S]
    (g : Nat → S) (xs : List Nat) (acc : S)
    (h : ∀ i, i ∈ xs → g i = 0) :
    xs.foldl (fun acc i => acc + g i) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hi : g i = 0 := h i List.mem_cons_self
      rw [hi]
      have hadd : acc + (0 : S) = acc := by grind
      rw [hadd]
      exact ih acc (fun j hj => h j (List.mem_cons_of_mem i hj))

/-- The top coefficient of a product of nonzero dense polynomials over any
commutative ring is the product of their top coefficients. -/
private theorem coeff_mul_top_general {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S)
    (hp : 0 < p.size) (hq : 0 < q.size) :
    (p * q).coeff (p.size - 1 + (q.size - 1)) =
      p.coeff (p.size - 1) * q.coeff (q.size - 1) := by
  rw [coeff_mul, mulCoeffSum_eq_diagonal, foldl_add_general_eq_at_predecessor _ p.size hp]
  · unfold diagonalMulCoeffTerm
    have hno : ¬ p.size - 1 + (q.size - 1) < p.size - 1 := by omega
    rw [if_neg hno]
    have hsub : p.size - 1 + (q.size - 1) - (p.size - 1) = q.size - 1 := by omega
    rw [hsub]
  · intro i hi
    unfold diagonalMulCoeffTerm
    have hno : ¬ p.size - 1 + (q.size - 1) < i := by omega
    rw [if_neg hno]
    have hsub : q.size ≤ p.size - 1 + (q.size - 1) - i := by omega
    rw [coeff_eq_zero_of_size_le q hsub]
    show p.coeff i * (Zero.zero : S) = 0
    have hzero_eq : (Zero.zero : S) = 0 := rfl
    rw [hzero_eq]
    grind

/-- Above the degree-sum top, the product of dense polynomials over any
commutative ring vanishes. -/
private theorem coeff_mul_above_top_general {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) {i : Nat}
    (hp : 0 < p.size) (hq : 0 < q.size)
    (hi : p.size - 1 + (q.size - 1) < i) :
    (p * q).coeff i = 0 := by
  rw [coeff_mul, mulCoeffSum_eq_diagonal]
  apply foldl_add_general_eq_zero_of_forall_zero
  intro k hk
  have hk_lt : k < p.size := List.mem_range.mp hk
  unfold diagonalMulCoeffTerm
  by_cases hlt : i < k
  · simp [hlt]
  · have hsub_ge : q.size ≤ i - k := by omega
    rw [if_neg hlt, coeff_eq_zero_of_size_le q hsub_ge]
    show p.coeff k * (Zero.zero : S) = 0
    have hzero_eq : (Zero.zero : S) = 0 := rfl
    rw [hzero_eq]
    grind

/-- If a polynomial's coefficients are all zero from some index onward, its
stored size is bounded by that index. -/
private theorem size_le_of_coeff_zero_above {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {p : DensePoly S} {N : Nat}
    (h : ∀ i, N ≤ i → p.coeff i = 0) :
    p.size ≤ N := by
  by_cases hle : p.size ≤ N
  · exact hle
  · exfalso
    have hlt : N < p.size := Nat.lt_of_not_ge hle
    have hpos : 0 < p.size := by omega
    have hpos' : N ≤ p.size - 1 := by omega
    have hzero : p.coeff (p.size - 1) = 0 := h (p.size - 1) hpos'
    have hne : p.coeff (p.size - 1) ≠ (Zero.zero : S) :=
      coeff_last_ne_zero_of_pos_size p hpos
    exact hne hzero

/-- Leading coefficient of a product, in the cancellation-free form needed over
commutative rings. The explicit nonzero top-coefficient product hypothesis is
the no-cancellation fact that callers over domains can derive from nonzero
factors. -/
theorem leadingCoeff_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S)
    (hp : 0 < p.size) (hq : 0 < q.size)
    (hprod : p.leadingCoeff * q.leadingCoeff ≠ (Zero.zero : S)) :
    (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
  let top := p.size - 1 + (q.size - 1)
  have hp_top : p.coeff (p.size - 1) = p.leadingCoeff := by
    rw [leadingCoeff_eq_coeff_last p hp]
  have hq_top : q.coeff (q.size - 1) = q.leadingCoeff := by
    rw [leadingCoeff_eq_coeff_last q hq]
  have htop_coeff :
      (p * q).coeff top = p.leadingCoeff * q.leadingCoeff := by
    unfold top
    rw [coeff_mul_top_general p q hp hq, hp_top, hq_top]
  have htop_ne : (p * q).coeff top ≠ (Zero.zero : S) := by
    rw [htop_coeff]
    exact hprod
  have hsize_lower : top < (p * q).size := by
    rcases Nat.lt_or_ge top (p * q).size with h | hle
    · exact h
    · exact False.elim (htop_ne (coeff_eq_zero_of_size_le _ hle))
  have hsize_upper : (p * q).size ≤ top + 1 := by
    apply size_le_of_coeff_zero_above
    intro i hi
    exact coeff_mul_above_top_general p q hp hq (by omega)
  have hsize : (p * q).size = top + 1 := by
    omega
  rw [leadingCoeff_eq_coeff_last (p * q) (by omega)]
  have hidx : (p * q).size - 1 = top := by omega
  rw [hidx, htop_coeff]

/-- Array-level "polynomial-multiple" reconstruction-and-termination identity
for `divModArrayAux`. When the running remainder coincides at the polynomial
level with `m * q` for some `DensePoly` factor `m`, and the leading-coefficient
scaling function exactly recovers any `a` from `a * lc`, the loop terminates
with a clean quotient `quot + m` and zero remainder.

This is the structural lemma used to derive the non-monic exact-multiple
public divMod identity in `HexPolyZ`. -/
private theorem divModArrayAux_eq_of_polynomial_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (q : Array S) (qDegree : Nat)
    (hsize_q : q.size = qDegree + 1)
    (hq_lc_ne : q.getD qDegree (Zero.zero : S) ≠ (Zero.zero : S))
    (scaleLead : S → S)
    (hexact : ∀ a : S, scaleLead (a * q.getD qDegree (Zero.zero : S)) = a)
    (h_top_ne : ∀ a : S, a ≠ (Zero.zero : S) →
        a * q.getD qDegree (Zero.zero : S) ≠ (Zero.zero : S))
    (fuel : Nat) (quot rem : Array S) (B : Nat) (m : DensePoly S)
    (hsize_match : rem.size ≤ qDegree + quot.size)
    (hzero_quot : ∀ i, i < B → quot.getD i (Zero.zero : S) = (Zero.zero : S))
    (hzero_rem : ∀ i, qDegree + B ≤ i → rem.getD i (Zero.zero : S) = (Zero.zero : S))
    (hm_size_le : m.size ≤ B)
    (h_inv : (ofCoeffs rem : DensePoly S) = m * ofCoeffs q)
    (hfuel : B ≤ fuel) :
    ((ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot rem).1 : DensePoly S) =
        ofCoeffs quot + m) ∧
      ((ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot rem).2 : DensePoly S) =
        (0 : DensePoly S)) := by
  -- Structural facts about ofCoeffs q: its size is qDegree + 1 and its leading
  -- coefficient is q.getD qDegree 0.
  have hofq_coeff : ∀ i, (ofCoeffs q : DensePoly S).coeff i = q.getD i (Zero.zero : S) :=
    fun i => coeff_ofCoeffs q i
  have hofq_size : (ofCoeffs q : DensePoly S).size = qDegree + 1 := by
    apply Nat.le_antisymm
    · apply size_le_of_coeff_zero_above
      intro i hi
      rw [hofq_coeff]
      unfold Array.getD
      have hnot : ¬ i < q.size := by omega
      exact dif_neg hnot
    · by_cases hge : qDegree + 1 ≤ (ofCoeffs q : DensePoly S).size
      · exact hge
      · exfalso
        have hle : (ofCoeffs q : DensePoly S).size ≤ qDegree := by omega
        have hzero : (ofCoeffs q : DensePoly S).coeff qDegree = 0 :=
          coeff_eq_zero_of_size_le _ hle
        rw [hofq_coeff] at hzero
        exact hq_lc_ne hzero
  -- Algebraic top-coefficient computation: (m * ofCoeffs q).coeff (m.size - 1 + qDegree)
  -- = m.leadingCoeff * q.getD qDegree 0 whenever m is nonzero.
  have hcoeff_top : ∀ (m' : DensePoly S), 0 < m'.size →
      (m' * ofCoeffs q).coeff (m'.size - 1 + qDegree) =
        m'.coeff (m'.size - 1) * q.getD qDegree (Zero.zero : S) := by
    intro m' hm'_pos
    have hofq_pos : 0 < (ofCoeffs q : DensePoly S).size := by rw [hofq_size]; omega
    have htop := coeff_mul_top_general m' (ofCoeffs q) hm'_pos hofq_pos
    rw [hofq_size] at htop
    have hsub_qd : qDegree + 1 - 1 = qDegree := by omega
    rw [hsub_qd, hofq_coeff] at htop
    exact htop
  -- Above-top vanishing: (m * ofCoeffs q).coeff i = 0 for i > m.size - 1 + qDegree.
  have hcoeff_above : ∀ (m' : DensePoly S) (i : Nat), 0 < m'.size →
      m'.size - 1 + qDegree < i → (m' * ofCoeffs q).coeff i = 0 := by
    intro m' i hm'_pos hi
    have hofq_pos : 0 < (ofCoeffs q : DensePoly S).size := by rw [hofq_size]; omega
    apply coeff_mul_above_top_general m' (ofCoeffs q) hm'_pos hofq_pos
    rw [hofq_size]; omega
  induction fuel generalizing quot rem B m with
  | zero =>
      -- B ≤ 0 forces B = 0, so m.size = 0, so m = 0.
      have hB_zero : B = 0 := by omega
      have hm_size : m.size = 0 := by omega
      have hm_zero : m = 0 := by
        apply ext_coeff
        intro i
        rw [coeff_zero]
        exact coeff_eq_zero_of_size_le m (by omega)
      have hrem_zero : (ofCoeffs rem : DensePoly S) = 0 := by
        rw [h_inv, hm_zero, zero_mul]
      refine ⟨?_, hrem_zero⟩
      simp [divModArrayAux]
      rw [hm_zero, add_zero_poly]
  | succ fuel ih =>
      unfold divModArrayAux
      cases hdeg : arrayDegree? rem with
      | none =>
          -- All entries of rem are zero, so m * ofCoeffs q = 0; this forces m = 0.
          have hrem_arr_zero : ∀ i, rem.getD i (Zero.zero : S) = (Zero.zero : S) :=
            fun i => arrayDegree?_none_getD_eq_zero hdeg
          have hrem_zero : (ofCoeffs rem : DensePoly S) = 0 := by
            apply ext_coeff
            intro i
            rw [coeff_ofCoeffs, coeff_zero]
            exact hrem_arr_zero i
          have hm_zero : m = 0 := by
            by_cases hmz : m = 0
            · exact hmz
            · exfalso
              have hm_pos : 0 < m.size := by
                by_cases h : 0 < m.size
                · exact h
                · exfalso
                  apply hmz
                  apply ext_coeff
                  intro i
                  rw [coeff_zero]
                  exact coeff_eq_zero_of_size_le m (by omega)
              have hlead_ne : m.coeff (m.size - 1) ≠ 0 :=
                coeff_last_ne_zero_of_pos_size m hm_pos
              have hprod_ne :
                  m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S) ≠
                    (Zero.zero : S) :=
                h_top_ne _ hlead_ne
              have hkey : (m * ofCoeffs q).coeff (m.size - 1 + qDegree) ≠ 0 := by
                rw [hcoeff_top m hm_pos]; exact hprod_ne
              have hzero_at : (m * ofCoeffs q).coeff (m.size - 1 + qDegree) = 0 := by
                rw [← h_inv, hrem_zero, coeff_zero]
              exact hkey hzero_at
          refine ⟨?_, hrem_zero⟩
          rw [hm_zero, add_zero_poly]
      | some rd =>
          have hrd_lt : rd < rem.size := arrayDegree?_some_lt hdeg
          have hrd_nonzero : rem.getD rd (Zero.zero : S) ≠ (Zero.zero : S) :=
            arrayDegree?_some_coeff_ne_zero hdeg
          have hrd_lt_B : rd < qDegree + B := by
            rcases Nat.lt_or_ge rd (qDegree + B) with hlt | hge
            · exact hlt
            · exact absurd (hzero_rem rd hge) hrd_nonzero
          by_cases hrd_lt_q : rd < qDegree
          · -- Loop exits: must show m = 0 (otherwise contradicting arrayDegree above bound).
            have hm_zero : m = 0 := by
              by_cases hmz : m = 0
              · exact hmz
              · exfalso
                have hm_pos : 0 < m.size := by
                  by_cases h : 0 < m.size
                  · exact h
                  · exfalso
                    apply hmz
                    apply ext_coeff
                    intro i
                    rw [coeff_zero]
                    exact coeff_eq_zero_of_size_le m (by omega)
                have hlead_ne : m.coeff (m.size - 1) ≠ 0 :=
                  coeff_last_ne_zero_of_pos_size m hm_pos
                have hprod_ne :
                    m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S) ≠
                      (Zero.zero : S) :=
                  h_top_ne _ hlead_ne
                have hkey : (m * ofCoeffs q).coeff (m.size - 1 + qDegree) ≠ 0 := by
                  rw [hcoeff_top m hm_pos]; exact hprod_ne
                have hrem_coeff_ne :
                    rem.getD (m.size - 1 + qDegree) (Zero.zero : S) ≠ 0 := by
                  rw [← coeff_ofCoeffs, h_inv]; exact hkey
                -- m.size - 1 + qDegree ≥ qDegree > rd, so this is above the topmost
                -- nonzero entry, contradicting arrayDegree's contract.
                have habove : rd < m.size - 1 + qDegree := by omega
                exact hrem_coeff_ne (arrayDegree?_some_above_eq_zero hdeg habove)
            have hrem_zero : (ofCoeffs rem : DensePoly S) = 0 := by
              rw [h_inv, hm_zero, zero_mul]
            refine ⟨?_, ?_⟩
            · simp [hrd_lt_q]
              rw [hm_zero, add_zero_poly]
            · simp [hrd_lt_q]
              exact hrem_zero
          · -- Recursive step: m must be nonzero, rd = qDegree + m.size - 1, and we
            -- peel off the leading monomial of m.
            have hm_ne : m ≠ 0 := by
              intro hmz
              apply hrd_nonzero
              have hzero : (ofCoeffs rem : DensePoly S) = 0 := by
                rw [h_inv, hmz, zero_mul]
              have h := congrArg (fun p : DensePoly S => p.coeff rd) hzero
              change (ofCoeffs rem).coeff rd = (0 : DensePoly S).coeff rd at h
              rw [coeff_ofCoeffs, coeff_zero] at h
              exact h
            have hm_pos : 0 < m.size := by
              by_cases h : 0 < m.size
              · exact h
              · exfalso
                apply hm_ne
                apply ext_coeff
                intro i
                rw [coeff_zero]
                exact coeff_eq_zero_of_size_le m (by omega)
            -- Establish rd = qDegree + m.size - 1.
            have hrd_ge : qDegree + m.size - 1 ≤ rd := by
              have hlead_ne : m.coeff (m.size - 1) ≠ 0 :=
                coeff_last_ne_zero_of_pos_size m hm_pos
              have hprod_ne :
                  m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S) ≠
                    (Zero.zero : S) :=
                h_top_ne _ hlead_ne
              have hkey : (m * ofCoeffs q).coeff (m.size - 1 + qDegree) ≠ 0 := by
                rw [hcoeff_top m hm_pos]; exact hprod_ne
              have hrem_ne_at :
                  rem.getD (m.size - 1 + qDegree) (Zero.zero : S) ≠ 0 := by
                rw [← coeff_ofCoeffs, h_inv]; exact hkey
              by_cases hle : m.size - 1 + qDegree ≤ rd
              · omega
              · exfalso
                have hgt : rd < m.size - 1 + qDegree := by omega
                exact hrem_ne_at (arrayDegree?_some_above_eq_zero hdeg hgt)
            have hrd_le : rd ≤ qDegree + m.size - 1 := by
              by_cases hle : rd ≤ qDegree + m.size - 1
              · exact hle
              · exfalso
                have hgt : m.size - 1 + qDegree < rd := by omega
                have habove := hcoeff_above m rd hm_pos hgt
                have hrem_eq : rem.getD rd (Zero.zero : S) = 0 := by
                  rw [← coeff_ofCoeffs, h_inv]; exact habove
                exact hrd_nonzero hrem_eq
            have hrd_eq : rd = qDegree + m.size - 1 := by omega
            have hshift_eq : rd - qDegree = m.size - 1 := by omega
            -- Compute coeff = scaleLead(rem.getD rd 0) = m.leadingCoeff.
            have hrem_at_rd :
                rem.getD rd (Zero.zero : S) =
                  m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S) := by
              rw [← coeff_ofCoeffs, h_inv]
              have hrd_alt : rd = m.size - 1 + qDegree := by omega
              rw [hrd_alt]
              exact hcoeff_top m hm_pos
            have hscale :
                scaleLead (rem.getD rd (Zero.zero : S)) = m.coeff (m.size - 1) := by
              rw [hrem_at_rd]
              exact hexact (m.coeff (m.size - 1))
            -- Abbreviations: shift := rd - qDegree, coeff := scaleLead (rem.getD rd 0).
            -- We use let-bindings so the names appear in the IH instantiation.
            let shift : Nat := rd - qDegree
            let coeff : S := scaleLead (rem.getD rd (Zero.zero : S))
            let m_new : DensePoly S := m - monomial shift coeff
            let quot' : Array S := quot.set! shift coeff
            let rem' : Array S := subtractScaledShift rem q shift coeff
            have hcoeff_eq : coeff = m.coeff (m.size - 1) := hscale
            have hshift_eq_size : shift = m.size - 1 := by
              show rd - qDegree = m.size - 1; omega
            have hshift_lt_quot : shift < quot.size := by
              show rd - qDegree < quot.size
              have h1 : rd < qDegree + quot.size :=
                Nat.lt_of_lt_of_le hrd_lt hsize_match
              omega
            have hquot_shift_zero :
                quot.getD shift (Zero.zero : S) = (Zero.zero : S) := by
              apply hzero_quot
              show rd - qDegree < B; omega
            have hbound_rem : ∀ j, j < q.size → shift + j < rem.size := by
              intro j hj
              have hj_le : j ≤ qDegree := by omega
              show rd - qDegree + j < rem.size
              calc rd - qDegree + j
                  ≤ rd - qDegree + qDegree := Nat.add_le_add_left hj_le _
                _ = rd := by omega
                _ < rem.size := hrd_lt
            have hm_new_size : m_new.size ≤ shift := by
              apply size_le_of_coeff_zero_above
              intro i hi
              have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
              show (m - monomial shift coeff).coeff i = 0
              rw [coeff_sub m (monomial shift coeff) i hzero_sub, coeff_monomial]
              by_cases hi_eq : i = shift
              · subst i
                rw [if_pos rfl, hcoeff_eq, hshift_eq_size]
                grind
              · rw [if_neg hi_eq]
                have hi_gt : shift < i := by omega
                have hi_ge_size : m.size ≤ i := by
                  have hsize_lt : m.size - 1 < i := by
                    rw [← hshift_eq_size]; exact hi_gt
                  omega
                rw [coeff_eq_zero_of_size_le m hi_ge_size]
                grind
            have hrem'_invariant :
                (ofCoeffs rem' : DensePoly S) = m_new * ofCoeffs q := by
              show (ofCoeffs (subtractScaledShift rem q shift coeff) : DensePoly S) =
                (m - monomial shift coeff) * ofCoeffs q
              rw [ofCoeffs_subtractScaledShift_eq_sub_monomial_mul rem q shift coeff hbound_rem,
                h_inv]
              apply ext_coeff
              intro n
              have hzero_add : (0 : S) + (0 : S) = 0 := by grind
              have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
              rw [coeff_sub (m * ofCoeffs q) (monomial shift coeff * ofCoeffs q) n hzero_sub]
              -- Use add_mul_sub_cancel_right with r = 0 to derive the distributive law.
              have hcancel :
                  (m - monomial shift coeff) + monomial shift coeff = m := by
                apply ext_coeff
                intro k
                rw [coeff_add (m - monomial shift coeff) (monomial shift coeff) k hzero_add,
                  coeff_sub m (monomial shift coeff) k hzero_sub]
                grind
              have hrhs := congrArg (fun p : DensePoly S => p.coeff n)
                (add_mul_sub_cancel_right (m - monomial shift coeff)
                  (monomial shift coeff) (ofCoeffs q) 0)
              rw [hcancel] at hrhs
              change ((m * ofCoeffs q + (0 - monomial shift coeff * ofCoeffs q)).coeff n =
                ((m - monomial shift coeff) * ofCoeffs q + 0).coeff n) at hrhs
              rw [coeff_add (m * ofCoeffs q) (0 - monomial shift coeff * ofCoeffs q) n hzero_add] at hrhs
              rw [coeff_sub 0 (monomial shift coeff * ofCoeffs q) n hzero_sub,
                coeff_zero] at hrhs
              rw [coeff_add ((m - monomial shift coeff) * ofCoeffs q) 0 n hzero_add,
                coeff_zero] at hrhs
              grind
            have hquot'_size : quot'.size = quot.size := by
              show (quot.set! shift coeff).size = quot.size
              simp [Array.set!_eq_setIfInBounds]
            have hrem'_size : rem'.size = rem.size := by
              show (subtractScaledShift rem q shift coeff).size = rem.size
              unfold subtractScaledShift
              exact subtractScaledShift_fold_size rem q shift coeff (List.range q.size)
            have hsize_match' : rem'.size ≤ qDegree + quot'.size := by
              rw [hrem'_size, hquot'_size]; exact hsize_match
            have hzero_quot' : ∀ i, i < shift →
                quot'.getD i (Zero.zero : S) = (Zero.zero : S) := by
              intro i hi
              show (quot.set! shift coeff).getD i (Zero.zero : S) = (Zero.zero : S)
              rw [array_getD_set!_ne quot i shift coeff (by omega)]
              apply hzero_quot
              show i < B
              have h1 : shift < B := by show rd - qDegree < B; omega
              omega
            have hzero_rem' : ∀ i, qDegree + shift ≤ i →
                rem'.getD i (Zero.zero : S) = (Zero.zero : S) := by
              intro i hi
              have hi_ge_rd : rd ≤ i := by
                have hsum : qDegree + shift = rd := by show qDegree + (rd - qDegree) = rd; omega
                omega
              show (subtractScaledShift rem q shift coeff).getD i (Zero.zero : S) =
                (Zero.zero : S)
              rcases Nat.lt_or_eq_of_le hi_ge_rd with hgt | heq
              · rw [subtractScaledShift_getD_above_last rem q shift qDegree coeff i
                  hsize_q (by show shift + qDegree < i; omega)]
                exact arrayDegree?_some_above_eq_zero hdeg hgt
              · have hi_eq : i = shift + qDegree := by
                  show i = (rd - qDegree) + qDegree; omega
                rw [hi_eq]
                apply subtractScaledShift_getD_last_cancel rem q shift qDegree coeff
                  hsize_q
                · show shift + qDegree < rem.size
                  show (rd - qDegree) + qDegree < rem.size
                  have : (rd - qDegree) + qDegree = rd := by omega
                  rw [this]; exact hrd_lt
                · -- rem.getD (shift + qDegree) - coeff * q.getD qDegree 0 = 0
                  have hidx_eq : shift + qDegree = rd := by
                    show (rd - qDegree) + qDegree = rd; omega
                  rw [hidx_eq, hrem_at_rd, hcoeff_eq]
                  show (m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S)) -
                    (m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S)) =
                      (Zero.zero : S)
                  have hzero_eq : (Zero.zero : S) = (0 : S) := rfl
                  rw [hzero_eq]
                  exact Lean.Grind.AddCommGroup.sub_self _
            have hfuel' : shift ≤ fuel := by show rd - qDegree ≤ fuel; omega
            -- Apply IH.
            have hih := ih quot' rem' shift m_new
              hsize_match' hzero_quot' hzero_rem' hm_new_size hrem'_invariant hfuel'
            -- After unfolding divModArrayAux and the some/¬lt branch, the goal is about
            -- divModArrayAux q qDegree scaleLead fuel quot' rem'.
            refine ⟨?_, ?_⟩
            · simp [hrd_lt_q]
              simp only [← Array.set!_eq_setIfInBounds, ← Array.getD_eq_getD_getElem?]
              -- Goal: ofCoeffs (divModArrayAux _ _ _ fuel quot' rem').1 = ofCoeffs quot + m
              -- From hih.1: ofCoeffs (... rem').1 = ofCoeffs quot' + m_new
              show (ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot' rem').1
                  : DensePoly S) = ofCoeffs quot + m
              rw [hih.1]
              -- Now show ofCoeffs quot' + m_new = ofCoeffs quot + m.
              have hquot'_expand : (ofCoeffs quot' : DensePoly S) =
                  ofCoeffs quot + monomial shift coeff := by
                show (ofCoeffs (quot.set! shift coeff) : DensePoly S) =
                  ofCoeffs quot + monomial shift coeff
                exact ofCoeffs_set!_eq_add_monomial quot shift coeff hshift_lt_quot
                  hquot_shift_zero
              rw [hquot'_expand]
              show (ofCoeffs quot + monomial shift coeff) + (m - monomial shift coeff) =
                ofCoeffs quot + m
              apply ext_coeff
              intro n
              have hzero_add : (0 : S) + (0 : S) = 0 := by grind
              have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
              rw [coeff_add (ofCoeffs quot + monomial shift coeff)
                (m - monomial shift coeff) n hzero_add]
              rw [coeff_add (ofCoeffs quot) (monomial shift coeff) n hzero_add,
                coeff_sub m (monomial shift coeff) n hzero_sub,
                coeff_add (ofCoeffs quot) m n hzero_add]
              grind
            · simp [hrd_lt_q]
              simp only [← Array.set!_eq_setIfInBounds, ← Array.getD_eq_getD_getElem?]
              show (ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot' rem').2
                  : DensePoly S) = (0 : DensePoly S)
              exact hih.2

/-- Size of a product is bounded above by the sum of sizes minus one. Generic to
any commutative ring; the bound is loose for non-domains where the leading-
coefficient product may cancel. -/
private theorem mul_size_le_top_succ_general {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (hp : 0 < p.size) (hq : 0 < q.size) :
    (p * q).size ≤ p.size + q.size - 1 := by
  apply size_le_of_coeff_zero_above
  intro i hi
  exact coeff_mul_above_top_general p q hp hq (by omega)

/-- Public `divMod` identity for non-monic exact-multiple inputs: if `qq * q = p`,
the scaling function `(· / q.leadingCoeff)` exactly recovers any `a` from
`a * q.leadingCoeff`, and the leading-coefficient product never cancels, then
`divMod p q = (qq, 0)`. The exactness and no-zero-divisor hypotheses replace the
global cancellation invariant `∀ a, a - (a / q.leadingCoeff) * q.leadingCoeff = 0`
required by `divMod_reconstruction` (which only holds in the monic case over
`Int`). -/
theorem divMod_eq_of_polynomial_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    (p q qq : DensePoly S)
    (hdegree : 0 < q.degree?.getD 0)
    (hexact : ∀ a : S, (a * q.leadingCoeff) / q.leadingCoeff = a)
    (h_top_ne : ∀ a : S, a ≠ (Zero.zero : S) →
        a * q.leadingCoeff ≠ (Zero.zero : S))
    (hmul : qq * q = p) :
    divMod p q = (qq, 0) := by
  -- Structural facts about q.
  have hq_pos : 0 < q.size := by
    unfold degree? at hdegree
    by_cases h : q.size = 0
    · simp [h] at hdegree
    · omega
  have hq_size_ge_two : 2 ≤ q.size := by
    unfold degree? at hdegree
    by_cases h : q.size = 0
    · simp [h] at hdegree
    · simp [h] at hdegree; omega
  have hq_lead_ne : q.leadingCoeff ≠ (Zero.zero : S) :=
    leadingCoeff_ne_zero_of_pos_size q hq_pos
  have hq_isZero : q.isZero = false := by
    have hq_size_ne_zero : q.coeffs.size ≠ 0 := by change q.size ≠ 0; omega
    simpa [isZero, Array.isEmpty_iff_size_eq_zero] using hq_size_ne_zero
  -- Helper: if qq ≠ 0, then p.size ≥ qq.size + q.size - 1.
  have hp_size_lower : qq ≠ 0 → qq.size + q.size - 1 ≤ p.size := by
    intro hqq_ne
    have hqq_pos : 0 < qq.size := by
      by_cases h : 0 < qq.size
      · exact h
      · exfalso; apply hqq_ne
        apply ext_coeff
        intro i; rw [coeff_zero]; exact coeff_eq_zero_of_size_le qq (by omega)
    have hqq_lead_ne : qq.coeff (qq.size - 1) ≠ 0 :=
      coeff_last_ne_zero_of_pos_size qq hqq_pos
    have hprod_ne :
        qq.coeff (qq.size - 1) * q.leadingCoeff ≠ (Zero.zero : S) :=
      h_top_ne _ hqq_lead_ne
    have hp_top :
        p.coeff (qq.size - 1 + (q.size - 1)) =
          qq.coeff (qq.size - 1) * q.coeff (q.size - 1) := by
      rw [← hmul]
      exact coeff_mul_top_general qq q hqq_pos hq_pos
    have hp_top_ne :
        p.coeff (qq.size - 1 + (q.size - 1)) ≠ 0 := by
      rw [hp_top, ← leadingCoeff_eq_coeff_last q hq_pos]
      exact hprod_ne
    by_cases hle : qq.size + q.size - 1 ≤ p.size
    · exact hle
    · exfalso
      have hidx_ge : p.size ≤ qq.size - 1 + (q.size - 1) := by omega
      exact hp_top_ne (coeff_eq_zero_of_size_le p hidx_ge)
  -- Helper: qq.size ≤ p.size always.
  have hqq_size_le_p : qq.size ≤ p.size := by
    by_cases hqq_zero : qq = 0
    · have hp_zero : p = 0 := by rw [← hmul, hqq_zero, zero_mul]
      have hqq_size : qq.size = 0 := by rw [hqq_zero]; rfl
      have hp_size : p.size = 0 := by rw [hp_zero]; rfl
      omega
    · have h := hp_size_lower hqq_zero; omega
  unfold divMod
  by_cases hdeg_short : p.degree?.getD 0 < q.degree?.getD 0
  · -- Short circuit: must show qq = 0 and p = 0.
    rw [if_pos hdeg_short]
    have hp_size_lt_q : p.size < q.size := by
      unfold degree? at hdeg_short
      have hq_ne : q.size ≠ 0 := by omega
      by_cases hp_zero_size : p.size = 0
      · omega
      · simp [hp_zero_size, hq_ne] at hdeg_short
        omega
    have hqq_zero : qq = 0 := by
      by_cases h : qq = 0
      · exact h
      · exfalso
        have h_lower := hp_size_lower h
        have hqq_pos : 0 < qq.size := by
          by_cases hp : 0 < qq.size
          · exact hp
          · exfalso; apply h
            apply ext_coeff
            intro i; rw [coeff_zero]; exact coeff_eq_zero_of_size_le qq (by omega)
        omega
    have hp_zero : p = 0 := by rw [← hmul, hqq_zero, zero_mul]
    rw [hp_zero, hqq_zero]
  · rw [if_neg hdeg_short]
    -- Apply the array-level lemma via divModArray.
    unfold divModArray
    rw [if_neg (by simp [hq_isZero])]
    -- Bookkeeping to feed divModArrayAux_eq_of_polynomial_mul.
    let qDeg := q.size - 1
    let scaleLead : S → S := fun coeff => coeff / q.leadingCoeff
    let quot0 : Array S := Array.replicate (p.size - qDeg) (Zero.zero : S)
    -- q.toArray characterization.
    have hq_toArray_size : q.toArray.size = q.size := by unfold toArray size; rfl
    have hq_lead_at_arr : q.toArray.getD qDeg (Zero.zero : S) = q.leadingCoeff := by
      show q.toArray.getD (q.size - 1) (Zero.zero : S) = q.leadingCoeff
      rw [leadingCoeff_eq_coeff_last q hq_pos]
      unfold coeff toArray; rfl
    have hsize_q : q.toArray.size = qDeg + 1 := by
      show q.toArray.size = q.size - 1 + 1
      rw [hq_toArray_size]; omega
    have hqArr_lc_ne : q.toArray.getD qDeg (Zero.zero : S) ≠ (Zero.zero : S) := by
      rw [hq_lead_at_arr]; exact hq_lead_ne
    have hexact' :
        ∀ a : S, scaleLead (a * q.toArray.getD qDeg (Zero.zero : S)) = a := by
      intro a
      show (a * q.toArray.getD qDeg (Zero.zero : S)) / q.leadingCoeff = a
      rw [hq_lead_at_arr]; exact hexact a
    have h_top_ne' :
        ∀ a : S, a ≠ (Zero.zero : S) →
          a * q.toArray.getD qDeg (Zero.zero : S) ≠ (Zero.zero : S) := by
      intro a ha
      rw [hq_lead_at_arr]; exact h_top_ne a ha
    -- p.degree ≥ q.degree in this branch, so p.size ≥ qDeg + 1.
    have hp_size_ge : qDeg + 1 ≤ p.size := by
      unfold degree? at hdeg_short
      have hq_ne : q.size ≠ 0 := by omega
      by_cases hp_zero_size : p.size = 0
      · simp [hp_zero_size, hq_ne] at hdeg_short
        omega
      · simp [hp_zero_size, hq_ne] at hdeg_short
        show q.size - 1 + 1 ≤ p.size
        omega
    have hp_toArray_size : p.toArray.size = p.size := by unfold toArray size; rfl
    -- Preconditions for the array lemma, with B = qq.size.
    have hsize_match : p.toArray.size ≤ qDeg + quot0.size := by
      show p.toArray.size ≤ qDeg + (Array.replicate (p.size - qDeg) (Zero.zero : S)).size
      rw [hp_toArray_size, Array.size_replicate]
      omega
    have hzero_quot : ∀ i, i < qq.size →
        quot0.getD i (Zero.zero : S) = (Zero.zero : S) := by
      intro i _
      show (Array.replicate (p.size - qDeg) (Zero.zero : S)).getD i (Zero.zero : S) =
        (Zero.zero : S)
      simp [Array.getD]
    have hzero_rem : ∀ i, qDeg + qq.size ≤ i →
        p.toArray.getD i (Zero.zero : S) = (Zero.zero : S) := by
      intro i hi
      have hp_le_i : p.size ≤ i := by
        by_cases hqq_zero : qq = 0
        · have hp_zero : p = 0 := by rw [← hmul, hqq_zero, zero_mul]
          have hp_size : p.size = 0 := by rw [hp_zero]; rfl
          omega
        · have hqq_pos : 0 < qq.size := by
            by_cases hp : 0 < qq.size
            · exact hp
            · exfalso; apply hqq_zero
              apply ext_coeff
              intro i; rw [coeff_zero]; exact coeff_eq_zero_of_size_le qq (by omega)
          have hp_eq : p = qq * q := hmul.symm
          have hp_size_le : p.size ≤ qq.size + q.size - 1 := by
            rw [hp_eq]
            exact mul_size_le_top_succ_general qq q hqq_pos hq_pos
          show p.size ≤ i
          show p.size ≤ i
          omega
      unfold toArray Array.getD
      have hcoeffs_le : p.coeffs.size ≤ i := by change p.size ≤ i; exact hp_le_i
      rw [dif_neg (Nat.not_lt.mpr hcoeffs_le)]
    have hm_size_le : qq.size ≤ qq.size := Nat.le_refl _
    have h_inv : (ofCoeffs p.toArray : DensePoly S) = qq * ofCoeffs q.toArray := by
      rw [ofCoeffs_toArray p, ofCoeffs_toArray q]
      exact hmul.symm
    have hfuel : qq.size ≤ p.size := hqq_size_le_p
    have hresult := divModArrayAux_eq_of_polynomial_mul q.toArray qDeg hsize_q
      hqArr_lc_ne scaleLead hexact' h_top_ne' p.size quot0 p.toArray qq.size qq
      hsize_match hzero_quot hzero_rem hm_size_le h_inv hfuel
    -- Translate the array-level conclusion into pair equality.
    have hquot_zero : (ofCoeffs quot0 : DensePoly S) = 0 := by
      show (ofCoeffs (Array.replicate (p.size - qDeg) (Zero.zero : S)) : DensePoly S) = 0
      exact ofCoeffs_replicate_zero (p.size - qDeg)
    have hresult1 := hresult.1
    rw [hquot_zero, zero_add] at hresult1
    have hresult2 := hresult.2
    -- Goal: (ofCoeffs result.1, ofCoeffs result.2) = (qq, 0).
    show ((ofCoeffs (divModArrayAux q.toArray (q.size - 1) scaleLead p.size quot0
        p.toArray).1 : DensePoly S),
      (ofCoeffs (divModArrayAux q.toArray (q.size - 1) scaleLead p.size quot0
        p.toArray).2 : DensePoly S)) = (qq, 0)
    rw [hresult1, hresult2]

end DensePoly
end Hex
