/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly.Conditional
public import Init.Grind.Ring.Basic
public import Init.Data.List.Lemmas
public import HexPoly.Operations
public import HexPoly.Euclid.MulRing
public import HexPoly.Euclid.Reconstruction
import all HexPoly.Operations
import all HexPoly.Euclid.MulRing
import all HexPoly.Euclid.Reconstruction

public section
set_option backward.proofsInPublic true

/-!
Horner evaluation is multiplicative: `eval (p * q) x = eval p x * eval q x`.

Together with {name}`Hex.DensePoly.eval_add_semiring` this makes `eval · x` a
ring homomorphism out of `DensePoly S`, which is what licenses evaluating a
product at a power of two — the substitution behind
`Hex.ZPoly.mulKronecker`.

The proof peels the top coefficient off the left factor: with `p.size ≤ n + 1`
and `c := p.coeff n`, the difference `p - monomial n c` has size at most `n`,
so right distributivity (`mul_add_left_poly`) reduces the product to a smaller
instance plus a monomial multiple, and `monomial n c * q` evaluates through
`shift`/`scale`.
-/

namespace Hex

universe u

namespace DensePoly

variable {S : Type u}

/-- Scaling every entry of a coefficient list scales its Horner value. -/
private theorem evalCoeffList_map_mul [Lean.Grind.CommSemiring S] [DecidableEq S]
    (c : S) (cs : List S) (x : S) :
    evalCoeffList (cs.map (fun a => c * a)) x = c * evalCoeffList cs x := by
  induction cs with
  | nil =>
      show (0 : S) = c * (0 : S)
      exact (Lean.Grind.Semiring.mul_zero c).symm
  | cons a as ih =>
      show evalCoeffList (as.map (fun a => c * a)) x * x + c * a =
        c * (evalCoeffList as x * x + a)
      rw [ih]
      grind

/-- Horner evaluation commutes with coefficientwise scaling. -/
theorem eval_scale_semiring [Lean.Grind.CommSemiring S] [DecidableEq S]
    (c : S) (p : DensePoly S) (x : S) :
    eval (scale c p) x = c * eval p x := by
  unfold scale
  rw [eval_ofList_eq_evalCoeffList _ x
      (by
        change (0 : S) * x + (0 : S) = (0 : S)
        rw [Lean.Grind.Semiring.zero_mul]
        exact Lean.Grind.Semiring.add_zero 0),
    evalCoeffList_map_mul, eval_eq_evalCoeffList]
  rfl

/-- Prepending `n` zero coefficients multiplies the Horner value by `x ^ n`. -/
private theorem evalCoeffList_replicate_zero_append [Lean.Grind.CommSemiring S] [DecidableEq S]
    (n : Nat) (cs : List S) (x : S) :
    evalCoeffList (List.replicate n (0 : S) ++ cs) x = evalCoeffList cs x * x ^ n := by
  induction n with
  | zero =>
      show evalCoeffList cs x = evalCoeffList cs x * x ^ 0
      rw [Lean.Grind.Semiring.pow_zero]
      exact (Lean.Grind.Semiring.mul_one _).symm
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      show evalCoeffList (List.replicate n (0 : S) ++ cs) x * x + (0 : S) =
        evalCoeffList cs x * x ^ (n + 1)
      rw [ih, Lean.Grind.Semiring.add_zero, Lean.Grind.Semiring.mul_assoc,
        ← Lean.Grind.Semiring.pow_succ]

/-- Horner evaluation turns a degree shift into multiplication by `x ^ n`. -/
theorem eval_shift_semiring [Lean.Grind.CommSemiring S] [DecidableEq S]
    (n : Nat) (p : DensePoly S) (x : S) :
    eval (shift n p) x = eval p x * x ^ n := by
  have hzero_horner : (0 : S) * x + (0 : S) = (0 : S) := by
    rw [Lean.Grind.Semiring.zero_mul]
    exact Lean.Grind.Semiring.add_zero 0
  unfold shift
  by_cases hz : p.isZero
  · have hp : p = 0 := (size_eq_zero_iff p).mp ((isZero_eq_true_iff p).mp hz)
    rw [HexPoly.ite_eq_left hz, hp, eval_zero]
    exact (Lean.Grind.Semiring.zero_mul _).symm
  · rw [HexPoly.ite_eq_right hz, eval_ofList_eq_evalCoeffList _ x hzero_horner]
    show evalCoeffList (List.replicate n (0 : S) ++ p.toList) x = eval p x * x ^ n
    rw [evalCoeffList_replicate_zero_append, eval_eq_evalCoeffList]
    rfl

/-- Evaluating a monomial multiple. -/
private theorem eval_monomial_mul [Lean.Grind.CommRing S] [DecidableEq S]
    (n : Nat) (c : S) (q : DensePoly S) (x : S) :
    eval (monomial n c * q) x = (c * x ^ n) * eval q x := by
  have hmono : monomial n c = scale c (monomial n 1) := by
    apply ext_coeff
    intro k
    rw [coeff_monomial, coeff_scale_semiring, coeff_monomial]
    by_cases hkn : k = n
    · simp only [hkn, ↓reduceIte]
      exact (Lean.Grind.Semiring.mul_one c).symm
    · simp only [hkn, ↓reduceIte]
      exact (Lean.Grind.Semiring.mul_zero c).symm
  rw [hmono, ← scale_mul, monomial_one_mul_poly_eq_shift, eval_scale_semiring,
    eval_shift_semiring]
  grind

/-- A polynomial all of whose coefficients from `n` on vanish has size at most `n`. -/
private theorem size_le_of_coeff_eq_zero [Zero S] [DecidableEq S] {p : DensePoly S} {n : Nat}
    (h : ∀ i, n ≤ i → p.coeff i = (Zero.zero : S)) : p.size ≤ n := by
  by_cases hlt : n < p.size
  · exact absurd (h (p.size - 1) (by omega)) (coeff_last_ne_zero_of_pos_size p (by omega))
  · omega

private theorem eval_mul_of_size_le [Lean.Grind.CommRing S] [DecidableEq S] :
    ∀ (n : Nat) (p q : DensePoly S) (x : S), p.size ≤ n →
      eval (p * q) x = eval p x * eval q x := by
  intro n
  induction n with
  | zero =>
      intro p q x hp
      have hp0 : p = 0 := (size_eq_zero_iff p).mp (Nat.le_zero.mp hp)
      subst hp0
      have hzq : (0 : DensePoly S) * q = 0 := by
        show mul 0 q = 0
        unfold mul
        rw [HexPoly.ite_eq_left (by simp [(isZero_eq_true_iff (0 : DensePoly S)).mpr rfl])]
      rw [hzq, eval_zero]
      exact (Lean.Grind.Semiring.zero_mul _).symm
  | succ n ih =>
      intro p q x hp
      by_cases hsmall : p.size ≤ n
      · exact ih p q x hsmall
      · have hsplit : p = (p - monomial n (p.coeff n)) + monomial n (p.coeff n) := by
          apply ext_coeff
          intro k
          rw [coeff_add_semiring, coeff_sub_ring]
          grind
        have hsize : (p - monomial n (p.coeff n)).size ≤ n := by
          apply size_le_of_coeff_eq_zero
          intro i hi
          rw [show (Zero.zero : S) = (0 : S) from rfl, coeff_sub_ring, coeff_monomial]
          by_cases hin : i = n
          · subst hin
            simp only [↓reduceIte]
            grind
          · have hzi : p.coeff i = 0 := coeff_eq_zero_of_size_le p (by omega)
            simp only [hin, ↓reduceIte, hzi]
            show (0 : S) - (0 : S) = (0 : S)
            grind
        calc
          eval (p * q) x
              = eval (((p - monomial n (p.coeff n)) + monomial n (p.coeff n)) * q) x := by
                rw [← hsplit]
          _ = eval ((p - monomial n (p.coeff n)) * q + monomial n (p.coeff n) * q) x := by
                rw [mul_add_left_poly]
          _ = eval ((p - monomial n (p.coeff n)) * q) x
                + eval (monomial n (p.coeff n) * q) x := by
                rw [eval_add_semiring]
          _ = eval (p - monomial n (p.coeff n)) x * eval q x
                + (p.coeff n * x ^ n) * eval q x := by
                rw [ih _ q x hsize, eval_monomial_mul]
          _ = (eval (p - monomial n (p.coeff n)) x + p.coeff n * x ^ n) * eval q x := by
                grind
          _ = eval p x * eval q x := by
                have hev : eval ((p - monomial n (p.coeff n)) + monomial n (p.coeff n)) x
                    = eval (p - monomial n (p.coeff n)) x + p.coeff n * x ^ n := by
                  rw [eval_add_semiring, eval_monomial_semiring]
                rw [← hev, ← hsplit]

/-- Horner evaluation is multiplicative. -/
@[simp, grind =] theorem eval_mul_commring [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (x : S) :
    eval (p * q) x = eval p x * eval q x :=
  eval_mul_of_size_le p.size p q x (Nat.le_refl _)

end DensePoly

end Hex
