/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.Fold
public import HexMvPolyMathlib.Equiv

public section

/-!
Algebra-hom evaluation for `Hex.MvPoly` and its exact correspondence with the
Mathlib-free evaluator.
-/

namespace HexMvPolyMathlib

open scoped BigOperators
open scoped HexMvPolyMathlib

open Hex
open Hex.MvPoly

universe u v

variable {n : Nat} {R : Type u} {S : Type v}
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [BEq R] [LawfulBEq R]

noncomputable section

/-- Auxiliary Mathlib-transported algebra evaluation used to prove the laws
of the public executable evaluator. -/
def aevalMathlib [CommSemiring R] [DecidableEq R]
    [CommSemiring S] [Algebra R S] (x : Fin n → S) :
    MvPoly n R cmp →ₐ[R] S :=
  (MvPolynomial.aeval x).comp
    (algEquiv (cmp := cmp)).toAlgHom

/-- Applying the auxiliary transported evaluator uses Mathlib evaluation
after conversion. -/
theorem aevalMathlib_apply [CommSemiring R] [DecidableEq R]
    [CommSemiring S] [Algebra R S]
    (x : Fin n → S) (p : MvPoly n R cmp) :
    aevalMathlib x p = MvPolynomial.aeval x (toMvPolynomial p) := by
  rw [aevalMathlib, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, algEquiv_apply]

/-- Executable monomial evaluation is the corresponding finite product. -/
theorem monoProd_eq_prod [CommSemiring S] (x : Fin n → S) (m : Mono n) :
    Mono.prod x m = ∏ i, x i ^ monoEquiv m i := by
  unfold Mono.prod
  simp_rw [Mono.powBySq_eq_pow]
  rw [← List.foldl_map, ← List.prod_eq_foldl,
    ← List.prod_toFinset _ (List.nodup_finRange n),
    List.toFinset_finRange]
  simp

/-- Evaluation transported through the Mathlib equivalence.

This auxiliary homomorphism supplies the laws for the public direct
evaluator. -/
def eval₂MathlibHom [CommSemiring R] [DecidableEq R]
    [CommSemiring S] (f : R →+* S) (x : Fin n → S) :
    MvPoly n R cmp →+* S :=
  (MvPolynomial.eval₂Hom f x).comp (equiv (cmp := cmp)).toRingHom

/-- The Mathlib-transported evaluation homomorphism applies as direct
`eval₂`. -/
theorem eval₂MathlibHom_apply [CommSemiring R] [DecidableEq R]
    [CommSemiring S] (f : R →+* S) (x : Fin n → S)
    (p : MvPoly n R cmp) :
    eval₂MathlibHom f x p = eval₂ f x p := by
  rw [eval₂MathlibHom, RingHom.comp_apply]
  change MvPolynomial.eval₂Hom f x (equiv p) = eval₂ f x p
  rw [equiv_apply]
  rw [toMvPolynomial_eq_sum]
  rw [map_sum (MvPolynomial.eval₂Hom f x), eval₂_eq]
  have eval_monomial (m : Mono n) (c : R) :
      (MvPolynomial.eval₂Hom f x)
          (MvPolynomial.monomial (monoEquiv m) c) =
        f c * Mono.prod x m := by
    change
      MvPolynomial.eval₂ f x
          (MvPolynomial.monomial (monoEquiv m) c) =
        f c * Mono.prod x m
    rw [MvPolynomial.eval₂_monomial, Finsupp.prod_pow,
      ← monoProd_eq_prod]
  simp_rw [eval_monomial]
  rw [List.sum_toFinset _ (monomials_nodup p),
    List.sum_eq_foldl, monomials, List.foldl_map, List.foldl_map]
  apply List.foldl_congr
  intro acc term hterm
  rw [coeff_eq_of_mem_terms p hterm]

/-- The auxiliary transported algebra evaluator is exactly the Mathlib-free
direct evaluator with the coefficient algebra map. -/
theorem aevalMathlib_eq_eval₂ [CommSemiring R] [DecidableEq R]
    [CommSemiring S] [Algebra R S]
    (x : Fin n → S) (p : MvPoly n R cmp) :
    aevalMathlib x p = eval₂ (algebraMap R S) x p := by
  rw [aevalMathlib, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    algEquiv_apply, toMvPolynomial_eq_sum]
  rw [map_sum, eval₂_eq]
  simp_rw [MvPolynomial.aeval_monomial, Finsupp.prod_pow,
    ← monoProd_eq_prod]
  rw [List.sum_toFinset _ (monomials_nodup p),
    List.sum_eq_foldl, monomials, List.foldl_map, List.foldl_map]
  apply List.foldl_congr
  intro acc term hterm
  rw [coeff_eq_of_mem_terms p hterm]

end

/-- Evaluation along an arbitrary coefficient ring homomorphism, packaged as
a ring homomorphism on executable polynomials. Its function field is
definitionally the direct Mathlib-free evaluator; lawful boolean equality is
converted to proposition-level equality only inside the erased law proofs. -/
@[expose] def eval₂Hom [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (x : Fin n → S) :
    MvPoly n R cmp →+* S := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  exact {
    toFun := eval₂ f x
    map_zero' := by
      rw [← eval₂MathlibHom_apply f x]
      exact map_zero (eval₂MathlibHom f x)
    map_one' := by
      rw [← eval₂MathlibHom_apply f x]
      exact map_one (eval₂MathlibHom f x)
    map_add' := fun p q => by
      rw [← eval₂MathlibHom_apply f x, ← eval₂MathlibHom_apply f x,
        ← eval₂MathlibHom_apply f x]
      exact map_add (eval₂MathlibHom f x) p q
    map_mul' := fun p q => by
      rw [← eval₂MathlibHom_apply f x, ← eval₂MathlibHom_apply f x,
        ← eval₂MathlibHom_apply f x]
      exact map_mul (eval₂MathlibHom f x) p q }

/-- The packaged ring homomorphism is the Mathlib-free direct evaluator. -/
@[simp] theorem eval₂Hom_apply [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (x : Fin n → S)
    (p : MvPoly n R cmp) :
    eval₂Hom f x p = eval₂ f x p := rfl

/-- Executable algebra evaluation. The function field is definitionally the
direct Mathlib-free evaluator. -/
@[expose] def aeval [CommSemiring R]
    [CommSemiring S] [Algebra R S] (x : Fin n → S) :
    MvPoly n R cmp →ₐ[R] S where
  toRingHom := eval₂Hom (algebraMap R S) x
  commutes' r := by
    letI : DecidableEq R := instDecidableEqOfLawfulBEq
    rw [algebraMap_apply]
    change
      eval₂ (algebraMap R S) x
          (C (n := n) (cmp := cmp) r : MvPoly n R cmp) =
        algebraMap R S r
    rw [← aevalMathlib_eq_eval₂ (cmp := cmp) x
      (C (n := n) (cmp := cmp) r)]
    simpa [algebraMap_apply] using
      (aevalMathlib (cmp := cmp) x).commutes r

/-- Applying executable algebra evaluation agrees with Mathlib evaluation
after conversion. -/
theorem aeval_apply [CommSemiring R] [DecidableEq R]
    [CommSemiring S] [Algebra R S]
    (x : Fin n → S) (p : MvPoly n R cmp) :
    aeval x p = MvPolynomial.aeval x (toMvPolynomial p) := by
  calc
    aeval (cmp := cmp) x p = eval₂ (algebraMap R S) x p := rfl
    _ = aevalMathlib (cmp := cmp) x p :=
      (aevalMathlib_eq_eval₂ (cmp := cmp) x p).symm
    _ = MvPolynomial.aeval x (toMvPolynomial p) :=
      aevalMathlib_apply (cmp := cmp) x p

/-- Algebra-hom evaluation is exactly the Mathlib-free direct evaluator with
the coefficient algebra map. -/
theorem aeval_eq_eval₂ [CommSemiring R]
    [CommSemiring S] [Algebra R S]
    (x : Fin n → S) (p : MvPoly n R cmp) :
    aeval x p = eval₂ (algebraMap R S) x p := rfl

/-- Evaluation into the coefficient ring agrees with the Mathlib-free
specialization. -/
theorem aeval_eq_eval [CommSemiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) :
    aeval x p = eval x p := by
  rw [aeval_eq_eval₂]
  unfold eval
  congr 1

/-- Algebra evaluation sends zero to zero. -/
@[simp] theorem aeval_zero [CommSemiring R]
    [CommSemiring S] [Algebra R S] (x : Fin n → S) :
    aeval x (0 : MvPoly n R cmp) = 0 :=
  map_zero (aeval x)

/-- Algebra evaluation sends one to one. -/
@[simp] theorem aeval_one [CommSemiring R]
    [CommSemiring S] [Algebra R S] (x : Fin n → S) :
    aeval x (1 : MvPoly n R cmp) = 1 :=
  map_one (aeval x)

/-- Algebra evaluation preserves addition. -/
@[simp] theorem aeval_add [CommSemiring R]
    [CommSemiring S] [Algebra R S] (x : Fin n → S)
    (p q : MvPoly n R cmp) :
    aeval x (p + q) = aeval x p + aeval x q :=
  map_add (aeval x) p q

/-- Algebra evaluation preserves multiplication. -/
@[simp] theorem aeval_mul [CommSemiring R]
    [CommSemiring S] [Algebra R S] (x : Fin n → S)
    (p q : MvPoly n R cmp) :
    aeval x (p * q) = aeval x p * aeval x q :=
  map_mul (aeval x) p q

/-- Algebra evaluation preserves natural powers. -/
@[simp] theorem aeval_pow [CommSemiring R]
    [CommSemiring S] [Algebra R S] (x : Fin n → S)
    (p : MvPoly n R cmp) (k : Nat) :
    aeval x (p ^ k) = aeval x p ^ k :=
  map_pow (aeval x) p k

/-- Algebra evaluation sends a constant polynomial through the algebra
map. -/
@[simp] theorem aeval_C [CommSemiring R]
    [CommSemiring S] [Algebra R S] (x : Fin n → S) (r : R) :
    aeval x (C r : MvPoly n R cmp) = algebraMap R S r := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  rw [aeval_apply, toMvPolynomial_C, MvPolynomial.aeval_C]

/-- Algebra evaluation sends a variable polynomial to its assigned value. -/
@[simp] theorem aeval_X [CommSemiring R]
    [CommSemiring S] [Algebra R S] (x : Fin n → S) (i : Fin n) :
    aeval x (X i : MvPoly n R cmp) = x i := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  rw [aeval_apply, toMvPolynomial_X, MvPolynomial.aeval_X]

/-- Algebra evaluation preserves negation. -/
@[simp] theorem aeval_neg [CommRing R]
    [CommRing S] [Algebra R S] (x : Fin n → S)
    (p : MvPoly n R cmp) :
    aeval x (-p) = -aeval x p :=
  map_neg (aeval x) p

/-- Algebra evaluation preserves subtraction. -/
@[simp] theorem aeval_sub [CommRing R]
    [CommRing S] [Algebra R S] (x : Fin n → S)
    (p q : MvPoly n R cmp) :
    aeval x (p - q) = aeval x p - aeval x q :=
  map_sub (aeval x) p q

end HexMvPolyMathlib
