/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvPolyMathlib
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.List.GetD

namespace CPoly

open Hex

abbrev CMvMonomial (n : Nat) := Mono n

abbrev CMvPolynomial (n : Nat) (R : Type*) [CommSemiring R] :=
  Hex.MvPoly n R Mono.lex

namespace CMvPolynomial

export Hex.MvPoly
  (C X monomial eval eval₂ bind bind₁)

/-- Executable algebra evaluation with the argument shape of CompPoly's
`CMvPolynomial.aeval`. -/
def aeval {n : Nat} {R σ : Type*}
    [CommSemiring R] [CommSemiring σ] [Algebra R σ]
    (x : Fin n → σ) (p : CMvPolynomial n R) : σ :=
  Hex.MvPoly.eval₂ (algebraMap R σ) x p

/-- Direct evaluation packaged as the ring homomorphism expected by SOS. -/
abbrev eval₂Hom {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] (f : R →+* σ) (x : Fin n → σ) :=
  HexMvPolyMathlib.eval₂Hom
    (n := n) (R := R) (S := σ) (cmp := Mono.lex) f x

@[simp] theorem eval₂Hom_apply {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] (f : R →+* σ) (x : Fin n → σ)
    (p : CMvPolynomial n R) :
    eval₂Hom f x p = eval₂ f x p := by
  exact HexMvPolyMathlib.eval₂Hom_apply (cmp := Mono.lex) f x p

/-- Algebra evaluation is direct evaluation through the coefficient algebra
map, matching CompPoly's compatibility theorem. -/
theorem aeval_eq_eval₂ {n : Nat} {R σ : Type*}
    [CommSemiring R] [CommSemiring σ] [Algebra R σ]
    (x : Fin n → σ) (p : CMvPolynomial n R) :
    aeval x p = eval₂ (algebraMap R σ) x p := by
  rfl

@[simp] theorem aeval_zero {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) :
    aeval x (0 : CMvPolynomial n R) = 0 := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  change eval₂ (algebraMap R σ) x (0 : CMvPolynomial n R) = 0
  simpa only [HexMvPolyMathlib.aeval_eq_eval₂] using
    (HexMvPolyMathlib.aeval_zero
      (n := n) (R := R) (S := σ) (cmp := Mono.lex) x)

@[simp] theorem aeval_one {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) :
    aeval x (1 : CMvPolynomial n R) = 1 := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  change eval₂ (algebraMap R σ) x (1 : CMvPolynomial n R) = 1
  simpa only [HexMvPolyMathlib.aeval_eq_eval₂] using
    (HexMvPolyMathlib.aeval_one
      (n := n) (R := R) (S := σ) (cmp := Mono.lex) x)

@[simp] theorem aeval_add {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ)
    (p q : CMvPolynomial n R) :
    aeval x (p + q) = aeval x p + aeval x q := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  change eval₂ (algebraMap R σ) x (p + q) =
    eval₂ (algebraMap R σ) x p + eval₂ (algebraMap R σ) x q
  simpa only [HexMvPolyMathlib.aeval_eq_eval₂] using
    (HexMvPolyMathlib.aeval_add
      (cmp := Mono.lex) x p q)

@[simp] theorem aeval_mul {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ)
    (p q : CMvPolynomial n R) :
    aeval x (p * q) = aeval x p * aeval x q := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  change eval₂ (algebraMap R σ) x (p * q) =
    eval₂ (algebraMap R σ) x p * eval₂ (algebraMap R σ) x q
  simpa only [HexMvPolyMathlib.aeval_eq_eval₂] using
    (HexMvPolyMathlib.aeval_mul
      (cmp := Mono.lex) x p q)

@[simp] theorem aeval_pow {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ)
    (p : CMvPolynomial n R) (k : Nat) :
    aeval x (p ^ k) = aeval x p ^ k := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  change eval₂ (algebraMap R σ) x (p ^ k) =
    eval₂ (algebraMap R σ) x p ^ k
  simpa only [HexMvPolyMathlib.aeval_eq_eval₂] using
    (HexMvPolyMathlib.aeval_pow
      (cmp := Mono.lex) x p k)

@[simp] theorem aeval_C {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) (r : R) :
    aeval x (C r : CMvPolynomial n R) = algebraMap R σ r := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  change eval₂ (algebraMap R σ) x (C r : CMvPolynomial n R) =
    algebraMap R σ r
  simpa [HexMvPolyMathlib.aeval_eq_eval₂] using
    (HexMvPolyMathlib.aeval_C (cmp := Mono.lex) x r)

@[simp] theorem aeval_X {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) (i : Fin n) :
    aeval x (X i : CMvPolynomial n R) = x i := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  change eval₂ (algebraMap R σ) x (X i : CMvPolynomial n R) = x i
  simpa [HexMvPolyMathlib.aeval_eq_eval₂] using
    (HexMvPolyMathlib.aeval_X
      (n := n) (R := R) (S := σ) (cmp := Mono.lex) x i)

@[simp] theorem aeval_neg {n : Nat} {R σ : Type*}
    [CommRing R] [BEq R] [LawfulBEq R]
    [CommRing σ] [Algebra R σ] (x : Fin n → σ)
    (p : CMvPolynomial n R) :
    aeval x (-p) = -aeval x p := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  change eval₂ (algebraMap R σ) x (-p) =
    -eval₂ (algebraMap R σ) x p
  simpa only [HexMvPolyMathlib.aeval_eq_eval₂] using
    (HexMvPolyMathlib.aeval_neg
      (cmp := Mono.lex) x p)

@[simp] theorem aeval_sub {n : Nat} {R σ : Type*}
    [CommRing R] [BEq R] [LawfulBEq R]
    [CommRing σ] [Algebra R σ] (x : Fin n → σ)
    (p q : CMvPolynomial n R) :
    aeval x (p - q) = aeval x p - aeval x q := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  change eval₂ (algebraMap R σ) x (p - q) =
    eval₂ (algebraMap R σ) x p - eval₂ (algebraMap R σ) x q
  simpa only [HexMvPolyMathlib.aeval_eq_eval₂] using
    (HexMvPolyMathlib.aeval_sub
      (cmp := Mono.lex) x p q)

def coeff {n : Nat} {R : Type*} [CommSemiring R]
    (p : CMvPolynomial n R) (m : CMvMonomial n) : R :=
  Hex.MvPoly.coeff m p

def monomials {n : Nat} {R : Type*} [CommSemiring R]
    (p : CMvPolynomial n R) : List (CMvMonomial n) :=
  Hex.MvPoly.monomials p

def support {n : Nat} {R : Type*} [CommSemiring R]
    (p : CMvPolynomial n R) : List (CMvMonomial n) :=
  Hex.MvPoly.support p

def totalDegree {n : Nat} {R : Type*} [CommSemiring R]
    (p : CMvPolynomial n R) : Nat :=
  Hex.MvPoly.totalDegree p

end CMvPolynomial

end CPoly
