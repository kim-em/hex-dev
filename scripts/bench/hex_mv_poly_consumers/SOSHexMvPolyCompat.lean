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

noncomputable def aeval {n : Nat} {R σ : Type*}
    [CommSemiring R] [DecidableEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) :
    CMvPolynomial n R →ₐ[R] σ :=
  HexMvPolyMathlib.aeval (cmp := Mono.lex) x

@[simp] theorem aeval_zero {n : Nat} {R σ : Type*}
    [CommSemiring R] [DecidableEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) :
    aeval x (0 : CMvPolynomial n R) = 0 :=
  map_zero (aeval x)

@[simp] theorem aeval_one {n : Nat} {R σ : Type*}
    [CommSemiring R] [DecidableEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) :
    aeval x (1 : CMvPolynomial n R) = 1 :=
  map_one (aeval x)

@[simp] theorem aeval_add {n : Nat} {R σ : Type*}
    [CommSemiring R] [DecidableEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ)
    (p q : CMvPolynomial n R) :
    aeval x (p + q) = aeval x p + aeval x q :=
  map_add (aeval x) p q

@[simp] theorem aeval_mul {n : Nat} {R σ : Type*}
    [CommSemiring R] [DecidableEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ)
    (p q : CMvPolynomial n R) :
    aeval x (p * q) = aeval x p * aeval x q :=
  map_mul (aeval x) p q

@[simp] theorem aeval_pow {n : Nat} {R σ : Type*}
    [CommSemiring R] [DecidableEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ)
    (p : CMvPolynomial n R) (k : Nat) :
    aeval x (p ^ k) = aeval x p ^ k :=
  map_pow (aeval x) p k

@[simp] theorem aeval_C {n : Nat} {R σ : Type*}
    [CommSemiring R] [DecidableEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) (r : R) :
    aeval x (C r : CMvPolynomial n R) = algebraMap R σ r :=
  HexMvPolyMathlib.aeval_C (cmp := Mono.lex) x r

@[simp] theorem aeval_X {n : Nat} {R σ : Type*}
    [CommSemiring R] [DecidableEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) (i : Fin n) :
    aeval x (X i : CMvPolynomial n R) = x i :=
  HexMvPolyMathlib.aeval_X (cmp := Mono.lex) x i

@[simp] theorem aeval_neg {n : Nat} {R σ : Type*}
    [CommRing R] [DecidableEq R]
    [CommRing σ] [Algebra R σ] (x : Fin n → σ)
    (p : CMvPolynomial n R) :
    aeval x (-p) = -aeval x p :=
  map_neg (aeval x) p

@[simp] theorem aeval_sub {n : Nat} {R σ : Type*}
    [CommRing R] [DecidableEq R]
    [CommRing σ] [Algebra R σ] (x : Fin n → σ)
    (p q : CMvPolynomial n R) :
    aeval x (p - q) = aeval x p - aeval x q :=
  map_sub (aeval x) p q

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
