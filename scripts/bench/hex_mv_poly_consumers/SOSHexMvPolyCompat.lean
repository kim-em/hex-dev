import HexMvPolyMathlib
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.List.GetD

namespace CPoly

open Hex

/-- Recover the proposition-level equality decision required by the Mathlib
bridge when a CompPoly-style caller supplies only lawful boolean equality. -/
instance (priority := 50) {R : Type*} [BEq R] [LawfulBEq R] : DecidableEq R :=
  instDecidableEqOfLawfulBEq

abbrev CMvMonomial (n : Nat) := Mono n

abbrev CMvPolynomial (n : Nat) (R : Type*) [CommSemiring R] :=
  Hex.MvPoly n R Mono.lex

namespace CMvPolynomial

export Hex.MvPoly
  (C X monomial eval eval₂ bind bind₁)

noncomputable abbrev aeval {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) :=
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  HexMvPolyMathlib.aeval (n := n) (R := R) (S := σ) (cmp := Mono.lex) x

/-- Direct evaluation packaged as the ring homomorphism expected by SOS. -/
noncomputable abbrev eval₂Hom {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] (f : R →+* σ) (x : Fin n → σ) :=
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  HexMvPolyMathlib.eval₂Hom
    (n := n) (R := R) (S := σ) (cmp := Mono.lex) f x

@[simp] theorem eval₂Hom_apply {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] (f : R →+* σ) (x : Fin n → σ)
    (p : CMvPolynomial n R) :
    eval₂Hom f x p = eval₂ f x p := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  exact HexMvPolyMathlib.eval₂Hom_apply (cmp := Mono.lex) f x p

/-- Algebra evaluation is direct evaluation through the coefficient algebra
map, matching CompPoly's compatibility theorem. -/
theorem aeval_eq_eval₂ {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ]
    (x : Fin n → σ) (p : CMvPolynomial n R) :
    aeval x p = eval₂ (algebraMap R σ) x p := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  exact HexMvPolyMathlib.aeval_eq_eval₂ (cmp := Mono.lex) x p

@[simp] theorem aeval_add {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ)
    (p q : CMvPolynomial n R) :
    aeval x (p + q) = aeval x p + aeval x q :=
  map_add (aeval x) p q

@[simp] theorem aeval_mul {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ)
    (p q : CMvPolynomial n R) :
    aeval x (p * q) = aeval x p * aeval x q :=
  map_mul (aeval x) p q

@[simp] theorem aeval_C {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) (r : R) :
    aeval x (C r : CMvPolynomial n R) = algebraMap R σ r := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  exact HexMvPolyMathlib.aeval_C (cmp := Mono.lex) x r

@[simp] theorem aeval_X {n : Nat} {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ] (x : Fin n → σ) (i : Fin n) :
    aeval x (X i : CMvPolynomial n R) = x i := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  exact HexMvPolyMathlib.aeval_X (cmp := Mono.lex) x i

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
