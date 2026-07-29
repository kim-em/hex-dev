/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Zitek-Estrada
-/

import CompPoly.Univariate.ToPoly.Impl
import HexMvPolyMathlib

/-!
# Equivalence between `CPolynomial` and `Hex.MvPoly 1`

This consumer adapter replaces CompPoly's former computable multivariate
polynomial with the canonical `Hex.MvPoly` representation.  It deliberately
uses only the public dense-polynomial and recursive-view equivalences.
-/

namespace CompPoly.CPolynomial

open Hex

variable {R : Type*}

/-- Ring equivalence between computable univariate polynomials and
single-variable executable multivariate polynomials. -/
noncomputable def cmvEquiv
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] :
    CPolynomial R ≃+* MvPoly 1 R Mono.lex :=
  (ringEquiv (R := R)).trans <|
    (Polynomial.mapEquiv
      (HexMvPolyMathlib.isEmptyRingEquiv
        (R := R) (cmp0 := (Mono.lex : Mono 0 → Mono 0 → Ordering))).symm).trans <|
      (HexPolyMathlib.equiv
        (R := MvPoly 0 R (Mono.lex : Mono 0 → Mono 0 → Ordering))).symm.trans <|
        (HexMvPolyMathlib.finSuccEquiv
          (R := R) (cmp := (Mono.lex : Mono 1 → Mono 1 → Ordering))
          (Mono.lex : Mono 0 → Mono 0 → Ordering)).symm

/-- `cmvEquiv` preserves addition. -/
theorem cmvEquiv_add
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] (p q : CPolynomial R) :
    cmvEquiv (p + q) = cmvEquiv p + cmvEquiv q :=
  (cmvEquiv (R := R)).map_add p q

/-- `cmvEquiv` preserves multiplication. -/
theorem cmvEquiv_mul
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] (p q : CPolynomial R) :
    cmvEquiv (p * q) = cmvEquiv p * cmvEquiv q :=
  (cmvEquiv (R := R)).map_mul p q

end CompPoly.CPolynomial
