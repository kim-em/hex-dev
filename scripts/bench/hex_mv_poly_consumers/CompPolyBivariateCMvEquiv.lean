/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.ToPoly
import HexMvPolyMathlib

/-!
# Equivalence between `CBivariate` and `Hex.MvPoly 2`

The two nested Mathlib polynomial layers are converted to executable dense
polynomials and folded with `HexMvPolyMathlib.finSuccEquiv`.
-/

namespace CompPoly.CBivariate

open scoped HexMvPolyMathlib

open Hex

variable {R : Type*}
variable [CommRing R] [Nontrivial R] [DecidableEq R]

/-- Ring equivalence between computable bivariate polynomials and
two-variable executable multivariate polynomials. -/
noncomputable def bivariateEquiv :
    CBivariate R ≃+* MvPoly 2 R Mono.lex :=
  let emptyEquiv :=
    HexMvPolyMathlib.isEmptyRingEquiv
      (R := R) (cmp0 := (Mono.lex : Mono 0 → Mono 0 → Ordering))
  let foldInner :=
    (HexPolyMathlib.equiv
      (R := MvPoly 0 R (Mono.lex : Mono 0 → Mono 0 → Ordering))).symm.trans
      (HexMvPolyMathlib.finSuccEquiv
        (R := R) (cmp := (Mono.lex : Mono 1 → Mono 1 → Ordering))
        (Mono.lex : Mono 0 → Mono 0 → Ordering)).symm
  let foldOuter :=
    (HexPolyMathlib.equiv
      (R := MvPoly 1 R (Mono.lex : Mono 1 → Mono 1 → Ordering))).symm.trans
      (HexMvPolyMathlib.finSuccEquiv
        (R := R) (cmp := (Mono.lex : Mono 2 → Mono 2 → Ordering))
        (Mono.lex : Mono 1 → Mono 1 → Ordering)).symm
  CBivariate.ringEquiv |>.trans
    (Polynomial.mapEquiv (Polynomial.mapEquiv emptyEquiv.symm)) |>.trans
    (Polynomial.mapEquiv foldInner) |>.trans
    foldOuter

/-- `bivariateEquiv` preserves addition. -/
theorem bivariateEquiv_add (p q : CBivariate R) :
    bivariateEquiv (p + q) =
      bivariateEquiv p + bivariateEquiv q :=
  bivariateEquiv.map_add p q

/-- `bivariateEquiv` preserves multiplication. -/
theorem bivariateEquiv_mul (p q : CBivariate R) :
    bivariateEquiv (p * q) =
      bivariateEquiv p * bivariateEquiv q :=
  bivariateEquiv.map_mul p q

/-- `bivariateEquiv` maps zero to zero. -/
theorem bivariateEquiv_zero :
    bivariateEquiv (0 : CBivariate R) = 0 :=
  map_zero bivariateEquiv

end CompPoly.CBivariate
