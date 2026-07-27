/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField
public import HexResultantMathlib
public import HexBerlekampZassenhausMathlib
public import HexRootsMathlib
public import HexPolyZMathlib
public import Mathlib.FieldTheory.Minpoly.Basic

public section

/-!
# Semantic interpretation of executable algebraic numbers

This module fixes the complex value represented by every selected isolation and
the evaluation map for a checked fixed presentation. The algebraic laws and
completeness results are split into later modules so downstream proof work can
depend on the semantic boundary without importing one monolithic development.
-/

namespace Hex

/-- A computationally checked irreducible integer polynomial is separable over
the rationals. The factorization correspondence supplies irreducibility; this
is the semantic bridge used by quotient-root interpretation. -/
theorem ZPoly.CheckedIrreducible.separable (p : ZPoly)
    [ZPoly.CheckedIrreducible p] :
    (HexPolyZMathlib.toPolyℚ p).Separable := by
  sorry

namespace AlgebraicRoot

/-- The complex value selected by a factorization-lazy algebraic root. -/
@[expose]
noncomputable def toComplex (a : AlgebraicRoot) : ℂ :=
  a.rep.root

/-- The selected value zeros the enclosing integer polynomial. -/
theorem toComplex_isRoot (a : AlgebraicRoot) :
    (HexRootsMathlib.toPolyℂ a.p).eval a.toComplex = 0 := by
  exact HexRootsMathlib.RefinedIsolation.isRoot a.rep

end AlgebraicRoot

namespace AlgebraicNumber

/-- The complex value selected by a canonical algebraic number. -/
@[expose]
noncomputable def toComplex (a : AlgebraicNumber) : ℂ :=
  a.rep.root

/-- A canonical algebraic number stores its primitive positive associate of the
rational minimal polynomial. -/
theorem p_eq_minpoly (a : AlgebraicNumber) :
    (a.p.leadingCoeff : Rat)⁻¹ • HexPolyZMathlib.toPolyℚ a.p =
      minpoly Rat a.toComplex := by
  sorry

end AlgebraicNumber

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Evaluate canonical fixed-field coordinates at their selected complex root.
The representative and quotient equality are explicit inputs so this semantic
map does not depend on an irreducibility proof. -/
@[expose]
noncomputable def toComplex (a : QAdjoin p x)
    (rep : RefinedIsolation p) (_h : SimpleRoot.mk rep = x) : ℂ :=
  (HexPolyMathlib.toPolynomial a.coeffs).eval₂ (algebraMap Rat ℂ)
    rep.root

/-- Fixed-presentation addition agrees with complex addition. -/
theorem map_add (a b : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (a + b) rep h = toComplex a rep h + toComplex b rep h := by
  sorry

/-- Fixed-presentation multiplication agrees with complex multiplication. -/
theorem map_mul (a b : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (a * b) rep h = toComplex a rep h * toComplex b rep h := by
  sorry

/-- Fixed-presentation inversion agrees with complex inversion, including the
computational convention `0⁻¹ = 0`. -/
theorem map_inv [ZPoly.CheckedIrreducible p] (a : QAdjoin p x)
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex a⁻¹ rep h = (toComplex a rep h)⁻¹ := by
  sorry

/-- Evaluation at the selected root is injective for a checked irreducible
presentation. -/
theorem toComplex_injective [ZPoly.CheckedIrreducible p]
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    Function.Injective (fun a : QAdjoin p x => toComplex a rep h) := by
  sorry

end QAdjoin

/-- Canonical Boolean equality is equality of represented complex values. -/
theorem AlgebraicNumber.beq_iff (a b : AlgebraicNumber) :
    (a == b) ↔ a.toComplex = b.toComplex := by
  sorry

/-- The executable zero predicate recognizes exactly the complex value zero. -/
theorem AlgebraicRoot.isZero_iff (a : AlgebraicRoot) :
    a.isZero ↔ a.toComplex = 0 := by
  sorry

/-- The canonical algebraic-number zero test recognizes exactly complex zero. -/
theorem AlgebraicNumber.isZero_iff (a : AlgebraicNumber) :
    a.isZero ↔ a.toComplex = 0 := by
  sorry

end Hex
