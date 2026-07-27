/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.AlgebraicPoly
public import Mathlib.Algebra.Polynomial.Div

public section

/-!
# Correctness of algebraic root APIs

This module gives `RootSet` a semantic interface independent of structural
equality on algebraic roots, then states completeness, multiplicity, and
normal-form contracts for both fixed-field and algebraic-coefficient drivers.
-/

namespace Hex

namespace RootSet

/-- Semantic membership in a root set.  Every complex number belongs to the
root set of the zero polynomial. -/
def Contains (roots : RootSet) (z : ℂ) : Prop :=
  match roots with
  | .all => True
  | .finite entries =>
      ∃ entry ∈ entries.toList, entry.root.toComplex = z

/-- The recorded multiplicity of a complex value, or zero when it is absent.
The `.all` case also returns zero, matching Mathlib's convention for
`Polynomial.rootMultiplicity` of the zero polynomial. -/
@[expose]
noncomputable def multiplicityOf (roots : RootSet) (z : ℂ) : Nat := by
  classical
  exact match roots with
  | .all => 0
  | .finite entries =>
      (entries.toList.find? fun entry => entry.root.toComplex = z).map
        (fun entry => entry.multiplicity) |>.getD 0

/-- Sum of the multiplicities in a finite root set. -/
@[expose]
def totalMultiplicity : RootSet → Nat
  | .all => 0
  | .finite entries =>
      entries.foldl (fun total entry => total + entry.multiplicity) 0

/-- Every stored entry has positive multiplicity. -/
def Positive : RootSet → Prop
  | .all => True
  | .finite entries => ∀ entry ∈ entries.toList, 0 < entry.multiplicity

/-- A finite root set contains no two entries with the same semantic value. -/
def NoDuplicates : RootSet → Prop
  | .all => True
  | .finite entries =>
      entries.toList.Pairwise fun a b =>
        a.root.toComplex ≠ b.root.toComplex

end RootSet

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Interpret a fixed-field dense polynomial at the selected embedding. -/
@[expose]
noncomputable def toPolynomial [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) : Polynomial ℂ :=
  f.toArray.foldr
    (fun a value => Polynomial.C (toComplex a) + Polynomial.X * value) 0

/-- Semantic coefficients agree with fixed-coordinate evaluation. -/
theorem coeff_toPolynomial [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (n : Nat) :
    (QAdjoin.toPolynomial f).coeff n = toComplex (f.coeff n) := by
  sorry

/-- The fixed-field root driver always produces a checked root set. -/
theorem roots?_isSome [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    (QAdjoin.roots? f rep h).isSome := by
  sorry

/-- The fixed-field driver returns `.all` exactly for the zero polynomial. -/
theorem roots_all_iff [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    QAdjoin.roots f rep h = RootSet.all ↔ QAdjoin.toPolynomial f = 0 := by
  sorry

/-- Semantic membership in the fixed-field output is exactly polynomial
vanishing. -/
theorem contains_roots_iff [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) :
    RootSet.Contains (QAdjoin.roots f rep h) z ↔
      Polynomial.eval z (QAdjoin.toPolynomial f) = 0 := by
  sorry

/-- Fixed-field root multiplicities agree with Mathlib multiplicities. -/
theorem multiplicity_roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) :
    (QAdjoin.roots f rep h).multiplicityOf z =
      Polynomial.rootMultiplicity z (QAdjoin.toPolynomial f) := by
  sorry

/-- The fixed-field driver produces positive multiplicities. -/
theorem roots_positive [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    RootSet.Positive (QAdjoin.roots f rep h) := by
  sorry

/-- The fixed-field driver merges all semantic duplicates. -/
theorem roots_noDuplicates [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    RootSet.NoDuplicates (QAdjoin.roots f rep h) := by
  sorry

/-- For a nonzero fixed-field polynomial, the output multiplicities sum to
its degree. -/
theorem totalMultiplicity_roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (hf : QAdjoin.toPolynomial f ≠ 0) :
    (QAdjoin.roots f rep h).totalMultiplicity =
      (QAdjoin.toPolynomial f).natDegree := by
  sorry

end QAdjoin

namespace AlgebraicPoly

/-- The algebraic-coefficient root driver always produces a checked root set. -/
theorem roots?_isSome (f : AlgebraicPoly) :
    f.roots?.isSome := by
  sorry

/-- The algebraic-coefficient driver returns `.all` exactly for the zero
polynomial. -/
theorem roots_all_iff (f : AlgebraicPoly) :
    f.roots = .all ↔ f.toPolynomial = 0 := by
  sorry

/-- Semantic membership in the algebraic-coefficient output is exactly
polynomial vanishing. -/
theorem contains_roots_iff (f : AlgebraicPoly) (z : ℂ) :
    RootSet.Contains f.roots z ↔
      Polynomial.eval z f.toPolynomial = 0 := by
  sorry

/-- Algebraic-coefficient root multiplicities agree with Mathlib. -/
theorem multiplicity_roots (f : AlgebraicPoly) (z : ℂ) :
    f.roots.multiplicityOf z =
      Polynomial.rootMultiplicity z f.toPolynomial := by
  sorry

/-- The algebraic-coefficient driver produces positive multiplicities. -/
theorem roots_positive (f : AlgebraicPoly) :
    RootSet.Positive f.roots := by
  sorry

/-- The algebraic-coefficient driver merges all semantic duplicates. -/
theorem roots_noDuplicates (f : AlgebraicPoly) :
    RootSet.NoDuplicates f.roots := by
  sorry

/-- For a nonzero algebraic-coefficient polynomial, output multiplicities sum
to its degree. -/
theorem totalMultiplicity_roots (f : AlgebraicPoly)
    (hf : f.toPolynomial ≠ 0) :
    f.roots.totalMultiplicity = f.toPolynomial.natDegree := by
  sorry

end AlgebraicPoly

end Hex
