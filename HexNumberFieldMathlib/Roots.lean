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
@[expose] def Contains (roots : RootSet) (z : ℂ) : Prop :=
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
@[expose] def Positive : RootSet → Prop
  | .all => True
  | .finite entries => ∀ entry ∈ entries.toList, 0 < entry.multiplicity

/-- A finite root set contains no two entries with the same semantic value. -/
@[expose] def NoDuplicates : RootSet → Prop
  | .all => True
  | .finite entries =>
      entries.toList.Pairwise fun a b =>
        a.root.toComplex ≠ b.root.toComplex

/-- Finite root entries occur in the executable canonical order. -/
@[expose] def Ordered : RootSet → Prop
  | .all => True
  | .finite entries =>
      entries.toList.Pairwise fun a b => QAdjoin.Roots.rootLe a b

end RootSet

namespace QAdjoin.Roots

/-- A successful lazy-root comparison decides equality of represented complex
values. -/
theorem sameValue?_sound (a b : AlgebraicRoot) {same : Bool}
    (h : sameValue? a b = some same) :
    same ↔ a.toComplex = b.toComplex := by
  sorry

/-- Lazy-root comparison always succeeds, exactifying only when the enclosing
polynomials differ. -/
theorem sameValue?_isSome (a b : AlgebraicRoot) :
    (sameValue? a b).isSome := by
  sorry

end QAdjoin.Roots

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Interpret a fixed-field dense polynomial at the selected embedding. -/
@[expose]
noncomputable def toPolynomialAt (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) : Polynomial ℂ :=
  f.toArray.foldr
    (fun a value => Polynomial.C (toComplex a rep h) +
      Polynomial.X * value) 0

/-- Semantic coefficients agree with fixed-coordinate evaluation. -/
theorem coeff_toPolynomialAt (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) (n : Nat) :
    (QAdjoin.toPolynomialAt f rep h).coeff n =
      toComplex (f.coeff n) rep h := by
  sorry

/-- Fixed-field executable zero detection agrees with semantic polynomial
zero. -/
theorem poly_isZero_iff (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    f.isZero ↔ QAdjoin.toPolynomialAt f rep h = 0 := by
  sorry

/-- A nonzero fixed-field polynomial has the expected semantic degree. -/
theorem natDegree_toPolynomialAt (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x)
    (hf : !f.isZero) :
    (QAdjoin.toPolynomialAt f rep h).natDegree = f.degree?.getD 0 := by
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
    QAdjoin.roots f rep h = RootSet.all ↔
      QAdjoin.toPolynomialAt f rep h = 0 := by
  sorry

/-- Semantic membership in the fixed-field output is exactly polynomial
vanishing. -/
theorem contains_roots_iff [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) :
    RootSet.Contains (QAdjoin.roots f rep h) z ↔
      Polynomial.eval z (QAdjoin.toPolynomialAt f rep h) = 0 := by
  sorry

/-- Fixed-field root multiplicities agree with Mathlib multiplicities. -/
theorem multiplicity_roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) :
    (QAdjoin.roots f rep h).multiplicityOf z =
      Polynomial.rootMultiplicity z (QAdjoin.toPolynomialAt f rep h) := by
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

/-- The fixed-field driver uses its deterministic canonical root order. -/
theorem roots_ordered [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    RootSet.Ordered (QAdjoin.roots f rep h) := by
  sorry

/-- For a nonzero fixed-field polynomial, the output multiplicities sum to
its degree. -/
theorem totalMultiplicity_roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x)
    (hf : QAdjoin.toPolynomialAt f rep h ≠ 0) :
    (QAdjoin.roots f rep h).totalMultiplicity =
      (QAdjoin.toPolynomialAt f rep h).natDegree := by
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

/-- The algebraic-coefficient driver uses its deterministic canonical order. -/
theorem roots_ordered (f : AlgebraicPoly) :
    RootSet.Ordered f.roots := by
  sorry

/-- For a nonzero algebraic-coefficient polynomial, output multiplicities sum
to its degree. -/
theorem totalMultiplicity_roots (f : AlgebraicPoly)
    (hf : f.toPolynomial ≠ 0) :
    f.roots.totalMultiplicity = f.toPolynomial.natDegree := by
  sorry

end AlgebraicPoly

end Hex
