/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Norm
public import HexBerlekampZassenhausMathlib

public section

/-!
# Correctness of recursive Trager factorization

The semantic irreducibility predicate is phrased directly on the executable
tower-polynomial carrier.  Once the arithmetic laws are packaged as a field,
it is equivalent to Mathlib's ordinary polynomial irreducibility predicate.
-/

namespace Hex.NumberTower

/-- A nonconstant tower polynomial has no factorization into two nonconstant
tower polynomials. -/
def PolynomialIrreducible (T : NumberTower) (f : Poly T) : Prop :=
  !f.isZero ∧ 0 < f.degree?.getD 0 ∧
    ∀ g h : Poly T, f = g * h →
      g.degree?.getD 0 = 0 ∨ h.degree?.getD 0 = 0

namespace Factorization

/-- Executable natural power without presupposing a law-bearing monoid
instance on tower coefficients. -/
@[expose]
def polyPow {T : NumberTower} (f : Poly T) : Nat → Poly T
  | 0 => 1
  | n + 1 => polyPow f n * f

/-- Reconstruct a polynomial from a public factorization payload. -/
@[expose]
def reconstruct {T : NumberTower} {f : Poly T}
    (r : Factorization T f) : Poly T :=
  r.factors.foldl
    (fun product factor => product * polyPow factor.1 factor.2)
    (DensePoly.C r.scalar)

/-- Mathematical meaning of a checked factorization payload. Strict
executable ordering of monic factors also rules out associates and duplicate
entries. -/
def Sound {T : NumberTower} {f : Poly T}
    (r : Factorization T f) : Prop :=
  r.reconstruct = f ∧
    (∀ factor ∈ r.factors.toList,
      factor.1.leadingCoeff = 1 ∧
      0 < factor.2 ∧
      PolynomialIrreducible T factor.1) ∧
    Factor.factorsSorted
      (r.factors.map fun factor =>
        (factor.1.toArray.map coeffs, factor.2))

end Factorization

/-- The recursive executable irreducibility test has exactly the intended
factor-theoretic meaning in a validated tower. -/
theorem isIrreducible_iff (T : NumberTower) (f : Poly T) :
    Factor.isIrreducible T.levels.toList
      (f.toArray.map coeffs) ↔
        f.leadingCoeff = 1 ∧ PolynomialIrreducible T f := by
  sorry

/-- Every returned Trager factorization satisfies reconstruction,
multiplicity, irreducibility, uniqueness, and ordering. -/
theorem factor?_sound (T : NumberTower) (f : Poly T)
    {r : Factorization T f} (h : T.factor? f = some r) :
    r.Sound := by
  sorry

/-- Recursive Trager factorization succeeds for every tower polynomial. -/
theorem factor?_isSome (T : NumberTower) (f : Poly T) :
    (T.factor? f).isSome := by
  sorry

end Hex.NumberTower
