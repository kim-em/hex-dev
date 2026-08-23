/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvHensel.Lift
public import HexMvGcd.Gcd
public import HexPolyZ.Mignotte

@[expose] public section

/-!
Uniqueness and conditional completeness for multivariate Hensel lifting.

The executable coefficient bound uses the mixed-radix Kronecker substitution
from the SPEC, applied after translating the evaluation point to the origin.
It computes the univariate image degree and coefficient norm directly from the
sparse term list, without allocating a dense polynomial with potentially
astronomical gaps.
-/

namespace Hex.MvHensel

open Hex
open Hex.MvPoly

universe u

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp] [IsMonomialOrder cmp']

/-! # Rational coprimality and uniqueness -/

/-- The checked modular partial-fraction witness implies pairwise
coprimality of the integer images after extension to `Rat`.

The bounds on `j` and `k` are essential because `Input.images` is a list and
the total `getD` operation returns zero outside its range. -/
theorem coprimeRat_of_witness {inp : Input n cmp cmp'}
    (h : valid inp = true) (j k : Nat)
    (hj : j < inp.images.length) (hk : k < inp.images.length)
    (hjk : j ≠ k) :
    ∃ u v : DensePoly Rat,
      u * ZPoly.toRatPoly (inp.images.getD j 0) +
        v * ZPoly.toRatPoly (inp.images.getD k 0) = 1 := by
  sorry

/-- At most one exact factor tuple is compatible with a valid lift input. -/
theorem lift_unique {inp : Input n cmp cmp'}
    {fs gs : List (MvPoly (n + 1) Int cmp)}
    (h : valid inp = true) (h1 : IsLiftOf inp fs)
    (h2 : IsLiftOf inp gs) : fs = gs := by
  sorry

/-! # Executable shifted coefficient bound -/

/-- Every compatible factor tuple has coefficients of its shifted factors
bounded in absolute value by `bound`. -/
def BoundsFactors (inp : Input n cmp cmp') (bound : Nat) : Prop :=
  ∀ fs, IsLiftOf inp fs → ∀ g, g ∈ fs → ∀ monomial,
    (MvPoly.coeff monomial
      (shift inp.setup.main inp.setup.point g)).natAbs ≤ bound

/-- Product of the earlier side-variable radices. -/
def kroneckerPrefix (sideDegrees : Fin n → Nat) (j : Fin n) : Nat :=
  (List.finRange n).foldl
    (fun radix k =>
      if k.val < j.val then radix * (sideDegrees k + 1) else radix) 1

/-- Mixed-radix weight of side variable `j`.  The factor `mainDegree + 1`
is deliberately present: without it the main variable and the first side
variable would both map to the same univariate monomial. -/
def kroneckerWeight (mainDegree : Nat) (sideDegrees : Fin n → Nat)
    (j : Fin n) : Nat :=
  (mainDegree + 1) * kroneckerPrefix sideDegrees j

/-- Exponent of a monomial under the mixed-radix Kronecker substitution. -/
def kroneckerExponent (i : Fin (n + 1)) (mainDegree : Nat)
    (sideDegrees : Fin n → Nat) (monomial : Mono (n + 1)) : Nat :=
  (List.finRange n).foldl
    (fun exponent j => exponent +
      Mono.degreeOf (remainingVar i j) monomial *
        kroneckerWeight mainDegree sideDegrees j)
    (Mono.degreeOf i monomial)

/-- Degree of the sparse Kronecker image, computed without materialising its
dense zero gaps. -/
def kroneckerDegree (i : Fin (n + 1)) (mainDegree : Nat)
    (sideDegrees : Fin n → Nat) (p : MvPoly (n + 1) Int cmp) : Nat :=
  p.foldTerms
    (fun degree monomial _ =>
      max degree (kroneckerExponent i mainDegree sideDegrees monomial)) 0

/-- Squared Euclidean coefficient norm.  Mixed-radix injectivity means this is
also the coefficient norm of the Kronecker image. -/
def mvCoeffNormSq (p : MvPoly (n + 1) Int cmp) : Nat :=
  p.foldTerms (fun norm _ coefficient => norm + coefficient.natAbs ^ 2) 0

/-- A uniform factor-coefficient bound obtained by translating the target,
using the corrected mixed-radix Kronecker substitution, and applying the
closed-form univariate Mignotte bound. -/
def coeffBound (inp : Input n cmp cmp') : Nat :=
  let shifted := shift inp.setup.main inp.setup.point inp.target
  let mainDegree := MvPoly.degreeOf inp.setup.main shifted
  let sideDegrees : Fin n → Nat := fun j =>
    MvPoly.degreeOf (remainingVar inp.setup.main j) shifted
  let degree := kroneckerDegree inp.setup.main mainDegree sideDegrees shifted
  Nat.binom degree (degree / 2) * ZPoly.ceilSqrt (mvCoeffNormSq shifted)

/-! # Conditional completeness -/

/-- Above twice a valid coefficient bound, every compatible factorization is
found by the concrete lift. -/
theorem lift_complete {inp : Input n cmp cmp'} {bound : Nat}
    (h : valid inp = true) (hB : BoundsFactors inp bound)
    (hq : 2 * bound < inp.setup.modulus)
    (hex : ∃ fs, IsLiftOf inp fs) :
    ∃ cert, lift inp = .ok cert := by
  sorry

/-- If no compatible factorization exists, progress forces the lift to end in
a reconstruction failure. -/
theorem lift_none {inp : Input n cmp cmp'}
    (h : valid inp = true) (hno : ¬ ∃ fs, IsLiftOf inp fs) :
    ∃ modulus, lift inp = .error (.reconstruct modulus) := by
  rcases lift_progress h with hsuccess | hfailure
  · rcases hsuccess with ⟨cert, hcert⟩
    exact False.elim (hno ⟨cert.factors,
      check_sound (lift_checks hcert)⟩)
  · exact hfailure

/-- Past the coefficient bound, reconstruction failure proves that the point
admits no compatible factorization. -/
theorem no_lift_of_reconstruct {inp : Input n cmp cmp'} {bound modulus : Nat}
    (h : valid inp = true) (hB : BoundsFactors inp bound)
    (hq : 2 * bound < inp.setup.modulus)
    (hfail : lift inp = .error (.reconstruct modulus)) :
    ¬ ∃ fs, IsLiftOf inp fs := by
  intro hex
  rcases lift_complete h hB hq hex with ⟨cert, hcert⟩
  rw [hcert] at hfail
  cases hfail

/-! # Mathlib-free irreducibility predicate -/

/-- No decomposition into two nonunits, stated without Mathlib so it applies
uniformly to dense and multivariate polynomials. -/
def Irred {α : Type u} [One α] [Mul α] (p : α) : Prop :=
  (¬ ∃ u, p * u = 1) ∧
    ∀ g h, p = g * h →
      (∃ u, g * u = 1) ∨ (∃ u, h * u = 1)

/-- With a valid primitive input and irreducible integer images, every factor
in a checked lift is irreducible.  Primitivity is measured by the actual
named-variable content operation supplied by `HexMvGcd`. -/
theorem irreducible_of_image_irreducible
    {inp : Input n cmp cmp'} {cert : Cert n cmp}
    (hv : valid inp = true) (h : check inp cert = true)
    (hprim : MvPoly.contentIn inp.setup.main cmp' inp.target = 1)
    (hirr : ∀ j, j < inp.images.length →
      Irred (inp.images.getD j 0)) :
    ∀ j, j < cert.factors.length →
      Irred (cert.factors.getD j 0) := by
  sorry

end Hex.MvHensel
