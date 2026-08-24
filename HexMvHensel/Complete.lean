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

/-- Prefix-product weights for a list of degree bounds. -/
def weightScan : List Nat → Nat → List Nat
  | [], _ => []
  | bound :: bounds, weight =>
      weight :: weightScan bounds (weight * (bound + 1))

/-- Degree bounds in mixed-radix digit order: main variable first. -/
def kroneckerBounds (mainDegree : Nat)
    (sideDegrees : Fin n → Nat) : List Nat :=
  mainDegree :: (List.finRange n).map sideDegrees

/-- Monomial exponents in mixed-radix digit order: main variable first. -/
def kroneckerDigits (i : Fin (n + 1))
    (monomial : Mono (n + 1)) : List Nat :=
  Mono.degreeOf i monomial :: (List.finRange n).map fun j =>
    Mono.degreeOf (remainingVar i j) monomial

/-- All mixed-radix weights, computed in one left-to-right pass. -/
def kroneckerWeights (mainDegree : Nat)
    (sideDegrees : Fin n → Nat) : List Nat :=
  weightScan (kroneckerBounds mainDegree sideDegrees) 1

/-- Dot product of equal-shape digit and weight lists.  The total fallback
truncates only for malformed direct calls; `kroneckerWeights` and
`kroneckerDigits` always have the same length. -/
def weightedSum : List Nat → List Nat → Nat
  | weight :: weights, digit :: digits =>
      digit * weight + weightedSum weights digits
  | _, _ => 0

/-- Mixed-radix weight of side variable `j`.  The factor `mainDegree + 1`
is deliberately present: without it the main variable and the first side
variable would both map to the same univariate monomial. -/
def kroneckerWeight (mainDegree : Nat) (sideDegrees : Fin n → Nat)
    (j : Fin n) : Nat :=
  (kroneckerWeights mainDegree sideDegrees).getD (j.val + 1) 1

/-- Exponent of a monomial with the side-variable weights already tabulated. -/
def kroneckerExponentWith (i : Fin (n + 1)) (weights : List Nat)
    (monomial : Mono (n + 1)) : Nat :=
  weightedSum weights (kroneckerDigits i monomial)

/-- Exponent of a monomial under the mixed-radix Kronecker substitution. -/
def kroneckerExponent (i : Fin (n + 1)) (mainDegree : Nat)
    (sideDegrees : Fin n → Nat) (monomial : Mono (n + 1)) : Nat :=
  kroneckerExponentWith i (kroneckerWeights mainDegree sideDegrees) monomial

/-! # Mixed-radix injectivity -/

/-- Horner form of a mixed-radix digit string. -/
private def radixCode : List Nat → List Nat → Nat
  | bound :: bounds, digit :: digits =>
      digit + (bound + 1) * radixCode bounds digits
  | _, _ => 0

/-- The digit list has the same shape as its bounds and lies inside them. -/
private def DigitsBounded : List Nat → List Nat → Prop
  | [], [] => True
  | bound :: bounds, digit :: digits =>
      digit ≤ bound ∧ DigitsBounded bounds digits
  | _, _ => False

/-- The precomputed-weight dot product is the corresponding Horner code. -/
private theorem weightedSum_weightScan (bounds digits : List Nat)
    (weight : Nat) (hlen : bounds.length = digits.length) :
    weightedSum (weightScan bounds weight) digits =
      weight * radixCode bounds digits := by
  induction bounds generalizing digits weight with
  | nil =>
      cases digits <;> simp_all [weightScan, weightedSum, radixCode]
  | cons bound bounds ih =>
      cases digits with
      | nil => simp at hlen
      | cons digit digits =>
          have hlen' : bounds.length = digits.length := by
            simp only [List.length_cons] at hlen
            omega
          rw [weightScan, weightedSum, radixCode,
            ih digits (weight * (bound + 1)) hlen']
          simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
          rw [← Nat.mul_assoc, Nat.mul_comm bound weight, Nat.mul_assoc]

/-- Horner mixed-radix coding is injective on bounded digit strings. -/
private theorem radixCode_inj {bounds xs ys : List Nat}
    (hx : DigitsBounded bounds xs) (hy : DigitsBounded bounds ys)
    (hcode : radixCode bounds xs = radixCode bounds ys) : xs = ys := by
  induction bounds generalizing xs ys with
  | nil =>
      cases xs <;> cases ys <;> simp_all [DigitsBounded]
  | cons bound bounds ih =>
      cases xs with
      | nil => simp [DigitsBounded] at hx
      | cons x xs =>
          cases ys with
          | nil => simp [DigitsBounded] at hy
          | cons y ys =>
              have hx' : x ≤ bound ∧ DigitsBounded bounds xs := hx
              have hy' : y ≤ bound ∧ DigitsBounded bounds ys := hy
              have hxlt : x < bound + 1 := by omega
              have hylt : y < bound + 1 := by omega
              have hmod := congrArg (fun value => value % (bound + 1)) hcode
              have hxy : x = y := by
                simpa [radixCode, Nat.mod_eq_of_lt hxlt,
                  Nat.mod_eq_of_lt hylt] using hmod
              subst y
              have hdiv := congrArg (fun value => value / (bound + 1)) hcode
              have htail : radixCode bounds xs = radixCode bounds ys := by
                simpa [radixCode, Nat.div_eq_of_lt hxlt,
                  Nat.add_mul_div_left, Nat.succ_pos] using hdiv
              rw [ih hx'.2 hy'.2 htail]

/-- Pointwise bounds give a bounded mapped digit string. -/
private theorem digitsBounded_map (js : List (Fin n))
    (bounds digits : Fin n → Nat)
    (h : ∀ j, j ∈ js → digits j ≤ bounds j) :
    DigitsBounded (js.map bounds) (js.map digits) := by
  induction js with
  | nil => simp [DigitsBounded]
  | cons j js ih =>
      simp only [List.map_cons, DigitsBounded]
      exact ⟨h j (by simp), ih fun k hk => h k (by simp [hk])⟩

/-- A monomial lies inside the degree box used by the Kronecker bound. -/
def InDegreeBox (i : Fin (n + 1)) (mainDegree : Nat)
    (sideDegrees : Fin n → Nat) (monomial : Mono (n + 1)) : Prop :=
  Mono.degreeOf i monomial ≤ mainDegree ∧
    ∀ j, Mono.degreeOf (remainingVar i j) monomial ≤ sideDegrees j

/-- Corrected mixed-radix substitution is injective on its degree box. -/
theorem kroneckerExponent_inj (i : Fin (n + 1)) (mainDegree : Nat)
    (sideDegrees : Fin n → Nat) {a b : Mono (n + 1)}
    (ha : InDegreeBox i mainDegree sideDegrees a)
    (hb : InDegreeBox i mainDegree sideDegrees b)
    (hcode : kroneckerExponent i mainDegree sideDegrees a =
      kroneckerExponent i mainDegree sideDegrees b) : a = b := by
  have hla :
      (kroneckerBounds mainDegree sideDegrees).length =
        (kroneckerDigits i a).length := by
    simp [kroneckerBounds, kroneckerDigits]
  have hlb :
      (kroneckerBounds mainDegree sideDegrees).length =
        (kroneckerDigits i b).length := by
    simp [kroneckerBounds, kroneckerDigits]
  have hcode' :
      radixCode (kroneckerBounds mainDegree sideDegrees)
          (kroneckerDigits i a) =
        radixCode (kroneckerBounds mainDegree sideDegrees)
          (kroneckerDigits i b) := by
    simpa [kroneckerExponent, kroneckerExponentWith, kroneckerWeights,
      weightedSum_weightScan _ _ 1 hla,
      weightedSum_weightScan _ _ 1 hlb] using hcode
  have hba : DigitsBounded (kroneckerBounds mainDegree sideDegrees)
      (kroneckerDigits i a) := by
    simp only [kroneckerBounds, kroneckerDigits, DigitsBounded]
    exact ⟨ha.1, digitsBounded_map _ _ _ fun j _ => ha.2 j⟩
  have hbb : DigitsBounded (kroneckerBounds mainDegree sideDegrees)
      (kroneckerDigits i b) := by
    simp only [kroneckerBounds, kroneckerDigits, DigitsBounded]
    exact ⟨hb.1, digitsBounded_map _ _ _ fun j _ => hb.2 j⟩
  have hdigits := radixCode_inj hba hbb hcode'
  have hmain : Mono.degreeOf i a = Mono.degreeOf i b :=
    (List.cons.inj hdigits).1
  have hsides :
      (List.finRange n).map
          (fun j => Mono.degreeOf (remainingVar i j) a) =
        (List.finRange n).map
          (fun j => Mono.degreeOf (remainingVar i j) b) :=
    (List.cons.inj hdigits).2
  have hside (j : Fin n) :
      Mono.degreeOf (remainingVar i j) a =
        Mono.degreeOf (remainingVar i j) b :=
    (List.map_inj_left.mp hsides) j (List.mem_finRange j)
  apply Vector.ext
  intro k hk
  let j : Fin (n + 1) := ⟨k, hk⟩
  change Mono.degreeOf j a = Mono.degreeOf j b
  by_cases hji : j = i
  · simpa [hji] using hmain
  · have h := hside (remainingIndex i j hji)
    simpa using h

/-- Degree of the sparse Kronecker image with its weights already tabulated. -/
def kroneckerDegreeWith (i : Fin (n + 1)) (weights : List Nat)
    (p : MvPoly (n + 1) Int cmp) : Nat :=
  p.foldTerms
    (fun degree monomial _ =>
      max degree (kroneckerExponentWith i weights monomial)) 0

/-- Degree of the sparse Kronecker image, computed without materialising its
dense zero gaps. -/
def kroneckerDegree (i : Fin (n + 1)) (mainDegree : Nat)
    (sideDegrees : Fin n → Nat) (p : MvPoly (n + 1) Int cmp) : Nat :=
  kroneckerDegreeWith i (kroneckerWeights mainDegree sideDegrees) p

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
  let weights := kroneckerWeights mainDegree sideDegrees
  let degree := kroneckerDegreeWith inp.setup.main weights shifted
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
