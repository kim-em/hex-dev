/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealClosure.Yun
public import HexPolyMathlib.Euclid
public import Mathlib.FieldTheory.Separable

public section

/-!
# Mathematical interpretation of Yun replay

The executable replay's gcd checks imply separability of each emitted rational
factor. This does not assert that every result produced by the Yun recurrence
passes replay.
-/

namespace Hex.RealClosure.Yun

/-- Convert powers without assuming a Mathlib monoid instance on `DensePoly`. -/
private theorem toPolynomial_pow (p : DensePoly Rat) (n : Nat) :
    HexPolyMathlib.toPolynomial (p ^ n) =
      (HexPolyMathlib.toPolynomial p) ^ n := by
  induction n with
  | zero => simp only [Lean.Grind.Semiring.pow_zero,
      HexPolyMathlib.toPolynomial_one]
  | succ n ih =>
      rw [Lean.Grind.Semiring.pow_succ, HexPolyMathlib.toPolynomial_mul,
        ih, pow_succ]

/-- Executable reconstruction agrees with multiplication of rational
polynomials. -/
theorem toPolynomial_reconstruct (unit : Rat)
    (entries : Array (DensePoly Rat × Nat)) :
    HexPolyMathlib.toPolynomial (reconstruct unit entries) =
      entries.toList.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (Polynomial.C unit) := by
  have hfold (l : List (DensePoly Rat × Nat)) (acc : DensePoly Rat) :
      HexPolyMathlib.toPolynomial
        (l.foldl (fun product entry => product * entry.1 ^ entry.2) acc) =
      l.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (HexPolyMathlib.toPolynomial acc) := by
    induction l generalizing acc with
    | nil => rfl
    | cons entry rest ih =>
        simpa only [List.foldl_cons, HexPolyMathlib.toPolynomial_mul,
          toPolynomial_pow] using
          ih (acc * entry.1 ^ entry.2)
  simpa only [reconstruct, ← Array.foldl_toList,
    HexPolyMathlib.toPolynomial_C] using
    hfold entries.toList (DensePoly.C unit)

/-- A replay-accepted result has the same product in Mathlib polynomials. -/
theorem check_product_polynomial (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (h : check f (.factors unit entries) = true) :
    HexPolyMathlib.toPolynomial f =
      entries.toList.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (Polynomial.C unit) := by
  rw [← toPolynomial_reconstruct,
    (check_reconstruct f unit entries h).1]

/-- A constant executable gcd maps to a unit gcd over `Rat`. -/
private theorem gcd_isUnit (p q : DensePoly Rat)
    (hp : p ≠ 0) (hdegree : (DensePoly.gcd p q).natDegree = 0) :
    IsUnit (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial p)
      (HexPolyMathlib.toPolynomial q)) := by
  let G := EuclideanDomain.gcd (HexPolyMathlib.toPolynomial p)
    (HexPolyMathlib.toPolynomial q)
  have hmap : HexPolyMathlib.toPolynomial p ≠ 0 := by
    intro hzero
    apply hp
    have h := congrArg HexPolyMathlib.ofPolynomial hzero
    simpa using h
  have hassociated : Associated
      (HexPolyMathlib.toPolynomial (DensePoly.gcd p q)) G :=
    HexPolyMathlib.toPolynomial_gcd_associated p q
  have hGzero : G ≠ 0 := by
    intro hzero
    exact hmap (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hdegreeG : G.natDegree = 0 := by
    have hdegreeAssoc := Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassociated)
    have hgmap : (HexPolyMathlib.toPolynomial (DensePoly.gcd p q)).natDegree = 0 := by
      simpa [HexPolyMathlib.natDegree_toPolynomial] using hdegree
    rw [hdegreeAssoc] at hgmap
    exact hgmap
  rw [Polynomial.isUnit_iff_degree_eq_zero,
    Polynomial.degree_eq_natDegree hGzero]
  exact_mod_cast hdegreeG

/-- A rational factor accepted by replay is separable. -/
theorem check_factor_separable (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (entry : DensePoly Rat × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) :
    (HexPolyMathlib.toPolynomial entry.1).Separable := by
  obtain ⟨_, hdegree, _, hgcd⟩ :=
    check_factor f unit entries entry hmem h
  have hp : entry.1 ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  have hGunit := gcd_isUnit entry.1
    (DensePoly.derivativeImpl entry.1) hp hgcd
  exact (Polynomial.separable_def _).2
    (EuclideanDomain.gcd_isUnit_iff.mp (by
      simpa [← DensePoly.derivative_eq_derivativeImpl,
        HexPolyMathlib.toPolynomial_derivative] using hGunit))

/-- Every accepted rational factor is squarefree. -/
theorem check_factor_squarefree (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (entry : DensePoly Rat × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) :
    Squarefree (HexPolyMathlib.toPolynomial entry.1) :=
  (check_factor_separable f unit entries entry hmem h).squarefree

/-- Accepted replay factors are pairwise coprime as mathematical polynomials. -/
theorem check_pairwise_coprime (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (h : check f (.factors unit entries) = true) :
    entries.toList.Pairwise (fun a b =>
      IsCoprime (HexPolyMathlib.toPolynomial a.1)
        (HexPolyMathlib.toPolynomial b.1)) := by
  apply (check_coprime f unit entries h).imp_of_mem
  intro a b ha _ hab
  have ha : a ∈ entries := Array.mem_toList_iff.mp ha
  have hdegree := (check_factor f unit entries a ha h).2.1
  have hnonzero : a.1 ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  exact EuclideanDomain.gcd_isUnit_iff.mp
    (gcd_isUnit a.1 b.1 hnonzero hab)

end Hex.RealClosure.Yun

/-- info: 'Hex.RealClosure.Yun.check_product_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_product_polynomial
/-- info: 'Hex.RealClosure.Yun.check_factor_separable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_factor_separable
/-- info: 'Hex.RealClosure.Yun.check_pairwise_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_pairwise_coprime
