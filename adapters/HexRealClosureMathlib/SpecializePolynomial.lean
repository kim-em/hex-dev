/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Specialize

public section

namespace Hex.RealClosure.Specialize

attribute [local instance 2000] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute one ordinary parameter into the stored coefficients of an outer
polynomial. Normalization retains the actual specialized degree; no global
zero-reflecting map of the infinitesimal coefficient field is assumed. -/
@[expose] noncomputable def polynomial (embedding : F →+* ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (t : ℝ) : Hex.DensePoly ℝ := by
  classical
  exact Hex.DensePoly.ofCoeffs (p.toArray.map (fun a => evalMapped embedding a t))

/-- Every specialized coefficient is the evaluation of its actual native
fraction, including implicit zero coefficients beyond the stored array. -/
theorem polynomial_coeff (embedding : F →+* ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (t : ℝ) (i : Nat) :
    (polynomial embedding p t).coeff i = evalMapped embedding (p.coeff i) t := by
  classical
  rw [polynomial, Hex.DensePoly.coeff_ofCoeffs]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : p.toArray[i]? with
  | none =>
    have zero : p.coeff i = 0 := by
      rw [← Hex.DensePoly.toArray_getD, Array.getD_eq_getD_getElem?, h]
      rfl
    simp only [Option.map_none, Option.getD_none, zero, evalMapped_zero]
    rfl
  | some a =>
    have coefficient : p.coeff i = a := by
      rw [← Hex.DensePoly.toArray_getD, Array.getD_eq_getD_getElem?, h]
      rfl
    simp only [Option.map_some, Option.getD_some, coefficient]

/-- Zero reflection is needed only for the finitely stored coefficients of
this polynomial. Coefficients outside that array specialize to zero directly. -/
theorem polynomial_zero (embedding : F →+* ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (t : ℝ)
    (reflects : ∀ i < p.size, evalMapped embedding (p.coeff i) t = 0 ↔ p.coeff i = 0) :
    polynomial embedding p t = 0 ↔ p = 0 := by
  classical
  constructor
  · intro zero
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [Hex.DensePoly.coeff_zero]
    by_cases hi : i < p.size
    · apply (reflects i hi).mp
      rw [← polynomial_coeff, zero, Hex.DensePoly.coeff_zero]
    · exact Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hi)
  · intro zero
    subst p
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [polynomial_coeff, Hex.DensePoly.coeff_zero, evalMapped_zero, Hex.DensePoly.coeff_zero]

/-- Preserving zero/nonzero for the stored coefficients preserves the actual
native degree. This does not assume global zero reflection for all fractions. -/
theorem polynomial_degree (embedding : F →+* ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (t : ℝ)
    (reflects : ∀ i < p.size, evalMapped embedding (p.coeff i) t = 0 ↔ p.coeff i = 0) :
    (polynomial embedding p t).natDegree = p.natDegree := by
  classical
  by_cases hp : p = 0
  · rw [hp, (polynomial_zero embedding 0 t (by simp)).mpr rfl,
      Hex.DensePoly.natDegree_zero]
    rfl
  · have positive : 0 < p.size := Nat.pos_of_ne_zero (fun h => hp ((Hex.DensePoly.size_eq_zero_iff p).mp h))
    rw [← HexPolyMathlib.natDegree_toPolynomial, Hex.DensePoly.natDegree_eq_size_sub_one]
    apply le_antisymm
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      rw [HexPolyMathlib.coeff_toPolynomial, polynomial_coeff,
        Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)]
      change evalMapped embedding (0 : Hex.RationalFn F) t = 0
      exact evalMapped_zero embedding t
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [HexPolyMathlib.coeff_toPolynomial, polynomial_coeff]
      exact (reflects (p.size - 1) (by omega)).not.mpr
        (Hex.DensePoly.coeff_last_ne_zero_of_pos_size p positive)

/-- The actual leading coefficient specializes to the original leading
coefficient whenever the finite coefficient zero pattern is preserved. -/
theorem polynomial_leading (embedding : F →+* ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (t : ℝ)
    (reflects : ∀ i < p.size, evalMapped embedding (p.coeff i) t = 0 ↔ p.coeff i = 0) :
    (polynomial embedding p t).leadingCoeff = evalMapped embedding p.leadingCoeff t := by
  classical
  have leading : p.coeff p.natDegree = p.leadingCoeff := by
    rw [← HexPolyMathlib.coeff_toPolynomial, ← HexPolyMathlib.natDegree_toPolynomial,
      ← Polynomial.leadingCoeff, HexPolyMathlib.leadingCoeff_toPolynomial]
  rw [← HexPolyMathlib.leadingCoeff_toPolynomial, Polynomial.leadingCoeff,
    HexPolyMathlib.natDegree_toPolynomial, HexPolyMathlib.coeff_toPolynomial,
    polynomial_degree embedding p t reflects, polynomial_coeff, leading]

private theorem sign_zero (a : ℝ) : (SignType.sign a : Int) = 0 ↔ a = 0 := by
  rw [← _root_.sign_eq_zero_iff (a := a)]
  cases SignType.sign a <;> decide

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- Agreement with the actual infinitesimal sign reflects zero for this one
fraction. No claim is made about coefficients outside the recorded family. -/
theorem fraction_zero (embedding : F →+* ℝ) (fraction : Hex.RationalFn F) (t : ℝ)
    (agrees : (SignType.sign (evalMapped embedding fraction t) : Int) =
      Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign fraction) :
    evalMapped embedding fraction t = 0 ↔ fraction = 0 := by
  rw [← sign_zero, agrees, Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff]

/-- A common positive neighborhood preserves the stored polynomial's
coefficient signs, coefficient denominator guards, zero status and degree.
Only its finite coefficient array enters the sign family. -/
theorem polynomial_signs (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (p : Hex.DensePoly (Hex.RationalFn F)) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      (∀ i < p.size,
        ((HexPolyMathlib.toPolynomial (p.coeff i).den).map embedding).eval t ≠ 0 ∧
        (SignType.sign ((polynomial embedding p t).coeff i) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign (p.coeff i)) ∧
      (polynomial embedding p t = 0 ↔ p = 0) ∧
      (polynomial embedding p t).natDegree = p.natDegree := by
  classical
  let fractions := p.toArray.toList.toFinset
  obtain ⟨η, positive, signs⟩ := finite_fractions_map embedding ordered fractions
  refine ⟨η, positive, fun t ht small => ?_⟩
  have member (i : Nat) (hi : i < p.size) : p.coeff i ∈ fractions := by
    have hi' : i < p.toArray.size := by simpa using hi
    have entry : p.toArray[i]? = some (p.coeff i) := by
      rw [Array.getElem?_eq_getElem hi', ← Hex.DensePoly.toArray_getD]
      congr 1
      exact Array.getElem_eq_getD (h := hi') 0
    exact List.mem_toFinset.mpr (by simpa using Array.mem_of_getElem? entry)
  have agrees (i : Nat) (hi : i < p.size) := signs t ht small (p.coeff i) (member i hi)
  have reflects (i : Nat) (hi : i < p.size) :=
    fraction_zero embedding (p.coeff i) t (agrees i hi).2
  refine ⟨?_, polynomial_zero embedding p t reflects, polynomial_degree embedding p t reflects⟩
  intro i hi
  rw [polynomial_coeff]
  exact agrees i hi

/-- info: 'Hex.RealClosure.Specialize.polynomial_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_coeff

/-- info: 'Hex.RealClosure.Specialize.polynomial_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_zero

/-- info: 'Hex.RealClosure.Specialize.polynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_degree

/-- info: 'Hex.RealClosure.Specialize.polynomial_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_leading

/-- info: 'Hex.RealClosure.Specialize.fraction_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.fraction_zero

/-- info: 'Hex.RealClosure.Specialize.polynomial_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_signs

end Hex.RealClosure.Specialize
