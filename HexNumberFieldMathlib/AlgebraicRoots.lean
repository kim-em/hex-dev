/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.ComponentRoots
public import HexNumberFieldMathlib.PresentationSemantics

public section

/-!
# Algebraic-coefficient root semantics

Transport of the fixed-field root contracts across the checked primitive
presentation of an algebraic coefficient array.
-/

namespace Hex.AlgebraicPoly

private theorem exists_nonzero_coeff (f : AlgebraicPoly)
    (hf : f.isZero = false) :
    ∃ a ∈ f.coeffs.toList, a.isZero = false := by
  have hsize : 0 < f.coeffs.size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hempty : f.coeffs = #[] := Array.eq_empty_of_size_eq_zero hzero
    change f.data = #[] at hempty
    have : f.isZero = true := by simp [AlgebraicPoly.isZero, hempty]
    simp [hf] at this
  let a := f.coeff (f.size - 1)
  have hi : f.size - 1 < f.coeffs.size := by
    change f.coeffs.size - 1 < f.coeffs.size
    omega
  have ha : f.coeffs[f.size - 1] = a := by
    rw [Array.getElem_eq_getD]
    rfl
  have haMem : a ∈ f.coeffs.toList := by
    apply Array.mem_toList_iff.mpr
    rw [Array.mem_iff_getElem]
    exact ⟨f.size - 1, hi, ha⟩
  refine ⟨a, haMem, ?_⟩
  exact last_isZero_false f (by simp [hf])

private theorem exists_presentation (f : AlgebraicPoly)
    (hf : f.isZero = false) :
    ∃ common, Common.presentation? f.coeffs = some common := by
  exact Option.isSome_iff_exists.mp <|
    Common.presentation?_isSome f.coeffs (exists_nonzero_coeff f hf)

/-- The algebraic-coefficient root driver always produces a checked root set. -/
theorem roots?_isSome (f : AlgebraicPoly) :
    f.roots?.isSome := by
  rw [AlgebraicPoly.roots?]
  split
  · simp
  next hzero =>
    have hf : f.isZero = false := by
      cases h : f.isZero <;> simp_all
    obtain ⟨common, hcommon⟩ := exists_presentation f hf
    rw [hcommon]
    letI : ZPoly.CheckedIrreducible common.generator.p :=
      common.generator.checked
    exact QAdjoin.roots?_isSome
      (DensePoly.ofCoeffs common.coefficients)
      common.generator.rep common.generator.rep_mk

/-- The total algebraic-coefficient root API is exactly the output of its
checked driver. -/
theorem roots?_eq_roots (f : AlgebraicPoly) :
    f.roots? = some f.roots := by
  unfold AlgebraicPoly.roots
  cases hrun : f.roots? with
  | none =>
      have hsome := roots?_isSome f
      simp [hrun] at hsome
  | some roots => simp

private theorem presentation_polynomial (f : AlgebraicPoly)
    (common : Common.Presentation)
    (hcommon : Common.presentation? f.coeffs = some common) :
    QAdjoin.toPolynomialAt
        (DensePoly.ofCoeffs common.coefficients)
        common.generator.rep common.generator.rep_mk =
      f.toPolynomial := by
  letI : ZPoly.CheckedIrreducible common.generator.p :=
    common.generator.checked
  obtain ⟨hsize, hvalues⟩ :=
    Common.presentation?_sound f.coeffs hcommon
  ext n
  rw [QAdjoin.coeff_toPolynomialAt, coeff_toPolynomial,
    DensePoly.coeff_ofCoeffs]
  change QAdjoin.toComplex
      (common.coefficients.getD n
        (0 : QAdjoin common.generator.p common.generator.x))
      common.generator.rep common.generator.rep_mk =
    (f.coeffs.getD n (0 : AlgebraicNumber)).toComplex
  by_cases hn : n < f.coeffs.size
  · have hnCommon : n < common.coefficients.size := by
      rw [hsize]
      exact hn
    rw [← Array.getElem_eq_getD
        (0 : QAdjoin common.generator.p common.generator.x),
      ← Array.getElem_eq_getD (0 : AlgebraicNumber)]
    exact hvalues n hn hnCommon
  · have hnCommon : ¬n < common.coefficients.size := by
      rw [hsize]
      exact hn
    rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by omega : common.coefficients.size ≤ n),
      Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by omega : f.coeffs.size ≤ n)]
    simp [QAdjoin.map_zero, AlgebraicNumber.zero_toComplex]

private theorem roots_eq_fixed (f : AlgebraicPoly)
    (common : Common.Presentation)
    (hf : f.isZero = false)
    (hcommon : Common.presentation? f.coeffs = some common) :
    f.roots = @QAdjoin.roots _ _ common.generator.checked
      (DensePoly.ofCoeffs common.coefficients)
      common.generator.rep common.generator.rep_mk := by
  letI : ZPoly.CheckedIrreducible common.generator.p :=
    common.generator.checked
  have halgebraic := roots?_eq_roots f
  rw [AlgebraicPoly.roots?, if_neg (by simp [hf])] at halgebraic
  obtain ⟨common', hcommon', hrun⟩ :=
    Option.bind_eq_some_iff.mp halgebraic
  have hcommonEq : common' = common :=
    Option.some.inj (hcommon'.symm.trans hcommon)
  subst common'
  have hfixed := QAdjoin.roots?_eq_roots
    (DensePoly.ofCoeffs common.coefficients)
    common.generator.rep common.generator.rep_mk
  exact (Option.some.inj (hfixed.symm.trans hrun)).symm

private theorem roots_eq_all_of_isZero (f : AlgebraicPoly)
    (hf : f.isZero = true) : f.roots = .all := by
  have hrun := roots?_eq_roots f
  rw [AlgebraicPoly.roots?, if_pos hf] at hrun
  exact (Option.some.inj hrun).symm

/-- The algebraic-coefficient driver returns `.all` exactly for the zero
polynomial. -/
theorem roots_all_iff (f : AlgebraicPoly) :
    f.roots = .all ↔ f.toPolynomial = 0 := by
  by_cases hzero : f.isZero = true
  · rw [roots_eq_all_of_isZero f hzero,
      (isZero_iff f).mp hzero]
    simp
  · have hf : f.isZero = false := by
      cases h : f.isZero <;> simp_all
    obtain ⟨common, hcommon⟩ := exists_presentation f hf
    letI : ZPoly.CheckedIrreducible common.generator.p :=
      common.generator.checked
    rw [roots_eq_fixed f common hf hcommon,
      ← presentation_polynomial f common hcommon]
    exact QAdjoin.roots_all_iff
      (DensePoly.ofCoeffs common.coefficients)
      common.generator.rep common.generator.rep_mk

/-- Semantic membership in the algebraic-coefficient output is exactly
polynomial vanishing. -/
theorem contains_roots_iff (f : AlgebraicPoly) (z : ℂ) :
    RootSet.Contains f.roots z ↔
      Polynomial.eval z f.toPolynomial = 0 := by
  by_cases hzero : f.isZero = true
  · rw [roots_eq_all_of_isZero f hzero,
      (isZero_iff f).mp hzero]
    simp [RootSet.Contains]
  · have hf : f.isZero = false := by
      cases h : f.isZero <;> simp_all
    obtain ⟨common, hcommon⟩ := exists_presentation f hf
    letI : ZPoly.CheckedIrreducible common.generator.p :=
      common.generator.checked
    rw [roots_eq_fixed f common hf hcommon,
      ← presentation_polynomial f common hcommon]
    exact QAdjoin.contains_roots_iff
      (DensePoly.ofCoeffs common.coefficients)
      common.generator.rep common.generator.rep_mk z

/-- Algebraic-coefficient root multiplicities agree with Mathlib. -/
theorem multiplicity_roots (f : AlgebraicPoly) (z : ℂ) :
    f.roots.multiplicityOf z =
      Polynomial.rootMultiplicity z f.toPolynomial := by
  by_cases hzero : f.isZero = true
  · rw [roots_eq_all_of_isZero f hzero,
      (isZero_iff f).mp hzero]
    simp [RootSet.multiplicityOf]
  · have hf : f.isZero = false := by
      cases h : f.isZero <;> simp_all
    obtain ⟨common, hcommon⟩ := exists_presentation f hf
    letI : ZPoly.CheckedIrreducible common.generator.p :=
      common.generator.checked
    rw [roots_eq_fixed f common hf hcommon,
      ← presentation_polynomial f common hcommon]
    exact QAdjoin.multiplicity_roots
      (DensePoly.ofCoeffs common.coefficients)
      common.generator.rep common.generator.rep_mk z

/-- The algebraic-coefficient driver produces positive multiplicities. -/
theorem roots_positive (f : AlgebraicPoly) :
    RootSet.Positive f.roots := by
  cases hroots : f.roots with
  | all => trivial
  | finite roots =>
      intro entry _hentry
      exact entry.multiplicity_pos

/-- The algebraic-coefficient driver merges all semantic duplicates. -/
theorem roots_noDuplicates (f : AlgebraicPoly) :
    RootSet.NoDuplicates f.roots := by
  by_cases hzero : f.isZero = true
  · rw [roots_eq_all_of_isZero f hzero]
    trivial
  · have hf : f.isZero = false := by
      cases h : f.isZero <;> simp_all
    obtain ⟨common, hcommon⟩ := exists_presentation f hf
    letI : ZPoly.CheckedIrreducible common.generator.p :=
      common.generator.checked
    rw [roots_eq_fixed f common hf hcommon]
    exact QAdjoin.roots_noDuplicates
      (DensePoly.ofCoeffs common.coefficients)
      common.generator.rep common.generator.rep_mk

/-- The algebraic-coefficient driver uses its deterministic canonical order. -/
theorem roots_ordered (f : AlgebraicPoly) :
    RootSet.Ordered f.roots := by
  by_cases hzero : f.isZero = true
  · rw [roots_eq_all_of_isZero f hzero]
    trivial
  · have hf : f.isZero = false := by
      cases h : f.isZero <;> simp_all
    obtain ⟨common, hcommon⟩ := exists_presentation f hf
    letI : ZPoly.CheckedIrreducible common.generator.p :=
      common.generator.checked
    rw [roots_eq_fixed f common hf hcommon]
    exact QAdjoin.roots_ordered
      (DensePoly.ofCoeffs common.coefficients)
      common.generator.rep common.generator.rep_mk

/-- For a nonzero algebraic-coefficient polynomial, output multiplicities sum
to its degree. -/
theorem totalMultiplicity_roots (f : AlgebraicPoly)
    (hfPolynomial : f.toPolynomial ≠ 0) :
    f.roots.totalMultiplicity = f.toPolynomial.natDegree := by
  have hf : f.isZero = false := by
    cases h : f.isZero with
    | false => rfl
    | true =>
        exact (hfPolynomial ((isZero_iff f).mp h)).elim
  obtain ⟨common, hcommon⟩ := exists_presentation f hf
  letI : ZPoly.CheckedIrreducible common.generator.p :=
    common.generator.checked
  have hpolynomial := presentation_polynomial f common hcommon
  rw [roots_eq_fixed f common hf hcommon, ← hpolynomial]
  exact QAdjoin.totalMultiplicity_roots
    (DensePoly.ofCoeffs common.coefficients)
    common.generator.rep common.generator.rep_mk
    (by rwa [hpolynomial])

end Hex.AlgebraicPoly

/-! The algebraic-coefficient contracts must not inherit unfinished proofs. -/

/--
info: 'Hex.AlgebraicPoly.roots?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.AlgebraicPoly.roots?_isSome

/--
info: 'Hex.AlgebraicPoly.roots_all_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.AlgebraicPoly.roots_all_iff

/--
info: 'Hex.AlgebraicPoly.contains_roots_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.AlgebraicPoly.contains_roots_iff

/--
info: 'Hex.AlgebraicPoly.multiplicity_roots' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.AlgebraicPoly.multiplicity_roots

/--
info: 'Hex.AlgebraicPoly.roots_noDuplicates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.AlgebraicPoly.roots_noDuplicates

/--
info: 'Hex.AlgebraicPoly.roots_ordered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.AlgebraicPoly.roots_ordered

/--
info: 'Hex.AlgebraicPoly.totalMultiplicity_roots' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.AlgebraicPoly.totalMultiplicity_roots
