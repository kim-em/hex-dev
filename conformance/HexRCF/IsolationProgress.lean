/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients

namespace Hex.RCF.IsolationProgressTests

open RealCoefficients

-- Close exact roots cannot be accepted while their strict intervals overlap.
private def closeHead : DensePoly RealAlgebraicNumber :=
  DensePoly.ofCoeffs #[0, RealAlgebraicNumber.ofRat (-1 / 4), 1]
#guard (isolateAt () closeHead 0).isNone
#guard ((isolateAt () closeHead 6).map (fun cert => cert.isolations.intervals.size)) == some 2

-- The total search must advance past the rejected precision zero above.
private theorem closePolynomial : HexPolyMathlib.Interpret.interpret
    RealAlgebraicNumber.toReal algebraic_zero closeHead =
      Polynomial.X * (Polynomial.X - Polynomial.C (1 / 4 : ℝ)) := by
  rw [mul_sub, ← pow_two, mul_comm (Polynomial.X : Polynomial ℝ) (Polynomial.C _)]
  ext i
  rw [HexPolyMathlib.Interpret.coeff_interpret]
  by_cases small : i ≤ 2
  · interval_cases i <;> norm_num [closeHead, DensePoly.coeff_ofCoeffs,
      Array.getD_eq_getD_getElem?, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  · have large : 3 ≤ i := by omega
    have absent : [(0 : RealAlgebraicNumber), RealAlgebraicNumber.ofRat (-1 / 4), 1][i]? = none :=
      List.getElem?_eq_none (by simpa using large)
    simp [closeHead, DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?, absent,
      Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      show i ≠ 2 by omega, show 1 ≠ i by omega]
    exact RealAlgebraicNumber.zero_toReal
private theorem closeSquarefree : Squarefree (HexPolyMathlib.Interpret.interpret
    RealAlgebraicNumber.toReal algebraic_zero closeHead) := by
  rw [closePolynomial]
  have distinct : IsUnit ((0 : ℝ) - 1 / 4) := (by norm_num : (0 : ℝ) - 1 / 4 ≠ 0).isUnit
  have coprime := Polynomial.isCoprime_X_sub_C_of_isUnit_sub distinct
  simp only [Polynomial.C_0, sub_zero] at coprime
  exact (Polynomial.separable_X.mul Polynomial.separable_X_sub_C coprime).squarefree
private theorem closeNonzero : closeHead ≠ 0 := by
  intro zero
  have interpreted := congrArg (HexPolyMathlib.Interpret.interpret
    RealAlgebraicNumber.toReal algebraic_zero) zero
  exact closeSquarefree.ne_zero (by simpa using interpreted)
#guard (isolate () closeHead closeNonzero closeSquarefree).val.isolations.intervals.size == 2

-- Constants have no root sections, while zero has no finite root list.
#guard ((isolateAt () (DensePoly.C (RealAlgebraicNumber.ofRat 3)) 0).map
  (fun cert => cert.isolations.intervals.size)) == some 0
#guard (isolateAt () (0 : DensePoly RealAlgebraicNumber) 6).isNone

-- The isolation layer requires squarefree input; the separate radical
-- stage owns repeated-root reduction before this layer is used.
#guard (isolateAt () (DensePoly.ofCoeffs #[(0 : RealAlgebraicNumber), 0, 1]) 6).isNone

private instance : SquareTwo.polynomial.CheckedIrreducible := SquareTwo.checked
private abbrev fieldRep := Field.literalRep SquareTwo.polynomial SquareTwo.square
  (by decide) (by decide)
private abbrev fieldRoot := SimpleRoot.mk fieldRep
private def fieldHead : DensePoly (PolyQuot SquareTwo.polynomial fieldRoot) :=
  DensePoly.ofCoeffs #[-SquareTwo.coordinate SquareTwo.square (by decide) (by decide), 0, 1]

-- These root sections are further roots over the selected coefficient field.
#guard ((FieldBuild.proposeCanonical fieldRep rfl fieldHead 8).map
  (fun cert => cert.intervals.size)) == some 2
#guard ((FieldBuild.isolateAt fieldRep rfl () fieldHead 8).map
  (fun cert => cert.isolations.intervals.size)) == some 2

-- A gap below the direct bisection depth forces the canonical fallback.
private def tinyHead : DensePoly (PolyQuot SquareTwo.polynomial fieldRoot) :=
  DensePoly.ofCoeffs #[0, PolyQuot.ofRat (-1 / (2 ^ 132)), 1]
#guard (FieldBuild.buildProposed (FieldBuild.proposalSign fieldRep rfl) () tinyHead
  (FieldIsolate.propose? (FieldBuild.proposalSign fieldRep rfl) FieldDecision.point tinyHead)).isNone
#guard ((FieldBuild.buildProposed (FieldBuild.proposalSign fieldRep rfl) () tinyHead
  (FieldBuild.proposeCanonical fieldRep rfl tinyHead 140)).map
    (fun cert => cert.isolations.intervals.size)) == some 2

-- Repeated atom occurrences still receive their own bound query lookup on
-- every further root, using the producer's shared squarefree chain.
private def formula : RealFormula.QF 1 :=
  .and (.atom ⟨MvPoly.X 0, .lt⟩)
    (.or (.atom ⟨MvPoly.X 0, .eq⟩) (.atom ⟨MvPoly.X 0 ^ 2, .le⟩))
private def query (atom : RealFormula.Poly 1) : DensePoly (PolyQuot SquareTwo.polynomial fieldRoot) :=
  FieldSpecialize.literalPolynomial (fun i : Fin 0 => i.elim0) atom
#guard ((FieldBuild.isolateAt fieldRep rfl () fieldHead 8).map fun cert =>
  (FieldRootSigns.Table.build (FieldBuild.proposalSign fieldRep rfl) FieldDecision.point
    () fieldHead cert query formula).isSome) == some true

-- The total entry points execute the checker search and return its
-- acceptance proof; a constant succeeds immediately without root sections.
#guard (isolate () (1 : DensePoly RealAlgebraicNumber)
  (by
    apply (not_congr (HexPolyMathlib.Interpret.interpret_eq_zero
      RealAlgebraicNumber.toReal algebraic_zero 1)).mp
    rw [HexPolyMathlib.Interpret.interpret_one _ _ RealAlgebraicNumber.one_toReal]
    exact one_ne_zero)
  (by simpa only [(HexPolyMathlib.Interpret.interpret_one RealAlgebraicNumber.toReal
      algebraic_zero RealAlgebraicNumber.one_toReal)]
    using (squarefree_one : Squarefree (1 : Polynomial ℝ)))).val.isolations.intervals.isEmpty

private theorem fieldReal : fieldRep.root.im = 0 :=
  Field.literalRep_real SquareTwo.polynomial SquareTwo.square (by decide) (by decide) (by decide)
#guard (FieldBuild.isolate fieldRep rfl fieldReal ()
  (1 : DensePoly (PolyQuot SquareTwo.polynomial fieldRoot))
  (by
    apply (not_congr (HexPolyMathlib.Interpret.interpret_eq_zero
      (Field.value fieldRep) (Field.value_eq_zero fieldRep rfl fieldReal) 1)).mp
    rw [HexPolyMathlib.Interpret.interpret_one _ _ (Field.value_one fieldRep rfl fieldReal)]
    exact one_ne_zero)
  (by simpa only [(HexPolyMathlib.Interpret.interpret_one (Field.value fieldRep)
      (Field.value_eq_zero fieldRep rfl fieldReal) (Field.value_one fieldRep rfl fieldReal))]
    using (squarefree_one : Squarefree (1 : Polynomial ℝ)))).val.isolations.intervals.isEmpty

end Hex.RCF.IsolationProgressTests

/-- info: 'Hex.RCF.RealCoefficients.IsolationReplay.build_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.IsolationReplay.build_squarefree
/-- info: 'Hex.RCF.RealCoefficients.IsolationReplay.build_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.IsolationReplay.build_success
/-- info: 'Hex.RCF.RealCoefficients.IsolationReplay.build_fromRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.IsolationReplay.build_fromRoots
/-- info: 'Hex.RCF.RealCoefficients.IsolationReplay.queryAt_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.IsolationReplay.queryAt_checked
/-- info: 'Hex.RCF.RealCoefficients.rootInterval_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.rootInterval_separated
/-- info: 'Hex.RCF.RealCoefficients.rootArray_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.rootArray_separated
/-- info: 'Hex.RCF.RealCoefficients.solverIntervals_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.solverIntervals_progress
/-- info: 'Hex.RCF.RealCoefficients.solverIntervals_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.solverIntervals_spec
/-- info: 'Hex.RCF.RealCoefficients.proposeIsolations_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.proposeIsolations_spec
/-- info: 'Hex.RCF.RealCoefficients.proposeIsolations_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.proposeIsolations_separated
/-- info: 'Hex.RCF.RealCoefficients.proposeIsolations_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.proposeIsolations_accepted
/-- info: 'Hex.RCF.RealCoefficients.isolateAt_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.isolateAt_progress
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.canonical_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.canonical_isSome
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.canonical_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.canonical_value
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.proposalSign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.proposalSign_spec
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.canonical_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.canonical_polynomial
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.proposeCanonical_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.proposeCanonical_progress
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.proposeCanonical_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.proposeCanonical_accepted
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.isolateAt_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.isolateAt_progress
/-- info: 'Hex.RCF.RealCoefficients.FieldRootSigns.Table.build_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldRootSigns.Table.build_success

/-- info: 'Hex.RCF.RealCoefficients.isolate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.isolate

/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.isolate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.isolate

/-- info: 'Hex.RCF.RealCoefficients.isolateAt_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.isolateAt_build
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.isolateAt_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.isolateAt_build
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.isolateFormula_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.isolateFormula_queries
