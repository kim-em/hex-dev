/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients

namespace Hex.RCF.AlgebraicProgress

open RealCoefficients

/-- Production cannot drop an exact or irrational root at any precision. -/
theorem interval_total (root : RealAlgebraicNumber) (precision : Nat) :
    (rootInterval root precision).isSome = true := by
  obtain ⟨interval, produced, _, _, _⟩ := rootInterval_spec root precision
  rw [produced]
  rfl

/-- Exact zero still has a strict interval, despite a zero approximation radius. -/
theorem zero_section (precision : Nat) : ∃ interval,
    rootInterval 0 precision = some interval ∧
    HexRealRootsMathlib.Dyadic.toReal interval.lower < 0 ∧
    0 < HexRealRootsMathlib.Dyadic.toReal interval.upper := by
  obtain ⟨interval, produced, hlo, hhi, _⟩ := rootInterval_spec 0 precision
  exact ⟨interval, produced, by simpa using hlo, by simpa using hhi⟩

/-- The canonical proposal API succeeds at every precision for every nonzero head. -/
theorem proposals
    (head : DensePoly RealAlgebraicNumber) (hne : head ≠ 0) (precision : Nat) :
    (proposeIsolations head precision).isSome = true :=
  proposeIsolations_isSome head hne precision

/-- The zero polynomial has universal roots, rather than a finite empty result. -/
theorem zero_proposals (precision : Nat) :
    proposeIsolations (0 : DensePoly RealAlgebraicNumber) precision = none :=
  proposeIsolations_zero precision

/-- Atom cancellation cannot prevent the canonical carrier from proposing cells. -/
theorem carrier_total
    (values : Fin n → RealAlgebraicNumber) (formula : RealFormula.QF (n + 1))
    (precision : Nat) :
    (proposeIsolations (Specialize.product values formula) precision).isSome = true :=
  carrier_proposals values formula precision

/-- A schedule tending to infinity yields arbitrarily narrow real enclosures. -/
theorem enclosure_progress (root : RealAlgebraicNumber)
    (schedule : Nat → Nat) (h : Filter.Tendsto schedule Filter.atTop Filter.atTop)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ K : Nat, ∀ k ≥ K, ∃ interval,
      rootInterval root (schedule k) = some interval ∧
      HexRealRootsMathlib.Dyadic.toReal interval.lower < root.toReal ∧
      root.toReal < HexRealRootsMathlib.Dyadic.toReal interval.upper ∧
      HexRealRootsMathlib.Dyadic.toReal interval.upper -
        HexRealRootsMathlib.Dyadic.toReal interval.lower < epsilon :=
  rootInterval_progress root schedule h epsilon hepsilon

-- Nonzero constants produce the empty finite root list, even at precision zero.
#guard ((proposeIsolations (DensePoly.C (RealAlgebraicNumber.ofRat 3)) 0).map
  (fun cert => cert.intervals.size)) == some 0

private def coordinate : Fin 2 → Rat := fun _ => 3
private def source : RealFormula.Poly 3 :=
  (MvPoly.X 0 - MvPoly.X 1) * MvPoly.X 2 ^ 3 + MvPoly.X 2
private def cancelled : DensePoly Rat := FieldSpecialize.polynomial coordinate source

-- Different parameter coordinates become equal only after specialization.
#guard cancelled.natDegree = 1
#guard cancelled.coeff 1 = 1
#guard cancelled.coeff 3 = 0
#guard (FieldSpecialize.polynomial coordinate (0 : RealFormula.Poly 3)).isZero
#guard (FieldSpecialize.polynomial coordinate (1 : RealFormula.Poly 3)).natDegree = 0

/-- Real interpretation preserves the computed degree after leading cancellation. -/
theorem cancelled_degree :
    ((HexPolyMathlib.toPolynomial cancelled).map (Rat.castHom ℝ)).natDegree =
      cancelled.natDegree :=
  FieldSpecialize.degree (Rat.castHom ℝ) (fun _ => Rat.cast_eq_zero) coordinate source


private abbrev fieldRoot := SimpleRoot.ofSquare SquareTwo.polynomial SquareTwo.square
  (by decide) (by decide)
private instance : SquareTwo.polynomial.CheckedIrreducible := SquareTwo.checked
private def fieldValues : Fin 2 → PolyQuot SquareTwo.polynomial fieldRoot :=
  fun _ => PolyQuot.ofRat 3
private def literalCancelled := FieldSpecialize.literalPolynomial fieldValues source

-- Exercise the executable literal compiler used by FieldBuild, with the
-- native fixed-field dictionary rather than the generic Rat correspondence.
#guard literalCancelled.natDegree = 1
#guard literalCancelled.coeff 1 = (1 : PolyQuot SquareTwo.polynomial fieldRoot)
#guard literalCancelled.coeff 3 = (0 : PolyQuot SquareTwo.polynomial fieldRoot)
#guard (FieldSpecialize.literalPolynomial fieldValues (0 : RealFormula.Poly 3)).isZero
#guard (FieldSpecialize.literalPolynomial fieldValues (1 : RealFormula.Poly 3)).natDegree = 0

private def oppositeValues : Fin 2 → PolyQuot SquareTwo.polynomial fieldRoot :=
  fun i => if i.val = 0 then
    -SquareTwo.coordinate SquareTwo.square (by decide) (by decide)
  else SquareTwo.coordinate SquareTwo.square (by decide) (by decide)
private def cubicSource : RealFormula.Poly 3 :=
  MvPoly.X 0 * MvPoly.X 2 ^ 3 + MvPoly.X 1 * MvPoly.X 2 ^ 3 + MvPoly.X 2 ^ 2
private def cubicFormula : RealFormula.QF 3 := .atom ⟨cubicSource, .le⟩
#guard (FieldSpecialize.literalPolynomial oppositeValues cubicSource).natDegree = 2
#guard (FieldCarrier.product oppositeValues cubicFormula).natDegree = 2

private def negative : RealAlgebraicNumber :=
  Selected.real SquareTwo.polynomial
    ⟨-SquareTwo.square.re, 0, SquareTwo.square.prec⟩ (by decide) (by decide)
    (by rfl) (by decide) (by decide) SquareTwo.checked SquareTwo.squarefree (by decide)

-- The parameter polynomial has degree three. Its leading coefficient cancels
-- only at the authenticated opposite embeddings, leaving the repeated zero root.
theorem leading_cancellation : ∀ x : ℝ,
    negative.toReal * x ^ 3 + Real.sqrt 2 * x ^ 3 + x ^ 2 ≥ 0 := by
  rcf

end Hex.RCF.AlgebraicProgress

/-- info: '_private.HexRCF.AlgebraicProgress.0.Hex.RCF.AlgebraicProgress.interval_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicProgress.interval_total

/-- info: '_private.HexRCF.AlgebraicProgress.0.Hex.RCF.AlgebraicProgress.zero_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicProgress.zero_section

/-- info: '_private.HexRCF.AlgebraicProgress.0.Hex.RCF.AlgebraicProgress.proposals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicProgress.proposals

/-- info: '_private.HexRCF.AlgebraicProgress.0.Hex.RCF.AlgebraicProgress.zero_proposals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicProgress.zero_proposals

/-- info: '_private.HexRCF.AlgebraicProgress.0.Hex.RCF.AlgebraicProgress.enclosure_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicProgress.enclosure_progress

/-- info: '_private.HexRCF.AlgebraicProgress.0.Hex.RCF.AlgebraicProgress.cancelled_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicProgress.cancelled_degree

/-- info: '_private.HexRCF.AlgebraicProgress.0.Hex.RCF.AlgebraicProgress.leading_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicProgress.leading_cancellation

/-- info: 'Hex.RCF.RealCoefficients.rootInterval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.rootInterval_spec

/-- info: 'Hex.RCF.RealCoefficients.rootInterval_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.rootInterval_progress

/-- info: 'Hex.RCF.RealCoefficients.proposeIsolations_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.proposeIsolations_isSome_iff

/-- info: 'Hex.RCF.RealCoefficients.Specialize.degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Specialize.degree

/-- info: 'Hex.RCF.RealCoefficients.FieldSpecialize.degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldSpecialize.degree

/-- info: 'Hex.RCF.RealCoefficients.FieldSpecialize.literal_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldSpecialize.literal_degree


/-- info: '_private.HexRCF.AlgebraicProgress.0.Hex.RCF.AlgebraicProgress.carrier_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicProgress.carrier_total

/-- info: 'Hex.RCF.RealCoefficients.Specialize.leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Specialize.leading

/-- info: 'Hex.RCF.RealCoefficients.FieldSpecialize.leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldSpecialize.leading

/-- info: 'Hex.RCF.RealCoefficients.FieldSpecialize.literal_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldSpecialize.literal_leading

/-- info: 'Hex.RCF.RealCoefficients.solver_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.solver_polynomial

/-- info: 'Hex.RCF.RealCoefficients.proposeIsolations_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.proposeIsolations_isSome

/-- info: 'Hex.RCF.RealCoefficients.proposeIsolations_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.proposeIsolations_zero

/-- info: 'Hex.RCF.RealCoefficients.carrier_proposals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.carrier_proposals
