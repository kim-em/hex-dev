/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampZassenhaus.FactorTactic
public meta import HexRCF.RealCoefficients

@[expose] public section

namespace Hex.RCF.ProofProbe.Division
open RealCoefficients
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

abbrev plasticPolynomial : ZPoly := DensePoly.ofList [-1, -1, 0, 1]
abbrev plasticSquare : DyadicSquare :=
  ⟨Dyadic.ofInt 5426 >>> (12 : Int), 0, 12⟩
theorem plasticChecked : plasticPolynomial.CheckedIrreducible :=
  ⟨(ZPoly.isIrreducible_iff plasticPolynomial).mpr (irreducibility plasticPolynomial),
    by decide⟩
theorem plasticSquarefree : HasOnlySimpleRoots plasticPolynomial := by
  have hne : plasticPolynomial ≠ 0 := by decide
  let : plasticPolynomial.CheckedIrreducible := plasticChecked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable plasticPolynomial hne).mpr
    (ZPoly.CheckedIrreducible.separable plasticPolynomial)
abbrev plasticRep : RefinedIsolation plasticPolynomial :=
  Field.literalRep plasticPolynomial plasticSquare (by decide) (by decide)
abbrev plasticAlgebraic : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized plasticPolynomial (by rfl) (by decide) (by decide)
    plasticChecked plasticSquarefree plasticRep
    (AlgebraicNumber.ofNormalized?_isSome _ _ _ _ _ _ _)
def alpha : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic plasticAlgebraic (by
    apply (AlgebraicNumber.isReal_iff _).mpr
    exact (congrArg Complex.im (Selected.normalized_toComplex
      plasticPolynomial (by rfl) (by decide) (by decide)
      plasticChecked plasticSquarefree plasticRep _)).trans
      (Field.literalRep_real _ _ _ _ (by decide)))
abbrev beta : RealAlgebraicNumber :=
  Coefficients.ofField alpha (alpha.toAlgebraic.toQAdjoin ^ 2 - 1)

abbrev directBeta : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic
    (alpha.toAlgebraic.toQAdjoin ^ 2 - 1).toAlgebraicNumber (by
      rw [AlgebraicNumber.isReal_iff, QAdjoin.toAlgebraicNumber,
        PolyQuot.toAlgebraicNumber_toComplex]
      exact QAdjoin.value_real _ alpha.property)

end Hex.RCF.ProofProbe.Division
