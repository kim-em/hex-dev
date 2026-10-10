/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Basic
import HexBerlekampZassenhausMathlib.KernelFactorTactic
import all HexArith.ExtGcd
import all HexArith.Barrett.Accumulator
import all HexArith.Barrett.Context
import all HexArith.Barrett.Reduce
import all HexArith.Barrett.ReduceNat
import all HexArith.Montgomery.Context
import all HexArith.Montgomery.InvNat
import all HexArith.Montgomery.Redc
import all HexArith.Montgomery.RedcNat
import all HexArith.Nat.ModArith
import all HexArith.Nat.Pow
import all HexArith.Nat.Prime
import all HexArith.UInt64.Wide
import all HexModArith.Residue
import all HexModArith.HotLoop
import all HexModArith.Prime
import all HexModArith.Ring
import all HexModArith.WordMod
import all HexPoly.Dense
import all HexPoly.Euclid
import all HexPoly.Operations
import all HexPoly.Euclid.Content
import all HexPoly.Euclid.DivGcd
import all HexPoly.Euclid.MonicUnique
import all HexPoly.Euclid.MulRing
import all HexPoly.Euclid.Reconstruction
import all HexPolyZ.IntegerPolynomial
import all HexPolyZ.Decomposition
import all HexPolyZ.Mignotte
import all HexPolyZ.Rational
import all HexPolyFp.Compose
import all HexPolyFp.Degree
import all HexPolyFp.Enumeration
import all HexPolyFp.Field
import all HexPolyFp.Frobenius
import all HexPolyFp.ModCompose
import all HexPolyFp.Packed
import all HexPolyFp.PackedMul
import all HexPolyFp.PrimeField
import all HexPolyFp.Quotient
import all HexPolyFp.QuotientFrobenius
import all HexPolyFp.Ring
import all HexPolyFp.SquareFree
import all HexPolyFp.Quotient.Ring
import all HexPolyFp.SquareFree.Algebra
import all HexPolyFp.SquareFree.YunContribution
import all HexPolyFp.SquareFree.YunCorrect
import all HexPolyFp.SquareFree.YunMeasure
import all HexPolyFp.SquareFree.YunReduce
import all HexBerlekamp.BerlekampMatrix
import all HexBerlekamp.CertificateSyntax
import all HexBerlekamp.DelayedKernel
import all HexBerlekamp.DistinctDegree
import all HexBerlekamp.Factor
import all HexBerlekamp.FactorPolyElab
import all HexBerlekamp.FactorTacticTests
import all HexBerlekamp.Factored
import all HexBerlekamp.Irreducibility
import all HexBerlekamp.IrreducibilityElab
import all HexBerlekamp.IrreducibleDecide
import all HexBerlekamp.RabinSoundness
import all HexBerlekamp.PolynomialTactic
import all HexBerlekamp.RabinSoundness.KernelWitness
import all HexBerlekamp.RabinSoundness.RabinCore
import all HexBerlekamp.RabinSoundness.RabinShape
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.CertificateSyntax
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.SquareFreeInput
import all HexBerlekampZassenhaus.Modular.PrimePlan
import all HexBerlekampZassenhaus.Hensel.DirectLift
import all HexBerlekampZassenhaus.Classical.Candidate
import all HexBerlekampZassenhaus.Classical.Obstruction
import all HexBerlekampZassenhaus.Classical.CombinationIterator
import all HexBerlekampZassenhaus.Classical.Search
import all HexBerlekampZassenhaus.Classical.Factorization
import all HexBerlekampZassenhaus.Factorization
import all HexBerlekampZassenhaus.FactorTactic
import all HexBerlekampZassenhaus.FactorTacticTests
import all HexBerlekampZassenhaus.Factored
import all HexBerlekampZassenhaus.FactorIrreducibility
import all HexBerlekampZassenhaus.IrreducibleDecide
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.PrimitiveFactors
import all HexBerlekampZassenhaus.FactorProduct
import all HexBerlekampZassenhaus.QuadraticFactors
import all HexBerlekampZassenhaus.FactorizationResult
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.RecombinationFactors
import all HexBerlekampZassenhaus.FactorizationData
import all HexBerlekampZassenhaus.SmallModSingleton
import all HexBerlekampZassenhaus.SquareFreeModularCert
import all HexBerlekampZassenhaus.TrialFactorization
import all HexBerlekampZassenhaus.WordCld
import all HexHensel.ModularPolynomial
import all HexHensel.Linear
import all HexHensel.Multifactor
import all HexHensel.Quadratic
import all HexHensel.QuadraticMultifactor
import all HexHensel.WordStep
import all HexHensel.WordTransport
import all HexMatrix.Basic
import all HexMatrix.Block
import all HexMatrix.DotProduct
import all HexMatrix.Elementary
import all HexMatrix.Gram
import all HexMatrix.MatrixAlgebra
import all HexMatrix.Notation
import all HexMatrix.Pad
import all HexMatrix.Strassen
import all HexMatrix.Submatrix
import all HexMatrix.Winograd
import all HexMatrix.Vector.Insert
import all HexRowReduce.Api
import all HexRowReduce.Loop
import all HexRowReduce.Nullspace
import all HexRowReduce.Pivot
import all HexRowReduce.RowEchelon
import all HexRowReduce.Span
import all HexRowReduce.RowEchelon.Contracts
import all HexRowReduce.RowEchelon.Elementary
import all HexBasic.Fold
import all HexBasic.ListShim
import all HexBasic.Vector.Modify
import all Init.Data.Array.Basic
import all Init.Data.Fin.Fold
import all Init.Data.Fin.Basic
import all Init.Data.Fin.Iterate
import all Init.Data.List.Basic
import all Init.Data.List.Range
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
public import HexRCF.SuppliedIrreducible
public import HexRCF.CertificationInputs
public import HexRCF.RealCoefficients
public meta import HexRCF.SuppliedIrreducible
public meta import HexRCF.CertificationInputs
public meta import HexRCF.ProofEvidence
public meta import Lean.Elab.Command
public meta import HexRCF.RealCoefficients
/-! Matched build-only probes for the cost of reconstructing the degree-eight
irreducibility theorem versus reusing an imported theorem. Both arms deliberately
carry the same private executable closure; ordinary-import support is tested
separately by `SuppliedIrreducibleProofs`. No runtime benchmark imports this file. -/
public section
open Hex Hex.RCF Hex.RCF.RealCoefficients
set_option maxRecDepth 32768
namespace Hex.RCF.ProofProbe.Supplied.Reuse
open scoped Hex.RCF.SuppliedIrreducible

theorem positive : ∀ x : ℝ,
    x ^ 2 + CertificationInputs.realAlgebraic.toReal + Real.sqrt 2 > 0 := by rcf
/-- info: 'Hex.RCF.ProofProbe.Supplied.Reuse.positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms positive
-- The external paired collector reads this complete inventory from stdout.
#print axioms positive
run_meta do
  unless ← Hex.RCF.ProofEvidence.contains ``positive (fun e => e.isConstOf ``Hex.RCF.SuppliedIrreducible.supplied) do
    throwError "fresh cost probe used a different supplied proof"
end Hex.RCF.ProofProbe.Supplied.Reuse
