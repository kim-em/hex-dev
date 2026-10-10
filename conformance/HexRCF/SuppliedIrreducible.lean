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
public section
open Hex
namespace Hex.RCF.SuppliedIrreducible
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
abbrev polynomial : ZPoly := DensePoly.ofCoeffs #[-2,-24,169,70,-127,-70,6,8,1]
theorem irreducible : polynomial.Irreducible := irreducibility! polynomial
theorem checked : polynomial.CheckedIrreducible :=
  ⟨(ZPoly.isIrreducible_iff polynomial).mpr irreducible, by decide +kernel⟩
/-- Supply the existing checked class for the frontend's quoted literal.
Kernel irreducibility checking reuses this theorem without factorizer reduction. -/
instance supplied : polynomial.CheckedIrreducible := checked
/-- info: 'Hex.RCF.SuppliedIrreducible.irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms irreducible
/-- info: 'Hex.RCF.SuppliedIrreducible.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked
/-- info: 'Hex.RCF.SuppliedIrreducible.supplied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supplied
end Hex.RCF.SuppliedIrreducible
