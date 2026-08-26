/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampZassenhaus.FactorTactic
public meta import HexBerlekampZassenhausMathlib.FactorTactic
public meta import HexBerlekampZassenhausMathlib.KernelFactorTactic
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampZassenhaus.FactorTactic
public import HexBerlekampZassenhausMathlib.FactorTactic
public import HexBerlekampZassenhausMathlib.KernelFactorTactic
-- The multi-prime proofs attach `Eq.refl true` for each certificate check, so
-- the kernel must reduce `checkIrreducibleCertLinear` (and its Berlekamp
-- pow-chain replay) plus the `Array`/`DensePoly` `==` comparisons; the bang
-- forms additionally make the kernel re-run the whole factorizer, whose
-- bodies are not `@[expose]`d. `import all` the executable closure so both
-- kinds of emitted checks reduce (this is the calling-module cost of the
-- bang forms documented in `KernelFactorTactic.lean`).
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
-- Kernel-reducible `Array`/`Vector` equality; see `HexBasic.ArrayDecEq`.
-- Drop once leanprover/lean4#14270 lands and the toolchain is bumped past it.
public import HexBasic.ArrayDecEq
import all Init.Data.Fin.Fold
import all Init.Data.Fin.Basic
import all Init.Data.Fin.Iterate
import all Init.Data.List.Basic
import all Init.Data.List.Range
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

open scoped Hex   -- kernel-reducible Array/Vector equality; see HexBasic.ArrayDecEq

public section

/-!
Conformance checks for the `HexBerlekampZassenhausMathlib` tactic and
certificate-checking runtime: the `factor_poly` / `irreducibility`
elaborators on `Polynomial ℤ` and strong `Hex.ZPoly` inputs, and their
kernel-decide fallbacks `factor_poly!` / `irreducibility!`.

Oracle: none. This module exercises a proof-emitting elaboration surface:
every accepted invocation is certified by the kernel (the emitted terms
carry reified literal data with Boolean certificate checks discharged by
`Eq.refl true`, and the `#print axioms` checks below pin the accepted
foundations), so the checked artifact is the kernel-verified proof term
itself rather than an untrusted value needing an external recomputation.
The compiled factorizer the tactics use as untrusted search is
oracle-checked against python-flint in the computational sibling's profile
(`conformance/HexBerlekampZassenhaus/`); the expected factorizations
asserted here are hand-derived cyclotomic/quadratic identities, not oracle
outputs.
Mode: `always`.

Covered operations:
- `irreducibility` (term, goal, and `h :` tactic forms) on `Polynomial ℤ`,
  strong `Hex.ZPoly`, and transported `HexPolyZMathlib.toPolynomial`
  statements
- `factor_poly` (term and tactic forms) on `Polynomial ℤ` and `Hex.ZPoly`
  inputs
- `irreducibility!`, the kernel-replay fallback, on certificate-served
  (pass-through) and certificate-declined (genuine fallback) inputs
- `factor_poly!` on a product with a certificate-declined factor

Covered properties:
- accepted factorizations return the hand-derived irreducible factor
  multiset (`X⁶ − 1` into its four cyclotomic factors; mixed-degree
  products with signed content; a squared factor listed with multiplicity)
- every named emitted proof depends on exactly
  `[propext, Classical.choice, Quot.sound]` (`#print axioms`)
- the decline diagnostics name the factor count and scalar on reducible
  inputs, and the kernel-replay budget cap on over-budget inputs

Covered edge cases:
- degree-1 input (empty certificate)
- reducible, zero, and unit (`-1`) inputs to `irreducibility` (targeted
  errors)
- constant input to `factor_poly` (scalar-only factorization)
- Eisenstein handover (`X⁶ + 3`), multi-prime degree-obstruction handover
  (`X⁴ + 8X + 12`, Galois group `A₄`), and balanced Swinnerton-Dyer
  decline (`X⁴ − 10X² + 1`, kernel fallback only)
- an over-budget kernel-fallback input (dense size 17 against the cap 13)
-/

namespace HexBerlekampZassenhausMathlib.Conformance

open Polynomial

/-! # `irreducibility`: certificate-backed acceptance

Typical (`X² − 3`, single-prime witness), edge (`X + 7`, degree 1, empty
certificate), and adversarial (`X⁴ + 8X + 12`, reducible mod every prime
with Galois group `A₄`, so only the multi-prime degree obstruction
certifies it; `X⁶ + 3`, certified by the free layer's Eisenstein witness
before the correspondence languages are consulted). -/

theorem sqrt3_irred : Irreducible ((X : Polynomial ℤ) ^ 2 - 3) :=
  irreducibility ((X : Polynomial ℤ) ^ 2 - 3)

/--
info: 'HexBerlekampZassenhausMathlib.Conformance.sqrt3_irred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sqrt3_irred

/-- `x + 7`: irreducible of degree 1 (empty certificate: no candidate
factor degrees to obstruct). -/
def linearSeven : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[7, 1]

example : Hex.ZPoly.Irreducible linearSeven := irreducibility linearSeven

/-- `x⁴ + 8x + 12`, irreducible with Galois group `A₄`: no single-prime
witness and not Eisenstein at any shift, so this certifies only through
the multi-prime degree obstruction. -/
theorem quarticA4_irred :
    Irreducible (X ^ 4 + Polynomial.C 8 * X + 12 : Polynomial ℤ) := by
  irreducibility

/--
info: 'HexBerlekampZassenhausMathlib.Conformance.quarticA4_irred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms quarticA4_irred

-- Eisenstein handover at degree 6, goal mode on the transported statement.
example :
    Irreducible
      (HexPolyZMathlib.toPolynomial (Hex.DensePoly.ofCoeffs #[3, 0, 0, 0, 0, 0, 1])) := by
  irreducibility

-- `h :` tactic form.
example : True := by
  irreducibility h : (X ^ 2 - 3 : Polynomial ℤ)
  exact True.intro

/-! # `irreducibility`: targeted errors on degenerate inputs -/

/--
error: irreducibility: the polynomial
  X ^ 2 - 4
is not irreducible over ℤ: factor_poly finds 2 irreducible factors (with multiplicity), scalar 1
-/
#guard_msgs in
example := irreducibility (X ^ 2 - 4 : Polynomial ℤ)

/-- error: irreducibility: the zero polynomial is not irreducible -/
#guard_msgs in
example := irreducibility (0 : Polynomial ℤ)

/--
error: irreducibility: the polynomial
  -1
is a unit (±1), not irreducible
-/
#guard_msgs in
example := irreducibility (-1 : Polynomial ℤ)

/-! # `factor_poly`: hand-derived factorizations

Typical (mixed-degree product with signed content), edge (irreducible
input; constant input), and adversarial (`X⁶ − 1`, whose four cyclotomic
factors `Φ₁ Φ₂ Φ₃ Φ₆` include a negative-coefficient quadratic; a squared
factor recorded with multiplicity). Each `factor_poly` value carries its
own kernel-checked product identity (`factors_mul`) and per-factor
irreducibility proofs (`factors_irred`); the checks below additionally pin
the factor lists to the independently hand-derived factorizations. -/

noncomputable def facMixed :=
  factor_poly (Polynomial.C (-6) * (X + 2) * (X ^ 2 + 3) : Polynomial ℤ)

example : facMixed.factors.length = 2 := rfl

example : facMixed.factors = [2 + X, 3 + X ^ 2] := by
  simp [facMixed, Finset.sum_range_succ]

/--
info: 'HexBerlekampZassenhausMathlib.Conformance.facMixed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms facMixed

-- Edge: an irreducible input factors as itself.
noncomputable def facIrred := factor_poly (X ^ 2 - 3 : Polynomial ℤ)

example : facIrred.factors.length = 1 := rfl

-- Edge: a constant input has scalar-only factorization.
noncomputable def facConst := factor_poly (Polynomial.C 6 : Polynomial ℤ)

example : facConst.factors.length = 0 := rfl

-- Adversarial: the cyclotomic factorization of `X⁶ − 1`, hand-derived as
-- the multiset `{X − 1, X + 1, X² − X + 1, X² + X + 1}` (`Φ₁ Φ₂ Φ₆ Φ₃`);
-- the list order is the factorizer's deterministic normalized order.
noncomputable def facCyclo6 := factor_poly (X ^ 6 - 1 : Polynomial ℤ)

example : facCyclo6.factors = [1 + X, -1 + X, 1 - X + X ^ 2, 1 + X + X ^ 2] := by
  simp [facCyclo6, Finset.sum_range_succ, sub_eq_add_neg]

/--
info: 'HexBerlekampZassenhausMathlib.Conformance.facCyclo6' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms facCyclo6

/-- `(x − 2)²(x + 1) = x³ − 3x² + 4`: the squared factor must be listed
with multiplicity. -/
def cubicSquared : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[4, 0, -3, 1]

noncomputable def facSquared : Hex.ZPoly.Factored cubicSquared :=
  factor_poly cubicSquared

example : facSquared.factors.length = 3 := rfl

-- Tactic form: the extension exposes the four local names.
example : True := by
  factor_poly (X ^ 2 - 3 : Polynomial ℤ)
  have : factors.length = 1 := rfl
  have := factors_mul
  have := factors_irred
  exact True.intro

/-! # The kernel-decide fallbacks

`X⁴ − 10X² + 1` (Swinnerton-Dyer for `√2 + √3`) is balanced mod every
prime, not Eisenstein at any small shift, and outside the multi-prime
degree-sum obstruction language, so no certificate exists and the bang
forms genuinely replay the factorizer in the kernel. Inputs the
certificate pipeline serves are pass-throughs. -/

/-- The Swinnerton-Dyer quartic `x⁴ − 10x² + 1`. -/
def swinDyerZ : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[1, 0, -10, 0, 1]

theorem swinDyerZ_irred : Hex.ZPoly.Irreducible swinDyerZ :=
  irreducibility! swinDyerZ

/--
info: 'HexBerlekampZassenhausMathlib.Conformance.swinDyerZ_irred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms swinDyerZ_irred

-- Pass-through: certificate-served inputs take the plain path under `!`.
example : Irreducible ((X : Polynomial ℤ) ^ 2 - 3) := by irreducibility!

-- `factor_poly!` on a product with a certificate-declined factor: the
-- fallback replays the factorizer in the kernel for the declined factor.
noncomputable def facBang :=
  factor_poly! ((X - 1) * (X ^ 4 - 10 * X ^ 2 + 1) : Polynomial ℤ)

example : facBang.factors.length = 2 := rfl

/--
info: 'HexBerlekampZassenhausMathlib.Conformance.facBang' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms facBang

-- Over-budget inputs fail cleanly at elaboration time. `X¹⁶ − 4` is
-- outside the certificate languages (it is reducible), so the bang form
-- reaches the fallback, whose budget check rejects dense size 17.
/--
error: irreducibility!: the kernel factorizer replay is capped at dense size 13 (degree 12), but the input has dense size 17; degree 12 already takes tens of seconds of kernel time
-/
#guard_msgs in
example := irreducibility!
  (Hex.DensePoly.ofCoeffs #[-4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Hex.ZPoly)

end HexBerlekampZassenhausMathlib.Conformance
