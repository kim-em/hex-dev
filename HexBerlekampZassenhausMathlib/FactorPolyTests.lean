/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampZassenhaus.FactorProvider
public meta import HexBerlekampZassenhausMathlib.FactorProvider
public meta import HexBerlekampZassenhausMathlib.BangElab
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampZassenhaus.FactorProvider
public import HexBerlekampZassenhausMathlib.FactorProvider
public import HexBerlekampZassenhausMathlib.BangElab
-- The multi-prime proofs attach `Eq.refl true` for each certificate check, so
-- the kernel must reduce `checkIrreducibleCertLinear` (and its Berlekamp
-- pow-chain replay) plus the `Array`/`DensePoly` `==` comparisons; the bang
-- forms additionally make the kernel re-run the whole factorizer, whose
-- bodies are not `@[expose]`d. `import all` the executable closure so both
-- kinds of emitted checks reduce (this is the calling-module cost of the
-- bang forms documented in `BangElab.lean`).
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
import all HexModArith.Basic
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
import all HexPolyZ.Core
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
import all HexBerlekamp.Basic
import all HexBerlekamp.CertReify
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
import all HexBerlekamp.TacticCore
import all HexBerlekamp.RabinSoundness.KernelWitness
import all HexBerlekamp.RabinSoundness.RabinCore
import all HexBerlekamp.RabinSoundness.RabinShape
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.CertReify
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.FactorEntryPoints
import all HexBerlekampZassenhaus.FactorProvider
import all HexBerlekampZassenhaus.FactorTacticTests
import all HexBerlekampZassenhaus.Factored
import all HexBerlekampZassenhaus.IrreducibleCore
import all HexBerlekampZassenhaus.IrreducibleDecide
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.PrimitivityProofs
import all HexBerlekampZassenhaus.ProductProofs
import all HexBerlekampZassenhaus.QuadraticRootProofs
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.RecombineProofs
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.SmallModSingleton
import all HexBerlekampZassenhaus.SquareFreeModularCert
import all HexBerlekampZassenhaus.TrialProofs
import all HexBerlekampZassenhaus.WordCld
import all HexHensel.Basic
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
import all Init.Data.Array.DecidableEq
import all Init.Data.Fin.Fold
import all Init.Data.Fin.Basic
import all Init.Data.Fin.Iterate
import all Init.Data.List.Basic
import all Init.Data.List.Range
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

/-!
End-to-end tests for the `Polynomial ℤ` / strong `Hex.ZPoly` provider of
`factor_poly`/`irreducibility`, including the goal-mode subsumption of the
deleted `irreducible_cert` tactic (its generator guard polynomials from
#8552 Part 1 migrate here), the certificate reification round-trips, the
decline→multi-prime handover on an A4 quartic the free provider cannot
certify, the free-layer Eisenstein handover on `x⁴ + 1`, and the decline
diagnostic for balanced inputs outside every certificate language.
-/

namespace HexBerlekampZassenhausMathlib.FactorPolyTests

open Lean Polynomial

/-! ### Elaboration-time evaluation shims for the round-trip tests -/

private meta unsafe def evalZPolyUnsafe (e : Expr) :
    MetaM (Except String Hex.ZPoly) :=
  try
    return .ok (← Meta.evalExpr Hex.ZPoly (mkConst ``Hex.ZPoly) e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalZPolyUnsafe]
private meta opaque evalZPolyCore (e : Expr) : MetaM (Except String Hex.ZPoly)

private meta def evalZPoly (e : Expr) : MetaM Hex.ZPoly := do
  match ← evalZPolyCore e with
  | .ok f => return f
  | .error msg => throwError "failed to evaluate the polynomial{indentExpr e}\n{msg}"

private meta unsafe def evalCertificateUnsafe (e : Expr) :
    MetaM (Except String Hex.ZPolyIrreducibilityCertificate) :=
  try
    return .ok (← Meta.evalExpr Hex.ZPolyIrreducibilityCertificate
      (mkConst ``Hex.ZPolyIrreducibilityCertificate) e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalCertificateUnsafe]
private meta opaque evalCertificateCore (e : Expr) :
    MetaM (Except String Hex.ZPolyIrreducibilityCertificate)

private meta def evalCertificate (e : Expr) :
    MetaM Hex.ZPolyIrreducibilityCertificate := do
  match ← evalCertificateCore e with
  | .ok cert => return cert
  | .error msg => throwError "failed to evaluate the certificate{indentExpr e}\n{msg}"

/-! ### Certificate reification round-trips

The generator guard polynomials from the compiled-generator PR (#8552
Part 1): two monic quadratics, a linear polynomial (empty certificate), and
the inert-prime cubic `x³ - x - 1`. Reify each generated certificate,
typecheck the resulting `Expr`, evaluate it back, and compare
field-by-field through the canonical `certificateData` serialization. -/

/-- `x² + 2`, irreducible with inert prime 3. -/
def quadTwo : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[2, 0, 1]

/-- `x² + x + 1`, irreducible with inert prime 5. -/
def quadOmega : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[1, 1, 1]

/-- `x + 3`, irreducible of degree 1 (empty certificate: no candidate factor
degrees to obstruct). -/
def linearThree : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[3, 1]

/-- `x³ - x - 1`, irreducible with inert prime 3: the single inert block
obstructs every proper factor degree at once. -/
def cubicInert : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[-1, -1, 0, 1]

private meta def roundTrips (f : Hex.ZPoly) : MetaM Bool := do
  match Hex.certifyIrreducible? f with
  | none => return false
  | some cert => do
      let certE := Hex.CertReify.reifyCertificate cert
      Meta.check certE
      let cert' ← evalCertificate certE
      let fE ← Hex.CertReify.reifyZPoly f
      Meta.check fE
      let f' ← evalZPoly fE
      return Hex.CertReify.certificateData cert == Hex.CertReify.certificateData cert'
        && f.toArray == f'.toArray
        && Hex.checkIrreducibleCertLinear f' cert'

run_meta do
  for (name, f) in [("quadTwo", quadTwo), ("quadOmega", quadOmega),
      ("linearThree", linearThree), ("cubicInert", cubicInert)] do
    unless (← roundTrips f) do
      throwError "certificate reification round-trip failed for {name}"

/-! ### Goal-mode subsumption of `irreducible_cert`

Every `Irreducible (HexPolyZMathlib.toPolynomial f)` goal the deleted
`irreducible_cert` tactic closed is now closed by goal-mode
`irreducibility`. -/

example : Irreducible (HexPolyZMathlib.toPolynomial quadTwo) := by
  irreducibility

example : Irreducible (HexPolyZMathlib.toPolynomial quadOmega) := by
  irreducibility

example : Irreducible (HexPolyZMathlib.toPolynomial linearThree) := by
  irreducibility

theorem cubicInert_irreducible :
    Irreducible (HexPolyZMathlib.toPolynomial cubicInert) := by
  irreducibility

-- The unfolded `HexPolyMathlib.toPolynomial` spelling at `R = ℤ` matches too.
example : Irreducible (HexPolyMathlib.toPolynomial cubicInert) := by
  irreducibility

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.cubicInert_irreducible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cubicInert_irreducible

/-! ### `Polynomial ℤ` inputs (bridge-only: the provider-liveness canary) -/

theorem sqrt2_irred : Irreducible ((X : Polynomial ℤ) ^ 2 - 2) :=
  irreducibility ((X : Polynomial ℤ) ^ 2 - 2)

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.sqrt2_irred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sqrt2_irred

-- Goal mode.
example : Irreducible ((X : Polynomial ℤ) ^ 2 - 2) := by irreducibility

-- `this` and `h :` tactic forms.
example : True := by
  irreducibility ((X : Polynomial ℤ) ^ 2 - 2)
  irreducibility h : (X ^ 2 + X + 1 : Polynomial ℤ)
  exact True.intro

-- Term form of `factor_poly`, with negation, `C` coefficients, and content.
noncomputable def facSqrt2 := factor_poly (X ^ 2 - 2 : Polynomial ℤ)

example : facSqrt2.factors.length = 1 := rfl

noncomputable def facSplit :=
  factor_poly (-(X - 1) * (X + 1) * Polynomial.C 6 : Polynomial ℤ)

example : facSplit.factors.length = 2 := rfl

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.facSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms facSplit

-- `obtain` on the term form.
example : True := by
  obtain ⟨scalar, factors, factors_mul, factors_irred⟩ :=
    factor_poly (X ^ 2 - 2 : Polynomial ℤ)
  trivial

-- Tactic form (providers emitting `FactoredPoly.ofZ` land as a single
-- `factored` hypothesis).
example : True := by
  factor_poly (X ^ 2 - 2 : Polynomial ℤ)
  exact True.intro

/-! ### The decline→multi-prime handover on `Hex.ZPoly`

`x⁴ + 8x + 12` has Galois group `A₄`: no 4-cycle, so it is reducible mod
every prime and `searchWitness` finds no single-prime witness; it is not
Eisenstein at any small shift either, so the free provider declines. Its
mod-p degree splittings `{1,3}` and `{2,2}` jointly obstruct every proper
factor degree, so `certifyIrreducible?` produces a multi-prime certificate
and this provider certifies it. -/

/-- `x⁴ + 8x + 12`, irreducible with Galois group `A₄`: no free-layer
witness exists, only the multi-prime degree obstruction. -/
def quarticA4 : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[12, 8, 0, 0, 1]

theorem quarticA4_irred : Hex.ZPoly.Irreducible quarticA4 :=
  irreducibility quarticA4

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.quarticA4_irred' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms quarticA4_irred

-- Goal mode on the free-layer statement.
example : Hex.ZPoly.Irreducible quarticA4 := by irreducibility

-- Goal mode on the transported statement.
example : Irreducible (HexPolyZMathlib.toPolynomial quarticA4) := by
  irreducibility

-- `factor_poly` on the same input: the `Hex.ZPoly.Factored` cover mixes in
-- the multi-prime certificate.
noncomputable def quarticA4_factored : Hex.ZPoly.Factored quarticA4 :=
  factor_poly quarticA4

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.quarticA4_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms quarticA4_factored

-- The same handover for a `Polynomial ℤ` input.
example : Irreducible (X ^ 4 + Polynomial.C 8 * X + 12 : Polynomial ℤ) := by
  irreducibility

/-! ### Reducible and degenerate inputs: targeted errors -/

/-- `x² - 1`, reducible: the provider reports the factor count instead of
handing the kernel a bogus certificate. -/
def reducibleQuad : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[-1, 0, 1]

/--
error: irreducibility: the polynomial
  reducibleQuad
is not irreducible over ℤ: factor_poly finds 2 irreducible factors (with multiplicity), scalar 1
-/
#guard_msgs in
example : Irreducible (HexPolyZMathlib.toPolynomial reducibleQuad) := by
  irreducibility

/--
error: irreducibility: the polynomial
  X ^ 2 - 1
is not irreducible over ℤ: factor_poly finds 2 irreducible factors (with multiplicity), scalar 1
-/
#guard_msgs in
example := irreducibility (X ^ 2 - 1 : Polynomial ℤ)

/-- error: irreducibility: the zero polynomial is not irreducible -/
#guard_msgs in
example := irreducibility (0 : Polynomial ℤ)

/--
error: irreducibility: the polynomial
  1
is a unit (±1), not irreducible
-/
#guard_msgs in
example := irreducibility (1 : Polynomial ℤ)

/-! ### The Eisenstein handover: `x⁴ + 1` never reaches this provider

`x⁴ + 1` is reducible mod every prime *and* a degree-2 factor sum is
available in every mod-p splitting (`{1,1,1,1}` or `{2,2}`), so neither the
single-prime witness nor the multi-prime degree obstruction applies. The
free layer's Eisenstein-after-shift search certifies it (shift `1`,
prime `2`) before either bridge certificate language is consulted. -/

def x4p1 : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[1, 0, 0, 0, 1]

theorem x4p1_irred : Hex.ZPoly.Irreducible x4p1 := irreducibility x4p1

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.x4p1_irred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x4p1_irred

-- The transported `Polynomial ℤ` statement.
example : Irreducible (X ^ 4 + 1 : Polynomial ℤ) := by irreducibility

/-! ### Balanced beyond every certificate language: the decline diagnostic

`x⁴ - 10x² + 1` (Swinnerton-Dyer for `√2 + √3`) is reducible mod every
prime, not Eisenstein at any small shift, and every mod-p splitting leaves
a degree-2 factor sum available, so the multi-prime degree obstruction
fails as well: no kernel-checkable certificate exists in the tree. -/

/--
error: irreducibility: unsupported polynomial type
  Hex.DensePoly ℤ
Supported without further imports: Hex.FpPoly p (prime p). Importing HexBerlekampZassenhaus adds Hex.ZPoly; the Mathlib bridge libraries add Polynomial (ZMod q) and Polynomial ℤ.

irreducibility: the irreducible factor
  Hex.DensePoly.ofCoeffs #[1, 0, -10, 0, 1]
has no single-prime modular witness among the candidate primes (its modular factorizations are balanced, e.g. Swinnerton-Dyer polynomials) and is not Eisenstein at any small shift; the Mathlib bridge's multi-prime degree-obstruction certificates may certify it — import HexBerlekampZassenhausMathlib.

irreducibility: the irreducible factor
  Hex.DensePoly.ofCoeffs #[1, 0, -10, 0, 1]
has no single-prime modular witness, is not Eisenstein at any small shift, and its balanced modular factorizations fall outside the multi-prime per-prime degree-sum obstruction language (e.g. Swinnerton-Dyer polynomials); no certificate-backed proof is available, but the kernel-decide fallbacks `irreducibility!` / `factor_poly!` can still certify small inputs by re-running the factorizer in the kernel
-/
#guard_msgs in
example := irreducibility (Hex.DensePoly.ofCoeffs #[1, 0, -10, 0, 1] : Hex.ZPoly)

/-! ### The kernel-decide fallbacks `irreducibility!` / `factor_poly!`

The Swinnerton-Dyer quartic `x⁴ - 10x² + 1` is exactly the decline case
above, so the bang forms exercise the genuine fallback path: the emitted
proofs make the kernel re-run the factorizer (which is why this file
carries the `import all` closure block). On inputs the certificate
pipeline handles — including `x⁴ + 1`, now Eisenstein-certified at shift
`1` — the bang forms are pass-throughs. -/

/-- `x⁴ + 1`, certified by the Eisenstein-after-shift witness, so a bang
pass-through. -/
def cyc8 : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[1, 0, 0, 0, 1]

/-- The Swinnerton-Dyer quartic `x⁴ - 10x² + 1`. -/
def swinDyer : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[1, 0, -10, 0, 1]

theorem cyc8_irred : Hex.ZPoly.Irreducible cyc8 := irreducibility! cyc8

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.cyc8_irred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cyc8_irred

-- Goal modes: free-layer, transported, and parsed `Polynomial ℤ`.
theorem swinDyer_irred : Hex.ZPoly.Irreducible swinDyer := by irreducibility!

example : Irreducible (HexPolyZMathlib.toPolynomial cyc8) := by irreducibility!

theorem sd_poly_irred : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : Polynomial ℤ) :=
  irreducibility! (X ^ 4 - 10 * X ^ 2 + 1 : Polynomial ℤ)

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.sd_poly_irred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sd_poly_irred

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.swinDyer_irred' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms swinDyer_irred

-- Pass-through: inputs the certificate pipeline serves take the plain path.
example : Hex.ZPoly.Irreducible quarticA4 := irreducibility! quarticA4
example : Irreducible ((X : Polynomial ℤ) ^ 2 - 2) := by irreducibility!

-- `this` and `h :` tactic forms.
example : True := by
  irreducibility! cyc8
  irreducibility! h : swinDyer
  exact True.intro

-- `factor_poly!` on a product with a balanced factor: the plain pipeline
-- declines on the `x⁴+1` factor, so the fallback replays the factorizer in
-- the kernel once per factor.
def cyc8Split : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[-1, 1] * cyc8

noncomputable def cyc8Split_factored : Hex.ZPoly.Factored cyc8Split :=
  factor_poly! cyc8Split

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.cyc8Split_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cyc8Split_factored

example : cyc8Split_factored.factors.length = 2 := rfl

-- `factor_poly!` term + tactic on `Polynomial ℤ`.
noncomputable def facBangP :=
  factor_poly! ((X - 1) * (X ^ 4 + 1) : Polynomial ℤ)

/--
info: 'HexBerlekampZassenhausMathlib.FactorPolyTests.facBangP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms facBangP

example : True := by
  factor_poly! ((X - 1) * (X ^ 4 + 1) : Polynomial ℤ)
  exact True.intro

-- Over-budget inputs fail cleanly at elaboration time.
/--
error: irreducibility!: the kernel factorizer replay is capped at dense size 13 (degree 12), but the input has dense size 17; degree 12 already takes tens of seconds of kernel time
-/
#guard_msgs in
example := irreducibility!
  (Hex.DensePoly.ofCoeffs #[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Hex.ZPoly)

end HexBerlekampZassenhausMathlib.FactorPolyTests
