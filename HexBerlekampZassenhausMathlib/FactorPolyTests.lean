/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampZassenhaus.FactorProvider
public meta import HexBerlekampZassenhausMathlib.FactorProvider
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampZassenhaus.FactorProvider
public import HexBerlekampZassenhausMathlib.FactorProvider
-- The multi-prime proofs attach `Eq.refl true` for each certificate check, so
-- the kernel must reduce `checkIrreducibleCertLinear` (and its Berlekamp
-- pow-chain replay) plus the `Array`/`DensePoly` `==` comparisons. Expose
-- those executable checker bodies and the efficient `Array` DecidableEq.
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.FactorEntryPoints
import all HexBerlekampZassenhaus.IrreducibleCore
import all HexBerlekampZassenhaus.RecombineProofs
import all HexBerlekampZassenhaus.TrialProofs
import all HexBerlekampZassenhaus.QuadraticRootProofs
import all HexBerlekampZassenhaus.PrimitivityProofs
import all HexBerlekampZassenhaus.ProductProofs
import all HexBerlekamp.Irreducibility
import all Init.Data.Array.DecidableEq

public section

/-!
End-to-end tests for the `Polynomial ℤ` / strong `Hex.ZPoly` provider of
`factor_poly`/`irreducibility`, including the goal-mode subsumption of the
deleted `irreducible_cert` tactic (its generator guard polynomials from
#8552 Part 1 migrate here), the certificate reification round-trips, the
decline→multi-prime handover on an A4 quartic the free provider cannot
certify, and the decline diagnostics for balanced inputs outside both
certificate languages.
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
every prime and `searchWitness` finds no single-prime witness — the free
provider declines. Its mod-p degree splittings `{1,3}` and `{2,2}` jointly
obstruct every proper factor degree, so `certifyIrreducible?` produces a
multi-prime certificate and this provider certifies it. -/

/-- `x⁴ + 8x + 12`, irreducible with Galois group `A₄`: no single-prime
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

/-! ### Balanced beyond both certificate languages: the decline diagnostic

`x⁴ + 1` is reducible mod every prime *and* a degree-2 factor sum is
available in every mod-p splitting (`{1,1,1,1}` or `{2,2}`), so neither the
single-prime witness nor the multi-prime degree obstruction applies. -/

/--
error: irreducibility: unsupported polynomial type
  Hex.DensePoly ℤ
Supported without further imports: Hex.FpPoly p (prime p). Importing HexBerlekampZassenhaus adds Hex.ZPoly; the Mathlib bridge libraries add Polynomial (ZMod q) and Polynomial ℤ.

irreducibility: the irreducible factor
  Hex.DensePoly.ofCoeffs #[1, 0, 0, 0, 1]
has no single-prime modular witness among the candidate primes (its modular factorizations are balanced, e.g. Swinnerton-Dyer polynomials or X⁴+1); the Mathlib bridge's multi-prime degree-obstruction certificates may certify it — import HexBerlekampZassenhausMathlib.

irreducibility: the irreducible factor
  Hex.DensePoly.ofCoeffs #[1, 0, 0, 0, 1]
has no single-prime modular witness, and its balanced modular factorizations also fall outside the multi-prime per-prime degree-sum obstruction language (e.g. Swinnerton-Dyer polynomials or X⁴+1), so no kernel-checkable certificate is available
-/
#guard_msgs in
example := irreducibility (Hex.DensePoly.ofCoeffs #[1, 0, 0, 0, 1] : Hex.ZPoly)

end HexBerlekampZassenhausMathlib.FactorPolyTests
