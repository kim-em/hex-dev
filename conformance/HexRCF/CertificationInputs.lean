/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import HexBerlekampZassenhausMathlib.FactorTactic
public meta import HexBerlekampZassenhausMathlib.FactorTactic
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhausMathlib.FactorTransport
import all Init.Data.Array.Basic
import all Init.Data.Fin.Fold
import all Init.Data.Fin.Basic
import all Init.Data.Fin.Iterate
import all Init.Data.List.Basic
import all Init.Data.List.Range
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section
namespace Hex.RCF.CertificationInputs
open RealCoefficients

abbrev polynomial : ZPoly := DensePoly.ofList [-2, -7, -1, 4, 1]
abbrev square : DyadicSquare := ⟨Dyadic.ofInt 2909722875 >>> (31 : Int), 0, 26⟩

run_meta do
  unless HexBerlekampZassenhaus.FactorTactic.searchWitness polynomial |>.isNone do
    throwError "expected the free witness search to decline"

#guard (QuadraticNormCertificate.certify? polynomial).isNone
#guard (certifyIrreducible? polynomial).isSome

example : Decidable.decide (Nat.Prime 11) = true := by decide +kernel
example : Decidable.decide (Nat.Prime 5) = true := by decide +kernel

local elab "quartic_certificate" : term => do
  let p : ZPoly := DensePoly.ofList [-2, -7, -1, 4, 1]
  let some cert := certifyIrreducible? p | throwError "no quartic certificate"
  return CertificateSyntax.reifyCertificate cert

@[expose] def certificate : ZPolyIrreducibilityCertificate := quartic_certificate
#guard HexBerlekampZassenhausMathlib.checkMultiPrimeCert polynomial certificate
example : certificate.perPrime.all (fun d => Decidable.decide (_root_.Nat.Prime d.p)) = true :=
  by decide +kernel
example : Decidable.decide (polynomial.content = 1) = true := by decide +kernel
example : checkIrreducibleCertLinear polynomial certificate = true := by decide +kernel

theorem irreducible : polynomial.Irreducible := by
  exact HexBerlekampZassenhausMathlib.zpolyIrreducible_of_checkMultiPrimeCert
    polynomial certificate (by decide +kernel)
theorem checked : polynomial.CheckedIrreducible :=
  ⟨(ZPoly.isIrreducible_iff polynomial).mpr irreducible, by decide⟩
theorem squarefree : HasOnlySimpleRoots polynomial := by
  let : polynomial.CheckedIrreducible := checked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable polynomial (by decide)).mpr
    (ZPoly.CheckedIrreducible.separable polynomial)

@[expose] def realAlgebraic : RealAlgebraicNumber :=
  Selected.real polynomial square (by decide) (by decide)
    (by rfl) (by decide) (by decide) checked squarefree (by decide)

@[expose] def normalizedAlgebraic : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized polynomial (by rfl) (by decide) (by decide)
    checked squarefree (Field.literalRep polynomial square (by decide) (by decide))
    (AlgebraicNumber.ofNormalized?_isSome _ _ _ _ _ _ _)

@[expose] def normalized : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic normalizedAlgebraic (by
    apply (AlgebraicNumber.isReal_iff _).mpr
    exact (congrArg Complex.im (Selected.normalized_toComplex polynomial
      (by rfl) (by decide) (by decide) checked squarefree
      (Field.literalRep polynomial square (by decide) (by decide)) _)).trans
      (Field.literalRep_real _ _ _ _ (by decide)))

end Hex.RCF.CertificationInputs

/-- info: 'Hex.RCF.CertificationInputs.irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationInputs.irreducible

/-- info: 'Hex.RCF.CertificationInputs.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationInputs.checked

/-- info: 'Hex.RCF.CertificationInputs.squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationInputs.squarefree
