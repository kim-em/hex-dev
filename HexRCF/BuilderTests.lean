/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Builder
public meta import HexRCF.Builder
public meta import HexRCF.Carrier
public meta import HexRCF.CommonRoot
public meta import HexRCF.SignMatrixCheck
public meta import HexRCF.SturmBuilder

public section

/-! Regression tests for compiled carrier and common-root preparation. -/

namespace Hex.RCF.BuilderTests

private def one : ZPoly := DensePoly.ofCoeffs #[(1 : Int)]
private def two : ZPoly := DensePoly.ofCoeffs #[(2 : Int)]
private def negTwelve : ZPoly := DensePoly.ofCoeffs #[(-12 : Int)]
private def zero : ZPoly := DensePoly.ofCoeffs #[]
private def x : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]
private def twiceX : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 2]
private def quad : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
private def xMinusOne : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 1]
private def xPlusOne : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 1]
private def repeated : ZPoly := DensePoly.scale (-6) (xMinusOne * xMinusOne)

private def quadSentence : Sentence := .forallReal (.atom ⟨quad, .ge⟩)
private def duplicateSentence : Sentence :=
  .existsReal (.and (.atom ⟨x, .ge⟩) (.atom ⟨x, .le⟩))
private def repeatedSentence : Sentence := .forallReal (.atom ⟨repeated, .ne⟩)
private def constantSentence : Sentence := .forallReal (.atom ⟨one, .gt⟩)
private def repeatedAtoms : Sentence := .existsReal
  (.and (.atom ⟨x, .eq⟩) (.and (.atom ⟨quad, .gt⟩) (.atom ⟨x, .le⟩)))

/-! Square-free, repeated-factor, nonprimitive, and constant carrier paths. -/

#guard (buildCarrier? quadSentence).isSome
#guard (match buildCarrier? quadSentence with
    | some cert => cert.check quadSentence
    | none => false)

/- Repeated occurrences produce `Q = x²`, hence carrier and repeated part
both equal `x`. -/
#guard (match buildCarrier? duplicateSentence with
    | some cert =>
        DensePoly.beqCoeffs cert.carrier x &&
          DensePoly.beqCoeffs cert.repeated x &&
          cert.factorScale == 1 &&
          cert.derivScale == 1 &&
          DensePoly.beqCoeffs cert.derivPart two &&
          cert.check duplicateSentence
    | none => false)

/- Negative nonprimitive content is retained in the signed factor scale. -/
#guard (match buildCarrier? repeatedSentence with
    | some cert =>
        DensePoly.beqCoeffs cert.carrier xMinusOne &&
        DensePoly.beqCoeffs cert.repeated xMinusOne &&
          cert.factorScale == -6 &&
          cert.derivScale == 1 &&
          DensePoly.beqCoeffs cert.derivPart negTwelve &&
          cert.check repeatedSentence
    | none => false)

/- Constant-only sentences belong to the carrier-free certificate branch. -/
#guard (buildCarrier? constantSentence).isNone

example {cert : CarrierCert} (h : buildCarrier? quadSentence = some cert) :
    cert.check quadSentence = true := check_buildCarrier h

/-! Coprime, scaled, shared, and equal common-root packages. -/

#guard (match buildCommonRoot? x quad with
    | some cert =>
        DensePoly.beqCoeffs cert.gcd one &&
          cert.replay.isNone && cert.check x quad
    | none => false)

/- Clearing the rational Bezout coefficients for `2*x` and `x²-1` produces a
genuine nonunit scale. -/
#guard (match buildCommonRoot? twiceX quad with
    | some cert =>
        DensePoly.beqCoeffs cert.gcd one &&
          cert.scale.natAbs == 2 && cert.replay.isNone &&
          cert.check twiceX quad
    | none => false)

#guard (match buildCommonRoot? xMinusOne quad with
    | some cert =>
        DensePoly.beqCoeffs cert.gcd xMinusOne &&
          DensePoly.beqCoeffs cert.atomFactor one &&
          DensePoly.beqCoeffs cert.carrierFactor xPlusOne &&
          cert.replay.isSome && cert.check xMinusOne quad
    | none => false)

#guard (match buildCommonRoot? quad quad with
    | some cert =>
        DensePoly.beqCoeffs cert.gcd quad &&
          DensePoly.beqCoeffs cert.atomFactor one &&
          DensePoly.beqCoeffs cert.carrierFactor one &&
          cert.replay.isSome && cert.check quad quad
    | none => false)

/- The undefined rational gcd case fails before emitting any certificate. -/
#guard (buildCommonRoot? zero zero).isNone

/- Common packages are constructed once per first-occurrence-preserving
distinct atom and remain positionally aligned with the checker. -/
#guard (match buildCommonRoots? repeatedAtoms (x * quad) with
    | some [xCommon, quadCommon] =>
        DensePoly.beqCoeffs xCommon.gcd x &&
          DensePoly.beqCoeffs quadCommon.gcd quad &&
          checkCommon (x * quad) (dedupPolys repeatedAtoms.polys)
            [xCommon, quadCommon]
    | _ => false)

example {cert : CommonRootCert} (h : buildCommonRoot? xMinusOne quad = some cert) :
    cert.check xMinusOne quad = true := check_buildCommonRoot h

example {commons : List CommonRootCert}
    (h : buildCommonRoots? repeatedAtoms (x * quad) = some commons) :
    checkCommon (x * quad) (dedupPolys repeatedAtoms.polys) commons = true :=
  check_buildCommonRoots h

end Hex.RCF.BuilderTests
