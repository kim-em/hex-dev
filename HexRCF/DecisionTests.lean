/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Decision
public meta import HexRCF.Decision

public section

/-! Compiled regressions for certificate assembly and decision. -/

namespace Hex.RCF.DecisionTests

private def one : ZPoly := DensePoly.ofCoeffs #[(1 : Int)]
private def x : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]
private def posQuad : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 0, 1]
private def square : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 0, 1]
private def quad : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
private def xMinusOne : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 1]

private def constantTrue : Sentence := .forallReal (.atom ⟨one, .gt⟩)
private def constantFalse : Sentence := .existsReal (.atom ⟨one, .lt⟩)
private def emptyForall : Sentence := .forallIoc 0 0 (.atom ⟨x, .lt⟩)
private def reversedExists : Sentence :=
  .existsIoc (Dyadic.ofInt 2) (Dyadic.ofInt 1) (.atom ⟨x, .eq⟩)
private def noRootTrue : Sentence := .forallReal (.atom ⟨posQuad, .gt⟩)
private def noRootFalse : Sentence := .existsReal (.atom ⟨posQuad, .eq⟩)
private def squareTrue : Sentence := .forallReal (.atom ⟨square, .ge⟩)
private def rootExists : Sentence := .existsReal (.atom ⟨x, .eq⟩)
private def upperIncluded : Sentence :=
  .existsIoc 0 1 (.atom ⟨xMinusOne, .eq⟩)
private def lowerExcluded : Sentence :=
  .existsIoc 1 2 (.atom ⟨xMinusOne, .eq⟩)
private def boundedForall : Sentence :=
  .forallIoc 0 1 (.atom ⟨xMinusOne, .le⟩)
private def twoRoots : Sentence := .existsReal (.atom ⟨quad, .eq⟩)
private def sharedRepeated : Sentence := .forallReal
  (.and (.atom ⟨square, .ge⟩) (.atom ⟨x, .eq⟩))
private def mixed : Sentence := .existsReal
  (.and (.atom ⟨one, .gt⟩) (.atom ⟨x, .eq⟩))

/- Equal and reversed bounded domains bypass every arithmetic builder. -/
#guard (match build? emptyForall with
    | some result => match result.certificate with
      | .emptyIoc => result.verdict
      | _ => false
    | none => false)
#guard (match build? reversedExists with
    | some result => match result.certificate with
      | .emptyIoc => !result.verdict
      | _ => false
    | none => false)

/- Constant true and false results retain the carrier-free branch. -/
#guard (match build? constantTrue with
    | some result => match result.certificate with
      | .constants => result.verdict
      | _ => false
    | none => false)
#guard (match build? constantFalse with
    | some result => match result.certificate with
      | .constants => !result.verdict
      | _ => false
    | none => false)

/- A checked empty isolation array uses the no-roots branch for either
diagnostic value and performs no common-root work. -/
#guard (match build? noRootTrue with
    | some result => match result.certificate with
      | .noRoots data => result.verdict && data.isolations.intervals.isEmpty
      | _ => false
    | none => false)
#guard (match build? noRootFalse with
    | some result => match result.certificate with
      | .noRoots data => !result.verdict && data.isolations.intervals.isEmpty
      | _ => false
    | none => false)

/- Real positive-root certificates omit endpoint data. -/
#guard (match build? rootExists with
    | some result => match result.certificate with
      | .cells data => result.verdict && data.iocCmps.isNone &&
          0 < data.isolations.intervals.size
      | _ => false
    | none => false)

/- Bounded positive-root certificates include checked endpoint data. -/
#guard (match build? upperIncluded with
    | some result => match result.certificate with
      | .cells data => result.verdict && data.iocCmps.isSome
      | _ => false
    | none => false)

/- Multiple roots produce one strictly separated interval per carrier root. -/
#guard (match build? twoRoots with
    | some result => match result.certificate with
      | .cells data => result.verdict && data.isolations.intervals.size == 2
      | _ => false
    | none => false)

/- Repeated factors and two distinct atoms sharing the same root produce a
square-free carrier and one common package per distinct polynomial. -/
#guard (match build? sharedRepeated with
    | some result => match result.certificate with
      | .cells data =>
          DensePoly.beqCoeffs data.carrier.carrier x &&
            DensePoly.beqCoeffs data.carrier.repeated square &&
            data.signs.commonRoots.length == 2 && !result.verdict
      | _ => false
    | none => false)

/- Constant atoms coexist with one nonconstant common-root package. -/
#guard (match build? mixed with
    | some result => match result.certificate with
      | .cells data => result.verdict && data.signs.commonRoots.length == 1
      | _ => false
    | none => false)

/- All four quantifier forms and half-open endpoint ownership. -/
#guard Hex.RCF.decide emptyForall == some true
#guard Hex.RCF.decide reversedExists == some false
#guard Hex.RCF.decide squareTrue == some true
#guard Hex.RCF.decide rootExists == some true
#guard Hex.RCF.decide boundedForall == some true
#guard Hex.RCF.decide upperIncluded == some true
#guard Hex.RCF.decide lowerExcluded == some false
#guard Hex.RCF.decide constantFalse == some false
#guard Hex.RCF.decide noRootFalse == some false

/- Retained false evidence remains diagnostic, while retained true evidence
passes the proof-producing checker. -/
#guard (match build? constantFalse with
    | some result => !result.certificate.check constantFalse
    | none => false)
#guard (match build? constantTrue with
    | some result => result.certificate.check constantTrue
    | none => false)

/- A replay belonging to another carrier is rejected before separation. -/
#guard (match buildCarrier? twoRoots, buildCarrier? rootExists with
    | some quadCarrier, some xCarrier =>
        (buildIsolations? { quadCarrier with replay := xCarrier.replay }).isNone
    | _, _ => false)

private def wide : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 2) (by decide)]⟩

/- A malformed interval whose endpoint prefix contains two roots makes batch
classification fail instead of inventing a comparison. -/
#guard (match buildCarrier? twoRoots with
    | some carrier =>
        (buildIocCmps? carrier wide (Dyadic.ofInt 2) (Dyadic.ofInt 3)).isNone
    | none => false)

example {carrier : CarrierCert} {isolations : IsolationCert}
    (h : buildIsolations? carrier = some isolations) :
    isolations.checkStrict carrier.replay = true := check_buildIsolations h

example {carrier : CarrierCert} {isolations : IsolationCert} {a b : Dyadic}
    {cmps : IocCmps isolations.intervals.size}
    (h : buildIocCmps? carrier isolations a b = some cmps) :
    cmps.check carrier.carrier carrier.replay isolations a b = true :=
  check_buildIocCmps h

example {s : Sentence} {carrier : CarrierCert} {signs : SignMatrixCert}
    (h : buildSignMatrix? s carrier = some signs) :
    signs.check s carrier = true := check_buildSignMatrix h

example {s : Sentence} {result : BuildResult} (h : build? s = some result) :
    result.certificate.replay? s = some result.verdict := replay_build h

example {s : Sentence} (h : Hex.RCF.decide s = some true) :
    ∃ cert : Certificate, cert.check s = true :=
  decide_eq_some_true_imp_exists_cert h

example {s : Sentence} (h : Hex.RCF.decide s = some true) : s.toProp :=
  decide_sound s h

end Hex.RCF.DecisionTests
