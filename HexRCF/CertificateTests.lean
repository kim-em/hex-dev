/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Soundness

public section

/-! Regression tests for quantified certificate replay and rejection paths. -/

namespace Hex.RCF.CertificateTests

open HexRealRootsMathlib

private def zero : ZPoly := 0
private def one : ZPoly := DensePoly.ofCoeffs #[(1 : Int)]
private def minusOne : ZPoly := DensePoly.ofCoeffs #[(-1 : Int)]
private def x : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]
private def twiceX : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 2]
private def quad : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
private def posQuad : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 0, 1]

/-! Strict option folds propagate active failures past decisive Booleans, but
bounded filtering ignores failures in irrelevant cells. -/

private def failAtOne (n : Nat) : Option Bool :=
  if n = 1 then none else some (n = 0)

private def falseThenFail (n : Nat) : Option Bool :=
  if n = 1 then none else some false

example : OptionFold.all failAtOne [0, 1] = none := by decide
example : OptionFold.any failAtOne [0, 1] = none := by decide
example : OptionFold.all falseThenFail [0, 1] = none := by decide
example : OptionFold.allArray #[] failAtOne = some true := by decide
example : OptionFold.anyArray #[] failAtOne = some false := by decide
example : OptionFold.allWhereArray #[0, 1] (fun n => n == 0) failAtOne =
    some true := by decide
example : OptionFold.anyWhereArray #[0, 1] (fun n => n == 0) failAtOne =
    some true := by decide
example : OptionFold.allWhereArray #[0, 1] (fun _ => true) falseThenFail =
    none := by decide
example : OptionFold.anyWhereArray #[0, 1] (fun _ => true) failAtOne =
    none := by decide
example : OptionFold.allWhereArray #[0, 1] (fun _ => false) failAtOne =
    some true := by decide
example : OptionFold.anyWhereArray #[0, 1] (fun _ => false) failAtOne =
    some false := by decide

/-! Empty bounded domains bypass every decomposition layer. -/

private def emptyForall : Sentence := .forallIoc 0 0 .ff
private def emptyExists : Sentence := .existsIoc 0 0 .tt
private def reverseForall : Sentence :=
  .forallIoc (Dyadic.ofInt 1) (Dyadic.ofInt (-1)) (.atom ⟨x, .eq⟩)
private def reverseExists : Sentence :=
  .existsIoc (Dyadic.ofInt 1) (Dyadic.ofInt (-1)) (.atom ⟨x, .eq⟩)

example : Certificate.emptyIoc.replay? emptyForall = some true := by decide
example : Certificate.emptyIoc.check emptyForall = true := by decide
example : Certificate.emptyIoc.replay? emptyExists = some false := by decide
example : Certificate.emptyIoc.check emptyExists = false := by decide
example : Certificate.emptyIoc.replay? reverseForall = some true := by decide
example : Certificate.emptyIoc.replay? reverseExists = some false := by decide
example : Certificate.emptyIoc.replay? (.forallReal .tt) = none := by decide
example : Certificate.emptyIoc.replay?
    (.forallIoc 0 (Dyadic.ofInt 1) .tt) = none := by decide
example : emptyForall.toProp := check_sound emptyForall .emptyIoc (by decide)
example : reverseForall.toProp := check_sound reverseForall .emptyIoc (by decide)

/-! Constant-only sentences never construct a carrier. -/

private def constantTrue : Formula :=
  .and (.atom ⟨zero, .eq⟩) (.atom ⟨one, .gt⟩)
private def constantFalse : Formula := .atom ⟨one, .lt⟩

example : Certificate.constants.replay? (.forallReal constantTrue) =
    some true := by decide
example : Certificate.constants.replay? (.existsReal constantTrue) =
    some true := by decide
example : Certificate.constants.replay?
    (.forallIoc 0 (Dyadic.ofInt 1) constantTrue) = some true := by decide
example : Certificate.constants.replay?
    (.existsIoc 0 (Dyadic.ofInt 1) constantTrue) = some true := by decide
example : Certificate.constants.replay? (.forallReal constantFalse) =
    some false := by decide
example : Certificate.constants.check (.forallReal constantFalse) = false := by decide
example : Certificate.constants.replay? (.forallReal (.atom ⟨x, .eq⟩)) =
    none := by decide
example : Certificate.constants.replay? (.forallIoc 0 0 constantTrue) =
    none := by decide
example : Sentence.toProp (.forallReal constantTrue) :=
  check_sound _ .constants (by decide)
example : Sentence.toProp (.existsIoc 0 (Dyadic.ofInt 1) constantTrue) :=
  check_sound _ .constants (by decide)

/-! A positive quadratic exercises the carrier branch with no real roots. -/

private def posReplay : SturmReplay where
  chain := #[posQuad, x, minusOne]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

private def posCarrier : CarrierCert where
  carrier := posQuad
  repeated := one
  derivPart := twiceX
  factorScale := 1
  derivScale := 1
  replay := posReplay

private def posCommon : CommonRootCert where
  gcd := posQuad
  atomFactor := one
  carrierFactor := one
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some posReplay

private def noRoots : IsolationCert := ⟨#[]⟩
private def noRootCert : Certificate :=
  .noRoots ⟨posCarrier, noRoots⟩

private def posGt : Formula := .atom ⟨posQuad, .gt⟩
private def posLt : Formula := .atom ⟨posQuad, .lt⟩

example : noRootCert.replay? (.forallReal posGt) = some true := by decide
example : noRootCert.replay? (.existsReal posGt) = some true := by decide
example : noRootCert.replay?
    (.forallIoc 0 (Dyadic.ofInt 1) posGt) = some true := by decide
example : noRootCert.replay?
    (.existsIoc 0 (Dyadic.ofInt 1) posGt) = some true := by decide
example : noRootCert.replay? (.forallReal posLt) = some false := by decide
example : noRootCert.replay? (.existsReal posLt) = some false := by decide
example : noRootCert.replay? (.forallIoc 0 0 posGt) = none := by decide
example : Sentence.toProp (.forallReal posGt) :=
  check_sound _ noRootCert (by decide)
example : Sentence.toProp (.existsIoc 0 (Dyadic.ofInt 1) posGt) :=
  check_sound _ noRootCert (by decide)

private def badNoRoots : Certificate :=
  .noRoots ⟨{ posCarrier with factorScale := 0 }, noRoots⟩
example : badNoRoots.replay? (.forallReal posGt) = none := by decide

/-! A singleton carrier covers all quantifiers and endpoint equality. -/

private def linearReplay : SturmReplay where
  chain := #[x, one]
  derivScale := 1
  steps := #[]

private def linearCarrier : CarrierCert where
  carrier := x
  repeated := one
  derivPart := one
  factorScale := 1
  derivScale := 1
  replay := linearReplay

private def linearCommon : CommonRootCert where
  gcd := x
  atomFactor := one
  carrierFactor := one
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some linearReplay

private def singleton : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-1)) (Dyadic.ofInt 1) (by decide)]⟩
private def linearMatrix : SignMatrixCert := ⟨[linearCommon]⟩

private def lowerGt : Vector Separation.RootCmp 1 := ⟨#[.gt], by decide⟩
private def lowerEq : Vector Separation.RootCmp 1 := ⟨#[.eq], by decide⟩
private def upperEq : Vector Separation.RootCmp 1 := ⟨#[.eq], by decide⟩
private def upperLt : Vector Separation.RootCmp 1 := ⟨#[.lt], by decide⟩
private def leftCmps : IocCmps 1 := ⟨lowerGt, upperEq⟩
private def rightCmps : IocCmps 1 := ⟨lowerEq, upperLt⟩

private def realLinear : Certificate := .cells
  ⟨linearCarrier, singleton, linearMatrix, none⟩
private def wrongNoRoots : Certificate := .noRoots
  ⟨linearCarrier, singleton⟩
private def leftLinear : Certificate := .cells
  ⟨linearCarrier, singleton, linearMatrix, some leftCmps⟩
private def rightLinear : Certificate := .cells
  ⟨linearCarrier, singleton, linearMatrix, some rightCmps⟩

private def xEq : Formula := .atom ⟨x, .eq⟩
private def xLe : Formula := .atom ⟨x, .le⟩
private def xGt : Formula := .atom ⟨x, .gt⟩

private def badRootCount : Certificate := .noRoots
  ⟨linearCarrier, noRoots⟩

example : realLinear.replay? (.existsReal xEq) = some true := by decide
example : wrongNoRoots.replay? (.existsReal xEq) = none := by decide
example : badRootCount.replay? (.forallReal xGt) = none := by decide
example : realLinear.replay? (.forallReal xEq) = some false := by decide
example : leftLinear.replay?
    (.forallIoc (Dyadic.ofInt (-1)) 0 xLe) = some true := by decide
example : leftLinear.replay?
    (.existsIoc (Dyadic.ofInt (-1)) 0 xEq) = some true := by decide
/-- Equality at the lower endpoint is excluded. -/
example : rightLinear.replay?
    (.existsIoc 0 (Dyadic.ofInt 1) xEq) = some false := by decide
example : rightLinear.replay?
    (.forallIoc 0 (Dyadic.ofInt 1) xGt) = some true := by decide
example : Sentence.toProp (.existsReal xEq) :=
  check_sound _ realLinear (by decide)
example : Sentence.toProp (.forallIoc 0 (Dyadic.ofInt 1) xGt) :=
  check_sound _ rightLinear (by decide)

/-! Real/bounded shape mismatches and malformed nested evidence fail closed. -/

example : leftLinear.replay? (.existsReal xEq) = none := by decide
example : realLinear.replay?
    (.existsIoc (Dyadic.ofInt (-1)) 0 xEq) = none := by decide
private def badMatrix : Certificate := .cells
  ⟨linearCarrier, singleton, ⟨[]⟩, none⟩
example : badMatrix.replay? (.existsReal xEq) = none := by decide
private def wrongSingleton : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt 1) (Dyadic.ofInt 2) (by decide)]⟩
private def badIsolation : Certificate := .cells
  ⟨linearCarrier, wrongSingleton, linearMatrix, none⟩
example : badIsolation.replay? (.existsReal xEq) = none := by decide
private def badCmps : IocCmps 1 := ⟨lowerEq, upperEq⟩
private def badEndpoint : Certificate := .cells
  ⟨linearCarrier, singleton, linearMatrix, some badCmps⟩
example : badEndpoint.replay?
    (.existsIoc (Dyadic.ofInt (-1)) 0 xEq) = none := by decide
private def zeroCells : Certificate := .cells
  ⟨posCarrier, noRoots, ⟨[posCommon]⟩, none⟩
example : zeroCells.replay? (.forallReal posGt) = none := by decide

/-! A two-root carrier exercises a nontrivial five-cell fold. -/

private def quadReplay : SturmReplay where
  chain := #[quad, x, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

private def quadCarrier : CarrierCert where
  carrier := quad
  repeated := one
  derivPart := twiceX
  factorScale := 1
  derivScale := 1
  replay := quadReplay

private def quadCommon : CommonRootCert where
  gcd := quad
  atomFactor := one
  carrierFactor := one
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some quadReplay

private def negHalf : Dyadic := Dyadic.ofInt (-1) >>> (1 : Int)
private def half : Dyadic := Dyadic.ofInt 1 >>> (1 : Int)
private def twoRoots : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-2)) negHalf (by decide),
  DyadicInterval.mk half (Dyadic.ofInt 2) (by decide)]⟩
private def realQuad : Certificate := .cells
  ⟨quadCarrier, twoRoots, ⟨[quadCommon]⟩, none⟩
private def quadEq : Formula := .atom ⟨quad, .eq⟩
private def quadNe : Formula := .atom ⟨quad, .ne⟩
private def quadLt : Formula := .atom ⟨quad, .lt⟩

private def gapLower : Vector Separation.RootCmp 2 :=
  ⟨#[.lt, .gt], by decide⟩
private def gapUpper : Vector Separation.RootCmp 2 :=
  ⟨#[.lt, .gt], by decide⟩
private def gapCmps : IocCmps 2 := ⟨gapLower, gapUpper⟩
private def boundedQuad : Certificate := .cells
  ⟨quadCarrier, twoRoots, ⟨[quadCommon]⟩, some gapCmps⟩

example : realQuad.replay? (.existsReal quadEq) = some true := by decide
example : realQuad.replay? (.forallReal quadNe) = some false := by decide
example : boundedQuad.replay? (.forallIoc negHalf half quadLt) =
    some true := by decide
example : boundedQuad.replay? (.existsIoc negHalf half quadLt) =
    some true := by decide
example : Sentence.toProp (.existsReal quadEq) :=
  check_sound _ realQuad (by decide)
example : Sentence.toProp (.forallIoc negHalf half quadLt) :=
  check_sound _ boundedQuad (by decide)

end Hex.RCF.CertificateTests
