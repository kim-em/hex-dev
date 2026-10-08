/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd

public section

/-!
Kernel-only replay probes for the recursive `hex-mv-gcd` certificate checker.

Each certificate branch has a valid example and a companion whose one changed
field must be rejected. The examples use `decide +kernel`; they do not run a
candidate producer or depend on native evaluation. The nested content example
checks that an outer coefficient fold can replay a lower-arity Bézout split.
-/

namespace Hex.MvGcdBench.Kernel

open Hex
open Hex.MvPoly

abbrev P0 := MvPoly 0 Int Mono.lex
abbrev P1 := MvPoly 1 Int Mono.lex
abbrev Q0 := MvPoly 0 Rat Mono.lex

@[expose] def x : P1 := X 0

theorem normalizeOneP0 : polyNormalize (1 : P0) == 1 := by
  change polyNormalize (C 1 : P0) == C 1
  unfold polyNormalize polyNormUnit
  rw [leadingTerm_C (by decide : (1 : Int) ≠ 0)]
  decide +kernel

theorem normalizeOneP1 : polyNormalize (1 : P1) == 1 := by
  change polyNormalize (C 1 : P1) == C 1
  unfold polyNormalize polyNormUnit
  rw [leadingTerm_C (by decide : (1 : Int) ≠ 0)]
  decide +kernel

theorem normalizeSixP0 : polyNormalize (C 6 : P0) == C 6 := by
  unfold polyNormalize polyNormUnit
  rw [leadingTerm_C (by decide : (6 : Int) ≠ 0)]
  decide +kernel

theorem normalizeX : polyNormalize x == x := by
  unfold x X polyNormalize polyNormUnit
  rw [leadingTerm_monomial (by decide : (1 : Int) ≠ 0)]
  decide +kernel

@[expose] def zeroZeroStep : GcdCert 0 Int Mono.lex :=
  .mk 0 1 1 .unit

@[expose] def zeroOneStep : GcdCert 0 Int Mono.lex :=
  .mk 1 0 1 .unit

@[expose] def oneOneStep : GcdCert 0 Int Mono.lex :=
  .mk 1 1 1 .unit

@[expose] def xContent : ContentCert 0 Int Mono.lex :=
  .ofSteps 1 [zeroZeroStep, zeroOneStep]

@[expose] def xPlusOneContent : ContentCert 0 Int Mono.lex :=
  .ofSteps 1 [zeroOneStep, oneOneStep]

@[expose] def primeTwo : ZMod64.Prime where
  m := 2
  bounds := inferInstance
  prime := by decide

@[expose] def noPoint (i : Fin 0) : @ZMod64 primeTwo.m primeTwo.bounds :=
  Fin.elim0 i

theorem viewX :
    (toUnivariate 0 Mono.lex x).toArray.toList = [0, 1] := by
  unfold x
  decide +kernel

theorem viewXPlusOne :
    (toUnivariate 0 Mono.lex (x + 1)).toArray.toList = [1, 1] := by
  unfold x
  decide +kernel

theorem modularDegreeX :
    letI : ZMod64.Bounds primeTwo.m := primeTwo.bounds
    letI : ZMod64.PrimeModulus primeTwo.m :=
      ZMod64.primeModulusOfPrime primeTwo.prime
    decide ((imageAt primeTwo (intCoeffHom primeTwo) noPoint
      0 Mono.lex x).degree? = (toUnivariate 0 Mono.lex x).degree?) = true := by
  unfold x imageAt
  decide +kernel

theorem modularDegreeXPlusOne :
    letI : ZMod64.Bounds primeTwo.m := primeTwo.bounds
    letI : ZMod64.PrimeModulus primeTwo.m :=
      ZMod64.primeModulusOfPrime primeTwo.prime
    decide ((imageAt primeTwo (intCoeffHom primeTwo) noPoint
      0 Mono.lex (x + 1)).degree? =
        (toUnivariate 0 Mono.lex (x + 1)).degree?) = true := by
  unfold x imageAt
  decide +kernel

theorem modularCombination :
    letI : ZMod64.Bounds primeTwo.m := primeTwo.bounds
    letI : ZMod64.PrimeModulus primeTwo.m :=
      ZMod64.primeModulusOfPrime primeTwo.prime
    let fImage := imageAt primeTwo (intCoeffHom primeTwo)
      noPoint 0 Mono.lex x
    let hImage := imageAt primeTwo (intCoeffHom primeTwo)
      noPoint 0 Mono.lex (x + 1)
    (1 * fImage + 1 * hImage == 1) = true := by
  unfold x imageAt
  decide +kernel

@[expose] def modularSplit : CoprimeCert 1 Int Mono.lex :=
  .split 0 Mono.lex primeTwo (intCoeffHom primeTwo) noPoint
    1 1 xContent xPlusOneContent .unit

@[expose] def badModularSplit : CoprimeCert 1 Int Mono.lex :=
  .split 0 Mono.lex primeTwo (intCoeffHom primeTwo) noPoint
    1 0 xContent xPlusOneContent .unit

theorem modularSplitValid : checkCoprime x (x + 1) modularSplit = true := by
  simp only [checkCoprime, succCheckCoprime, Cert.succCheck, modularSplit]
  unfold checkContentUsing checkContentSteps checkGcdUsing
    xContent xPlusOneContent zeroZeroStep zeroOneStep oneOneStep
  unfold baseCheckCoprime Cert.baseCheck
  unfold Nat.Internal.elimOffset
  dsimp only
  simp only [modularDegreeX, modularDegreeXPlusOne, modularCombination,
    viewX, viewXPlusOne, polyNormalize_zero, normalizeOneP0]
  simp only [checkContentSteps, normalizeOneP0]
  decide +kernel

theorem modularSplitCorrupt :
    checkCoprime x (x + 1) badModularSplit = false := by
  decide +kernel

@[expose] def bezoutSplit : CoprimeCert 1 Int Mono.lex :=
  .splitBezout 0 Mono.lex (-1) 1 1
    xContent xPlusOneContent .unit

@[expose] def badBezoutSplit : CoprimeCert 1 Int Mono.lex :=
  .splitBezout 0 Mono.lex (-1) 1 2
    xContent xPlusOneContent .unit

theorem bezoutSplitValid : checkCoprime x (x + 1) bezoutSplit = true := by
  unfold checkCoprime checkOps succCheckCoprime Cert.succCheck bezoutSplit
  dsimp only
  unfold checkContentUsing checkContentSteps checkGcdUsing
    xContent xPlusOneContent zeroZeroStep zeroOneStep oneOneStep
  unfold baseCheckCoprime Cert.baseCheck
  unfold Nat.Internal.elimOffset
  dsimp only
  simp only [viewX, viewXPlusOne, polyNormalize_zero, normalizeOneP0]
  simp only [checkContentSteps, normalizeOneP0]
  decide +kernel

theorem bezoutSplitCorrupt :
    checkCoprime x (x + 1) badBezoutSplit = false := by
  decide +kernel

@[expose] def strippedReplay (cert : CoprimeCert 1 Int Mono.lex) : Bool :=
  match Cert.stripCoprime? cert with
  | none => false
  | some ordinary =>
      (Cert.checkOps (S := Int) (E := Cert.NoLeaves)
        (fun _ _ _ _ _ impossible => nomatch impossible) 1).coprime
          Mono.lex x (x + 1) ordinary

/-- Extraction preserves modular replay, including both content folds. -/
theorem stripModularValid : strippedReplay modularSplit = true := by
  change checkCoprime x (x + 1) modularSplit = true
  exact modularSplitValid

/-- Extraction preserves Bézout replay, including both content folds. -/
theorem stripBezoutValid : strippedReplay bezoutSplit = true := by
  change checkCoprime x (x + 1) bezoutSplit = true
  exact bezoutSplitValid

@[expose] def directBezout : CoprimeCert 1 Int Mono.lex :=
  .bezout (-1) 1

@[expose] def badDirectBezout : CoprimeCert 1 Int Mono.lex :=
  .bezout 0 1

theorem directBezoutValid :
    checkCoprime x (x + 1) directBezout = true := by
  unfold checkCoprime checkOps succCheckCoprime directBezout
  unfold x
  decide +kernel

theorem directBezoutCorrupt :
    checkCoprime x (x + 1) badDirectBezout = false := by
  unfold checkCoprime checkOps succCheckCoprime badDirectBezout
  unfold x
  decide +kernel

@[expose] def baseCert : GcdCert 0 Int Mono.lex :=
  .mk (C 6) (C 2) (C 3) (.base (-1) 1)

@[expose] def badBaseCert : GcdCert 0 Int Mono.lex :=
  .mk (C 6) (C 2) (C 3) (.base 0 1)

theorem baseValid : checkGcd (C 12 : P0) (C 18) baseCert = true := by
  unfold checkGcd checkOps checkGcdUsing baseCert
  dsimp only
  rw [normalizeSixP0]
  decide +kernel

theorem baseCorrupt : checkGcd (C 12 : P0) (C 18) badBaseCert = false := by
  unfold checkGcd checkOps checkGcdUsing badBaseCert
  dsimp only
  rw [normalizeSixP0]
  decide +kernel

@[expose] def ratLift : CoprimeCert 0 Rat Mono.lex :=
  .ratLift 2 3 1 1 .unit

@[expose] def badRatLift : CoprimeCert 0 Rat Mono.lex :=
  .ratLift 2 4 1 1 .unit

theorem ratLiftValid : checkCoprime (C 2 : Q0) (C 3) ratLift = true := by
  decide +kernel

theorem ratLiftCorrupt :
    checkCoprime (C 2 : Q0) (C 3) badRatLift = false := by
  decide +kernel

@[expose] def firstNestedStep : GcdCert 1 Int Mono.lex :=
  .mk x 0 1 .unit

@[expose] def secondNestedStep : GcdCert 1 Int Mono.lex :=
  .mk 1 x (x + 1) bezoutSplit

@[expose] def nestedContent : ContentCert 1 Int Mono.lex :=
  .ofSteps 1 [firstNestedStep, secondNestedStep]

@[expose] def badNestedContent : ContentCert 1 Int Mono.lex :=
  .ofSteps 2 [firstNestedStep, secondNestedStep]

theorem firstNestedValid :
    checkGcdUsing (succCheckCoprime (checkOps 0))
      (0 : P1) x firstNestedStep = true := by
  unfold checkGcdUsing firstNestedStep
  rw [normalizeX]
  unfold x
  decide +kernel

theorem bezoutReplay :
    succCheckCoprime (checkOps 0) x (x + 1) bezoutSplit = true := by
  exact bezoutSplitValid

theorem secondNestedValid :
    checkGcdUsing (succCheckCoprime (checkOps 0))
      x (x + 1) secondNestedStep = true := by
  unfold checkGcdUsing secondNestedStep
  rw [normalizeOneP1, bezoutReplay]
  unfold x
  decide +kernel

theorem firstNestedGcd : firstNestedStep.gcd = x := by
  rfl

theorem secondNestedGcd : secondNestedStep.gcd = 1 := by
  rfl

theorem nestedContentValid :
    checkContent [x, x + 1] nestedContent = true := by
  unfold checkContent checkOps checkContentUsing nestedContent
  simp only [checkContentSteps, firstNestedGcd,
    secondNestedGcd, firstNestedValid, secondNestedValid]
  decide +kernel

theorem nestedContentCorrupt :
    checkContent [x, x + 1] badNestedContent = false := by
  unfold checkContent checkOps checkContentUsing badNestedContent
  simp only [checkContentSteps, firstNestedGcd,
    secondNestedGcd, firstNestedValid, secondNestedValid]
  decide +kernel

@[expose] def zeroCert : GcdCert 0 Int Mono.lex :=
  .mk 0 1 1 .unit

@[expose] def badZeroCert : GcdCert 0 Int Mono.lex :=
  .mk 1 1 1 .unit

theorem zeroValid : checkGcd (0 : P0) 0 zeroCert = true := by
  decide +kernel

theorem zeroCorrupt : checkGcd (0 : P0) 0 badZeroCert = false := by
  decide +kernel

@[expose] def unitCert : GcdCert 1 Int Mono.lex :=
  .mk 1 1 (x + 1) .unit

@[expose] def badUnitCert : GcdCert 1 Int Mono.lex :=
  .mk 1 1 x .unit

theorem unitValid : checkGcd 1 (x + 1) unitCert = true := by
  unfold checkGcd checkOps checkGcdUsing unitCert
  dsimp only
  rw [normalizeOneP1]
  decide +kernel

theorem unitCorrupt : checkGcd 1 (x + 1) badUnitCert = false := by
  unfold checkGcd checkOps checkGcdUsing badUnitCert
  dsimp only
  rw [normalizeOneP1]
  decide +kernel

section ConstructionApi

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp]
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [BezoutOps R] [GcdProducer R]

/-- Executable construction does not require either checker proof package. -/
example (f h : MvPoly n R cmp) : GcdCert n R cmp :=
  prsCert f h

example (cfg : GcdConfig) (f h : MvPoly n R cmp) : GcdRun n R cmp :=
  gcdCertWith cfg f h

example : GcdOps (MvPoly n R cmp) := inferInstance

end ConstructionApi

@[expose] def orderedProducer (_ q : P0) : GcdCert 0 Int Mono.lex :=
  .mk q 0 0 .unit

@[expose] def orderedContent : ContentCert 0 Int Mono.lex :=
  contentCertWith orderedProducer [C 2, C 3, C 5]

/-- Producer accumulation preserves coefficient order in the public steps. -/
theorem orderedContentSteps :
    orderedContent.steps.map GcdCert.gcd = [C 2, C 3, C 5] := by
  decide +kernel

@[expose] def flatRatLift : RatLiftCert 0 Mono.lex where
  scaleL := 2
  scaleR := 3
  left := 1
  right := 1
  cert := .unit

theorem flatRatLiftValid : checkRatLift (C 2) (C 3) flatRatLift = true := by
  decide +kernel

/-- Integer coefficients cannot supply a rational-lift representation. -/
theorem noIntegerLift (model : RatModel Int) : False :=
  model.not_int

end Hex.MvGcdBench.Kernel
