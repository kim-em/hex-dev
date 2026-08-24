/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Gcd

public section

/-! Small kernel-reduced checker replays. Full route-4 producers are tested
with VM evaluation in `HexMvGcd.Eval`; these examples deliberately isolate
the certificate branches so the kernel can reduce them without compiling the
entire recursive PRS producer. -/

namespace Hex.MvPoly

private abbrev P0 := MvPoly 0 Int Mono.lex
private abbrev P1 := MvPoly 1 Int Mono.lex

section OpsOnly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp]
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [BezoutOps R] [GcdProducer R]

/-- Executable construction must not require either proof-law package. -/
example (f h : MvPoly n R cmp) : GcdCert n R cmp :=
  prsCert f h

example (cfg : GcdConfig) (f h : MvPoly n R cmp) : GcdRun n R cmp :=
  gcdCertWith cfg f h

example : GcdOps (MvPoly n R cmp) := inferInstance

end OpsOnly

private def zeroCert : GcdCert 0 Int Mono.lex :=
  .mk 0 1 1 .unit

example : checkGcd (0 : P0) 0 zeroCert = true := by
  decide +kernel

private def baseCert : GcdCert 0 Int Mono.lex :=
  .mk (C 6) (C 2) (C 3) (.base (-1) 1)

example : baseCheckCoprime (C 2 : P0) (C 3) (.base (-1) 1) = true := by
  decide +kernel

private theorem normalizeC6 : polyNormalize (C 6 : P0) == C 6 := by
  unfold polyNormalize polyNormUnit
  rw [leadingTerm_C (by decide : (6 : Int) ≠ 0)]
  decide +kernel

example : polyNormalize (C 6 : P0) == C 6 := normalizeC6

example : (C 6 : P0) * C 2 == C 12 := by
  decide +kernel

example : checkGcd (C 12 : P0) (C 18) baseCert = true := by
  unfold checkGcd checkOps checkGcdUsing baseCert
  dsimp only
  rw [normalizeC6]
  decide +kernel

private def unitCert : GcdCert 1 Int Mono.lex :=
  .mk 1 1 (X 0 + 2) .unit

private theorem normalizeOne : polyNormalize (1 : P1) == 1 := by
  change polyNormalize (C 1 : P1) == C 1
  unfold polyNormalize polyNormUnit
  rw [leadingTerm_C (by decide : (1 : Int) ≠ 0)]
  decide +kernel

example : checkGcd (1 : P1) (X 0 + 2) unitCert = true := by
  unfold checkGcd checkOps checkGcdUsing unitCert
  dsimp only
  rw [normalizeOne]
  decide +kernel

private def contentStep₁ : GcdCert 0 Int Mono.lex :=
  .mk (C 2) 0 1 .unit

private def contentStep₂ : GcdCert 0 Int Mono.lex :=
  .mk (C 2) 1 (C 2) .unit

private def contentCert : ContentCert 0 Int Mono.lex :=
  .ofSteps (C 2) [contentStep₁, contentStep₂]

private theorem normalizeC2 : polyNormalize (C 2 : P0) == C 2 := by
  unfold polyNormalize polyNormUnit
  rw [leadingTerm_C (by decide : (2 : Int) ≠ 0)]
  decide +kernel

example : checkContent ([C 2, C 4] : List P0) contentCert = true := by
  unfold checkContent checkOps checkContentUsing checkContentSteps contentCert
  dsimp only
  unfold checkGcdUsing contentStep₁ contentStep₂ checkContentSteps
  simp only [normalizeC2]
  decide +kernel

private def orderedProducer (_ q : P0) : GcdCert 0 Int Mono.lex :=
  .mk q 0 0 .unit

private def orderedContent : ContentCert 0 Int Mono.lex :=
  contentCertWith orderedProducer [C 2, C 3, C 5]

/-- Producer accumulation preserves coefficient order in the public step list. -/
example : orderedContent.steps.map GcdCert.gcd = [C 2, C 3, C 5] := by
  decide +kernel

private def badBaseCert : GcdCert 0 Int Mono.lex :=
  .mk (C 6) (C 2) (C 2) (.base (-1) 1)

example : checkGcd (C 12 : P0) (C 18) badBaseCert = false := by
  decide +kernel

private def ratLift : RatLiftCert 0 Mono.lex where
  scaleL := 2
  scaleR := 3
  left := 1
  right := 1
  cert := .unit

example : checkRatLift (C 2) (C 3) ratLift = true := by
  decide +kernel

private def ratLiftCoprime : CoprimeCert 0 Rat Mono.lex :=
  .ratLift 2 3 1 1 .unit

example : checkCoprime (C 2) (C 3) ratLiftCoprime = true := by
  decide +kernel

private def intEmbedding : CoeffEmbedding Int Int where
  toFun := fun z => z

/-- The universe-polymorphic implementation constructor must not turn mere
nonzero scaling into a coprimality witness outside a field. -/
private def nonunitLift : CoprimeCert 0 Int Mono.lex :=
  .ratLiftCore intEmbedding (by rfl) (by rfl)
    (by intros; rfl) (by intros; rfl) (by intro a b h; exact h)
    2 2 1 1 1 1 .unit

example : checkCoprime (C 2) (C 2) nonunitLift = false := by
  decide +kernel

end Hex.MvPoly
