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

private def zeroCert : GcdCert 0 Int Mono.lex :=
  .mk 0 1 1 .unit

example : checkGcd (0 : P0) 0 zeroCert = true := by
  decide +kernel

private def baseCert : GcdCert 0 Int Mono.lex :=
  .mk (C 6) (C 2) (C 3) (.base (-1) 1)

example : baseCheckCoprime (C 2 : P0) (C 3) (.base (-1) 1) = true := by
  decide +kernel

example : polyNormalize (C 6 : P0) == C 6 := by
  decide +kernel

example : (C 6 : P0) * C 2 == C 12 := by
  decide +kernel

example : checkGcd (C 12 : P0) (C 18) baseCert = true := by
  decide +kernel

private def unitCert : GcdCert 1 Int Mono.lex :=
  .mk 1 1 (X 0 + 2) .unit

example : checkGcd (1 : P1) (X 0 + 2) unitCert = true := by
  decide +kernel

private def contentStep₁ : GcdCert 0 Int Mono.lex :=
  .mk (C 2) 0 1 .unit

private def contentStep₂ : GcdCert 0 Int Mono.lex :=
  .mk (C 2) 1 (C 2) .unit

private def contentCert : ContentCert 0 Int Mono.lex :=
  .ofSteps (C 2) [contentStep₁, contentStep₂]

example : checkContent ([C 2, C 4] : List P0) contentCert = true := by
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
