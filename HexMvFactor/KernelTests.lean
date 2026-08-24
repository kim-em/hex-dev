/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvFactor.Irred
public meta import HexMvPoly.Ring
public import HexMvFactor.Irred

public section

/-! Small kernel-reduced replays for the milestone 1–2 checkers. -/

namespace Hex.MvFactor.KernelTests

open Hex
open Hex.MvPoly
open Hex.MvFactor

private abbrev P0 := MvPoly 0 Int Mono.lex
private abbrev P1 := MvPoly 1 Int Mono.lex
private abbrev P2 := MvPoly 2 Int Mono.lex

private def x : P2 := X 0
private def y : P2 := X 1

private def good : Decomp 2 Mono.lex :=
  ⟨1, [⟨x + y, 2⟩, ⟨x + 1, 1⟩]⟩

#guard checkDecomp ((x + y) ^ 2 * (x + 1)) good

private def zeroMultiplicity : Decomp 2 Mono.lex :=
  ⟨1, [⟨x + y, 0⟩]⟩

example : checkDecomp 1 zeroMultiplicity = false := by
  decide +kernel

private def constantFactor : Decomp 2 Mono.lex :=
  ⟨1, [⟨1, 1⟩]⟩

#guard !checkDecomp 1 constantFactor

private def nonprimitive : Decomp 2 Mono.lex :=
  ⟨1, [⟨C 2 * x, 1⟩]⟩

#guard !checkDecomp (C 2 * x) nonprimitive

private def duplicate : Decomp 2 Mono.lex :=
  ⟨1, [⟨x + 1, 1⟩, ⟨x + 1, 2⟩]⟩

#guard !checkDecomp ((x + 1) ^ 3) duplicate

#guard
  match structural? (0 : P2) with
  | some D => D.content == 0 && D.factors.isEmpty && checkDecomp 0 D
  | none => false

#guard
  let f : P2 := C 6 * x ^ 2 * y
  match structural? f with
  | some D =>
      match D.factors with
      | [left, right] =>
          D.content == 6 && left.factor == x && left.multiplicity == 2 &&
            right.factor == y && right.multiplicity == 1 && checkDecomp f D
      | _ => false
  | _ => false

private def split : Split 2 Mono.lex :=
  ⟨x + 1, y + 2⟩

example : checkSplit ((x + 1) * (y + 2)) split = true := by
  decide +kernel

example : checkSplit (x + 1) (⟨1, x + 1⟩ : Split 2 Mono.lex) = false := by
  decide +kernel

private def zeroStep : GcdCert 0 Int Mono.lex :=
  .mk 0 1 1 .unit

private def oneStep : GcdCert 0 Int Mono.lex :=
  .mk 1 0 1 .unit

private def primitiveX : ContentCert 0 Int Mono.lex :=
  .ofSteps 1 [zeroStep, oneStep]

private def x1 : P1 := X 0

private def degreeOneCert : IrredCert 1 Mono.lex :=
  .degreeOne 0 Mono.lex primitiveX

#guard checkIrred x1 degreeOneCert

example : obligations x1 degreeOneCert = [] := by
  decide +kernel

private def noPoint : Fin 0 → Int := fun i => nomatch i

private def imageCert : IrredCert 1 Mono.lex :=
  .image 0 Mono.lex noPoint primitiveX

#guard checkIrred x1 imageCert

#guard obligations x1 imageCert == [DensePoly.ofList [0, 1]]

private def embedded : P2 := constIn (cmp := Mono.lex) 1 Mono.lex x1

private def embedCert : IrredCert 2 Mono.lex :=
  .embed 1 Mono.lex x1 degreeOneCert

#guard checkIrred embedded embedCert

private def completeX : Complete 1 Mono.lex :=
  ⟨⟨1, [⟨x1, 1⟩]⟩, [degreeOneCert]⟩

#guard checkComplete x1 completeX

example : NoKronecker completeX = true := by
  decide +kernel

example :
    checkComplete (0 : P1) (⟨⟨0, []⟩, []⟩ : Complete 1 Mono.lex) = false := by
  decide +kernel

example :
    checkComplete (C 12 : P1)
      (⟨⟨12, []⟩, []⟩ : Complete 1 Mono.lex) = true := by
  decide +kernel

end Hex.MvFactor.KernelTests
