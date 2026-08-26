/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexMvFactor

/-!
Deterministic public-answer and point-route fixtures for `HexMvFactor`.

Factorization results retain the integer content and multiplicities, while
factor order is deliberately left to the oracle's comparator-aware
normalization. Irreducibility fixtures record the certificate producer used
by Lean; the Boolean decision alone is compared with SymPy. Point fixtures
exercise the caller-selected Wang point before search can recover at another
point.
-/

namespace Hex.MvFactorEmit

open Hex
open Hex.Conformance.Emit
open Hex.MvPoly
open Hex.MvFactor
open scoped Hex

private def lib : String := "HexMvFactor"

private def wireTerms {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) : List (List Nat × Int) :=
  p.termsList.map fun term => (term.1.toList, term.2)

private def coefficients (p : ZPoly) : List Int :=
  p.toArray.toList

private def constructorName {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : IrredCert n cmp → String
  | @IrredCert.degreeOne _ _ _ _ _ _ _ _ => "degreeOne"
  | @IrredCert.image _ _ _ _ _ _ _ _ _ => "image"
  | @IrredCert.embed _ _ _ _ _ _ _ _ _ => "embed"
  | @IrredCert.kronecker _ _ _ _ _ _ => "kronecker"

private def emitFactor {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] (case order : String) (subject : MvPoly n Int cmp) :
    IO Unit := do
  emitMvFactorFixture lib case n order (wireTerms subject)
  match factor? subject with
  | .error _ => throw <| IO.userError s!"factor search exhausted for {case}"
  | .ok answer =>
      let factors := answer.raw.factors.map fun entry =>
        (wireTerms entry.factor, entry.multiplicity)
      emitResult lib case "mvfactor"
        (mvFactorValue answer.raw.content factors)

private def emitIrred {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] (case order : String) (subject : MvPoly n Int cmp) :
    IO Unit := do
  emitMvIrredFixture lib case n order (wireTerms subject)
  let cfg := { Config.default with kronecker := true }
  match irredCert? cfg subject with
  | .ok (cert, _) =>
      emitResult lib case "mvirred"
        (mvIrredValue true (constructorName cert))
  | .error _ =>
      match kronDecide subject with
      | .reducible split =>
          if checkSplit subject split then
            emitResult lib case "mvirred" (mvIrredValue false "split")
          else
            throw <| IO.userError s!"unchecked reducibility split for {case}"
      | .irreducible cert =>
          if checkIrred subject cert then
            emitResult lib case "mvirred"
              (mvIrredValue true (constructorName cert))
          else
            throw <| IO.userError s!"unchecked irreducibility certificate for {case}"

private def pointRejectName : PointReject → String
  | .degreeDrop => "degreeDrop"
  | .notSquarefree => "notSquarefree"
  | .leadingSplit => "leadingSplit"

private def emitPoint (case : String) (point : Fin 1 → Int)
    (subject : MvPoly 2 Int Mono.lex) : IO Unit := do
  emitMvPointFixture lib case 2 "lex" (wireTerms subject) 0 (List.ofFn point)
  let leadingCoeff := MvHensel.lcIn 0 Mono.lex subject
  match factor? leadingCoeff with
  | .error _ => throw <| IO.userError s!"leading factorization failed for {case}"
  | .ok leading =>
      match probe Config.default 0 Mono.lex point subject leading.raw
          (Rand.ofSeed 0) with
      | .error reject =>
          emitResult lib case "mvpoint"
            (mvPointRejectValue (pointRejectName reject))
      | .ok (accepted, _) =>
          emitResult lib case "mvpoint"
            (mvPointSuccessValue (accepted.images.map coefficients)
              (accepted.leading.map wireTerms))

private def emitStructural : IO Unit := do
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  emitFactor "structural/zero" "lex" (0 : MvPoly 2 Int Mono.lex)
  emitFactor "structural/one" "lex" (1 : MvPoly 2 Int Mono.lex)
  emitFactor "structural/negative-one" "lex" (-1 : MvPoly 2 Int Mono.lex)
  emitFactor "structural/six" "lex" (C 6 : MvPoly 2 Int Mono.lex)
  emitFactor "structural/twelve-x" "lex" (C 12 * x)
  emitFactor "structural/x2-y3" "lex" (x ^ 2 * y ^ 3)
  emitFactor "structural/six-x2-y" "lex" (C 6 * x ^ 2 * y)

private def emitFactorCases : IO Unit := do
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let g := x + y + 1
  let h := x + 1
  emitFactor "factor/repeated-3-1" "lex" (g ^ 3 * h)
  emitFactor "factor/repeated-2-5" "lex" (g ^ 2 * h ^ 5)
  emitFactor "factor/nonconstant-shared-leading" "lex"
    (((y + 1) * x + 1) * ((y + 1) * x + 2))
  emitFactor "factor/split-leading-content" "lex"
    ((C 2 * y * x + 1) * (C 3 * x + y))
  emitFactor "factor/three-way" "lex" ((x + 1) * (x + y + 2) * (x - y + 3))
  emitFactor "factor/sparse-dense-lift" "lex"
    ((x + y ^ 2 + 1) * (x - y ^ 2 + 2))

  let x3 : MvPoly 3 Int Mono.lex := X 0
  emitFactor "factor/arity-three" "lex"
    ((x3 + X 1 + 1) * (x3 + X 2 + 2))
  let x4 : MvPoly 4 Int Mono.lex := X 0
  emitFactor "factor/arity-four" "lex"
    ((x4 + X 1 + X 2 + 1) * (x4 + X 3 + 2))
  let x5 : MvPoly 5 Int Mono.lex := X 0
  emitFactor "factor/arity-five" "lex"
    ((x5 + X 1 + X 2 + 1) * (x5 + X 3 + X 4 + 2))

  let gx : MvPoly 2 Int Mono.grlex := X 0
  let gy : MvPoly 2 Int Mono.grlex := X 1
  emitFactor "factor/grlex-order" "grlex"
    ((gx - gy) * (gx + gy + 1))
  let rx : MvPoly 2 Int Mono.grevlex := X 0
  let ry : MvPoly 2 Int Mono.grevlex := X 1
  emitFactor "factor/grevlex-order" "grevlex"
    ((rx - ry) * (rx + ry + 1))

private def emitIrredCases : IO Unit := do
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  emitIrred "irred/degree-one" "lex" (x + y + 1)
  emitIrred "irred/constant-leading" "lex" (x ^ 2 + y ^ 2 + 1)
  emitIrred "irred/monomial-leading" "lex" (y * x ^ 2 + x + y + 1)
  emitIrred "irred/nonconstant-leading" "lex" ((y + 1) * x ^ 2 + x + y)
  emitIrred "irred/reducible" "lex" ((x + 1) * (y + 1))
  let x3 : MvPoly 3 Int Mono.lex := X 0
  emitIrred "irred/arity-three" "lex" (x3 + X 1 + X 2 + 1)
  let x4 : MvPoly 4 Int Mono.lex := X 0
  emitIrred "irred/arity-four" "lex" (x4 + X 1 + X 2 + X 3 + 1)
  let x5 : MvPoly 5 Int Mono.lex := X 0
  emitIrred "irred/arity-five" "lex" (x5 + X 1 + X 2 + X 3 + X 4 + 1)

private def emitPointCases : IO Unit := do
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let atZero : Fin 1 → Int := fun _ => 0
  let atNegOne : Fin 1 → Int := fun _ => -1
  let atOne : Fin 1 → Int := fun _ => 1
  let atFive : Fin 1 → Int := fun _ => 5
  emitPoint "point/degree-drop" atZero (y * x + 1)
  emitPoint "point/not-squarefree" atZero ((x + 1) ^ 2 + y)
  emitPoint "point/unlucky-split" atNegOne (x ^ 2 + y)
  emitPoint "point/unlucky-recovery" atOne (x ^ 2 + y)
  emitPoint "point/split-leading-content" atFive
    ((C 2 * y * x + 1) * (C 3 * x + y))

end Hex.MvFactorEmit

def main : IO Unit := do
  Hex.MvFactorEmit.emitStructural
  Hex.MvFactorEmit.emitFactorCases
  Hex.MvFactorEmit.emitIrredCases
  Hex.MvFactorEmit.emitPointCases
