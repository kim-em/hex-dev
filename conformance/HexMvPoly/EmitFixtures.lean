/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexMvPolyFixtures

/-!
JSONL emit driver for the `hex-mv-poly` SymPy oracle.

The stream covers normalization, arithmetic (including cancellation), powers,
derivatives, zero/constant queries, arity zero, collision-producing
rename/substitution/partial evaluation, comparator changes, and evaluation.
-/

namespace Hex.MvPolyEmit

open Hex
open Hex.Conformance.Emit
open Hex.MvPoly
open Hex.MvPolyFixtures

private def lib : String := "HexMvPoly"

private def wireTerms {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) : List (List Nat × Int) :=
  p.termsList.map fun term => (term.1.toList, term.2)

private def emitPoly {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (case order : String) (p : MvPoly n Int cmp) : IO Unit :=
  emitMvPolyFixture lib case n order (wireTerms p)

private def emitPolyResult {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (case op : String) (p : MvPoly n Int cmp) : IO Unit :=
  emitResult lib case op (mvPolyValue (wireTerms p))

private def leadingValue {n : Nat}
    (term? : Option (Mono n × Int)) : List Int :=
  match term? with
  | none => []
  | some term => term.1.toList.map Int.ofNat ++ [term.2]

private def emitQueries {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [IsMonomialOrder cmp]
    (case : String) (p : MvPoly n Int cmp) : IO Unit := do
  emitResult lib case "totalDegree" (intListValue [Int.ofNat p.totalDegree])
  emitResult lib case "degreeOf"
    (intListValue ((List.finRange n).map fun i => Int.ofNat (p.degreeOf i)))
  emitResult lib case "vars"
    (intListValue (p.vars.map fun i => Int.ofNat i.val))
  emitResult lib case "leadingCoeff" (intListValue [p.leadingCoeff])
  emitResult lib case "leadingTerm"
    (intListValue (leadingValue p.leadingTerm))

private structure BinaryCase where
  id : String
  left : P3
  right : P3

private def addCases : List BinaryCase := [
  ⟨"add/typical", viewInput, addLeft⟩,
  ⟨"add/edge", zero3, viewInput⟩,
  ⟨"add/adversarial", addLeft, addRight⟩]

private def subCases : List BinaryCase := [
  ⟨"sub/typical", viewInput, addLeft⟩,
  ⟨"sub/edge", zero3, viewInput⟩,
  ⟨"sub/adversarial", addLeft, addLeft⟩]

private def mulCases : List BinaryCase := [
  ⟨"mul/typical", viewInput, mulLeft⟩,
  ⟨"mul/edge", zero3, mulRight⟩,
  ⟨"mul/adversarial", mulLeft, mulRight⟩]

private def emitBinary (op : String) (f : P3 → P3 → P3)
    (cases : List BinaryCase) : IO Unit := do
  for c in cases do
    emitPoly (c.id ++ "/left") "grlex" c.left
    emitPoly (c.id ++ "/right") "grlex" c.right
    emitPolyResult c.id op (f c.left c.right)

private def emitCanonical (case : String) (terms : List (Mono 3 × Int)) :
    IO Unit := do
  emitMvPolyFixture lib case 3 "grlex"
    (terms.map fun term => (term.1.toList, term.2))
  emitPolyResult case "canonicalize" (ofTerms terms : P3)

private def emitEval (case : String) (p : P3) (x : Fin 3 → Int)
    (pointName : String) : IO Unit := do
  emitPoly case "grlex" p
  emitResult lib case ("eval/" ++ pointName) (intListValue [eval x p])
  emitResult lib case ("evalHorner/" ++ pointName)
    (intListValue [evalHorner x p])

private def emitAll : IO Unit := do
  emitCanonical "canonicalize/typical" viewInput.termsList
  emitCanonical "canonicalize/edge" [(Mono.zero, 0)]
  emitCanonical "canonicalize/adversarial" duplicateTerms

  emitBinary "add" (· + ·) addCases
  emitBinary "sub" (· - ·) subCases
  emitBinary "mul" (· * ·) mulCases

  emitPoly "neg/typical" "grlex" viewInput
  emitPolyResult "neg/typical" "neg" (-viewInput)
  emitPoly "neg/edge" "grlex" zero3
  emitPolyResult "neg/edge" "neg" (-zero3)
  emitPoly "neg/adversarial" "grlex" duplicateInput
  emitPolyResult "neg/adversarial" "neg" (-duplicateInput)

  emitPoly "pow/typical" "grlex" viewInput
  emitPolyResult "pow/typical" "pow/2" (viewInput ^ 2)
  emitPoly "pow/edge" "grlex" zero3
  emitPolyResult "pow/edge" "pow/5" (zero3 ^ 5)
  emitPoly "pow/adversarial" "grlex" duplicateInput
  emitPolyResult "pow/adversarial" "pow/0" (duplicateInput ^ 0)

  emitPoly "queries/zero" "grlex" zero3
  emitQueries "queries/zero" zero3

  emitPoly "queries/constant" "grlex" constant3
  emitQueries "queries/constant" constant3

  emitPoly "queries/arityZero" "grlex" arityZero
  emitQueries "queries/arityZero" arityZero

  emitPoly "rename/typical" "grlex" viewInput
  emitPolyResult "rename/typical" "rename/swapFanIn"
    (rename Mono.grlex
      (fun i => if i = 1 then (0 : Fin 2) else 1) viewInput)
  emitPoly "rename/edge" "grlex" zero3
  emitPolyResult "rename/edge" "rename/identity"
    (rename Mono.lex id zero3)
  emitPoly "rename/adversarial" "grlex" renameInput
  emitPolyResult "rename/adversarial" "rename/allToX0"
    (rename Mono.lex (fun _ => (0 : Fin 1)) renameInput)

  emitPoly "subst/typical" "grlex" viewInput
  emitPolyResult "subst/typical" "subst/typical"
    (subst (targetCmp := Mono.grlex)
      (fun i =>
        if i = 0 then (X 0 : P2) + X 1
        else if i = 1 then X 1
        else C 2)
      viewInput)
  emitPoly "subst/edge" "grlex" zero3
  emitPolyResult "subst/edge" "subst/allToX0"
    (subst (targetCmp := Mono.lex) (fun _ => (X 0 : P1)) zero3)
  emitPoly "subst/adversarial" "grlex" substInput
  emitPolyResult "subst/adversarial" "subst/allToX0"
    (subst (targetCmp := Mono.lex) (fun _ => (X 0 : P1)) substInput)

  emitPoly "partialEval/typical" "grlex" viewInput
  emitPolyResult "partialEval/typical" "partialEval/x0=2"
    (partialEval (fun i => if i = 0 then some 2 else none) viewInput)
  emitPoly "partialEval/edge" "grlex" zero3
  emitPolyResult "partialEval/edge" "partialEval/all"
    (partialEval (fun i => some #[4, 0, -2][i]) zero3)
  emitPoly "partialEval/adversarial" "grlex" partialInput
  emitPolyResult "partialEval/adversarial" "partialEval/x0=2"
    (partialEval (fun i => if i = 0 then some 2 else none) partialInput)

  emitPoly "reorder/typical" "grlex" viewInput
  emitPolyResult "reorder/typical" "reorder/grevlex"
    (reorder Mono.grevlex viewInput)
  emitPoly "reorder/edge" "grlex" zero3
  emitPolyResult "reorder/edge" "reorder/lex" (reorder Mono.lex zero3)
  emitPoly "reorder/adversarial" "grlex" duplicateInput
  emitPolyResult "reorder/adversarial" "reorder/lex"
    (reorder Mono.lex duplicateInput)

  emitPoly "queries/typical" "grlex" viewInput
  emitQueries "queries/typical" viewInput

  emitPoly "derivative/typical" "grlex" viewInput
  emitPolyResult "derivative/typical" "derivative/i1"
    (derivative 1 viewInput)
  emitPoly "derivative/edge" "grlex" zero3
  emitPolyResult "derivative/edge" "derivative/i0"
    (derivative 0 zero3)
  emitPoly "derivative/adversarial" "grlex" duplicateInput
  emitPolyResult "derivative/adversarial" "derivative/i2"
    (derivative 2 duplicateInput)

  emitEval "eval/typical" viewInput (fun i => #[2, -1, 3][i])
    "[2,-1,3]"
  emitEval "eval/edge" zero3 (fun _ => 0) "[0,0,0]"
  emitEval "eval/adversarial" duplicateInput (fun i => #[-2, 5, 1][i])
    "[-2,5,1]"

end Hex.MvPolyEmit

def main : IO Unit :=
  Hex.MvPolyEmit.emitAll
