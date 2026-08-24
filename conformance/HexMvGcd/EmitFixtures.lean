/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexMvGcd

/-!
Deterministic JSONL fixtures for the `HexMvGcd` SymPy oracle.

The integer gcd stream includes the normalized gcd and both checked cofactors.
Characteristic-zero squarefree records include scalar content and the ordered
factor/multiplicity ladder.  Characteristic-three records exercise only the
exact Boolean decision, as positive-characteristic decomposition is outside
the library's scope.
-/

namespace Hex.MvGcdEmit

open Hex
open Hex.Conformance.Emit
open Hex.MvPoly

private def lib : String := "HexMvGcd"

private def wireTerms {n : Nat} {R : Type} [Zero R]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (coeff : R → Int) (p : MvPoly n R cmp) : List (List Nat × Int) :=
  p.termsList.map fun term => (term.1.toList, coeff term.2)

private def intTerms {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) : List (List Nat × Int) :=
  wireTerms id p

private def gcdValue {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (g left right : MvPoly n Int cmp) : String :=
  "{" ++ "\"gcd\":" ++ mvPolyValue (intTerms g) ++
    ",\"left\":" ++ mvPolyValue (intTerms left) ++
    ",\"right\":" ++ mvPolyValue (intTerms right) ++ "}"

private def emitGcd {n : Nat} (case : String)
    (f h : MvPoly n Int Mono.lex) : IO Unit := do
  emitMvGcdFixture lib case n "lex" "int" none (intTerms f) (intTerms h)
  let cert := gcdCert f h
  emitResult lib case "mvgcd" (gcdValue cert.gcd cert.cofL cert.cofR)

private def factorsValue {n : Nat}
    (factors : List (SqfFactor n Int Mono.lex)) : String :=
  let values := factors.map fun factor =>
    "{" ++ "\"factor\":" ++ mvPolyValue (intTerms factor.factor) ++
      ",\"multiplicity\":" ++ toString factor.multiplicity ++ "}"
  "[" ++ String.intercalate "," values ++ "]"

private def sqfValue {n : Nat} (d : SqfDecomp n Int Mono.lex) : String :=
  "{" ++ "\"content\":" ++ toString d.content ++
    ",\"factors\":" ++ factorsValue d.factors ++ "}"

private def emitSqf {n : Nat} (case : String)
    (p : MvPoly n Int Mono.lex) : IO Unit := do
  emitMvSqfFixture lib case n "lex" "int" (intTerms p)
  emitResult lib case "mvsqf" (sqfValue (sqfDecomp p))

private theorem boundsThree : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
attribute [local instance] boundsThree

private theorem primeThree : ZMod64.PrimeModulus 3 :=
  ZMod64.primeModulusOfPrime (by decide)
attribute [local instance] primeThree

private def modThreeTerms {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n (ZMod64 3) cmp) : List (List Nat × Int) :=
  wireTerms (fun coefficient => Int.ofNat coefficient.toNat) p

private def emitSquarefree (case : String)
    (p : MvPoly 2 (ZMod64 3) Mono.lex) : IO Unit := do
  emitMvSquarefreeFixture lib case 2 "lex" 3 (modThreeTerms p)
  emitResult lib case "mvsquarefree" (toString (isSquarefree p))

private def emitGcdCases : IO Unit := do
  let zero2 : MvPoly 2 Int Mono.lex := 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  emitGcd "gcd/zero-zero" zero2 zero2
  emitGcd "gcd/zero-right" zero2 (C 6 * x - C 3 * y)
  emitGcd "gcd/right-unit" (x ^ 2 + y + 1) 1
  emitGcd "gcd/constants" (C 12 : MvPoly 2 Int Mono.lex) (C 18)
  emitGcd "gcd/coprime-linear" (x + y + 1) (x + C 2 * y + 3)
  emitGcd "gcd/coprime-dense" (x ^ 3 + x * y + y ^ 2 + 1)
    (x ^ 2 * y + x + y ^ 3 + 2)
  emitGcd "gcd/pure-monomial" (C 6 * x ^ 2 * y * (x + 1))
    (C 9 * x ^ 2 * y * (y + 1))
  emitGcd "gcd/recursive-content" ((y + 1) * (x + 1))
    ((y + 1) * (x + 2))
  let nonmonic := (y + 1) * x + 1
  emitGcd "gcd/nonmonic-main" (nonmonic * (x + y + 2))
    (nonmonic * (x + C 2 * y + 3))
  let vanishingLeading := y * x + 1
  emitGcd "gcd/vanishing-leading-point"
    (vanishingLeading * (x + 1)) (vanishingLeading * (y + 1))
  emitGcd "gcd/unlucky-point" (x + y) (x + C 2 * y)
  emitGcd "gcd/unlucky-prime" (x + y) (x + y + 2)
  emitGcd "gcd/prs-swell"
    (x ^ 5 + C 3 * x ^ 3 * y - C 7 * x * y ^ 3 + y ^ 5 + 1)
    (C 2 * x ^ 4 * y - C 5 * x ^ 2 * y ^ 3 + C 11 * y ^ 4 + x + 3)
  let x1 : MvPoly 1 Int Mono.lex := X 0
  emitGcd "gcd/arity-one" ((x1 + 1) * (x1 ^ 2 + 1))
    ((x1 + 1) * (x1 ^ 3 + 2))
  emitGcd "gcd/arity-zero" (C 42 : MvPoly 0 Int Mono.lex) (C 30)

private def emitSqfCases : IO Unit := do
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let g := x + y + 1
  let h := x + C 2 * y + 3
  emitSqf "sqf/zero" (0 : MvPoly 2 Int Mono.lex)
  emitSqf "sqf/high-multiplicity" (g ^ 7 * h)
  emitSqf "sqf/multiplicity-gap" (g * h ^ 5)
  emitSqf "sqf/repeated-content" ((y + 1) ^ 3 * (x + 1))
  emitSqf "sqf/every-variable" ((x + y + 1) ^ 3 * (x * y + 1))
  emitSqf "sqf/squarefree" ((x + 1) * (y + 1) * (x + y + 1))
  emitSqf "sqf/content-two-x" (C 2 * x)
  emitSqf "sqf/content-twelve-x" (C 12 * x)
  emitSqf "sqf/content-six" (C 6 : MvPoly 2 Int Mono.lex)
  emitSqf "sqf/content-four-x-square" (C 4 * x ^ 2 + C 4 * x)
  emitSqf "sqf/arity-zero" (C 18 : MvPoly 0 Int Mono.lex)

private def emitSquarefreeCases : IO Unit := do
  let x : MvPoly 2 (ZMod64 3) Mono.lex := X 0
  let y : MvPoly 2 (ZMod64 3) Mono.lex := X 1
  emitSquarefree "squarefree/one-derivative-zero" (x ^ 3 + y)
  emitSquarefree "squarefree/repeated-mixed" ((x ^ 3 + y) ^ 2)
  emitSquarefree "squarefree/pth-power" ((x + y) ^ 3)
  emitSquarefree "squarefree/two-repeated" ((x ^ 3 + y) ^ 2 * (x + y ^ 3) ^ 2)

end Hex.MvGcdEmit

def main : IO Unit := do
  Hex.MvGcdEmit.emitGcdCases
  Hex.MvGcdEmit.emitSqfCases
  Hex.MvGcdEmit.emitSquarefreeCases
