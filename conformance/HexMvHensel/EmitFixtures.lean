/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexMvHensel

/-!
Deterministic fixtures for the `HexMvHensel` SymPy oracle.

The lift stream records the complete checked input except for the derived
partial-fraction witness. The oracle derives its own modular data before
calling SymPy's Wang lift. The diophantine stream includes the bases and
witness because those are caller-controlled inputs to the public checked
solver; SymPy independently solves the corresponding image equation.
-/

namespace Hex.MvHenselEmit

open Hex
open Hex.Conformance.Emit
open Hex.MvPoly
open Hex.MvHensel
open scoped Hex

private def lib : String := "HexMvHensel"

private def prime2 : ZMod64.Prime where
  m := 2
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

private def prime3 : ZMod64.Prime where
  m := 3
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

private def prime5 : ZMod64.Prime where
  m := 5
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

private def prime101 : ZMod64.Prime where
  m := 101
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

private def wireTerms {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) : List (List Nat × Int) :=
  p.termsList.map fun term => (term.1.toList, term.2)

private def coefficients (p : ZPoly) : List Int :=
  p.toArray.toList

private def inputOf? {n : Nat} (point : Fin n → Int)
    (prime : ZMod64.Prime) (exponent : Nat)
    (factors : List (MvPoly (n + 1) Int Mono.lex)) :
    Option (Input n Mono.lex Mono.lex) := do
  let setup : Setup n :=
    { main := 0, point := point, prime := prime, exponent := exponent }
  let images := factors.map (imageAt setup.main Mono.lex point)
  let leading := factors.map (lcIn setup.main Mono.lex)
  let witness ← witnessOf? setup images
  some
    { setup := setup
      target := mvProduct factors
      images := images
      leading := leading
      witness := witness }

private def failureName : Failure → String
  | .arity => "arity"
  | .degreeDrop => "degreeDrop"
  | .imageProduct => "imageProduct"
  | .leadingProduct => "leadingProduct"
  | .leadingImage j => s!"leadingImage:{j}"
  | .primeDividesLc j => s!"primeDividesLc:{j}"
  | .notCoprime => "notCoprime"
  | .witnessDegree j => s!"witnessDegree:{j}"
  | .reconstruct modulus => s!"reconstruct:{modulus}"

private def emitLift {n : Nat} (case : String)
    (inp : Input n Mono.lex Mono.lex) : IO Unit := do
  emitMvHenselFixture lib case (n + 1) "lex" inp.setup.main.val
    (List.ofFn inp.setup.point) inp.setup.prime.m inp.setup.exponent
    (wireTerms inp.target) (inp.images.map coefficients)
    (inp.leading.map wireTerms)
  match lift inp with
  | .ok cert =>
      emitResult lib case "mvhensel"
        (mvHenselSuccessValue (cert.factors.map wireTerms))
  | .error failure =>
      emitResult lib case "mvhensel"
        (mvHenselFailureValue (failureName failure))

private def emitFactors {n : Nat} (case : String) (point : Fin n → Int)
    (prime : ZMod64.Prime) (exponent : Nat)
    (factors : List (MvPoly (n + 1) Int Mono.lex)) : IO Unit := do
  match inputOf? point prime exponent factors with
  | some inp => emitLift case inp
  | none => throw <| IO.userError s!"could not derive witness for {case}"

private def emitLiftCases : IO Unit := do
  let point1 : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1

  emitFactors "lift/r2-v2" point1 prime101 1 [x + y + 1, x + 2]
  emitFactors "lift/r3-v2" point1 prime101 1 [x + y + 1, x + 2, x + 3]
  emitFactors "lift/r4-v2" point1 prime101 1
    [x + y + 1, x + 2, x + 3, x + 4]
  emitFactors "lift/r5-v2" point1 prime101 1
    [x + y + 1, x + 2, x + 3, x + 4, x + 5]

  let point2 : Fin 2 → Int := fun _ => 0
  let x3 : MvPoly 3 Int Mono.lex := X 0
  emitFactors "lift/r2-v3" point2 prime101 1
    [x3 + X 1 + X 2 + 1, x3 + 2]
  let point3 : Fin 3 → Int := fun _ => 0
  let x4 : MvPoly 4 Int Mono.lex := X 0
  emitFactors "lift/r2-v4" point3 prime101 1
    [x4 + X 1 + X 2 + X 3 + 1, x4 + 2]
  let point4 : Fin 4 → Int := fun _ => 0
  let x5 : MvPoly 5 Int Mono.lex := X 0
  emitFactors "lift/r2-v5" point4 prime101 1
    [x5 + X 1 + X 2 + X 3 + X 4 + 1, x5 + 2]

  let shared := y + 1
  emitFactors "lift/shared-leading" point1 prime101 1
    [shared * x + 1, shared * x + 2]
  emitFactors "lift/leading-over-modulus" point1 prime5 1
    [(y + 6) * x + 1, x + 2]
  emitFactors "lift/linear-main-r1" point1 prime101 1
    [(y + 1) * x + y + 2]

  let a := x + y + 1
  let b := x + 2
  let c := x + 3
  emitFactors "lift/coarse-splitting" point1 prime101 1 [a * b, c]
  emitFactors "lift/degenerate-r1" point1 prime101 1 [a * b * c]

  let point0 : Fin 0 → Int := fun j => nomatch j
  let xu : MvPoly 1 Int Mono.lex := X 0
  emitFactors "lift/arity-one" point0 prime101 1 [xu, xu + 1]

  let nonSquarefree : Input 1 Mono.lex Mono.lex :=
    { setup := { main := 0, point := point1, prime := prime5, exponent := 1 }
      target := (x + y) * (x - y)
      images := [DensePoly.ofCoeffs #[0, 1], DensePoly.ofCoeffs #[0, 1]]
      leading := [1, 1]
      witness := [0, 0] }
  emitLift "failure/non-squarefree-image" nonSquarefree

  let badSetup : Setup 1 :=
    { main := 0, point := point1, prime := prime2, exponent := 1 }
  let badFactors := [x + y - 1, x + y + 1]
  let badPrime : Input 1 Mono.lex Mono.lex :=
    { setup := badSetup
      target := mvProduct badFactors
      images := badFactors.map (imageAt badSetup.main Mono.lex point1)
      leading := badFactors.map (lcIn badSetup.main Mono.lex)
      witness := [0, 0] }
  emitLift "failure/resultant-prime-2" badPrime
  emitFactors "lift/resultant-next-prime-3" point1 prime3 1 badFactors

  let pointNegOne : Fin 1 → Int := fun _ => -1
  let unlucky : Input 1 Mono.lex Mono.lex :=
    { setup :=
        { main := 0, point := pointNegOne, prime := prime5, exponent := 1 }
      target := x ^ 2 + y
      images := [DensePoly.ofCoeffs #[-1, 1], DensePoly.ofCoeffs #[1, 1]]
      leading := [1, 1]
      witness := [DensePoly.C (-2), DensePoly.C 2] }
  emitLift "failure/unlucky-point" unlucky

  let retryFactors := [x + 3 * y, x + 1]
  match inputOf? point1 prime5 1 retryFactors with
  | none => throw <| IO.userError "could not derive retry witness"
  | some small =>
      emitLift "failure/small-exponent" small
      match raiseExponent? small with
      | none => throw <| IO.userError "could not raise retry exponent"
      | some large => emitLift "lift/larger-exponent" large

  let pointTen : Fin 1 → Int := fun _ => 10
  emitFactors "lift/far-point" pointTen prime101 1 [x + y ^ 2, x + 1]

  let y3 : MvPoly 3 Int Mono.lex := X 1
  let z : MvPoly 3 Int Mono.lex := X 2
  emitFactors "lift/sparse-target-dense-intermediate" point2 prime101 1
    [x3 + y3 + z + 1, x3 - y3 - z + 2]

private def ux : ZPoly := DensePoly.ofCoeffs #[0, 1]
private def uxPlusOne : ZPoly := DensePoly.ofCoeffs #[1, 1]
private def images : List ZPoly := [ux, uxPlusOne]
private def witness : List ZPoly := [1, -1]

private def emitDioph {n : Nat} (case : String) (q : Nat)
    (degrees : Fin n → Nat) (bases : List (MvPoly (n + 1) Int Mono.lex))
    (images witness : List ZPoly) (rhs : MvPoly (n + 1) Int Mono.lex) :
    IO Unit := do
  emitMvDiophFixture lib case (n + 1) "lex" 0 q (List.ofFn degrees)
    (bases.map wireTerms) (images.map coefficients) (witness.map coefficients)
    (wireTerms rhs)
  let answer := diophantine q (0 : Fin (n + 1)) Mono.lex degrees
    bases images witness rhs
  emitResult lib case "mvdioph" (mvDiophValue (answer.map (·.map wireTerms)))

private def emitDiophCases : IO Unit := do
  let x1 : MvPoly 1 Int Mono.lex := X 0
  let d0 : Fin 0 → Nat := fun j => nomatch j
  emitDioph "dioph/univariate" 5 d0 [x1 + 1, x1] images witness 1

  let x2 : MvPoly 2 Int Mono.lex := X 0
  let y2 : MvPoly 2 Int Mono.lex := X 1
  let d1 : Fin 1 → Nat := fun _ => 1
  emitDioph "dioph/one-side-variable" 5 d1 [x2 + 1, x2] images witness
    (1 + y2 * x2)

  let x3 : MvPoly 3 Int Mono.lex := X 0
  let y3 : MvPoly 3 Int Mono.lex := X 1
  let z3 : MvPoly 3 Int Mono.lex := X 2
  let d2 : Fin 2 → Nat := fun _ => 1
  emitDioph "dioph/two-side-variables" 5 d2 [x3 + 1, x3] images witness
    (1 + y3 * x3 + z3 * (x3 + 1) + y3 * z3)

  emitDioph "dioph/degree-bound-rejected" 5 d1
    [x2 + 1 + y2 * x2 ^ 3, x2] images witness 1

end Hex.MvHenselEmit

def main : IO Unit := do
  Hex.MvHenselEmit.emitLiftCases
  Hex.MvHenselEmit.emitDiophCases
