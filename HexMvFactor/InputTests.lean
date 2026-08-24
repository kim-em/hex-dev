/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvFactor.Input
public import HexMvFactor.Input

public section

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

private def x : MvPoly 2 Int Mono.lex := X 0
private def y : MvPoly 2 Int Mono.lex := X 1
private def innerY : MvPoly 1 Int Mono.lex := X 0
private def atFive : Fin 1 → Int := fun _ => 5

private def target : MvPoly 2 Int Mono.lex :=
  (C 2 * y * x + 1) * (C 3 * x + y)

private def image₁ : ZPoly := DensePoly.ofList [1, 10]
private def image₂ : ZPoly := DensePoly.ofList [5, 3]

private def accepted : Probe 1 Mono.lex Mono.lex :=
  { point := atFive
    images := [image₁, image₂]
    leading := [C 2 * innerY, C 3]
    uni := [image₁, image₂] }

/- Prime 2 is rejected by V5 before witness production. -/
#guard
  match (ZMod64.primesBelow 2 1)[0]? with
  | none => false
  | some prime =>
      match inputAtPrime 0 target accepted prime 2 with
      | .error .primeDividesLeading => true
      | _ => false

/- At prime 7 the images remain coprime, `witnessOf?` supplies V6, and the
   completed route passes the actual Hensel V1--V6 checker. -/
#guard
  match (ZMod64.primesBelow 7 1)[0]? with
  | none => false
  | some prime =>
      match inputAtPrime 0 target accepted prime 2 with
      | .ok inp => MvHensel.valid inp
      | .error _ => false

/- Malformed accepted-probe data is a caller error, not a reason to consume
   the rest of the prime budget. -/
private def malformed : Probe 1 Mono.lex Mono.lex :=
  { accepted with leading := [] }

#guard
  match (ZMod64.primesBelow 7 1)[0]? with
  | none => false
  | some prime =>
      match inputFromPrimes 0 target malformed 2 [prime] with
      | .error (.invalid .arity) => true
      | _ => false

#guard exponentSchedule 3 3 == [3, 6, 12, 24]
#guard startingExponent 20 = 6
#guard (factorPrimes 5).map (fun prime => prime.m) == [2, 3, 5, 7, 11]

end Hex.MvFactor
