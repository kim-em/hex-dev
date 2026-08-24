/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvGcd

/-!
Core conformance checks for checked multivariate gcd and squarefree operations.

Oracle: SymPy `gcd`, `cofactors`, `sqf_list`, and finite-field derivatives
Mode: always
Covered operations:
- `divExact?`, `checkCoprime`, `checkContent`, and `checkGcd`
- structural reduction, modular coprimality, heuristic, Brown, and PRS routes
- `gcd`, `cofactors`, `isCoprime`, `gcdList`, `lcm`, and named-variable content
- `sqfDecomp`, `radical`, and `isSquarefree`
Covered properties:
- every accepted route result passes the common recursive checker
- gcds divide both inputs and their cofactors reconstruct both inputs
- route-0 factors are restored after checked gcd on the reduced pair
- squarefree factors reassemble the input with positive sorted multiplicities
Covered edge cases:
- arities zero and one, zero, units, constants, and scalar content
- pure monomial and recursive-content gcds
- heuristic false positives, bad Brown points, unlucky images, and restarts
- high and gapped multiplicities, repeated content, and every-variable factors
- characteristic-three vanishing derivatives and inseparable powers
-/

namespace Hex.MvPoly.Conformance

open Hex
open Hex.MvPoly

private abbrev P0 := MvPoly 0 Int Mono.lex
private abbrev P1 := MvPoly 1 Int Mono.lex
private abbrev P2 := MvPoly 2 Int Mono.lex
private abbrev Q2 := MvPoly 2 Rat Mono.lex

private def primeAt? (p : Nat) : Option ZMod64.Prime :=
  (ZMod64.primesBelow p 1)[0]?

private def gcdContract {n : Nat} (f h expected : MvPoly n Int Mono.lex) : Bool :=
  let cert := gcdCert f h
  checkGcd f h cert && cert.gcd == expected &&
    cert.gcd * cert.cofL == f && cert.gcd * cert.cofR == h &&
    gcd f h == expected && cofactors f h == (cert.cofL, cert.cofR)

private def sqfProduct {n : Nat} (d : SqfDecomp n Int Mono.lex) :
    MvPoly n Int Mono.lex :=
  d.factors.foldl (fun acc factor => acc * factor.factor ^ factor.multiplicity)
    (C d.content)

private def sqfContract {n : Nat} (p : MvPoly n Int Mono.lex) : Bool :=
  let d := sqfDecomp p
  sqfProduct d == p &&
    d.factors.all (fun factor =>
      0 < factor.multiplicity && isSquarefree factor.factor) &&
    List.Pairwise (fun f g => f.multiplicity < g.multiplicity) d.factors

/-! Public certificate and gcd contracts, including the two lower arities. -/

#guard gcdContract (0 : P0) 0 0
#guard gcdContract (C 12 : P0) (C 18) (C 6)

#guard
  let x : P1 := X 0
  let common := C 2 * x + 1
  gcdContract (common * (x + 1)) (common * (x + 2)) common

#guard
  let x : P1 := X 0
  let f := C 12 * x
  let h := C 18 * x
  brownOfZPoly (ZPoly.gcd (brownToZPoly f) (brownToZPoly h)) == gcd f h

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let common := x + y + 1
  gcdContract (common * (x + 2)) (common * (y + 3)) common

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  gcdContract (C 6 * x * y * (x + 1))
    (C 9 * x * y * (y + 1)) (C 3 * x * y)

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  isCoprime (x + y + 1) (x * y + x + 2)

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  gcdList [C 6 * x, C 9 * x * y, C 15 * x * (y + 1)] == C 3 * x

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  lcm (x + 1) (y + 1) == (x + 1) * (y + 1)

/-! Named-variable content and route-0 restoration. -/

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let coefficientPart : MvPoly 1 Int Mono.lex := X 0 + 1
  let p := (y + 1) * (x ^ 2 + x + 1)
  contentIn (0 : Fin 2) Mono.lex p == coefficientPart &&
    constIn (cmp := Mono.lex) (0 : Fin 2) Mono.lex coefficientPart *
      primPartIn (0 : Fin 2) Mono.lex p == p

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let f := C 6 * x * y * (x + 1)
  let h := C 9 * x * y * (y + 1)
  match structuralReduction? f h with
  | none => false
  | some reduced =>
      reduced.factor == C 3 * x * y &&
        match restoreStructural? f h reduced (prsCert reduced.left reduced.right) with
        | some cert => cert.gcd == C 3 * x * y && checkGcd f h cert
        | none => false

/-! Route-level traps. -/

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let f := x + y + 1
  let h := x * y + x + 2
  match (intTryCoprimeCert? 8 (Rand.ofSeed 17) f h).1 with
  | some cert => cert.gcd == 1 && checkGcd f h cert
  | none => false

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let common := x + y + 1
  let f := common * (x + 2)
  let h := common * (y + 3)
  (checkedCandidate? f h (intHeuristicCandidateAt f h 101)).isSome

#guard
  let x : P1 := X 0
  let f := x
  let h := x + 5
  (checkedCandidate? f h (intHeuristicCandidateAt f h 5)).isNone

#guard
  let state : BrownPointState := { bestDegree? := some 2, accepted := 3 }
  let bad := state.offer false true 1
  let unlucky := state.offer true true 4
  let restart := state.offer true true 1
  bad.1 == .bad && bad.2 == state &&
    unlucky.1 == .unlucky && unlucky.2 == state &&
    restart.1 == .restart && restart.2.accepted == 1

#guard
  let x : Q2 := X 0
  let y : Q2 := X 1
  let gamma : MvPoly 1 Rat Mono.lex := X 0
  brownPointBad 0 gamma (y * x + 1) (y * x + 2)

#guard
  let x : Mono 1 := Mono.unit 0
  let state : BrownPrimeState 1 :=
    { bestDegree? := some 1, support := [Mono.zero, x], stableRounds := 0 }
  let stable := state.offer true true 1 [Mono.zero, x]
  let restart := state.offer true true 1 [x]
  stable.1 == .stable && stable.2.stableRounds == 1 &&
    restart.1 == .restart && restart.2.stableRounds == 0

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let integral := x + C 2 * y ^ 3 + y ^ 2
  match primeAt? 2, primeAt? 3 with
  | some p2, some p3 =>
      let low := mapCoeffs (@ZMod64.intCast p2.m p2.bounds) integral
      let high := mapCoeffs (@ZMod64.intCast p3.m p3.bounds) integral
      let main := brownMainIndex integral integral
      let first := ({} : BrownPrimeState 2).offer true true
        (brownImageDegree main high) high.monomials
      let second := first.2.offer true true
        (brownImageDegree main low) low.monomials
      high.totalDegree == 3 && low.totalDegree == 2 &&
        first.1 == .accumulate && second.1 == .restart
  | _, _ => false

#guard
  let x : P1 := X 0
  let common := C 2 * x + 1
  let f := common * (x + 1)
  let h := common * (x + 2)
  match intBrownCert? Mono.lex GcdConfig.default f h with
  | some cert => cert.gcd == common && checkGcd f h cert
  | none => false

/-! Characteristic-zero squarefree decomposition. -/

#guard sqfContract (0 : P2)
#guard
  let x : P2 := X 0
  sqfContract (C 2 * x)
#guard
  let x : P2 := X 0
  sqfContract (C 12 * x)
#guard sqfContract (C 6 : P2)
#guard
  let x : P2 := X 0
  sqfContract (C 4 * x ^ 2 + C 4 * x)

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let g := x + y + 1
  let h := x + C 2 * y + 3
  sqfContract (g ^ 7 * h) && sqfContract (g * h ^ 5)

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  sqfContract ((y + 1) ^ 3 * (x + 1)) &&
    sqfContract ((x + y + 1) ^ 3 * (x * y + 1)) &&
    sqfContract ((x + 1) * (y + 1) * (x + y + 1))

#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let p := (x + y + 1) ^ 3 * (x + 2)
  radical p == (x + 2) * (x + y + 1) && isSquarefree (radical p)

/-! Positive-characteristic exact decisions. -/

private theorem boundsThree : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
attribute [local instance] boundsThree

private theorem primeThree : ZMod64.PrimeModulus 3 :=
  ZMod64.primeModulusOfPrime (by decide)
attribute [local instance] primeThree

private abbrev F3P2 := MvPoly 2 (ZMod64 3) Mono.lex

#guard
  let x : F3P2 := X 0
  let y : F3P2 := X 1
  isSquarefree (x ^ 3 + y) && !isSquarefree ((x ^ 3 + y) ^ 2)

#guard
  let x : F3P2 := X 0
  let y : F3P2 := X 1
  !isSquarefree ((x + y) ^ 3) &&
    !isSquarefree ((x ^ 3 + y) ^ 2 * (x + y ^ 3) ^ 2)

end Hex.MvPoly.Conformance
