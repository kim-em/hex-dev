/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public meta import HexMvGcd.Gcd
public meta import HexMvGcd.Prs
public meta import HexMvGcd.Squarefree
public meta import HexMvPoly.Ring
public import HexMvGcd.Gcd
public import HexMvGcd.Squarefree
public section
namespace Hex.MvPoly
private abbrev P0 := MvPoly 0 Int Mono.lex
private abbrev P1 := MvPoly 1 Int Mono.lex
private abbrev P2 := MvPoly 2 Int Mono.lex
private abbrev Q2 := MvPoly 2 Rat Mono.lex
private def brownPrimeAt? (p : Nat) : Option ZMod64.Prime :=
  (ZMod64.primesBelow p 1)[0]?
#guard (smallPrimeSupply 47 5).map (fun P => P.m) == [2, 3, 5, 7, 11]
@[instance_reducible] private def rejectingProducer : GcdProducer Int where
  propose := fun _ _ _ f h =>
    ⟨some (.mk 1 f h .unit), Rand.ofSeed 99⟩
#guard checkGcd (0 : P0) 0 (rawPrsCert 0 0)
#guard
  let f : P0 := C 12
  let h : P0 := C 18
  checkGcd f h (rawPrsCert f h)
#guard
  let x : P1 := X 0
  let f := C 12 * x
  let h := C 18 * x
  checkGcd f h (rawPrsCert f h)
#guard
  let x : P1 := X 0
  let common := x + 1
  let f := common * (x + 2)
  let h := common * (x + 3)
  checkGcd f h (rawPrsCert f h)
#guard
  let x : P1 := X 0
  let common := x + 1
  let f := common * (x + 2)
  let h := common * (x + 3)
  checkGcd f h (intArityOneRaw f h)
#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let common := x + y + 1
  let f := common * (x + 2)
  let h := common * (y + 3)
  checkGcd f h (rawPrsCert f h)
#guard (fastProposal GcdConfig.default (0 : P1) 0).cert?.isSome
#guard
  let x : P1 := X 0
  (intTryCoprimeCert? 8 (Rand.ofSeed 0) (x + 1) (x + 2)).1.isSome
#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let f := x + y + 1
  let h := x * y + x + 2
  let run := intTryCoprimeCert? 8 (Rand.ofSeed 17) f h
  match run.1 with
  | some cert => checkGcd f h cert && cert.gcd == 1
  | none => false
#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let f := C 6 * x * y * (x + 1)
  let h := C 9 * x * y * (y + 1)
  let run := intFastProposal GcdConfig.default f h
  match run.cert? with
  | some cert => checkGcd f h cert && cert.gcd == C 3 * x * y
  | none => false
#guard
  let x : P1 := X 0
  let common := x + 1
  (intTryCoprimeCert? 8 (Rand.ofSeed 0)
    (common * (x + 2)) (common * (x + 3))).1.isNone
#guard
  let x : P1 := X 0
  let common := x + 1
  let f := common * (x + 2)
  let h := common * (x + 3)
  let cfg : GcdConfig :=
    { GcdConfig.default with brownPrimeFuel := 0, brownPointFuel := 0 }
  let cfg : GcdConfig := { cfg with heuristicBitBudget := 0 }
  let proposal := GcdProducer.propose Mono.lex cfg f h
  match proposal.cert? with
  | some cert => cert.gcd == common && checkGcd f h cert
  | none => false
#guard
  let x : P1 := X 0
  (intHeuristicCert? { GcdConfig.default with heuristicBitBudget := 0 }
    (x + 1) (x + 2)).isNone
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
  letI : GcdProducer Int := rejectingProducer
  let x : P1 := X 0
  let common := x + 1
  let f := common * (x + 2)
  let h := common * (x + 3)
  let run := gcdCertWith GcdConfig.default f h
  checkGcd f h run.cert && run.rand == Rand.ofSeed 99
#guard
  let state : BrownPointState :=
    { bestDegree? := some 2, accepted := 3 }
  let offered := state.offer false true 1
  offered.1 == .bad && offered.2 == state
#guard
  let state : BrownPointState :=
    { bestDegree? := some 2, accepted := 3 }
  let larger := state.offer true true 4
  let smaller := state.offer true true 1
  larger.1 == .unlucky && larger.2 == state &&
    smaller.1 == .restart &&
    smaller.2 == { bestDegree? := some 1, accepted := 1 }
#guard
  let x : P2 := X 0
  let y : P2 := X 1
  brownMainIndex (x ^ 5 + y) (x ^ 4 + y) == some (1 : Fin 2)
#guard
  let x : Q2 := X 0
  let y : Q2 := X 1
  let gamma : MvPoly 1 Rat Mono.lex := X 0
  brownPointBad 0 gamma (y * x + 1) (y * x + 2)
#guard
  let x : Mono 1 := Mono.unit 0
  let state : BrownPrimeState 1 :=
    { bestDegree? := some 1, support := [Mono.zero, x], stableRounds := 0 }
  let same := state.offer true true 1 [Mono.zero, x]
  let changed := state.offer true true 1 [x]
  same.1 == .stable && same.2.stableRounds == 1 &&
    changed.1 == .restart && changed.2.stableRounds == 0
#guard
  match brownCorrectImage? (2 : Rat) (DensePoly.ofList [1, 1]) with
  | some image => image == DensePoly.ofList [2, 2]
  | none => false
#guard
  let samples : List (Rat × MvPoly 0 Rat Mono.lex) :=
    [(0, C 2), (1, C 5)]
  match brownInterpolate? samples with
  | some interpolation =>
      interpolation == DensePoly.ofList [C 2, C 3]
  | none => false
#guard
  let x : P1 := X 0
  let common := C 2 * x + 1
  let f := common * (x + 1)
  let h := common * (x + 2)
  match intBrownCert? Mono.lex GcdConfig.default f h with
  | some cert => checkGcd f h cert
  | none => false
#guard
  let x : Q2 := X 0
  let y : Q2 := X 1
  let common := x + y + 1
  let f := common * (x + 2)
  let h := common * (y + 3)
  match brownFieldCert? 12 [0, 1, 2, 3] f h with
  | some cert => checkGcd f h cert && cert.gcd == common
  | none => false
#guard
  let x : Q2 := X 0
  let y : Q2 := X 1
  let left := C ((1 : Rat) / 2) * x + C ((1 : Rat) / 3) * y + 1
  let right := C ((1 : Rat) / 5) * x * y + x + 2
  match ratLiftCoprime? left right with
  | some cert => checkCoprime left right cert
  | none => false
#guard
  let x : Q2 := X 0
  let p := -(C ((1 : Rat) / 2) * x + 1)
  let model := ratPrimitiveModel p
  C model.scale * intModelToRat model.poly == p
#guard
  let x : Q2 := X 0
  let y : Q2 := X 1
  let common := C ((1 : Rat) / 2) * x + C ((1 : Rat) / 3) * y + 1
  let f := common * (x + C ((1 : Rat) / 5))
  let h := common * (y + C ((1 : Rat) / 7))
  match ratIntegerLiftCert? f h with
  | some cert => checkGcd f h cert
  | none => false
#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let common := x + y + 1
  let f := common * (x + 2)
  let h := common * (y + 3)
  let cfg : GcdConfig :=
    { GcdConfig.default with brownPrimeFuel := 8, brownPointFuel := 8 }
  match intBrownModularCert? cfg f h with
  | some cert => checkGcd f h cert && cert.gcd == common
  | none => false
#guard
  let x : P2 := X 0
  let f := C 2 * x + 1
  let h := C 2 * x + 3
  match brownPrimeAt? 2 with
  | some prime => (intBrownImage? 4 f h prime).isNone
  | none => false
#guard
  let x : P2 := X 0
  let f := x
  let h := x + 2
  match brownPrimeAt? 2, brownPrimeAt? 3 with
  | some p2, some p3 =>
      match intBrownImage? 4 f h p2, intBrownImage? 4 f h p3 with
      | some image2, some image3 =>
          let first := ({} : BrownPrimeState 2).offer
            true true image2.degree image2.support
          let second := first.2.offer
            true true image3.degree image3.support
          first.1 == .accumulate && second.1 == .restart
      | _, _ => false
  | _, _ => false
#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let common := C 2 * x + y + 1
  let f := common * (x + 1)
  let h := common * (y + 2)
  match brownPrimeAt? 5 with
  | some prime =>
      match intBrownImage? 8 f h prime with
      | none => false
      | some image =>
          letI : ZMod64.Bounds prime.m := prime.bounds
          letI : ZMod64.PrimeModulus prime.m :=
            ZMod64.primeModulusOfPrime prime.prime
          let expected := mapCoeffs (ZMod64.intCast prime.m) common
          image.support == expected.monomials &&
            image.residues == expected.termsList.map
              (fun term => Int.ofNat term.2.toNat)
  | none => false
#guard
  let d := sqfDecomp (C 6 : P1)
  d.content == 6 && d.factors.isEmpty
#guard
  let d := sqfDecomp (C (-6) : P1)
  d.content == -6 && d.factors.isEmpty
#guard
  let x : P1 := X 0
  !isSquarefree ((x + 1) ^ 2)
#guard
  let x : P1 := X 0
  isSquarefree ((x + 1) * (x + 2))
#guard
  let x : P1 := X 0
  let p := (x + 1) ^ 2 * (x + 2) ^ 3
  radical p == (x + 1) * (x + 2)
#guard
  let x : P1 := X 0
  let p := (C 6 : P1) * (x + 1) ^ 2 * (x + 2) ^ 3
  let d := sqfDecomp p
  d.factors.foldl
    (fun acc f => acc * f.factor ^ f.multiplicity) (C d.content) == p
#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let p := (x + 1) * (y + 1) ^ 2
  let d := sqfDecomp p
  d.factors.map (fun f => f.multiplicity) == [1, 2] &&
    d.factors.foldl
      (fun acc f => acc * f.factor ^ f.multiplicity) (C d.content) == p
end Hex.MvPoly
