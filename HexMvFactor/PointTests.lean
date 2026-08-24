/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvFactor.Point
public import HexMvFactor.Point

public section

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

private def x : MvPoly 2 Int Mono.lex := X 0
private def y : MvPoly 2 Int Mono.lex := X 1
private def innerY : MvPoly 1 Int Mono.lex := X 0
private def zeroPoint : Fin 1 → Int := fun _ => 0
private def atFive : Fin 1 → Int := fun _ => 5

private def coordinates {n : Nat} (a : Fin n → Int) : List Int :=
  (List.finRange n).map a

private def samePointSet {n : Nat} (as bs : List (Fin n → Int)) : Bool :=
  as.length == bs.length &&
    as.all fun a => bs.any fun b => coordinates a == coordinates b

private def variableLeading : Decomp 1 Mono.lex :=
  { content := 1, factors := [⟨innerY, 1⟩] }

private def constantLeading : Decomp 1 Mono.lex :=
  { content := 1, factors := [] }

private def splitLeading : Decomp 1 Mono.lex :=
  { content := 6, factors := [⟨innerY, 1⟩] }

/- V2 is checked before either squarefreeness or univariate factorization. -/
#guard
  match probe Config.default 0 Mono.lex zeroPoint (y * x + 1)
      variableLeading (Rand.ofSeed 0) with
  | .error .degreeDrop => true
  | _ => false

/- Relative squarefreeness rejects the repeated image `(x+1)^2`. -/
#guard
  match probe Config.default 0 Mono.lex zeroPoint ((x + 1) ^ 2)
      constantLeading (Rand.ofSeed 0) with
  | .error .notSquarefree => true
  | _ => false

/- The complete point route factors the squarefree image, distributes `6y`,
   and returns the rescaled image product without recomputation. -/
#guard
  let target := (C 2 * y * x + 1) * (C 3 * x + y)
  match probe Config.default 0 Mono.lex atFive target splitLeading
      (Rand.ofSeed 9) with
  | .ok (accepted, _) =>
      accepted.images.length = 2 &&
        MvHensel.uniProduct accepted.images ==
          MvHensel.imageAt 0 Mono.lex atFive target &&
        MvHensel.mvProduct accepted.leading ==
          MvHensel.lcIn 0 Mono.lex target
  | .error _ => false

/- Shell zero is the origin and the one-dimensional radius-one shell has
   exactly the two endpoints. -/
#guard (shellPoints 1 0).length = 1
#guard (shellPoints 1 1).length = 2
#guard (shellPoints 2 1).length = 8

/- Full budget-visible small shells agree with the materialized reference.
   Comparing coordinate sets and lengths catches both omissions and
   duplicate ranks while allowing the intended within-shell permutation. -/
#guard
  let actual := (boundedShellOrder 1 2 5 (Rand.ofSeed 23)).1
  samePointSet (actual.filter fun a => pointNorm a == 2) (shellPoints 1 2)

#guard
  let actual := (boundedShellOrder 2 1 9 (Rand.ofSeed 29)).1
  samePointSet (actual.filter fun a => pointNorm a == 1) (shellPoints 2 1)

#guard
  let actual := (boundedShellOrder 2 2 25 (Rand.ofSeed 37)).1
  samePointSet (actual.filter fun a => pointNorm a == 2) (shellPoints 2 2)

/- Ordering consumes one generator word per point and remains replayable. -/
#guard
  (orderShell (shellPoints 1 1) (Rand.ofSeed 17)).2 =
    (orderShell (shellPoints 1 1) (Rand.ofSeed 17)).2

/- The production enumerator is capped before constructing any cube. -/
#guard
  let seed := Rand.ofSeed 31
  let ordered := boundedShellOrder 512 8 0 seed
  ordered.1.isEmpty && ordered.2 == seed

#guard
  let ordered := boundedShellOrder 128 8 3 (Rand.ofSeed 31)
  ordered.1.length == 3

/- Zero fuel reaches neither shell construction nor random advancement in
   the actual scouting API. -/
#guard
  let cfg := { Config.default with pointFuel := 0 }
  let seed := Rand.ofSeed 44
  let result := scoutPoints cfg 0 Mono.lex (x + 1) constantLeading seed
  result.attempts == 0 && result.accepted.isEmpty && result.rand == seed

end Hex.MvFactor
