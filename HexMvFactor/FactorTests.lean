/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvFactor.Factor
public import HexMvFactor.Factor

public section

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

private abbrev P0 := MvPoly 0 Int Mono.lex
private abbrev P1 := MvPoly 1 Int Mono.lex
private abbrev P2 := MvPoly 2 Int Mono.lex

private def ux : P1 := X 0
private def x : P2 := X 0
private def y : P2 := X 1

def accepted {k : Nat} {order : Mono k → Mono k → Ordering}
    [IsMonomialOrder order] (f : MvPoly k Int order) : Bool :=
  match factor? f with
  | .ok answer => checkDecomp f answer.raw
  | .error stoppedAnswer => checkDecomp f stoppedAnswer.found.raw

/- All structural conventions are public successes, including zero and
   arity zero. -/
#guard
  match factor? (0 : P2) with
  | .ok answer => answer.raw.content == 0 && answer.raw.factors.isEmpty
  | .error _ => false

#guard
  match factor? (C 12 : P0) with
  | .ok answer => answer.raw.content == 12 && answer.raw.factors.isEmpty
  | .error _ => false

#guard
  let subject : P2 := C 6 * x ^ 2 * y
  match factor? subject with
  | .ok answer =>
      answer.raw.content == 6 && answer.raw.factors.length == 2 &&
        checkDecomp subject answer.raw
  | .error _ => false

/- Sign normalization and equality merging happen before final replay. -/
#guard
  let g := x + y + 1
  let D := normalizeDecomp 1 [⟨-g, 1⟩, ⟨g, 3⟩]
  D.content == -1 &&
    match D.factors with
    | [entry] => entry.factor == g && entry.multiplicity == 4
    | _ => false

/- Arity one runs through the empty-point EEZ route and returns the actual
   two factors, not a singleton fallback. -/
private def univariateRoute : Bool :=
  let subject := (ux + 1) * (ux + 2)
  match factor? subject with
  | .ok answer =>
      answer.raw.factors.length == 2 && checkDecomp subject answer.raw
  | .error _ => false

#guard univariateRoute

/- Squarefree multiplicities are transferred to the final entries and the
   merge pass leaves one copy of each normalized factor. -/
private def repeatedRoute : Bool :=
  let subject := (x + y + 1) ^ 3 * (x + 1)
  match factor? subject with
  | .ok answer =>
      answer.raw.factors.length == 2 &&
        answer.raw.factors.any (fun entry => entry.multiplicity == 3) &&
        checkDecomp subject answer.raw
  | .error _ => false

#guard repeatedRoute

/- A zero point budget remains a point failure, carries an independently
   checked coarse decomposition, and does no shell work or RNG advancement. -/
private def noPoints : Config :=
  { Config.default with
    rand := Rand.ofSeed 91
    pointFuel := 0 }

#guard
  let subject := ux + 1
  match factorWith noPoints subject with
  | .ok _ => false
  | .error stoppedAnswer =>
      (match stoppedAnswer.reason with
       | .point 0 none => true
       | _ => false) &&
        checkDecomp subject stoppedAnswer.found.raw &&
        stoppedAnswer.rand == noPoints.rand

private def noPrimeSupply : Config :=
  { Config.default with primeFuel := 0 }

/- Exhausting the per-point prime supply changes point and eventually
   reports `.point`; it is not mislabeled as subset recombination. -/
#guard
  let subject := (ux + 1) * (ux + 2)
  match factorWith noPrimeSupply subject with
  | .ok _ => false
  | .error stoppedAnswer =>
      match stoppedAnswer.reason with
      | .point _ _ => checkDecomp subject stoppedAnswer.found.raw
      | _ => false

private def oneOrigin : Config :=
  { Config.default with
    rand := Rand.ofSeed 73
    pointFuel := 1
    pointShell := 0 }

/- The multiplicity-one component succeeds at the origin; the later
   multiplicity-two component has the nonsquarefree image `x^2` and stops.
   The checked partial keeps the earlier factor and only leaves the stopped
   component coarse. -/
#guard
  let first := x + 1
  let later := x ^ 2 + y
  let subject := first * later ^ 2
  match factorWith oneOrigin subject with
  | .ok _ => false
  | .error stoppedAnswer =>
      (match stoppedAnswer.reason with
       | .point _ (some .notSquarefree) => true
       | _ => false) &&
        stoppedAnswer.found.raw.factors.length == 2 &&
        stoppedAnswer.found.raw.factors.any (fun entry =>
          entry.factor == first && entry.multiplicity == 1) &&
        stoppedAnswer.found.raw.factors.any (fun entry =>
          entry.factor == later && entry.multiplicity == 2) &&
        checkDecomp subject stoppedAnswer.found.raw

/- Regardless of bounded-search outcome, both arms expose only data tied to
   the original subject by `checkDecomp`. -/
#guard accepted ((C 2 * y * x + 1) * (C 3 * x + y))

end Hex.MvFactor
