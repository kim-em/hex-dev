/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexRCF.DecisionCheck

/-!
JSONL fixture emission for the independent HexRCF oracle.

The committed profile contains exactly thirty deterministic sentences.  Each
fixture serialises only the reflected sentence AST; the companion FLINT oracle
reconstructs the real-cell decomposition independently.  The Lean verdict is
emitted separately, and a builder failure aborts emission instead of becoming
a false result.

The structured schedule guarantees coverage that unconstrained random formulas
cannot: all comparisons and connectives, all four quantifiers with both
verdicts, constants, root-free polynomials, shared and repeated roots, half-open
endpoint ownership, empty/reversed intervals, and a close-root polynomial.  Its
remaining atoms come from the POSIX LCG with seed `0x524346` and degrees 8--12.

Passing `local` emits three developer-only stress cases (quadratic,
degree-10/three-atom, and degree-50 Mignotte) without changing the committed CI
snapshot.
-/

namespace Hex.RCF.Emit

open Hex.Conformance.Emit

private def lib : String := "HexRCF"

private structure Case where
  id : String
  sentence : Sentence

private def poly (coeffs : List Int) : ZPoly :=
  DensePoly.ofCoeffs coeffs.toArray

private def atom (coeffs : List Int) (cmp : Cmp) : Formula :=
  .atom ⟨poly coeffs, cmp⟩

private def x : List Int := [0, 1]
private def xMinusOne : List Int := [-1, 1]
private def posQuad : List Int := [1, 0, 1]
private def posOctic : List Int := [1, 0, 0, 0, 0, 0, 0, 0, 1]
private def x8MinusOne : List Int := [-1, 0, 0, 0, 0, 0, 0, 0, 1]
private def x9MinusOne : List Int := [-1, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- `x^12 - (3*x - 1)^2`, with a certified close pair of real roots. -/
private def closeRoots : List Int :=
  [-1, 6, -9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- POSIX `rand` LCG step. -/
private def lcgStep (state : Nat) : Nat :=
  (1103515245 * state + 12345) % 2147483648

private def lcgIterate (seed : Nat) : Nat → Nat
  | 0 => seed
  | n + 1 => lcgIterate (lcgStep seed) n

private def ciSeed : Nat := 0x524346

private def foldCoeff (raw : Nat) : Int :=
  Int.ofNat (raw % 7) - 3

/-- A deterministic degree-8--12 polynomial.  The monic leading coefficient
is a deliberate repair, so no candidate filtering consults Lean. -/
private def seededPoly (i : Nat) : List Int :=
  let degree := 8 + i % 5
  let lower := (List.range degree).map fun j =>
    foldCoeff (lcgIterate ciSeed (i * 13 + j + 1))
  lower ++ [1]

private def cmpAt (i : Nat) : Cmp :=
  match i % 6 with
  | 0 => .lt
  | 1 => .le
  | 2 => .eq
  | 3 => .ge
  | 4 => .gt
  | _ => .ne

private def seededAtom (i : Nat) : Formula :=
  atom (seededPoly i) (cmpAt i)

/-- Include the seeded atom without changing the truth of `formula`. -/
private def withSeed (i : Nat) (formula : Formula) : Formula :=
  let a := seededAtom i
  .and formula (.or a (.not a))

private def truthAt (i : Nat) : Formula :=
  let a := seededAtom i
  match i % 4 with
  | 0 => .or a (.not a)
  | 1 => .not (.and a (.not a))
  | 2 => .imp a a
  | _ => .and .tt (.or a (.not a))

private def falseAt (i : Nat) : Formula :=
  let a := seededAtom i
  match i % 4 with
  | 0 => .and a (.not a)
  | 1 => .not (.or a (.not a))
  | 2 => .and .ff a
  | _ => .not (.imp a a)

private def fixedCases : List Case := [
  { id := "ci/seed-524346/00-no-roots-true",
    sentence := .forallReal (atom posOctic .gt) },
  { id := "ci/seed-524346/01-no-roots-false",
    sentence := .forallReal (atom posOctic .eq) },
  { id := "ci/seed-524346/02-real-exists-true",
    sentence := .existsReal (withSeed 2 (atom x .eq)) },
  { id := "ci/seed-524346/03-real-exists-false",
    sentence := .existsReal (withSeed 3 (atom posQuad .eq)) },
  { id := "ci/seed-524346/04-ioc-forall-root",
    sentence := .forallIoc 0 1 (withSeed 4 (atom xMinusOne .le)) },
  { id := "ci/seed-524346/05-ioc-lower-open",
    sentence := .forallIoc 0 1 (withSeed 5 (atom x .gt)) },
  { id := "ci/seed-524346/06-ioc-upper-included",
    sentence := .existsIoc 0 1 (withSeed 6 (atom xMinusOne .eq)) },
  { id := "ci/seed-524346/07-ioc-lower-excluded",
    sentence := .existsIoc 1 2 (withSeed 7 (atom xMinusOne .eq)) },
  { id := "ci/seed-524346/08-equal-forall",
    sentence := .forallIoc 1 1 (falseAt 8) },
  { id := "ci/seed-524346/09-equal-exists",
    sentence := .existsIoc 1 1 (truthAt 9) },
  { id := "ci/seed-524346/10-reversed-forall",
    sentence := .forallIoc 2 1 (falseAt 10) },
  { id := "ci/seed-524346/11-reversed-exists",
    sentence := .existsIoc 2 1 (truthAt 11) },
  { id := "ci/seed-524346/12-shared-root",
    sentence := .existsReal
      (withSeed 12 (.and (atom x8MinusOne .eq) (atom x9MinusOne .eq))) },
  { id := "ci/seed-524346/13-repeated-atom",
    sentence := .forallReal (truthAt 13) },
  { id := "ci/seed-524346/14-constant-true",
    sentence := .forallReal (atom [1] .gt) },
  { id := "ci/seed-524346/15-constant-false",
    sentence := .existsReal (atom [1] .lt) },
  { id := "ci/seed-524346/16-close-roots",
    sentence := .existsReal (withSeed 16 (atom closeRoots .eq)) },
  { id := "ci/seed-524346/17-tt",
    sentence := .forallReal (.and .tt (truthAt 17)) }
]

/-- The last twelve entries exercise every quantifier/verdict combination
again while the comparison and connective schedules cycle independently. -/
private def generatedCases : List Case :=
  (List.range 12).map fun offset =>
    let i := offset + 18
    let formula := if offset % 2 = 0 then truthAt i else falseAt i
    let sentence := match offset % 8 with
      | 0 => Sentence.forallReal formula
      | 1 => Sentence.forallReal formula
      | 2 => Sentence.existsReal formula
      | 3 => Sentence.existsReal formula
      | 4 => Sentence.forallIoc (-2) 2 formula
      | 5 => Sentence.forallIoc (-2) 2 formula
      | 6 => Sentence.existsIoc (-2) 2 formula
      | _ => Sentence.existsIoc (-2) 2 formula
    { id := s!"ci/seed-524346/{i}", sentence }

private def ciCases : List Case := fixedCases ++ generatedCases

private def wireCmp : Cmp → Hex.Conformance.Emit.Rcf.Cmp
  | .lt => .lt
  | .le => .le
  | .eq => .eq
  | .ge => .ge
  | .gt => .gt
  | .ne => .ne

private def wireFormula : Formula → Hex.Conformance.Emit.Rcf.Formula
  | .atom a => .atom a.p.coeffs.toList (wireCmp a.cmp)
  | .tt => .tt
  | .ff => .ff
  | .not arg => .not (wireFormula arg)
  | .and left right => .and (wireFormula left) (wireFormula right)
  | .or left right => .or (wireFormula left) (wireFormula right)
  | .imp left right => .imp (wireFormula left) (wireFormula right)

private def wireDyadic : Dyadic → Hex.Conformance.Emit.Rcf.Dyadic
  | .zero => (0, 0)
  | .ofOdd numerator exponent _ => (numerator, exponent)

private def wireSentence : Sentence → Hex.Conformance.Emit.Rcf.Sentence
  | .forallReal formula => .forallReal (wireFormula formula)
  | .existsReal formula => .existsReal (wireFormula formula)
  | .forallIoc lower upper formula =>
      .forallIoc (wireDyadic lower) (wireDyadic upper) (wireFormula formula)
  | .existsIoc lower upper formula =>
      .existsIoc (wireDyadic lower) (wireDyadic upper) (wireFormula formula)

private def emitCase (case : Case) : IO Unit := do
  emitRcfFixture lib case.id (wireSentence case.sentence)
  match Hex.RCF.decide case.sentence with
  | some verdict => emitResult lib case.id "decide" (if verdict then "true" else "false")
  | none => throw <| IO.userError s!"{lib}/{case.id}: certificate builder returned none"

private def degree50 : List Int :=
  [-1, 20, -100] ++ List.replicate 47 0 ++ [1]

private def degree10a : List Int := [1, -1, 0, 2, 0, -1, 0, 1, 0, 0, 1]
private def degree10b : List Int := [-1, 0, 1, 0, -2, 0, 1, 0, 0, 1, 1]
private def degree10c : List Int := [2, 1, 0, -1, 0, 1, 0, -1, 0, 0, 1]

private def localCases : List Case := [
  { id := "local/quadratic",
    sentence := .forallReal (atom posQuad .gt) },
  { id := "local/degree10-three-atoms",
    sentence := .forallReal (.or
      (.atom ⟨poly degree10a, .ne⟩)
      (.and (.atom ⟨poly degree10b, .le⟩) (.atom ⟨poly degree10c, .gt⟩))) },
  { id := "local/mignotte-degree50",
    sentence := .existsReal (atom degree50 .eq) }
]

private def emitAll (cases : List Case) : IO Unit := do
  for case in cases do emitCase case

end Hex.RCF.Emit

open Hex.RCF.Emit in
def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      if ciCases.length != 30 then
        throw <| IO.userError s!"ci tier has {ciCases.length} cases; expected exactly 30"
      emitAll ciCases
  | ["local"] => emitAll localCases
  | _ => throw <| IO.userError "usage: hexrcf_emit_fixtures [local]"
