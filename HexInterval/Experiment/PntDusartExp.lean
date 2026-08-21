/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Rational

@[expose] public section

/-!
# Source-pinned Dusart exponential leaves

Seven of the eight executable numerical leaves in PNT+'s
`Dusart.proposition_5_4a` and `Dusart.proposition_5_4b` are fixed comparisons
checked here after a 64-way reduction and one degree-11 Taylor window.  The
remaining `exp 22` leaf is supplied by an existing stronger package theorem
in the Mathlib companion.
-/

namespace Hex.Interval.Experiment.PntDusartExp

abbrev Q := Rat

inductive Relation where
  | upperLe
  | upperLt
  | lowerLe
  deriving DecidableEq, Repr

structure Certificate where
  sourceIndex : Nat
  argumentNum : Nat
  argumentDen : Nat
  target : Nat
  relation : Relation
  split : Nat
  terms : Nat
  deriving DecidableEq, Repr

def qadd : Q → Q → Q := Rational.add
def qmul : Q → Q → Q := Rational.mul

def qpow (value : Q) : Nat → Q
  | 0 => 1
  | n + 1 => qmul (qpow value n) value

/-- Six squarings implement the fixed 64-way range-reduction power. -/
def qpow64 (value : Q) : Q :=
  let p2 := qmul value value
  let p4 := qmul p2 p2
  let p8 := qmul p4 p4
  let p16 := qmul p8 p8
  let p32 := qmul p16 p16
  qmul p32 p32

def qLe (left right : Q) : Bool :=
  decide (left.num * (right.den : Int) ≤ right.num * (left.den : Int))

def qLt (left right : Q) : Bool :=
  decide (left.num * (right.den : Int) < right.num * (left.den : Int))

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def term (value : Q) (degree : Nat) : Q :=
  qmul (qpow value degree) (Rat.divInt 1 (factorial degree))

def sumTerms (value : Q) : Nat → Q
  | 0 => 0
  | n + 1 => qadd (sumTerms value n) (term value n)

/-- The degree-11 Taylor polynomial plus the explicit degree-12 remainder
majorant used on `[0, 1]`. -/
def taylorUpper (value : Q) : Q :=
  qadd (sumTerms value 12)
    (qmul (qpow value 12) (Rat.divInt 13 (factorial 12 * 12)))

def Certificate.reduced (value : Certificate) : Q :=
  Rat.divInt value.argumentNum (value.argumentDen * value.split)

def Certificate.targetQ (value : Certificate) : Q := value.target

def comparisonHolds (value : Certificate) : Bool :=
  let lower := qpow64 (sumTerms value.reduced value.terms)
  let upper := qpow64 (taylorUpper value.reduced)
  match value.relation with
  | .upperLe => qLe upper value.targetQ
  | .upperLt => qLt upper value.targetQ
  | .lowerLe => qLe value.targetQ lower

def sourceRows : List Certificate := [
  ⟨0, 29, 1, 4000000000000000000, .upperLe, 64, 12⟩,
  ⟨1, 10, 1, 4000000000000000000, .upperLt, 64, 12⟩,
  ⟨2, 1283, 100, 370261, .lowerLe, 64, 12⟩,
  ⟨3, 1312, 100, 492113, .lowerLe, 64, 12⟩,
  ⟨4, 1452, 100, 2010733, .lowerLe, 64, 12⟩,
  ⟨5, 1666, 100, 17051707, .lowerLe, 64, 12⟩,
  ⟨6, 43, 1, 4000000000000000000, .lowerLe, 64, 12⟩
]

/-- Authenticate the exact source row and the bounded Taylor computation. -/
def validCertificate (value : Certificate) : Bool :=
  sourceRows[value.sourceIndex]? == some value &&
    decide (value.argumentDen ≠ 0) && value.split == 64 && value.terms == 12 &&
      qLe 0 value.reduced && qLe value.reduced 1 && comparisonHolds value

def certificates : List Certificate := sourceRows

def firstFailure? : List Certificate → Option Nat
  | [] => none
  | value :: values =>
      if validCertificate value then firstFailure? values else some value.sourceIndex

end Hex.Interval.Experiment.PntDusartExp

end
