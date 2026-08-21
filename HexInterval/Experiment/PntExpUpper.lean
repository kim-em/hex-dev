/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntFks2Shard

@[expose] public section

/-!
# Source-pinned positive exponential upper bounds

Three pinned PNT+ leaves bound `exp` at positive integer arguments. This
module authenticates their exact source coordinates and reduces all three to
the package-owned FKS2 degree-11 Taylor bound followed by seven squarings.
-/

namespace Hex.Interval.Experiment.PntExpUpper

open PntFks2Shard

abbrev Q := PntFks2Shard.Q

inductive SourceFile where
  | fks2Floor
  | goldbach
  deriving DecidableEq, Repr

inductive Relation where
  | strict
  | weak
  deriving DecidableEq, Repr

structure Coordinate where
  file : SourceFile
  line : Nat
  deriving DecidableEq, Repr

structure Certificate where
  coordinate : Coordinate
  relation : Relation
  exponent : Nat
  additive : Nat
  target : Nat
  deriving DecidableEq, Repr

def Certificate.reducedQ (value : Certificate) : Q :=
  Rat.divInt value.exponent 128

def Certificate.additiveQ (value : Certificate) : Q :=
  Rat.divInt value.additive 1

def Certificate.targetQ (value : Certificate) : Q :=
  Rat.divInt value.target 1

def checkComparison (value : Certificate) : Bool :=
  qLe 0 value.reducedQ && qLe value.reducedQ 1 &&
    let upper := qadd (qpow128 (taylorUpper value.reducedQ)) value.additiveQ
    match value.relation with
    | .strict => qLt upper value.targetQ
    | .weak => qLe upper value.targetQ

def sourceRows : List Certificate := [
  ⟨⟨.fks2Floor, 11⟩, .strict, 10, 0, 22027⟩,
  ⟨⟨.goldbach, 250⟩, .weak, 59, 5, 113250000000000000000000000⟩,
  ⟨⟨.goldbach, 267⟩, .weak, 60, 5, 7785131284000000000000000004⟩
]

def validCertificate (index : Nat) (value : Certificate) : Bool :=
  sourceRows[index]? == some value && checkComparison value

def certificates : List Certificate := sourceRows

def firstFailure? : Nat → List Certificate → Option Coordinate
  | _, [] => none
  | index, value :: values =>
      if validCertificate index value then firstFailure? (index + 1) values
      else
        match sourceRows[index]? with
        | some expected => some expected.coordinate
        | none => some value.coordinate

end Hex.Interval.Experiment.PntExpUpper

end
