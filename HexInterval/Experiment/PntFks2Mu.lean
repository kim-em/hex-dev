/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntFks2Shard

@[expose] public section

/-!
# Source-pinned FKS2 mu-asymptotic leaves

The two pinned `mu_asymp` proofs repeat the same square-root lower bound and
small positive exponential upper bound. This module records all four exact
source coordinates and checks the unique rational obligations with the
package-owned FKS2 Taylor arithmetic.
-/

namespace Hex.Interval.Experiment.PntFks2Mu

open PntFks2Shard

abbrev Q := PntFks2Shard.Q

inductive SourceFile where
  | fks2
  | cor14
  deriving DecidableEq, Repr

inductive Relation where
  | sqrtLower
  | expUpper
  deriving DecidableEq, Repr

structure Coordinate where
  file : SourceFile
  line : Nat
  deriving DecidableEq, Repr

structure Certificate where
  coordinate : Coordinate
  relation : Relation
  inputNum : Nat
  inputDen : Nat
  targetNum : Nat
  targetDen : Nat
  deriving DecidableEq, Repr

def Certificate.inputQ (value : Certificate) : Q :=
  Rat.divInt value.inputNum value.inputDen

def Certificate.targetQ (value : Certificate) : Q :=
  Rat.divInt value.targetNum value.targetDen

def checkComparison (value : Certificate) : Bool :=
  match value.relation with
  | .sqrtLower =>
      qLe 0 value.targetQ &&
        qLe (qmul value.targetQ value.targetQ) value.inputQ
  | .expUpper =>
      qLe 0 value.inputQ && qLe value.inputQ 1 &&
        qLe (taylorUpper value.inputQ) value.targetQ

def sourceRows : List Certificate := [
  ⟨⟨.fks2, 4274⟩, .sqrtLower, 20000, 1, 1414213562, 10000000⟩,
  ⟨⟨.fks2, 4282⟩, .expUpper, 13689, 1000000, 10138790, 10000000⟩,
  ⟨⟨.cor14, 24⟩, .sqrtLower, 20000, 1, 1414213562, 10000000⟩,
  ⟨⟨.cor14, 32⟩, .expUpper, 13689, 1000000, 10138790, 10000000⟩
]

def validCertificate (index : Nat) (value : Certificate) : Bool :=
  sourceRows[index]? == some value &&
    decide (value.inputDen ≠ 0) && decide (value.targetDen ≠ 0) &&
      checkComparison value

def certificates : List Certificate := sourceRows

def firstFailure? : Nat → List Certificate → Option Coordinate
  | _, [] => none
  | index, value :: values =>
      if validCertificate index value then firstFailure? (index + 1) values
      else some value.coordinate

end Hex.Interval.Experiment.PntFks2Mu

end
