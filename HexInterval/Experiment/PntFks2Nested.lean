/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

@[expose] public section

/-!
# Source-pinned FKS2 nested-log premise

The pinned `FKS2.theorem_6_2` proof needs one concrete positivity fact at 14.
This module authenticates the exact source coordinate and the fixed constants
for a two-sided natural-log Taylor certificate.
-/

namespace Hex.Interval.Experiment.PntFks2Nested

structure Coordinate where
  line : Nat
  deriving DecidableEq, Repr

structure Certificate where
  coordinate : Coordinate
  input : Nat
  shift : Nat
  xNum : Nat
  xDen : Nat
  terms : Nat
  lower : Nat
  upper : Nat
  threshold : Nat
  deriving DecidableEq, Repr

/-- Check the arithmetic shape of the one source payload. This does not prove
the semantic logarithm window; `certificateHolds` proves the authenticated
source literal independently in the Mathlib companion. -/
def checkShape (value : Certificate) : Bool :=
  let power := 2 ^ value.shift
  value.input ≥ power &&
    value.xNum * (value.input + power) ==
      value.xDen * (value.input - power) &&
    value.xNum < value.xDen && value.terms == 8 &&
    value.lower < value.upper && 1 < value.lower &&
    value.threshold < value.lower

def sourceRows : List Certificate := [
  ⟨⟨3605⟩, 14, 3, 3, 11, 8, 2, 3, 1⟩
]

def validCertificate (index : Nat) (value : Certificate) : Bool :=
  sourceRows[index]? == some value && checkShape value

def certificates : List Certificate := sourceRows

def firstFailure? : Nat → List Certificate → Option Coordinate
  | _, [] => none
  | index, value :: values =>
      if validCertificate index value then firstFailure? (index + 1) values
      else
        match sourceRows[index]? with
        | some expected => some expected.coordinate
        | none => some value.coordinate

end Hex.Interval.Experiment.PntFks2Nested

end
