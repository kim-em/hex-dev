/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntFks2FamilyData
public import HexInterval.Experiment.PntFks2Shard

@[expose] public section

/-!
# Source-pinned FKS2 inverse-power prefixes

The six analytic Corollary 24 prefixes all ask whether a copied Table 4 cell
obeys `eps <= exp (-b' / n)`.  This module checks them with one exact rational
Taylor package.  It also checks a lower Taylor witness at each first excluded
cell; those witnesses prove actual failure of the analytic inequality rather
than merely failure of an enclosure algorithm.
-/

namespace Hex.Interval.Experiment.PntFks2Xpow

open PntFks2Shard
open PntFks2Family (allCells)

abbrev Q := PntFks2Shard.Q

inductive SourceFile where
  | row6
  | row7
  | row8
  | row9
  | row10
  | row11
  deriving DecidableEq, Repr

structure Prefix where
  file : SourceFile
  n : Nat
  cells : Nat
  boundary : Nat
  deriving DecidableEq, Repr

def maxCells : Nat := 3746

def Prefix.reducedQ (value : Prefix) (cell : Cell) : Q :=
  Rat.divInt cell.b' (128 * value.n)

def checkCell (value : Prefix) (cell : Cell) : Bool :=
  let reduced := value.reducedQ cell
  qLt 0 cell.eps && qLe 0 reduced && qLe reduced 1 &&
    qLe (qmul cell.eps (qpow128 (taylorUpper reduced))) 1

def checkBoundary (value : Prefix) (cell : Cell) : Bool :=
  let reduced := value.reducedQ cell
  qLt 0 cell.eps && qLe 0 reduced && qLe reduced 1 &&
    qLt 1 (qmul cell.eps (qpow128 (sumTerms reduced 12)))

def withinCap (value : Prefix) : Bool :=
  decide (0 < value.n) && decide (value.cells ≤ maxCells)

def prefixOkWith (data : List Cell) (value : Prefix) : Bool :=
  (data.take value.cells).all (checkCell value)

def boundaryOkWith (data : List Cell) (value : Prefix) : Bool :=
  match data[value.cells]? with
  | some cell => decide (cell.b = value.boundary) && checkBoundary value cell
  | none => false

def prefixOk (value : Prefix) : Bool :=
  withinCap value && prefixOkWith allCells value && boundaryOkWith allCells value

def prefixes : List Prefix := [
  ⟨.row6, 3, 70, 80⟩,
  ⟨.row7, 4, 97, 107⟩,
  ⟨.row8, 5, 124, 134⟩,
  ⟨.row9, 10, 260, 270⟩,
  ⟨.row10, 50, 1348, 1358⟩,
  ⟨.row11, 100, 3746, 3756⟩
]

/-- Disjoint pieces authenticated at the strongest source exponent that holds
on the piece.  Their concatenation is exactly the first 3,746 source cells. -/
structure Band where
  certificate : Nat
  start : Nat
  count : Nat
  deriving DecidableEq, Repr

def bands : List Band := [
  ⟨0, 0, 70⟩,
  ⟨1, 70, 27⟩,
  ⟨2, 97, 27⟩,
  ⟨3, 124, 136⟩,
  ⟨4, 260, 1088⟩,
  ⟨5, 1348, 2398⟩
]

def Band.cells (value : Band) : List Cell :=
  (allCells.drop value.start).take value.count

inductive SourceFact where
  | prefix
  | boundary
  | sample
  deriving DecidableEq, Repr

structure SourceRow where
  file : SourceFile
  line : Nat
  declaration : String
  fact : SourceFact
  certificate : Nat
  deriving DecidableEq, Repr

/- The declaration names and one-based decision-token lines are exact
coordinates in PNT+ revision 21998bb6196b56789f72a52656a781a75e134eb0. -/
def sourceRows : List SourceRow := [
  ⟨.row6, 46, "allCells_take_checkXpow_row6", .prefix, 0⟩,
  ⟨.row6, 52, "boundaryCell_fails_row6", .boundary, 0⟩,
  ⟨.row7, 46, "allCells_take_checkXpow_row7", .prefix, 1⟩,
  ⟨.row7, 52, "boundaryCell_fails_row7", .boundary, 1⟩,
  ⟨.row8, 46, "allCells_take_checkXpow_row8", .prefix, 2⟩,
  ⟨.row8, 52, "boundaryCell_fails_row8", .boundary, 2⟩,
  ⟨.row9, 46, "allCells_take_checkXpow_row9", .prefix, 3⟩,
  ⟨.row9, 52, "boundaryCell_fails_row9", .boundary, 3⟩,
  ⟨.row10, 46, "allCells_take_checkXpow_row10", .prefix, 4⟩,
  ⟨.row10, 52, "boundaryCell_fails_row10", .boundary, 4⟩,
  ⟨.row11, 187, "sampleCells_checkXpow", .sample, 5⟩,
  ⟨.row11, 193, "boundaryCell_fails", .boundary, 5⟩,
  ⟨.row11, 393, "allCells_take_checkXpow", .prefix, 5⟩
]

inductive Failure where
  | identity
  | capacity
  | prefix
  | boundary
  deriving DecidableEq, Repr

structure Coordinate where
  certificate : Nat
  file : Option SourceFile
  failure : Failure
  deriving DecidableEq, Repr

def certificateFiles : List SourceFile :=
  [.row6, .row7, .row8, .row9, .row10, .row11]

def validCertificate (index : Nat) (value : Prefix) : Bool :=
  prefixes[index]? == some value && prefixOk value

def failureAt? (data : List Cell) (index : Nat) (value : Prefix) : Option Failure :=
  if !withinCap value then some .capacity
  else if !prefixOkWith data value then some .prefix
  else if !boundaryOkWith data value then some .boundary
  else if !(prefixes[index]? == some value) then some .identity
  else none

def firstFailureWith? (data : List Cell) : Nat → List Prefix → Option Coordinate
  | _, [] => none
  | index, value :: values =>
      match failureAt? data index value with
      | some failure => some ⟨index, certificateFiles[index]?, failure⟩
      | none => firstFailureWith? data (index + 1) values

def firstFailure? (index : Nat) (values : List Prefix) : Option Coordinate :=
  firstFailureWith? allCells index values

end Hex.Interval.Experiment.PntFks2Xpow

end
