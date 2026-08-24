/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntFks2XpowResults

/-!
# Source-pinned FKS2 inverse-power conformance

The six nested prefixes and six first-excluded cells share one exact rational
Taylor provider.  Row 11 additionally exposes the source's forty-cell sample.
-/

namespace Hex.IntervalMathlib.PntFks2XpowConformance

open Hex.Interval.Experiment
open PntFks2Shard (Cell)
open PntFks2Family (allCells)
open PntFks2Xpow

#guard prefixes.length == 6
#guard bands.length == 6
#guard sourceRows.length == 13
#guard (bands.map Band.cells).flatten == allCells.take maxCells
#guard prefixes.all prefixOk
#guard prefixes.all (fun value => (allCells[value.cells]?).isSome)
#guard firstFailure? 0 prefixes == none
#guard prefixes[0]? == some ⟨.row6, 3, 70, 80⟩
#guard prefixes[5]? == some ⟨.row11, 100, 3746, 3756⟩
#guard bands[0]? == some ⟨0, 0, 70⟩
#guard bands[5]? == some ⟨5, 1348, 2398⟩
#guard sourceRows[0]? ==
  some ⟨.row6, 46, "allCells_take_checkXpow_row6", .prefix, 0⟩
#guard sourceRows[10]? ==
  some ⟨.row11, 187, "sampleCells_checkXpow", .sample, 5⟩
#guard sourceRows[12]? ==
  some ⟨.row11, 393, "allCells_take_checkXpow", .prefix, 5⟩

def wrongFile : List Prefix := { prefixes[0] with file := .row7 } :: prefixes.drop 1
def oversized : List Prefix :=
  { prefixes[0] with cells := maxCells + 1 } :: prefixes.drop 1

def alterAt (index : Nat) (alter : Cell → Cell) : List Cell → List Cell
  | [] => []
  | cell :: cells =>
      if index = 0 then alter cell :: cells
      else cell :: alterAt (index - 1) alter cells

def brokenPrefix : List Cell :=
  alterAt 0 (fun cell => { cell with eps := 100 }) allCells

def brokenBoundary : List Cell :=
  alterAt 70 (fun cell => { cell with eps := 1 / 100000000000000000000 }) allCells

#guard firstFailure? 0 wrongFile == some ⟨0, some .row6, .identity⟩
#guard prefixOk wrongFile[0]
#guard !validCertificate 0 wrongFile[0]
#guard firstFailure? 0 oversized == some ⟨0, some .row6, .capacity⟩
#guard firstFailureWith? brokenPrefix 0 prefixes == some ⟨0, some .row6, .prefix⟩
#guard firstFailureWith? brokenBoundary 0 prefixes == some ⟨0, some .row6, .boundary⟩

/-- Source-shaped semantic replacement for the largest Boolean prefix. -/
theorem fullPrefix (cell : Cell) (member : cell ∈ allCells.take 3746) :
    PntFks2Xpow.XpowHolds prefixes[5] cell :=
  row11_prefix cell (by simpa [prefixes] using member)

/-- Source-shaped semantic replacement for the row-11 sample. -/
theorem sample (cell : Cell) (member : cell ∈ sampleCells) :
    PntFks2Xpow.XpowHolds prefixes[5] cell :=
  row11_sample cell member

/-- The first excluded row-11 cell genuinely violates the analytic bound. -/
theorem boundary (cell : Cell) (found : allCells[3746]? = some cell) :
    ¬ PntFks2Xpow.XpowHolds prefixes[5] cell :=
  row11_boundary cell (by simpa [prefixes] using found)

/-- info: 'Hex.Interval.Experiment.PntFks2Xpow.row11_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PntFks2Xpow.row11_prefix

/-- info: 'Hex.IntervalMathlib.PntFks2XpowConformance.fullPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fullPrefix

/-- info: 'Hex.Interval.Experiment.PntFks2Xpow.row11_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PntFks2Xpow.row11_boundary

/-- info: 'Hex.Interval.Experiment.PntFks2Xpow.row11_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PntFks2Xpow.row11_sample

end Hex.IntervalMathlib.PntFks2XpowConformance
