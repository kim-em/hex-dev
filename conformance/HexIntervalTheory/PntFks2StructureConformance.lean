/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Data.Rat.Cast.Order
import HexInterval.Experiment.PntFks2Structure

/-!
# Source-pinned FKS2 list-structure conformance

Seven bounded certificates replace 21 `native_decide` leaves: the full
extended Table 4 list and six Corollary 24 prefixes each contribute chain,
nonempty, and final-coordinate facts.
-/

namespace Hex.IntervalMathlib.PntFks2StructureConformance

open Hex.Interval.Experiment
open PntFks2Structure
open PntFks2Family (allCells)

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

#guard prefixes.length == 7
#guard sourceRows.length == 21
#guard prefixes.all prefixOk
#guard firstFailure? 0 prefixes == none
#guard prefixes[0]? == some ⟨36, 70, 80⟩
#guard prefixes[5]? == some ⟨383, 3746, 3756⟩
#guard prefixes[6]? == some ⟨99, 13590, 20000⟩
#guard sourceRows[0]? ==
  some ⟨.cor24Row6, 36, "midCells_chain_row6", .chain, 0⟩
#guard sourceRows[17]? ==
  some ⟨.cor24Row11, 387, "midCells_last", .last, 5⟩
#guard sourceRows[20]? ==
  some ⟨.table4Ext, 104, "allCells_ne_nil", .nonempty, 6⟩
#guard certificateFiles == [
  .cor24Row6, .cor24Row7, .cor24Row8, .cor24Row9, .cor24Row10,
  .cor24Row11, .table4Ext]

def wrongLast6 : List Prefix := { prefixes[0] with last := 79 } :: prefixes.drop 1
def wrongLast7 : List Prefix :=
  prefixes[0] :: { prefixes[1] with last := 106 } :: prefixes.drop 2
def capOnly : Prefix := { prefixes[6] with cells := maxCells + 1 }
def oversized : List Prefix := prefixes.take 6 ++ [capOnly]
def nonemptyOnly : Prefix := ⟨36, 0, 10⟩
def emptyPrefix : List Prefix := nonemptyOnly :: prefixes.drop 1
def wrongLine : List Prefix := { prefixes[0] with line := 37 } :: prefixes.drop 1
def brokenChain : List PntFks2Shard.Cell :=
  match allCells with
  | [] => []
  | cell :: cells => { cell with b := 11 } :: cells

#guard firstFailure? 0 wrongLast6 ==
  some ⟨0, some .cor24Row6, .fact .last⟩
#guard firstFailure? 0 wrongLast7 ==
  some ⟨1, some .cor24Row7, .fact .last⟩
#guard !prefixOk wrongLast6[0]

/- Each negative value below violates exactly the named checker conjunct. -/
#guard !withinCap capOnly
#guard nonemptyOk allCells capOnly
#guard chainOk allCells capOnly
#guard lastOk allCells capOnly
#guard !prefixOk capOnly
#guard firstFailure? 0 oversized ==
  some ⟨6, some .table4Ext, .capacity⟩

#guard withinCap nonemptyOnly
#guard !nonemptyOk allCells nonemptyOnly
#guard chainOk allCells nonemptyOnly
#guard lastOk allCells nonemptyOnly
#guard !prefixOk nonemptyOnly
#guard firstFailure? 0 emptyPrefix ==
  some ⟨0, some .cor24Row6, .fact .nonempty⟩

#guard withinCap prefixes[0]
#guard nonemptyOk brokenChain prefixes[0]
#guard !chainOk brokenChain prefixes[0]
#guard lastOk brokenChain prefixes[0]
#guard !prefixOkWith brokenChain prefixes[0]
#guard firstFailureWith? brokenChain 0 prefixes ==
  some ⟨0, some .cor24Row6, .fact .chain⟩

#guard firstFailure? 0 wrongLine ==
  some ⟨0, some .cor24Row6, .identity⟩
#guard prefixOk wrongLine[0]
#guard !validCertificate 0 wrongLine[0]

private theorem holdsAt (index : Nat) (value : Prefix)
    (row : prefixes[index]? = some value) (member : value ∈ prefixes) : Holds value := by
  apply certificateHolds index value
  simp only [validCertificate, Bool.and_eq_true]
  exact ⟨beq_iff_eq.mpr row,
    List.all_eq_true.mp prefixes_checked value member⟩

theorem prefix70 : Holds prefixes[0] := by
  apply holdsAt 0 prefixes[0]
  · decide
  · simp [prefixes]

theorem prefix97 : Holds prefixes[1] := by
  apply holdsAt 1 prefixes[1]
  · decide
  · simp [prefixes]

theorem prefix124 : Holds prefixes[2] := by
  apply holdsAt 2 prefixes[2]
  · decide
  · simp [prefixes]

theorem prefix260 : Holds prefixes[3] := by
  apply holdsAt 3 prefixes[3]
  · decide
  · simp [prefixes]

theorem prefix1348 : Holds prefixes[4] := by
  apply holdsAt 4 prefixes[4]
  · decide
  · simp [prefixes]

theorem prefix3746 : Holds prefixes[5] := by
  apply holdsAt 5 prefixes[5]
  · decide
  · simp [prefixes]

theorem fullFamily : Holds prefixes[6] := by
  apply holdsAt 6 prefixes[6]
  · decide
  · simp [prefixes]

/- The bridge is ordinary kernel reduction over package-owned data. -/
/-- info: 'Hex.Interval.Experiment.PntFks2Structure.certificateHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificateHolds

/-- info: 'Hex.IntervalMathlib.PntFks2StructureConformance.fullFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fullFamily

end Hex.IntervalMathlib.PntFks2StructureConformance
