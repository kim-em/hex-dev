/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntFks2FamilyData

@[expose] public section

/-!
# Structural certificates for pinned PNT+ FKS2 prefixes

The extended Table 4 list and the six Corollary 24 prefixes use the same three
structural facts: the list is nonempty, adjacent cell endpoints form a chain,
and the last endpoint is the declared upper coordinate.  This module checks
those facts with one package-owned bounded fold over the exact copied cells.
-/

namespace Hex.Interval.Experiment.PntFks2Structure

open PntFks2Shard (Cell)
open PntFks2Family (allCells)

def chainFrom : Nat → List Cell → Bool
  | _, [] => true
  | expected, cell :: cells =>
      cell.b == expected && chainFrom cell.b' cells

def lastB (fallback : Nat) : List Cell → Nat
  | [] => fallback
  | cell :: cells => lastB cell.b' cells

structure Prefix where
  line : Nat
  cells : Nat
  last : Nat
  deriving DecidableEq, Repr

def maxCells : Nat := 13590

def withinCap (spec : Prefix) : Bool := decide (spec.cells ≤ maxCells)

def nonemptyOk (data : List Cell) (spec : Prefix) : Bool :=
  decide (0 < (data.take spec.cells).length)

def chainOk (data : List Cell) (spec : Prefix) : Bool :=
  chainFrom 10 (data.take spec.cells)

def lastOk (data : List Cell) (spec : Prefix) : Bool :=
  lastB 10 (data.take spec.cells) == spec.last

def prefixOkWith (data : List Cell) (spec : Prefix) : Bool :=
  withinCap spec && nonemptyOk data spec && chainOk data spec && lastOk data spec

def prefixOk (spec : Prefix) : Bool := prefixOkWith allCells spec

/- The lengths below are byte-pinned, audited literal mappings from the seven
upstream prefix definitions.  The source matcher pins these values exactly; it
does not derive them from the upstream syntax. -/
def prefixes : List Prefix := [
  ⟨36, 70, 80⟩,
  ⟨36, 97, 107⟩,
  ⟨36, 124, 134⟩,
  ⟨36, 260, 270⟩,
  ⟨36, 1348, 1358⟩,
  ⟨383, 3746, 3756⟩,
  ⟨99, 13590, 20000⟩
]

inductive SourceFile where
  | table4Ext
  | cor24Row6
  | cor24Row7
  | cor24Row8
  | cor24Row9
  | cor24Row10
  | cor24Row11
  deriving DecidableEq, Repr

inductive Fact where
  | chain
  | nonempty
  | last
  deriving DecidableEq, Repr

inductive Failure where
  | identity
  | capacity
  | fact (value : Fact)
  deriving DecidableEq, Repr

structure Coordinate where
  certificate : Nat
  file : Option SourceFile
  failure : Failure
  deriving DecidableEq, Repr

def certificateFiles : List SourceFile := [
  .cor24Row6,
  .cor24Row7,
  .cor24Row8,
  .cor24Row9,
  .cor24Row10,
  .cor24Row11,
  .table4Ext
]

structure SourceRow where
  file : SourceFile
  line : Nat
  declaration : String
  fact : Fact
  certificate : Nat
  deriving DecidableEq, Repr

/- The 21 pinned native leaves share seven certificates.  The declaration and
line fields are data, not diagnostics inferred from list contents. -/
def sourceRows : List SourceRow := [
  ⟨.cor24Row6, 36, "midCells_chain_row6", .chain, 0⟩,
  ⟨.cor24Row6, 38, "midCells_ne_nil_row6", .nonempty, 0⟩,
  ⟨.cor24Row6, 40, "midCells_last_row6", .last, 0⟩,
  ⟨.cor24Row7, 36, "midCells_chain_row7", .chain, 1⟩,
  ⟨.cor24Row7, 38, "midCells_ne_nil_row7", .nonempty, 1⟩,
  ⟨.cor24Row7, 40, "midCells_last_row7", .last, 1⟩,
  ⟨.cor24Row8, 36, "midCells_chain_row8", .chain, 2⟩,
  ⟨.cor24Row8, 38, "midCells_ne_nil_row8", .nonempty, 2⟩,
  ⟨.cor24Row8, 40, "midCells_last_row8", .last, 2⟩,
  ⟨.cor24Row9, 36, "midCells_chain_row9", .chain, 3⟩,
  ⟨.cor24Row9, 38, "midCells_ne_nil_row9", .nonempty, 3⟩,
  ⟨.cor24Row9, 40, "midCells_last_row9", .last, 3⟩,
  ⟨.cor24Row10, 36, "midCells_chain_row10", .chain, 4⟩,
  ⟨.cor24Row10, 38, "midCells_ne_nil_row10", .nonempty, 4⟩,
  ⟨.cor24Row10, 40, "midCells_last_row10", .last, 4⟩,
  ⟨.cor24Row11, 383, "midCells_chain", .chain, 5⟩,
  ⟨.cor24Row11, 385, "midCells_ne_nil", .nonempty, 5⟩,
  ⟨.cor24Row11, 387, "midCells_last", .last, 5⟩,
  ⟨.table4Ext, 99, "allCells_chain", .chain, 6⟩,
  ⟨.table4Ext, 102, "allCells_last", .last, 6⟩,
  ⟨.table4Ext, 104, "allCells_ne_nil", .nonempty, 6⟩
]

def validCertificate (index : Nat) (value : Prefix) : Bool :=
  prefixes[index]? == some value && prefixOk value

def failureAt? (data : List Cell) (index : Nat) (value : Prefix) : Option Failure :=
  if !withinCap value then some .capacity
  else if !nonemptyOk data value then some (.fact .nonempty)
  else if !chainOk data value then some (.fact .chain)
  else if !lastOk data value then some (.fact .last)
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

def Holds (value : Prefix) : Prop :=
  let cells := allCells.take value.cells
  cells ≠ [] ∧ chainFrom 10 cells = true ∧ lastB 10 cells = value.last

theorem holds_of_check (value : Prefix) (checked : prefixOk value = true) :
    Holds value := by
  simp only [prefixOk, prefixOkWith, Bool.and_eq_true, withinCap,
    nonemptyOk, chainOk, lastOk, decide_eq_true_eq] at checked
  have nonempty : allCells.take value.cells ≠ [] := by
    intro empty
    rw [empty] at checked
    simp at checked
  exact ⟨nonempty, checked.1.2, beq_iff_eq.mp checked.2⟩

theorem certificateHolds (index : Nat) (value : Prefix)
    (valid : validCertificate index value = true) : Holds value := by
  simp only [validCertificate, Bool.and_eq_true] at valid
  exact holds_of_check value valid.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem prefixes_checked : prefixes.all prefixOk = true := by
  decide

end Hex.Interval.Experiment.PntFks2Structure
