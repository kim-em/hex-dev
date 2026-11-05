/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.GeneratorWindowInputs
public meta import HexRCF.GeneratorWindowInputs
public import HexRCF.RealCoefficients.FiniteIndex
public meta import HexRCF.RealCoefficients.FiniteIndex
public meta import Lean.Elab.Command
public section
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta
open Hex.RCF.GeneratorWindowTests
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
run_meta do
  let some data := FieldBuild.build SquareTwo.polynomial SquareTwo.square hw hp values matrix (17 : Nat) 8 |
    throwError "indexed context fixture production failed"
  let query := RepresentationSpecialize.polynomial values
  let keys := FieldCells.keys query matrix data.radical.core data.isolation data.rootSigns
  let some table := FieldBuild.buildTable SquareTwo.polynomial SquareTwo.square hw hp
      (data.signs.entries.map (·.key) ++ keys) | throwError "indexed sign production failed"
  let good := LiteralSign.Index.build table.entries.toArray Field.keyOrder
  let routes := #[good, .empty, .node (table.entries.length+1) .empty .empty]
  for compare in #[Field.keyOrder, (fun (_ _ : K) => Ordering.eq)] do
    for index in routes do
      let check context table := FieldCells.checkIndex table compare index context query matrix
        data.radical data.isolation data.rootSigns
      unless check 17 table do throwError "routing changed valid acceptance"
      if check 18 table then throwError "swapped context accepted"
      if check 17 {table with entries := []} then throwError "missing indexed signs accepted"
      let corrupt := {table with entries := table.entries.map fun entry =>
        {entry with value := entry.value+1}}
      if check 17 corrupt then throwError "corrupted indexed signs accepted"
  for name in #[``Field.lookupIndex_eq, ``FieldQuery.cachedIndex_eq, ``FieldCells.checkIndex_eq] do
    let axioms ← collectAxioms name
    unless axioms.toList.mergeSort Name.quickLt ==
        [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
      throwError "unexpected index law axioms: {name}: {axioms}"
  logInfo "FINITE_INDEX_CHECKS: valid/malformed routes; degenerate comparator; missing/corrupt signs; swapped Nat contexts; standard axioms only"
