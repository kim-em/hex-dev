/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Elimination
import HexGroebner.Fixtures

namespace Hex.Groebner.MatrixPrimitiveConformance

private def same (a b : Except MatrixError Unit × MatrixStats) : Bool :=
  a.2 == b.2 && match a.1,b.1 with
  | .ok _,.ok _ => true
  | .error a,.error b => a == b
  | _,_ => false

/-- Compare exact row-validation errors, prefix charges and all untouched counters. -/
def checked : Bool := Id.run do
  for field in Fixtures.fields do
    let some row := SparseRow.ofEntries field 3 #[(0,1),(2,1)] | return false
    let ordinal (n : Nat) : SparseRow := {
      columns := (Array.range n).foldl (fun b i => Packed.push .u32 b i.toUInt64) {}
      coefficients := (Array.range n).foldl (fun b _ => Packed.push field.width b 1) {} }
    let shared := (ordinal 2).columns
    let rows := #[{},ordinal 4,ordinal 5,row,{columns := shared,coefficients := shared},
      {row with columns := Packed.set .u32 row.columns 1 65536},
      {row with columns := Packed.set .u32 row.columns 1 65537},
      {row with columns := Packed.set .u32 row.columns 1 4294967295},{row with columns := row.columns.push 0},
      {row with coefficients := row.coefficients.push 0},
      {row with coefficients := Packed.set field.width row.coefficients 1 0},
      {row with coefficients := Packed.set field.width row.coefficients 1 field.modulus},
      {row with columns := Packed.set .u32 row.columns 1 0},
      {row with columns := Packed.set .u32 row.columns 1 3}]
    for input in rows do
      let saved := (input.columns.data.toList,input.coefficients.data.toList)
      for index in [0,2^90] do
        for columns in [0,2,3,65536,65537,2^90] do
          for allowance in [0,1,2,3,4,8,16,64,2^62+17,2^63-1,2^90] do
            for limits in ([
                {work := allowance,inputEntries := allowance,packedBytes := allowance},
                {work := allowance},{inputEntries := allowance},{packedBytes := allowance},
                {work := allowance+1,inputEntries := allowance,packedBytes := allowance+7},
                {work := 2^90,packedBytes := allowance},
                {work := allowance,inputEntries := 2^90},
                {work := 2^62+17,inputEntries := allowance,packedBytes := 2^90}]
                : List MatrixLimits) do
              for stats in ([{}, {work := 1,inputEntries := 2,packedBytes := 3,outputEntries := 4,traceNodes := 5,processedRows := 6,reductions := 7,zeroRows := 8},
                  {work := 2^62-1},{work := 2^62},{zeroRows := 2^90}] : List MatrixStats) do
                let savedLimits := [limits.columns,limits.rows,limits.inputEntries,
                  limits.outputEntries,limits.packedBytes,limits.work,limits.traceNodes]
                let savedStats := [stats.work,stats.inputEntries,stats.outputEntries,
                  stats.packedBytes,stats.traceNodes,stats.processedRows,stats.reductions,stats.zeroRows]
                let expected := (Matrix.validate field limits columns index input).run stats
                let actual := (Matrix.validateWith field limits columns index input).run stats
                if !same expected actual then return false
                let admitted := USize.size == 2^64 && columns <= 65536 && input.size <= columns+1 &&
                  ([stats.work,stats.inputEntries,stats.outputEntries,stats.packedBytes,
                    stats.traceNodes,stats.processedRows,stats.reductions,stats.zeroRows].all (· <= 2^62-1))
                let attempted := Matrix.attemptValidation field limits columns index input stats
                if attempted.isSome != admitted then return false
                if let some result := attempted then
                  if !same result expected then return false
                if savedLimits != [limits.columns,limits.rows,limits.inputEntries,
                    limits.outputEntries,limits.packedBytes,limits.work,limits.traceNodes] ||
                    savedStats != [stats.work,stats.inputEntries,stats.outputEntries,
                      stats.packedBytes,stats.traceNodes,stats.processedRows,stats.reductions,stats.zeroRows] then
                  return false
                if saved != (input.columns.data.toList,input.coefficients.data.toList) then
                  return false
  for size in [0,1,4095,4096,4097,65536,1048576,1048577] do
    let actual := Matrix.zerosWith size
    if actual.size != size || !actual.data.all (· == 0) then return false
    let attempted := Matrix.attemptZeros size
    if attempted.isSome != (size <= 1048576) then return false
    if let some bytes := attempted then
      if bytes.data != actual.data then return false
  return true

/-- The disabled native-row route succeeds on every field fixture. The compiled
harness additionally requires both primitive call counters to remain unchanged. -/
@[noinline] def portable (seed : Nat) : Bool := Id.run do
  for field in Fixtures.fields do
    let some row := SparseRow.ofEntries field 3 #[(0,1),(2,1)] | return false
    let result := Elimination.run field {} (3+seed%2) #[row] #[row] false #[] false false
    if !result.result.isOk then return false
  return true

/-- Traced native elimination bypasses the bulk provider and must exercise
both bounded primitives. The harness checks admission counters around this call. -/
@[noinline] def integrated (seed : Nat) : Bool := Id.run do
  for field in Fixtures.fields do
    let some row := SparseRow.ofEntries field 3 #[(0,1),(2,1)] | return false
    let result := Elimination.run field {} (3+seed%2) #[row] #[row] true #[] true false
    if !result.result.isOk then return false
  return true

#guard integrated 0

#guard portable 0

#guard checked

/-- info: 'Hex.Groebner.Matrix.validateWith_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Matrix.validateWith_spec
/-- info: 'Hex.Groebner.Matrix.zerosWith_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Matrix.zerosWith_spec

end Hex.Groebner.MatrixPrimitiveConformance
