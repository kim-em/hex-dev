/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebnerStateNative
import HexGroebner.Elimination
import HexGroebner.Fixtures

namespace Hex.Groebner.MatrixStateConformance

private def rowEq (a b : SparseRow) : Bool :=
  a.columns.data == b.columns.data && a.coefficients.data == b.coefficients.data

private def equal (a b : Elimination.Result) : Bool :=
  a.stats == b.stats && match a.result,b.result with
  | .error a,.error b => a == b
  | .ok (a,ar),.ok (b,br) =>
    a.reducerRank == b.reducerRank && a.trace == b.trace &&
    a.rows.size == b.rows.size && ar.size == br.size &&
    ((a.rows.zip b.rows).all fun (a,b) => rowEq a.row b.row &&
      a.fromTarget == b.fromTarget && a.derivation == b.derivation &&
      a.multiplier == b.multiplier && a.sugar == b.sugar) &&
    ((ar.zip br).all fun (a,b) => rowEq a.row b.row &&
      a.derivation == b.derivation && a.sugar == b.sugar)
  | _,_ => false

/-- Lists detach the byte values from every reference-counted native buffer. -/
private def snapshot (s : MatrixState.State) : Array (List UInt8) × Array Nat := Id.run do
  let mut bytes := #[s.dense.data.toList,s.slots.data.toList,s.scan.dense.data.toList,
    s.gather.dense.data.toList,s.gather.columns.data.toList,s.gather.coefficients.data.toList]
  let mut values := #[s.field.modulus.toNat,s.columns,s.validation,s.input,s.rank,s.leading,
    s.sugar,s.inverse.toNat,s.quanta,s.scan.column,s.scan.last,s.scan.chargedUntil,s.scan.leading,
    s.scan.pending,s.scan.entry,s.scan.sugar,s.scan.factor.toNat,s.gather.cursor,
    s.stats.work,s.stats.inputEntries,s.stats.outputEntries,s.stats.packedBytes,
    s.stats.traceNodes,s.stats.processedRows,s.stats.reductions,s.stats.zeroRows,
    s.reducers.size,s.targets.size,s.pivots.size,s.nativePivots.size,s.remainders.size,
    s.limits.columns,s.limits.rows,s.limits.inputEntries,s.limits.outputEntries,
    s.limits.packedBytes,s.limits.work,s.limits.traceNodes,if s.independent then 1 else 0,
    if s.result.isSome then 1 else 0]
  values := values ++ s.sugars
  for row in s.reducers ++ s.targets do
    bytes := bytes.push row.columns.data.toList |>.push row.coefficients.data.toList
  for pivot in s.pivots do
    bytes := bytes.push pivot.row.columns.data.toList |>.push pivot.row.coefficients.data.toList
    values := values ++ #[pivot.sugar,pivot.multiplier.toNat,if pivot.fromTarget then 1 else 0,
      pivot.derivation.getD 0,if pivot.derivation.isSome then 1 else 0]
  for pivot in s.nativePivots do
    bytes := bytes.push pivot.columns.data.toList |>.push pivot.coefficients.data.toList
    values := values.push pivot.sugar
  for row in s.remainders do
    bytes := bytes.push row.row.columns.data.toList |>.push row.row.coefficients.data.toList
    values := values ++ #[row.sugar,row.derivation.getD 0,if row.derivation.isSome then 1 else 0]
  return (bytes,values)

def stepChecks : Bool := Id.run do
  for field in Fixtures.fields do
    for c in Fixtures.cases field do
      let .ok reducers := Fixtures.sparse field c.columns c.reducers | return false
      let .ok targets := Fixtures.sparse field c.columns c.targets | return false
      for independent in [false,true] do
        let mut state := MatrixState.start field {} c.columns reducers targets
          ((Array.range (reducers.size+targets.size)).map fun i => 2^90+17*i) independent
        for _ in [:1000] do
          if state.phase == .done then break
          let saved := snapshot state
          for quantum in [0,1,2,63,64,4096,2^90] do
            let expected := MatrixState.advancePortable state quantum
            let actual := MatrixState.advance state quantum
            if expected.phase != actual.phase || snapshot expected != snapshot actual then return false
            if snapshot state != saved then return false
            if let some expected := expected.result then
              let some actual := actual.result | return false
              if !equal ⟨expected,{}⟩ ⟨actual,{}⟩ then return false
          state := MatrixState.advance state 1
        if state.phase != .done then return false
  return true

#guard stepChecks

private def compare (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) : Bool := Id.run do
  let expected := Elimination.reference field limits columns reducers targets sugars independent
  let state := MatrixState.start field limits columns reducers targets sugars independent
  for quantum in [1,2,63,64] do
    let (result,stats) := MatrixState.finishWith quantum state
    if !equal expected ⟨result,stats⟩ then return false
    let (result,stats) := MatrixState.finishWith quantum state true
    if !equal expected ⟨result,stats⟩ then return false
  return true

def checked : Bool := Id.run do
  for field in Fixtures.fields do
    for c in Fixtures.cases field do
      let .ok reducers := Fixtures.sparse field c.columns c.reducers | return false
      let .ok targets := Fixtures.sparse field c.columns c.targets | return false
      let sugars := (Array.range (reducers.size+targets.size)).map fun i => 2^90+17*i
      for independent in [false,true] do
        let expected := Elimination.reference field {} c.columns reducers targets sugars independent
        if !compare field {} c.columns reducers targets sugars independent then return false
        for work in [0,1,64,expected.stats.work/2,expected.stats.work-1,expected.stats.work] do
          if !compare field { work } c.columns reducers targets sugars independent then return false
        for packedBytes in [0,1,expected.stats.packedBytes/2,expected.stats.packedBytes-1,
            expected.stats.packedBytes] do
          if !compare field { packedBytes } c.columns reducers targets sugars independent then return false
        for outputEntries in [0,expected.stats.outputEntries-1,expected.stats.outputEntries] do
          if !compare field { outputEntries } c.columns reducers targets sugars independent then return false
  return true

#guard checked

def boundaries : Bool := Id.run do
  let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let some r := SparseRow.ofEntries field 3 #[(0,2),(2,1)] | return false
  let some t := SparseRow.ofEntries field 3 #[(0,4),(1,1)] | return false
  let malformed : Array SparseRow := #[
    { r with columns := r.columns.push 0 },
    { r with coefficients := r.coefficients.push 0 },
    { r with coefficients := Packed.set field.width r.coefficients 0 0 },
    { r with columns := Packed.set .u32 r.columns 0 3 },
    { r with columns := Packed.set .u32 r.columns 1 0 }]
  for independent in [false,true] do
    for row in malformed do
      if !compare field {} 3 #[row] #[t] #[] independent then return false
      if !compare field {} 3 #[r] #[row] #[] independent then return false
    for columns in [0,2,3,4096,4097,2^90] do
      for sugars in [#[],#[2],#[2,3],#[2,2^90]] do
        if !compare field {} columns #[r] #[t] sugars independent then return false
    for n in [:128] do
      for limits in ([{ columns := n },{ rows := n },{ inputEntries := n },
          { outputEntries := n },{ packedBytes := n },{ work := n }] : List MatrixLimits) do
        if !compare field limits 3 #[r,r] #[t,t] #[2,3,4,2^90] independent then return false
  return true

#guard boundaries

/-- Paused failure states, not only terminal counters, agree under every
small allowance and arbitrary-precision work/byte allowances. -/
def resourceSteps : Bool := Id.run do
  let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let some r := SparseRow.ofEntries field 3 #[(0,2),(2,1)] | return false
  let some t := SparseRow.ofEntries field 3 #[(0,4),(1,2),(2,3)] | return false
  for independent in [false,true] do
    for n in (Array.range 128).push (2^90) do
      for limits in ([{ columns := n },{ rows := n },{ inputEntries := n },
          { outputEntries := n },{ packedBytes := n },{ work := n }] : List MatrixLimits) do
        let mut state := MatrixState.start field limits 3 #[r,r] #[t,t] #[2^90,3,4,5] independent
        for _ in [:1000] do
          if state.phase == .done then break
          let saved := snapshot state
          for quantum in [1,64] do
            let expected := MatrixState.advancePortable state quantum
            let actual := MatrixState.advance state quantum
            if expected.phase != actual.phase || snapshot expected != snapshot actual then return false
            if snapshot state != saved then return false
            if let some expected := expected.result then
              let some actual := actual.result | return false
              if !equal ⟨expected,{}⟩ ⟨actual,{}⟩ then return false
          state := MatrixState.advance state 1
        if state.phase != .done then return false
  return true

#guard resourceSteps

/-- Cross the old whole-frame cutoff and multiple prepaid scan/gather chunks,
including the new admission boundary. Supplied arrays can share ownership. -/
def largeChecks : Bool := Id.run do
  for field in Fixtures.fields do
    for columns in [4095,4096,4097,65535,65536,65537] do
      let some r := SparseRow.ofEntries field columns ((Array.range columns).filterMap fun i =>
        if i%2 == 0 then some (i,1) else none) | return false
      let coefficient := if field.modulus == 2 then 1 else 2
      let some t := SparseRow.ofEntries field columns
        ((Array.range columns).map fun i => (i,coefficient)) | return false
      for independent in [false,true] do
        let limits : MatrixLimits := { work := 2^90,packedBytes := 2^90 }
        let expected := Elimination.reference field limits columns #[r] #[t] #[2^90,3] independent
        let start := MatrixState.start field limits columns #[r] #[t] #[2^90,3] independent
        let (result,stats) := MatrixState.finishWith 64 start true
        if !equal expected ⟨result,stats⟩ then return false
        let (result,stats) := MatrixState.finishWith 64 start false
        if !equal expected ⟨result,stats⟩ then return false
    let some r := SparseRow.ofEntries field 3 #[(0,1),(2,1)] | return false
    let rows := Array.replicate 257 r
    for independent in [false,true] do
      if !compare field {} 3 rows rows #[] independent then return false
  return true

#guard largeChecks

/-- The imported theorem replays the modeled native boundary in the kernel. -/
example := MatrixState.validation_example

/-- info: 'Hex.Groebner.MatrixState.validation_example' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.validation_example

end Hex.Groebner.MatrixStateConformance
