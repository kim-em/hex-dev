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
    let (result,stats) := MatrixState.finishWith quantum state false
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

/-- Native validation preserves malformed-input errors, charged prefixes and
shared paused states across coefficient widths and the native row-size bound. -/
def validationChecks : Bool := Id.run do
  for field in Fixtures.fields do
    let some valid := SparseRow.ofEntries field 3 #[(0,1),(2,1)] | return false
    let raw (columns : Array Nat) (coefficients : Array UInt64) : SparseRow :=
      ⟨columns.foldl (fun b c => Packed.push .u32 b c.toUInt64) {},
        coefficients.foldl (fun b c => Packed.push field.width b c) {}⟩
    let rows : Array SparseRow := #[
      {valid with columns := valid.columns.push 0},
      {valid with coefficients := valid.coefficients.push 0},
      raw #[0,2] #[1,0], raw #[0,2] #[1,field.modulus],
      raw #[0,1,2,3] #[1,1,1,1], raw #[0,1,2,2] #[1,1,1,1],
      raw #[0,0,0,0,0] #[1,1,1,1,1]]
    for row in rows do
      for targets in [false,true] do
        let reducers := if targets then #[valid] else #[valid,row]
        let targetRows := if targets then #[valid,row] else #[valid]
        -- The preceding two-entry valid row charges 1+2 work. Limits 3 and 4
        -- therefore distinguish initial-work and entry-work exhaustion.
        for limits in ([{}, {inputEntries := 3}, {packedBytes := 25},
            {work := 3}, {work := 4}, {work := 2^90, packedBytes := 2^90}] : List MatrixLimits) do
          let mut state := MatrixState.start field limits 3 reducers targetRows #[] false
          for _ in [:32] do
            if state.phase == .done then break
            let saved := snapshot state
            for quantum in [1,2,64] do
              let expected := MatrixState.advancePortable state quantum
              let actual := MatrixState.advance state quantum
              if expected.phase != actual.phase || snapshot expected != snapshot actual ||
                  snapshot state != saved then return false
              if expected.phase == .done then
                if !equal ⟨expected.result.getD (.error .rowUpdate),expected.stats⟩
                    ⟨actual.result.getD (.error .rowUpdate),actual.stats⟩ then return false
            state := MatrixState.advance state 1
          if state.phase != .done then return false
  return true

/-- Exercise workspace charges immediately below/at the exact boundary for
all coefficient widths, including a work failure after the byte charge. -/
def workspaceChecks : Bool := Id.run do
  for field in Fixtures.fields do
    let some row := SparseRow.ofEntries field 3 #[(0,1),(2,1)] | return false
    let initial := MatrixState.start field {} 3 #[row] #[row] #[] false
    let mut validated := initial
    for _ in [:8] do
      if validated.phase == .workspace then break
      validated := MatrixState.advancePortable validated 1
    if validated.phase != .workspace then return false
    let bytes := 3*(field.width.bytes+4)
    let total := validated.stats.packedBytes+bytes
    let work := validated.stats.work+bytes
    for (limits,failure) in ([({packedBytes := total-1},some Resource.packedBytes),
        ({packedBytes := total},none),({work := work-1},some Resource.work),
        ({work},none)] : List (MatrixLimits × Option Resource)) do
      let mut state := MatrixState.start field limits 3 #[row] #[row] #[] false
      for _ in [:8] do
        if state.phase == .workspace then break
        state := MatrixState.advance state 1
      if state.phase != .workspace then return false
      let saved := snapshot state
      let expected := MatrixState.advancePortable state 1
      let actual := MatrixState.advance state 1
      match failure with
      | none =>
        if expected.phase != .input || expected.result.isSome ||
            expected.stats.packedBytes != total || expected.stats.work != work then return false
      | some resource =>
        if expected.phase != .done then return false
        match expected.result with
        | some (.error (.exhausted actualResource)) =>
          if actualResource != resource then return false
        | _ => return false
      if expected.phase != actual.phase || snapshot expected != snapshot actual ||
          snapshot state != saved then return false
      if expected.phase == .done then
        if !equal ⟨expected.result.getD (.error .rowUpdate),expected.stats⟩
            ⟨actual.result.getD (.error .rowUpdate),actual.stats⟩ then return false
  return true

#guard workspaceChecks

#guard validationChecks

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

private def pauseCheck (field : PrimeField) (columns : Nat) (reducers targets : Array SparseRow)
    (limits : MatrixLimits) (stride : Nat) : Bool := Id.run do
  let expected := Elimination.reference field limits columns reducers targets #[] false
  let mut state := MatrixState.start field limits columns reducers targets #[] false
  for tick in [:256] do
    if state.phase == .done then break
    let inspect := (state.phase == .scan || state.phase == .gather) && tick%stride == 0
    if inspect then
      let saved := snapshot state
      let scalar := MatrixState.advancePortable state 1
      let actual := MatrixState.advance state 1
      if scalar.phase != actual.phase || snapshot scalar != snapshot actual then return false
      if snapshot state != saved then return false
      if let some scalarResult := scalar.result then
        let some actualResult := actual.result | return false
        if !equal ⟨scalarResult,{}⟩ ⟨actualResult,{}⟩ then return false
      state := actual
    else state := MatrixState.advance state 1
  let some result := state.result | return false
  return equal expected ⟨result,state.stats⟩

/-- Saved workspaces and exact exhausted prefixes cross scan and gather quanta.
The work limit omits the final coefficient/column charge, after earlier quanta
have completed; output and byte limits similarly fail in the second gather. -/
def pauseChecks : Bool := Id.run do
  let some field8 := Fixtures.fields[1]? | return false
  let some field16 := Fixtures.fields[3]? | return false
  let some field32 := Fixtures.fields[5]? | return false
  for field in [field8,field16,field32] do
    let columns := 4097
    let some r := SparseRow.ofEntries field columns
      ((Array.range columns).map fun i => (i,1)) | return false
    let some t := SparseRow.ofEntries field columns
      ((Array.range columns).map fun i => (i,2)) | return false
    for reducers in [#[],#[r]] do
      let total := (Elimination.reference field {} columns reducers #[t] #[] false).stats
      for limits in ([{}, { work := total.work-columns-1 },
          { outputEntries := total.outputEntries-1 },
          { packedBytes := total.packedBytes-1 }] : List MatrixLimits) do
        if !pauseCheck field columns reducers #[t] limits 1 then return false
  let field := field8
  for columns in [65536,65537] do
    let some t := SparseRow.ofEntries field columns #[(0,2),(columns-1,1)] | return false
    if !pauseCheck field columns #[] #[t] {} 8 then return false
  return true

#guard pauseChecks

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

end Hex.Groebner.MatrixStateConformance
