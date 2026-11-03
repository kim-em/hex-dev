/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebnerStateNative
import HexGroebner.Elimination
import HexGroebner.F4

namespace Hex.Groebner.DenseMatrixConformance

private def field : PrimeField :=
  ⟨2147483647,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

private def pivot (n : Nat) : SparseRow := Id.run do
  let mut ids : ByteArray := {}
  let mut coefficients : ByteArray := {}
  for i in [:n] do
    ids := Packed.push .u32 ids (i+i/3).toUInt64
    coefficients := Packed.push .u32 coefficients (i+1).toUInt64
  return ⟨ids,coefficients⟩

private def resultEq (a b : Option (Except MatrixError (Echelon × Array RemainderRow))) : Bool :=
  match a,b with
  | none,none => true
  | some (.error a),some (.error b) => a == b
  | some (.ok (a,ar)),some (.ok (b,br)) =>
    a.reducerRank == b.reducerRank && a.trace == b.trace &&
    a.rows.map (fun r => (r.row.columns,r.row.coefficients,r.fromTarget,r.multiplier,r.sugar,r.derivation)) ==
      b.rows.map (fun r => (r.row.columns,r.row.coefficients,r.fromTarget,r.multiplier,r.sugar,r.derivation)) &&
    ar.map (fun r => (r.row.columns,r.row.coefficients,r.sugar,r.derivation)) ==
      br.map (fun r => (r.row.columns,r.row.coefficients,r.sugar,r.derivation))
  | _,_ => false

private def same (a b : MatrixState.State) : Bool :=
  resultEq a.result b.result && a.phase == b.phase && a.validation == b.validation && a.input == b.input && a.rank == b.rank &&
  a.leading == b.leading && a.inverse == b.inverse && a.sugar == b.sugar && a.quanta == b.quanta &&
  a.scan.last == b.scan.last && a.scan.chargedUntil == b.scan.chargedUntil &&
  a.scan.leading == b.scan.leading && a.scan.sugar == b.scan.sugar && a.scan.factor == b.scan.factor &&
  a.gather.cursor == b.gather.cursor &&
  a.stats == b.stats && a.scan.dense == b.scan.dense && a.scan.column == b.scan.column &&
  a.scan.pending == b.scan.pending && a.scan.entry == b.scan.entry &&
  a.gather.dense == b.gather.dense && a.gather.columns == b.gather.columns &&
  a.gather.coefficients == b.gather.coefficients && a.dense == b.dense && a.slots == b.slots &&
  a.nativePivots.size == b.nativePivots.size &&
  a.densePivots.isSome == b.densePivots.isSome &&
  a.densePivots.map (·.active) == b.densePivots.map (·.active) &&
  (a.densePivots.map fun c => c.rows.map fun r =>
    (r.source.columns,r.source.coefficients,r.source.sugar,r.dense,r.first,r.size)) ==
  (b.densePivots.map fun c => c.rows.map fun r =>
    (r.source.columns,r.source.coefficients,r.source.sugar,r.dense,r.first,r.size))

/-- Cache-bearing matrix states compare at every phase, including suspended
updates and parent resource exhaustion. Targets are exact pivot multiples. -/
def checks (seed : Nat) : Bool := Id.run do
  let row := pivot 128
  let columns := 174
  let prepared := Matrix.preparePivot field { densePivots := true } columns
    ⟨row.columns,row.coefficients,seed⟩ {}
  if prepared.row.dense.isEmpty then return false
  for work in [0,1024,2048,4096,1000000] do
    for bytes in [0,1024,4096,1000000] do
      let limits : MatrixLimits := { work := work,packedBytes := bytes,densePivots := true }
      let initial := MatrixState.start field limits columns #[row] #[row,row] #[seed,7,11] false
      let mut native := initial
      let mut portable := initial
      for _ in [:64] do
        native := MatrixState.advance native 1
        portable := MatrixState.advancePortable portable 1
        if !same native portable then return false
        if native.phase == .done then break
      if native.phase != .done then return false
      if work == 1000000 && bytes == 1000000 then
        if native.stats.zeroRows != 2 || native.stats.reductions != 2 || native.pivots.size != 1 then return false
        let some cache := native.densePivots | return false
        if cache.rows.size != 1 || (cache.rows[0]?.map (·.dense.isEmpty)).getD true then return false
  return true

/-- Admission refusal after workspace allocation succeeds, in both target
modes, leaves exact sparse execution and charges no optimization payload. -/
def admissionChecks (seed : Nat) : Bool := Id.run do
  let row := pivot 128
  let base := 4*(row.columns.size+row.coefficients.size)+174*8
  let bytes := (Matrix.preparePivot field { densePivots := true } 174
    ⟨row.columns,row.coefficients,seed⟩ {}).packedBytes
  if bytes == 0 then return false
  for independent in [false,true] do
    for allowance in [base,base+bytes-1,base+bytes] do
      let limits : MatrixLimits := { work := 1000000,packedBytes := allowance,densePivots := true }
      let initial := MatrixState.start field limits 174 #[row] #[row,row] #[seed,7,11] independent
      let a := MatrixState.finishState 1 initial
      let b := MatrixState.finishState 1 initial false
      if !same a b || a.phase != .done || a.stats.zeroRows != 2 then return false
      let some cache := a.densePivots | return false
      let admitted := allowance == base+bytes
      if cache.active != admitted || a.stats.packedBytes != base+(if admitted then bytes else 0) then return false
  return true

private def unitRow (column : Nat) : SparseRow :=
  ⟨Packed.push .u32 {} column.toUInt64,Packed.push .u32 {} 1⟩

/-- Return a live shared checkpoint after the first nonempty cache is installed. -/
def snapshotState (seed : Nat) (independent : Bool) : MatrixState.State := Id.run do
  let a := pivot 128
  let b := unitRow 1
  let mut c := a
  for i in [:128] do
    let columns := Packed.set .u32 c.columns i ((Packed.read .u32 a.columns i)+2)
    c := { c with columns }
  let target (row : SparseRow) (column : Nat) : SparseRow :=
    ⟨Packed.push .u32 row.columns column.toUInt64,Packed.push .u32 row.coefficients 1⟩
  let mut state := MatrixState.start field { work := 1000000,densePivots := true } 174
    #[a,b,c] #[target a 173,target c 172,target b 171] #[seed,1,3,5,7,11] independent
  for _ in [:16] do
    state := MatrixState.advance state 1
    if state.pivots.size == 1 then break
  return state

/-- Mixed raw/dense pivots, nonzero gathered residuals, independent remainders
and shared nonempty-cache pushes agree across continuation schedules. -/
def mixedChecks (seed : Nat) : Bool := Id.run do
  for independent in [false,true] do
    let initial := snapshotState seed independent
    if initial.pivots.size != 1 || initial.densePivots.map (·.active) != some true then return false
    let a := MatrixState.finishState 1 initial
    let b := MatrixState.finishState 64 initial
    let c := MatrixState.finishState 1 initial false
    if !same a b || !same a c || a.phase != .done then return false
    let some old := initial.densePivots | return false
    let some cache := a.densePivots | return false
    if old.rows.size != 1 || initial.nativePivots.size != 1 then return false
    if cache.rows.size != (if independent then 3 else 6) || cache.rows.size != a.nativePivots.size then return false
    if (cache.rows[0]?.map (·.dense.isEmpty)).getD true ||
        !(cache.rows[1]?.map (·.dense.isEmpty)).getD false ||
        (cache.rows[2]?.map (·.dense.isEmpty)).getD true then return false
    if independent && (a.remainders.size != 3 || a.remainders.any (·.row.size != 1)) then return false
  return true

/-- Public dispatch compares rows and exact charges, including preparation
refusal after the input and output payload reservations have succeeded. -/
def dispatchChecks (seed : Nat) (boundaries : Bool) : Bool := Id.run do
  for columns in [128,129,174] do
    for n in [127,128] do
      let mut row : SparseRow := ⟨{},{}⟩
      for i in [:n] do
        let column := if i+1 == n then (if columns == 174 then 169 else columns-1) else i
        row := ⟨Packed.push .u32 row.columns column.toUInt64,
          Packed.push .u32 row.coefficients (i+1).toUInt64⟩
      let base := 4*(row.columns.size+row.coefficients.size)+columns*8
      let bytes := (Matrix.preparePivot field { densePivots := true } columns
        ⟨row.columns,row.coefficients,seed⟩ {}).packedBytes
      let allowances := if boundaries then [base-1,base,base+bytes-1,base+bytes] else [1000000]
      let workLimits := if boundaries then [0,2000,3000,4000,1000000] else [1000000]
      for allowance in allowances do
        for work in workLimits do
          for independent in [false,true] do
            let limits : MatrixLimits := { work,packedBytes := allowance,densePivots := true }
            let a := Elimination.run field limits columns #[row] #[row,row] false #[seed,3,5] true independent
            let b := Elimination.run field limits columns #[row] #[row,row] false #[seed,3,5] false independent
            if a.stats != b.stats || !resultEq (some a.result) (some b.result) then return false
  return true

/-- Preparation charges can exhaust the bulk frame's fixed quantum even when
its original sparse shape bound admits the frame. Accepted and declined results
agree with the independent reference evaluation. -/
def capChecks (seed : Nat) : Bool := Id.run do
  for count in [512,1024] do
    let mut rows : Array SparseRow := #[]
    for j in [:count] do
      let mut row := pivot 128
      for i in [:row.size] do
        let columns := Packed.set .u32 row.columns i ((Packed.read .u32 row.columns i)+j.toUInt64)
        row := { row with columns }
      rows := rows.push row
    let limits : MatrixLimits := { work := 10000000,densePivots := true }
    let sugars := Array.replicate count seed
    let a := Elimination.attempt field limits 4096 rows #[] sugars false
    let b := Elimination.attemptPortable field limits 4096 rows #[] sugars false
    if !resultEq (a.map (·.result)) (b.map (·.result)) || a.map (·.stats) != b.map (·.stats) ||
        a.isSome != (count == 512) then return false
  return true

#guard capChecks 0

#guard dispatchChecks 0 false
#guard dispatchChecks 0 true

#guard admissionChecks 0
#guard mixedChecks 0

/-- Complete linear-ideal F4 candidates use a three-quarter-full reducer
inside a wider symbolic column set. Sixty-six inputs exceed the bulk-frame
target cap, so the native continuation exercises its dense update. Output
equality is separate from timing. -/
def fullChecks (seed : Nat) : Bool := Id.run do
  let context : Context := ⟨field,238,.grevlex⟩
  let mut full : RawPolynomial := #[]
  let mut sparse : RawPolynomial := #[]
  for j in [:174] do
    let powers := (Array.replicate 238 0).set! j 1
    if j == 0 || j ≥ 2 then full := full.push ⟨powers,(j+1).toUInt64⟩
    if j == 1 || (j ≥ 2 && j%4 != 0) then sparse := sparse.push ⟨powers,(j+1).toUInt64⟩
  full := full.push ⟨(Array.replicate 238 0).set! 1 1,(seed%2147483646+1).toUInt64⟩
  let mut generators := #[full,sparse]
  for j in [174:238] do
    generators := generators.push #[⟨(Array.replicate 238 0).set! j 1,1⟩]
  match computeWith context { work := 1000000000,densePivots := true } generators,
      computeWith context { work := 1000000000 } generators with
  | .candidate cachedAnswer _,.candidate sparseAnswer _ => return cachedAnswer.polynomials == sparseAnswer.polynomials
  | _,_ => return false

#guard fullChecks 0

#guard checks 0

end Hex.Groebner.DenseMatrixConformance
