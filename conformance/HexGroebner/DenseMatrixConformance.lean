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

/-- Complete linear-ideal F4 candidates use a three-quarter-full reducer
inside a wider symbolic column set. Output equality is separate from timing. -/
def fullChecks (seed : Nat) : Bool := Id.run do
  let context : Context := ⟨field,174,.grevlex⟩
  let mut full : RawPolynomial := #[]
  let mut sparse : RawPolynomial := #[]
  for j in [:174] do
    let powers := (Array.replicate 174 0).set! j 1
    if j == 0 || j ≥ 2 then full := full.push ⟨powers,(j+1).toUInt64⟩
    if j == 1 || (j ≥ 2 && j%4 != 0) then sparse := sparse.push ⟨powers,(j+1).toUInt64⟩
  full := full.push ⟨(Array.replicate 174 0).set! 1 1,(seed%2147483646+1).toUInt64⟩
  let generators := #[full,sparse]
  match computeWith context { work := 1000000000,densePivots := true } generators,
      computeWith context { work := 1000000000 } generators with
  | .candidate cachedAnswer _,.candidate sparseAnswer _ => return cachedAnswer.polynomials == sparseAnswer.polynomials
  | _,_ => return false

#guard fullChecks 0

#guard checks 0

end Hex.Groebner.DenseMatrixConformance
