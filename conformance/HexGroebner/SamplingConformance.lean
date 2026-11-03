/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebnerStateNative
import HexGroebner.Fixtures

open Hex.Groebner

namespace Hex.Groebner.SamplingChecks

private def field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

private def row : SparseRow := ⟨Packed.push .u32 (Packed.push .u32 {} 0) 1,
  Packed.push .u8 (Packed.push .u8 {} 1) 1⟩

private def limits : MatrixLimits := { work := 10000000,packedBytes := 10000000 }

private def run (state : Sampling.State) : Sampling.State := Id.run do
  let mut state := state
  for _ in [:1000] do
    state := Sampling.next limits state
    if state.failure.isSome || state.phase == .done then break
  return state

private def same (a b : Sampling.State) : Bool :=
  a.failure == b.failure && a.random.state == b.random.state && a.statistics == b.statistics &&
  a.rows.map (fun p => (p.row.columns,p.row.coefficients,p.sugar)) ==
    b.rows.map (fun p => (p.row.columns,p.row.coefficients,p.sugar)) &&
  a.phase == b.phase

private def seek (phase : Sampling.Phase) (state : Sampling.State) : Sampling.State := Id.run do
  let mut state := state
  for _ in [:1000] do
    if state.phase == phase || state.failure.isSome || state.phase == .done then break
    state := Sampling.next limits state
  return state

/-- Seed 9 deliberately misses the rank-one input. Unchecked completion must
remain distinct from exact span verification or a completed checked basis. -/
def miss (native : Bool) : Bool :=
  let state := run (Sampling.start field 2 #[] #[row] (Hex.Rand.ofSeed 9) {} #[] native)
  state.failure.isNone && state.phase == .done && state.rows.isEmpty &&
    state.statistics.randomWords == 3 && state.statistics.combinations == 3 &&
    state.statistics.matrix.zeroRows == 3 &&
    state.random.state == (Hex.Rand.ofSeed 9).next.2.next.2.next.2.state

/-- Seed 2 has two zeros, a pivot, then a zero. The stopping count is total
zeros, so this block takes rank+3 trials rather than resetting a zero streak. -/
def totalZeros (native : Bool) : Bool :=
  let state := run (Sampling.start field 2 #[] #[row] (Hex.Rand.ofSeed 2) {} #[] native)
  state.failure.isNone && state.phase == .done && state.rows.size == 1 &&
    state.statistics.randomWords == 4 && state.statistics.combinations == 4 &&
    state.statistics.matrix.zeroRows == 3 && state.statistics.completedBlocks == 1

/-- A consumed nonzero draw stays attached to its pending row update. Exhaustion
before that update changes neither the draw nor its counter; resuming does not
redraw and reproduces the uninterrupted computation, including all statistics. -/
def resumeCombine (native : Bool) : Bool :=
  let initial := Sampling.start field 2 #[] #[row] (Hex.Rand.ofSeed 2) {} #[] native
  let ready := seek .combine initial
  let exhausted := Sampling.next { limits with work := ready.statistics.matrix.work+1 } ready
  exhausted.failure == some (.exhausted .work) && exhausted.phase == .combine &&
    exhausted.random.state == ready.random.state &&
    exhausted.statistics.randomWords == 3 && same (run exhausted) (run initial)

/-- Output exhaustion preserves the first appended entry. A later allowance
finishes that row without redrawing or charging its first entry again. -/
def resumeGather (native : Bool) : Bool := Id.run do
  let initial := Sampling.start field 2 #[] #[row] (Hex.Rand.ofSeed 2) {} #[] native
  let ready := seek .gather initial
  let snapshot := ready.gather.dense.data
  let exhausted := Sampling.next { limits with outputEntries := 1 } ready
  let completed := run exhausted
  return exhausted.failure == some (.exhausted .outputEntries) && exhausted.phase == .gather &&
    exhausted.random.state == ready.random.state && exhausted.gather.columns.size == 4 &&
    same completed (run initial) && ready.gather.dense.data == snapshot

/-- Every insufficient inverse/gather allowance leaves the phase uncharged.
The full resumed result includes exactly the uninterrupted statistics. -/
def resumeInverse (native : Bool) : Bool := Id.run do
  let some field := Fixtures.fields[6]? | return false
  let some row := SparseRow.ofEntries field 5 #[(1,3),(4,1)] | return false
  let initial := Sampling.start field 5 #[] #[row] (Hex.Rand.ofSeed 0) {} #[] native
  let ready := seek .inverse initial
  if ready.phase != .inverse then return false
  let after := Sampling.next limits ready
  let charge := after.statistics.matrix.work-ready.statistics.matrix.work
  if charge < 4 then return false
  let snapshot := ready.scan.dense.data
  for extra in [:charge] do
    let stopped := Sampling.next { limits with work := ready.statistics.matrix.work+extra } ready
    if stopped.failure != some (.exhausted .work) || stopped.phase != .inverse ||
        stopped.statistics != ready.statistics || stopped.random != ready.random ||
        !same (run stopped) (run initial) then return false
  return ready.scan.dense.data == snapshot

/-- A short target's reduction may reach far beyond its own last column.
The scan extends its bound when applying that pivot, and gather keeps the tail. -/
def extendRange (native : Bool) : Bool := Id.run do
  let some reducer := SparseRow.ofEntries field 4097 #[(3,1),(4096,1)] | return false
  let some target := SparseRow.ofEntries field 4097 #[(3,1)] | return false
  let initial := Sampling.start field 4097 #[reducer] #[target]
    (Hex.Rand.ofSeed 2) {} #[] native
  let ready := seek .scan initial
  if ready.scan.column != 4097 then return false -- First sampled coefficient is zero.
  let completed := run initial
  return completed.failure.isNone && completed.rows.size == 1 &&
    completed.rows[0]!.row.entries field == #[(4096,1)]

/-- Split a 4097-entry combination across calls, exhaust before the final
entry, and preserve an externally retained snapshot while completing it. -/
def resumeSlice (native : Bool) : Bool := Id.run do
  let some row := SparseRow.ofEntries field 4097 ((Array.range 4097).map fun i => (i,1)) |
    return false
  let initial := Sampling.start field 4097 #[] #[row] (Hex.Rand.ofSeed 0) {} #[] native
  let ready := seek .combine initial
  let pending := Sampling.next limits ready
  if pending.offset != 4096 || pending.phase != .combine then return false
  let snapshot := pending.dense.data
  let exhausted := Sampling.next { limits with work := pending.statistics.matrix.work } pending
  let resumed := run exhausted
  return exhausted.failure == some (.exhausted .work) &&
    exhausted.random.state == pending.random.state && same resumed (run initial) &&
    pending.dense.data == snapshot

/-- A pivot application can be interrupted after its full work was prepaid.
Resumption finishes the pending entries without charging the pivot twice. -/
def resumeScan (native : Bool) : Bool := Id.run do
  let some row := SparseRow.ofEntries field 4097 ((Array.range 4097).map fun i => (i,1)) |
    return false
  let initial := Sampling.start field 4097 #[] #[row] (Hex.Rand.ofSeed 0) {} #[] native
  let mut pending := initial
  for _ in [:1000] do
    if pending.phase == .scan && pending.statistics.combinations == 3 then break
    pending := Sampling.next limits pending
  pending := Sampling.next limits pending
  if pending.scan.pending == 0 || pending.scan.entry == 0 then return false
  let snapshot := pending.scan.dense.data
  let exhausted := Sampling.next { limits with work := pending.statistics.matrix.work } pending
  let completed := run exhausted
  return exhausted.failure == some (.exhausted .work) &&
    exhausted.random.state == pending.random.state && same completed (run initial) &&
    pending.scan.dense.data == snapshot

/-- Seeded native/scalar comparisons span all coefficient widths. Every output
is independently reduced against the full original matrix row space. A rank
miss is permitted here because these are explicitly unchecked candidates. -/
def corpus : Bool := Id.run do
  for field in Fixtures.fields do
    for c in Fixtures.cases field do
      let .ok reducers := Fixtures.sparse field c.columns c.reducers | return false
      let .ok targets := Fixtures.sparse field c.columns c.targets | return false
      let .ok known := (eliminateWith field limits c.columns reducers #[] false #[] false).result |
        return false
      let reducers := known.rows.map (·.row)
      for seed in [:3] do
        let initial := Sampling.start field c.columns reducers targets (Hex.Rand.ofSeed seed)
        let a := run initial
        let b := run (Sampling.start field c.columns reducers targets (Hex.Rand.ofSeed seed) {} #[] false)
        if !same a b || a.failure.isSome || a.phase != .done then return false
        let mut leading := reducers.map fun r => (Packed.read .u32 r.columns 0).toNat
        for pivot in a.rows do
          let r := pivot.row
          if r.size == 0 || Packed.read field.width r.coefficients 0 != 1 then return false
          let column := (Packed.read .u32 r.columns 0).toNat
          if leading.contains column then return false
          leading := leading.push column
        let .ok original := (eliminateWith field limits c.columns (reducers++targets) #[] false #[] false).result |
          return false
        let .ok check := (reduceRowsWith field limits c.columns (original.rows.map (·.row))
          (a.rows.map (·.row)) false #[] false).result | return false
        if check.rows.size != a.rows.size || !check.rows.all (·.row.size == 0) then return false
  return true

/-- Work, input-entry and packed-payload failures precede the atomic validator.
No reservation is charged twice when the caller supplies a larger allowance. -/
def resumeValidation (native : Bool) : Bool := Id.run do
  let initial := Sampling.start field 2 #[] #[row] (Hex.Rand.ofSeed 0) {} #[] native
  let ready := seek .validate initial
  for (caps,resource) in #[({ limits with work := 2 },Resource.work),
      ({ limits with inputEntries := 1 },Resource.inputEntries),
      ({ limits with packedBytes := 9 },Resource.packedBytes)] do
    let stopped := Sampling.next caps ready
    if stopped.failure != some (.exhausted resource) || stopped.statistics != ready.statistics ||
        stopped.random != ready.random || !same (run stopped) (run initial) then return false
  return true

/-- Combining a target consumes words before its new elimination row is
submitted. Row exhaustion keeps that dense combination and its advanced state. -/
def resumeRows (native : Bool) : Bool := Id.run do
  let initial := Sampling.start field 2 #[] #[row] (Hex.Rand.ofSeed 2) {} #[] native
  let ready := Sampling.next limits (seek .draw initial)
  let stopped := Sampling.next { limits with rows := 1 } ready
  return stopped.failure == some (.exhausted .rows) &&
    stopped.statistics.randomWords == 1 && stopped.statistics.combinations == 0 &&
    stopped.random == ready.random && same (run stopped) (run initial)

/-- Fresh known-pivot growth for instrumented ownership checks. The caller
uses a runtime size and observes the result before reading native counters. -/
def grow (n : Nat) : Bool := Id.run do
  let reducers := (Array.range n).map fun i => SparseRow.mk
    (Packed.push .u32 {} i.toUInt64) (Packed.push field.width {} 1)
  let mut state := Sampling.start field n reducers #[] (Hex.Rand.ofSeed 0)
  for _ in [:3*n+64] do
    state := Sampling.advance limits 64 state
    if state.failure.isSome || state.phase == .done then break
  return state.failure.isNone && state.phase == .done && state.pivots.size == n &&
    state.rows.isEmpty && state.statistics.randomWords == 0 &&
    ((state.pivots.zipIdx).all fun (row,i) =>
      (SparseRow.mk row.columns row.coefficients).entries field == #[(i,1)])

/-- Fresh target pivots exercise gather insertion rather than reducer setup.
The fixed M31 stream is checked for complete rank on these diagnostic sizes. -/
def growTargets (n : Nat) : Bool := Id.run do
  let some field := Fixtures.fields[6]? | return false
  let targets := (Array.range n).map fun i => SparseRow.mk
    (Packed.push .u32 {} i.toUInt64) (Packed.push field.width {} 1)
  let mut state := Sampling.start field n #[] targets (Hex.Rand.ofSeed 0)
    { blockRows := 1,zeroTests := 1 }
  for _ in [:32*n+64] do
    state := Sampling.advance limits 64 state
    if state.failure.isSome || state.phase == .done then break
  return state.failure.isNone && state.phase == .done && state.pivots.size == n &&
    state.rows.size == n && state.statistics.combinations == 2*n &&
    ((state.pivots.zipIdx).all fun (row,i) =>
      (SparseRow.mk row.columns row.coefficients).entries field == #[(i,1)])

#guard miss false && miss true
#guard totalZeros false && totalZeros true
#guard resumeCombine false && resumeCombine true
#guard resumeGather false && resumeGather true
#guard resumeInverse false && resumeInverse true
#guard extendRange false && extendRange true
#guard resumeSlice false && resumeSlice true
#guard resumeScan false && resumeScan true
#guard resumeValidation false && resumeValidation true
#guard resumeRows false && resumeRows true
#guard grow 128
#guard growTargets 128
#guard corpus

end Hex.Groebner.SamplingChecks
