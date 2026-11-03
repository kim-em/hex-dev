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
def resumeGather (native : Bool) : Bool :=
  let initial := Sampling.start field 2 #[] #[row] (Hex.Rand.ofSeed 2) {} #[] native
  let ready := seek .gather initial
  let exhausted := Sampling.next { limits with outputEntries := 1 } ready
  exhausted.failure == some (.exhausted .outputEntries) && exhausted.phase == .gather &&
    exhausted.random.state == ready.random.state && exhausted.gather.columns.size == 4 &&
    same (run exhausted) (run initial)

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
  let exhausted := Sampling.next { limits with work := pending.statistics.matrix.work } pending
  return exhausted.failure == some (.exhausted .work) &&
    exhausted.random.state == pending.random.state && same (run exhausted) (run initial)

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
        let .ok original := (eliminateWith field limits c.columns (reducers++targets) #[] false #[] false).result |
          return false
        let .ok check := (reduceRowsWith field limits c.columns (original.rows.map (·.row))
          (a.rows.map (·.row)) false #[] false).result | return false
        if check.rows.size != a.rows.size || !check.rows.all (·.row.size == 0) then return false
  return true

#guard miss false && miss true
#guard totalZeros false && totalZeros true
#guard resumeCombine false && resumeCombine true
#guard resumeGather false && resumeGather true
#guard resumeSlice false && resumeSlice true
#guard resumeScan false && resumeScan true
#guard corpus

end Hex.Groebner.SamplingChecks
