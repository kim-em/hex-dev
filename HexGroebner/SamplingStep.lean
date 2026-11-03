/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.Sampling
public import HexGroebner.Sampling

public section

namespace Hex.Groebner.Sampling

private abbrev Work := ExceptT MatrixError (StateM State)

private def liftWork (action : Matrix.Work α) : Work α := ExceptT.mk fun s =>
  let (result,stats) := action.run s.statistics.matrix
  (result,{ s with statistics.matrix := stats })

private def spend (limits : MatrixLimits) (n : Nat) : Work Unit :=
  liftWork (Matrix.work limits n)

private def takeDense : Work ByteArray := do
  let dense := (← get).dense
  modify fun s => { s with
    dense := {} }
  return dense

private def takeScan : Work Native.Scan.State := do
  let scan := (← get).scan
  modify fun s => { s with
    scan := { scan with dense := {} } }
  return scan

private def takeGather : Work Native.Gather.State := do
  let gather := (← get).gather
  modify fun s => { s with
    gather := ⟨{},{},{},0⟩ }
  return gather

private def step (limits : MatrixLimits) (native : Bool) : Work Unit := do
  let s ← get
  match s.phase with
  | .check =>
    if s.config.blockRows == 0 || s.config.blockRows > 4096 || s.config.zeroTests == 0 then
      throw .dimensions
    if s.columns > 4294967295 || s.reducers.size+s.targets.size > 4294967295 then throw .dimensions
    if s.columns > limits.columns then throw (.exhausted .columns)
    if s.reducers.size+s.targets.size > limits.rows then throw (.exhausted .rows)
    if !s.sugars.isEmpty && s.sugars.size != s.reducers.size+s.targets.size then throw .dimensions
    modify fun s => { s with
      phase := .validate }
  | .validate =>
    if s.validation == s.reducers.size+s.targets.size then
      modify fun s => { s with
        phase := .workspace }
    else
      let row := if s.validation < s.reducers.size then s.reducers[s.validation]!
        else s.targets[s.validation-s.reducers.size]!
      -- Validation is one atomic row operation. Check its complete reservations
      -- first, so resumption never reserves the same input payload twice.
      if s.statistics.matrix.work+1+row.size > limits.work then throw (.exhausted .work)
      if s.statistics.matrix.inputEntries+row.size > limits.inputEntries then throw (.exhausted .inputEntries)
      if s.statistics.matrix.packedBytes+row.columns.size+row.coefficients.size > limits.packedBytes then
        throw (.exhausted .packedBytes)
      liftWork (if native then Matrix.validateWith s.field limits s.columns s.validation row
        else Matrix.validate s.field limits s.columns s.validation row)
      modify fun s => { s with
        validation := s.validation+1 }
  | .workspace =>
    let bytes := s.columns*(s.field.width.bytes+4)
    if bytes ≥ USize.size then throw .dimensions
    -- Check both reservations before either cumulative charge, so an exhausted
    -- allocation can be retried without charging the same workspace twice.
    if s.statistics.matrix.packedBytes+bytes > limits.packedBytes then throw (.exhausted .packedBytes)
    spend limits bytes
    liftWork (Matrix.packedBytes limits bytes)
    modify fun s => { s with
      dense := if native then Matrix.zerosWith (s.columns*s.field.width.bytes)
        else Matrix.zeros (s.columns*s.field.width.bytes)
      slots := if native then Matrix.zerosWith (s.columns*4) else Matrix.zeros (s.columns*4)
      phase := .install }
  | .install =>
    if s.installed == s.reducers.size then
      modify fun s => { s with
        phase := .block }
    else
      let row := s.reducers[s.installed]!
      if row.size == 0 || Packed.read s.field.width row.coefficients 0 != 1 then
        throw (.coefficient s.installed 0)
      let leading := (Packed.read .u32 row.columns 0).toNat
      if Packed.read .u32 s.slots leading != 0 then throw (.column s.installed 0)
      spend limits 1
      modify fun s => { s with
        slots := Packed.set .u32 s.slots leading (s.pivots.size+1).toUInt64
        pivots := s.pivots.push ⟨row.columns,row.coefficients,s.sugars[s.installed]?.getD 0⟩
        installed := s.installed+1
        statistics.matrix.processedRows := s.statistics.matrix.processedRows+1 }
  | .block =>
    if s.start == s.targets.size then modify fun s => { s with phase := .done }
    else
      let stop := min s.targets.size (s.start+s.config.blockRows)
      spend limits (stop-s.start)
      let sugar := (List.range (stop-s.start)).foldl
        (fun n i => max n (s.sugars[s.reducers.size+s.start+i]?.getD 0)) 0
      modify fun s => { s with
        stop,row := s.start,zeros := 0,trials := 0,sugar,phase := .draw }
  | .draw =>
    if s.row == s.stop then
      let dense ← takeDense
      modify fun s => { s with
        phase := .scan,
        scan := { dense,column := 0,last := s.columns-1,chargedUntil := 0,sugar := s.sugar },
        statistics.combinations := s.statistics.combinations+1,trials := s.trials+1 }
    else
      spend limits 1
      match s.random.nat s.field.modulus.toNat 1 with
      | .ok (value,random) =>
        modify fun s => { s with
          random,multiplier := value.toUInt64,offset := 0,
          row := if value == 0 then s.row+1 else s.row,
          phase := if value == 0 then .draw else .combine,
          statistics.randomWords := s.statistics.randomWords+1 }
      | .error (.exhausted _ random) =>
        modify fun s => { s with
          random,statistics.randomWords := s.statistics.randomWords+1 }
      | .error .zeroBound => throw .dimensions
  | .combine =>
    let row := s.targets[s.row]!
    let count := min 4096 (row.size-s.offset)
    spend limits count
    let field := s.field
        let offset := s.offset
    let factor := field.modulus-s.multiplier
    let dense ← takeDense
    let updated := if native then
      Native.subtract field.modulus dense row.columns row.coefficients offset count factor
      else Native.subtractPortable field.modulus dense row.columns row.coefficients offset count factor
    let some dense := updated | throw .rowUpdate
    modify fun s => { s with
      dense,offset := offset+count,
      row := if offset+count == row.size then s.row+1 else s.row,
      phase := if offset+count == row.size then .draw else .combine,
      statistics.combinationEntries := s.statistics.combinationEntries+count }
  | .scan =>
    let field := s.field
    let slots := s.slots
    let pivots := s.pivots
        let zeroTests := s.config.zeroTests
    let zeros := s.zeros
    let blockRows := s.stop-s.start
    let trials := s.trials
    let remaining := limits.work-s.statistics.matrix.work
    let scan ← takeScan
    let out := if native then Native.Scan.transition field.modulus slots pivots scan 4096 remaining 0 false
      else Native.Scan.portable field.modulus slots pivots scan 4096 remaining 0 false
    spend limits out.work
    modify fun s => { s with
      scan := out.state,
      statistics.matrix.reductions := s.statistics.matrix.reductions+out.reductions }
    if out.status == 2 then throw (.exhausted .work)
    if out.status != 0 && out.status != 1 then throw .rowUpdate
    if out.status == 1 then
      if out.state.leading == 0 then
        modify fun s => { s with
          dense := out.state.dense,scan := { out.state with dense := {} },
          zeros := s.zeros+1,statistics.matrix.zeroRows := s.statistics.matrix.zeroRows+1,
          statistics.matrix.processedRows := s.statistics.matrix.processedRows+1 }
        if zeros+1 == zeroTests then
          modify fun s => { s with
            start := s.stop,phase := .block,
            statistics.completedBlocks := s.statistics.completedBlocks+1 }
        else
          if trials ≥ blockRows+zeroTests then throw .rowUpdate
          modify fun s => { s with
            row := s.start,phase := .draw }
      else modify fun s => { s with phase := .inverse }
  | .inverse =>
    let leading := s.scan.leading-1
    let factor ← liftWork (Matrix.inverse s.field s.field.barrett limits
      (Packed.read s.field.width s.scan.dense leading))
    spend limits (s.columns-leading)
    modify fun s => { s with
      inverse := factor,phase := .gather,
      gather := ⟨s.scan.dense,{},{},leading⟩,scan := { s.scan with dense := {} } }
  | .gather =>
    -- Limit entries first: Gather tests this before charging an append.
    -- Matching byte/product capacities prevent later partially charged
    -- append failures and allow exact continuation inside a sparse output row.
    let entries := limits.outputEntries-s.statistics.matrix.outputEntries
    let stride := 4+s.field.width.bytes
    let bytes := (limits.packedBytes-s.statistics.matrix.packedBytes)/stride
    let products := if s.inverse == 1 then 4096 else limits.work-s.statistics.matrix.work
    let capacity := min 4096 (min entries (min bytes products))
    let field := s.field
        let columns := s.columns
    let inverse := s.inverse
    let sugar := s.scan.sugar
    let trials := s.trials
    let blockRows := s.stop-s.start
    let zeroTests := s.config.zeroTests
    let gather ← takeGather
    let out := if native then Native.Gather.gather field.modulus gather columns 4096 capacity (capacity*stride) capacity inverse
      else Native.Gather.portable field.modulus gather columns 4096 capacity (capacity*stride) capacity inverse
    liftWork (Matrix.charge .outputEntries out.entries limits.outputEntries
      (·.outputEntries) fun stats n => { stats with outputEntries := n })
    liftWork (Matrix.packedBytes limits out.bytes)
    spend limits out.work
    modify fun s => { s with
      gather := out.state }
    if out.status == 2 then
      if capacity == entries then throw (.exhausted .outputEntries)
      if capacity == bytes then throw (.exhausted .packedBytes)
      throw (.exhausted .work)
    if out.status != 0 && out.status != 1 then throw .rowUpdate
    if out.status == 1 || out.state.cursor == columns then
      let row : SparseRow := ⟨out.state.columns,out.state.coefficients⟩
      let leading := (Packed.read .u32 row.columns 0).toNat
      modify fun s => { s with
        dense := out.state.dense,gather := ⟨{},{},{},0⟩
        pivots := s.pivots.push ⟨row.columns,row.coefficients,sugar⟩
        slots := Packed.set .u32 s.slots leading (s.pivots.size+1).toUInt64
        rows := s.rows.push ⟨row,true,none,inverse,sugar⟩,
        statistics.matrix.processedRows := s.statistics.matrix.processedRows+1 }
      if trials ≥ blockRows+zeroTests then throw .rowUpdate
      modify fun s => { s with
        row := s.start,phase := .draw }
  | .done => pure ()

private theorem step_spec (limits : MatrixLimits) (native : Bool) :
    step limits native = step limits false := by
  simp only [step,Native.subtract,Native.Scan.transition,Native.Gather.gather,
    Matrix.zerosWith_spec,Matrix.validateWith_spec,ite_self]

/-- Advance one bounded phase. Exhaustion preserves the pending coefficient,
partial dense row, advanced random state and charged prefix. Other errors are
terminal. Native row updates and scan/gather inspect at most 4096 entries per
call; workspace initialization uses the existing capped native allocator. -/
private def nextWith (limits : MatrixLimits) (state : State) (native : Bool) : State := Id.run do
  match state.failure with
  | some (.exhausted _) => pure ()
  | some _ => return state
  | none => pure ()
  if state.columns > limits.columns then return { state with failure := some (.exhausted .columns) }
  if state.reducers.size+state.targets.size > limits.rows then return { state with failure := some (.exhausted .rows) }
  let stats := state.statistics.matrix
  if stats.work > limits.work then return { state with failure := some (.exhausted .work) }
  if stats.packedBytes > limits.packedBytes then return { state with failure := some (.exhausted .packedBytes) }
  if stats.inputEntries > limits.inputEntries then return { state with failure := some (.exhausted .inputEntries) }
  if stats.outputEntries > limits.outputEntries then return { state with failure := some (.exhausted .outputEntries) }
  if state.phase == .done then return { state with failure := none }
  let (result,state) := (step limits native).run { state with failure := none }
  match result with
  | .ok _ => return state
  | .error error => return { state with failure := some error }

/-- Advance using the implementation mode fixed at initialization. -/
def next (limits : MatrixLimits) (state : State) : State := nextWith limits state state.native

/-- Scalar reference phase with identical state, accounting and random draws. -/
def nextPortable (limits : MatrixLimits) (state : State) : State := nextWith limits state false

@[simp] theorem next_spec (limits : MatrixLimits) (state : State) :
    next limits state = nextPortable limits state := by
  simp only [next,nextPortable,nextWith,step_spec]

/-- Advance at most 64 phases, returning immediately on failure or completion.
This is a scheduling quantum, not an additional matrix-work allowance. -/
private def advanceWith (limits : MatrixLimits) (steps : Nat) (initial : State) (native : Bool) : State := Id.run do
  let mut state := initial
  for _ in [:min steps 64] do
    state := if native then next limits state else nextPortable limits state
    if state.failure.isSome || state.phase == .done then break
  return state

/-- Run a bounded scheduling quantum in the initialized implementation mode. -/
def advance (limits : MatrixLimits) (steps : Nat) (state : State) : State :=
  advanceWith limits steps state true

/-- Run the same quantum using scalar Lean primitives. -/
def advancePortable (limits : MatrixLimits) (steps : Nat) (state : State) : State :=
  advanceWith limits steps state false

@[simp] theorem advance_spec (limits : MatrixLimits) (steps : Nat) (state : State) :
    advance limits steps state = advancePortable limits steps state := by
  simp only [advance,advancePortable,advanceWith,next_spec,ite_self]

/-- New monic target pivots, available only after unchecked completion. Empty
output can be a sampling miss, and must not establish rank or completeness. -/
def State.candidate? (state : State) : Option (Array Pivot) :=
  if state.phase == .done && state.failure.isNone then some state.rows else none

end Hex.Groebner.Sampling
