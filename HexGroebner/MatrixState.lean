/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Matrix
public import HexGroebner.NativeScan
public import HexGroebner.NativeGather
import Init.Data.Range.Lemmas

public section

namespace Hex.Groebner.MatrixState

inductive Phase where
  | check | validate | workspace | input | scan | gather | order | done
  deriving BEq, Inhabited

/-- Private matrix continuation. The input identity travels with its workspace;
no continuation can be resumed against a different field, matrix or allowance.
Only untraced elimination is modeled here.

The 64-bit ABI has 20 object fields in declaration order after scalar fields
are removed: limits, columns, reducers, targets, sugars, validation, input,
dense, slots, pivots, nativePivots, remainders, rank, scan, gather, leading,
sugar, stats, result and quanta. Scalar storage is modulus/inverse (two UInt64), then
independent/phase (two UInt8). Native continuation owns the state and may copy
shared buffers; input matrices and saved snapshots remain immutable. -/
structure State where
  private mk ::
  field : PrimeField
  limits : MatrixLimits
  columns : Nat
  reducers : Array SparseRow
  targets : Array SparseRow
  sugars : Array Nat
  independent : Bool
  phase : Phase := .check
  validation : Nat := 0
  input : Nat := 0
  dense : ByteArray := {}
  slots : ByteArray := {}
  pivots : Array Pivot := #[]
  nativePivots : Array Native.Scan.Pivot := #[]
  remainders : Array RemainderRow := #[]
  rank : Nat := 0
  scan : Native.Scan.State := { dense := {},column := 0,last := 0,chargedUntil := 0 }
  gather : Native.Gather.State := ⟨{},{},{},0⟩
  leading : Nat := 0
  sugar : Nat := 0
  inverse : UInt64 := 1
  stats : MatrixStats := {}
  result : Option (Except MatrixError (Echelon × Array RemainderRow)) := none
  quanta : Nat := 0

def start (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) : State :=
  { field,limits,columns,reducers,targets,sugars,independent }

private abbrev Work := ExceptT MatrixError (StateM State)

private def liftWork (action : Matrix.Work α) : Work α := ExceptT.mk fun s =>
  let (result,stats) := action.run s.stats
  (result,{ s with stats })

private def work (n : Nat) : Work Unit := do
  liftWork (Matrix.work (← get).limits n)

private def completeRow : Work Unit :=
  modify fun s => { s with
    input := s.input+1
    phase := .input
    stats.processedRows := s.stats.processedRows+1 }

private def isTarget (s : State) : Bool := s.input >= s.reducers.size

private def install (row : SparseRow) (column : Nat) (inverse : UInt64) (sugar : Nat) : Work Unit := do
  let s ← get
  if s.independent && isTarget s then
    set { s with remainders := s.remainders.push ⟨row,none,sugar⟩ }
  else
    set { s with
      slots := Packed.set .u32 s.slots column (s.pivots.size+1).toUInt64
      pivots := s.pivots.push ⟨row,isTarget s,none,inverse,sugar⟩
      nativePivots := s.nativePivots.push ⟨row.columns,row.coefficients,sugar⟩
      rank := s.rank + if isTarget s then 0 else 1 }
  completeRow

private def zeroRow : Work Unit := do
  modify fun s => { s with
    remainders := if s.independent && isTarget s then
      s.remainders.push ⟨{},none,s.sugar⟩ else s.remainders
    stats.zeroRows := s.stats.zeroRows+1 }
  completeRow

private def takeDense : Work ByteArray := do
  let state ← get
  set { state with dense := {} }
  return state.dense

private def takeScan : Work Native.Scan.State := do
  let state ← get
  set { state with scan := { dense := {},column := 0,last := 0,chargedUntil := 0 } }
  return state.scan

private def takeGather : Work Native.Gather.State := do
  let state ← get
  set { state with gather := ⟨{},{},{},0⟩ }
  return state.gather

private def scanFuel (columns : Nat) : Nat := (columns*(columns+2)+4095)/4096+1

private def step (native : Bool) : Work Unit := do
  let s ← get
  match s.phase with
  | .check =>
    if s.columns > 4294967295 || s.reducers.size+s.targets.size > 4294967295 then
      throw .dimensions
    if s.columns > s.limits.columns then throw (.exhausted .columns)
    if s.reducers.size+s.targets.size > s.limits.rows then throw (.exhausted .rows)
    if !s.sugars.isEmpty && s.sugars.size != s.reducers.size+s.targets.size then throw .dimensions
    set { s with phase := .validate }
  | .validate =>
    if s.validation >= s.reducers.size+s.targets.size then
      set { s with phase := .workspace }
    else
      let row := if s.validation < s.reducers.size then s.reducers[s.validation]!
        else s.targets[s.validation-s.reducers.size]!
      liftWork (Matrix.validate s.field s.limits s.columns s.validation row)
      modify fun s => { s with validation := s.validation+1 }
  | .workspace =>
    let bytes := s.columns*(s.field.width.bytes+4)
    if bytes >= USize.size then throw .dimensions
    liftWork (Matrix.packedBytes s.limits bytes)
    work bytes
    modify fun s => { s with
      dense := Matrix.zeros (s.columns*s.field.width.bytes)
      slots := Matrix.zeros (s.columns*4), phase := .input }
  | .input =>
    if s.input >= s.reducers.size+s.targets.size then
      set { s with phase := .order }
    else
      work 1
      let row := if isTarget s then s.targets[s.input-s.reducers.size]! else s.reducers[s.input]!
      let sugar := s.sugars[s.input]?.getD 0
      modify fun s => { s with sugar }
      if row.size == 0 then zeroRow else
        let first := (Packed.read .u32 row.columns 0).toNat
        if !isTarget s && Packed.read .u32 s.slots first == 0 then
          let inverse ← liftWork (Matrix.inverse s.field s.field.barrett s.limits
            (Packed.read s.field.width row.coefficients 0))
          let output ← liftWork (Matrix.scaleSparse s.field s.field.barrett s.limits row inverse)
          install output first inverse sugar
        else
          work row.size
          let field := s.field
          let quanta := scanFuel s.columns
          let mut dense ← takeDense
          for i in [:row.size] do
            dense := Packed.set field.width dense (Packed.read .u32 row.columns i).toNat
              (Packed.read field.width row.coefficients i)
          modify fun s => { s with
            dense := {}
            phase := .scan
            quanta := quanta
            scan := {
              dense := dense
              column := first
              last := (Packed.read .u32 row.columns (row.size-1)).toNat
              chargedUntil := first
              sugar := sugar } }
  | .scan =>
    let field := s.field
    let limits := s.limits
    let slots := s.slots
    let pivots := s.nativePivots
    let remaining := s.limits.work-s.stats.work
    let independent := s.independent && isTarget s
    let quanta := s.quanta
    if quanta == 0 then throw .rowUpdate
    let initial ← takeScan
    modify fun s => { s with quanta := quanta-1 }
    let output := if native then
      Native.Scan.transition field.modulus slots pivots initial 4096 remaining 0 false
      else Native.Scan.portable field.modulus slots pivots initial 4096 remaining 0 false
    work output.work
    modify fun s => { s with
      scan := output.state
      stats.reductions := s.stats.reductions+output.reductions }
    if output.status == 2 then throw (.exhausted .work)
    if output.status == 3 then throw (.exhausted .traceNodes)
    if output.status != 0 && output.status != 1 then throw .rowUpdate
    if output.status == 0 && quanta == 1 then throw .rowUpdate
    if output.status == 1 then
      let state := output.state
      modify fun s => { s with sugar := state.sugar }
      if state.leading == 0 then
        modify fun s => { s with dense := state.dense,scan := { s.scan with dense := {} } }
        zeroRow
      else
        let column := state.leading-1
        let inverse ← if independent then pure 1 else
          liftWork (Matrix.inverse field field.barrett limits
            (Packed.read field.width state.dense column))
        work (state.last+1-column)
        modify fun s => { s with
          phase := .gather
          leading := column
          inverse := inverse
          quanta := (state.last+1-column+4095)/4096+1
          scan := { s.scan with dense := {} }
          gather := ⟨state.dense,{},{},column⟩ }
  | .gather =>
    let field := s.field
    let stop := s.scan.last+1
    let entries := s.limits.outputEntries-s.stats.outputEntries
    let bytes := s.limits.packedBytes-s.stats.packedBytes
    let remaining := s.limits.work-s.stats.work
    let limits := s.limits
    let inverse := s.inverse
    let leading := s.leading
    let sugar := s.sugar
    let quanta := s.quanta
    if quanta == 0 then throw .rowUpdate
    let initial ← takeGather
    modify fun s => { s with quanta := quanta-1 }
    let output := if native then
      Native.Gather.gather field.modulus initial stop 4096 entries bytes remaining inverse
      else Native.Gather.portable field.modulus initial stop 4096 entries bytes remaining inverse
    liftWork (Matrix.charge .outputEntries output.entries limits.outputEntries
      (·.outputEntries) fun stats n => { stats with outputEntries := n })
    liftWork (Matrix.packedBytes limits output.bytes)
    work output.work
    modify fun s => { s with gather := output.state }
    if output.status == 2 then throw (.exhausted .outputEntries)
    if output.status == 3 then throw (.exhausted .packedBytes)
    if output.status == 4 then throw (.exhausted .work)
    if output.status == 5 then throw .dimensions
    if output.status != 0 && output.status != 1 then throw .rowUpdate
    if output.status == 0 && quanta == 1 then throw .rowUpdate
    if output.status == 1 then
      let state := output.state
      modify fun s => { s with dense := state.dense,gather := ⟨{},{},{},0⟩ }
      install ⟨state.columns,state.coefficients⟩ leading inverse sugar
  | .order =>
    let mut ordered := #[]
    if !s.independent then
      work s.columns
      for column in [:s.columns] do
        let slot := (Packed.read .u32 s.slots column).toNat
        if slot != 0 then ordered := ordered.push s.pivots[slot-1]!
    modify fun s => { s with
      phase := .done
      result := some (.ok (⟨ordered,s.rank,#[]⟩,s.remainders)) }
  | .done => pure ()

private def advancePhase (state : State) (native : Bool) : State := Id.run do
  if state.phase == .done then return state
  let (result,state) := (step native).run state
  match result with
  | .ok _ => return state
  | .error e => return { state with phase := .done,result := some (.error e) }

/-- One phase using bounded native scan/gather. The exported Lean phase handles
non-hot phases and scalar values outside the frame's native fast path. -/
@[export lean_hex_matrix_step]
def next (state : State) : State := advancePhase state true

/-- Scalar model of one phase, including terminal error preservation. -/
def nextPortable (state : State) : State := advancePhase state false

@[simp] theorem next_spec (state : State) : next state = nextPortable state := by rfl

/-- Advance a bounded number of atomic phases. The shape-dependent cap budgets
workspace initialization, pending sparse-row charges and array growth
conservatively: at most max(1, 2^20/(8*columns+2*rows+4224)) phases per call. -/
private def advanceWith (state : State) (steps : Nat) (native : Bool) : State := Id.run do
  let count := min steps (max 1 (1048576 / (8*state.columns+2*(state.reducers.size+state.targets.size)+4224)))
  let mut state := state
  for _ in [:count] do
    if state.phase == .done then break
    state := advancePhase state native
  return state

/-- Scalar portable continuation, independent of all native scan/gather code. -/
def advancePortable (state : State) (steps : Nat) : State := advanceWith state steps false

/-- Ordinary Lean phase scheduling with bounded native scan/gather kernels. -/
def advanceKernels (state : State) (steps : Nat) : State := advanceWith state steps true

@[simp] theorem advanceKernels_spec (state : State) (steps : Nat) :
    advanceKernels state steps = advancePortable state steps := by rfl

/-- A native call uses the 64-bit ABI and admits at most 65536 columns and input rows. Other shapes take no transition
here, allowing the caller to run the portable continuation outside native code.
The state is owned and steps is borrowed Nat. C mirrors every intermediate
cursor, pending update, sugar label, charged prefix and terminal outcome.
Large counter values use the bounded Lean phase within the admitted geometry;
large allowances saturate above all totals reachable in one fast native call. -/
@[extern "lean_hex_matrix_advance"]
private def advanceSmall (state : State) (steps : @& Nat) : State :=
  if USize.size != 2^64 || state.columns > 65536 ||
      state.reducers.size+state.targets.size > 65536 then state
  else advancePortable state steps

/-- Bounded native continuation with the same scalar definition. -/
def advance (state : State) (steps : Nat) : State :=
  if USize.size != 2^64 || state.columns > 65536 ||
      state.reducers.size+state.targets.size > 65536 then
    advanceKernels state steps else advanceSmall state steps

@[simp] theorem advance_spec (state : State) (steps : Nat) :
    advance state steps = advancePortable state steps := by
  unfold advance advanceSmall
  split <;> simp_all [advanceKernels_spec]

/-- Shape-dependent outer phase allowance, independent of consumed budgets. -/
def State.allowance (state : State) : Nat :=
  6+(state.reducers.size+state.targets.size+1)*
    (3+scanFuel state.columns+(state.columns+4095)/4096+1)

/-- Run the untraced continuation with the selected native or scalar scheduler.
It is not selected by the public F4 route.

The shape allowance covers validation, workspace setup, input rows, bounded
scan/gather quanta and final ordering. Each unfinished call advances at least
one phase because the requested quantum is clamped to one. `MatrixStateFuel`
proves that every geometrically valid continuation reaches a terminal state
within this allowance, including states resumed partway through a row.
A scan or gather still unfinished at its last per-row quantum returns
`rowUpdate`; terminal completion alone does not rule out that error. -/
def finishState (quantum : Nat) (state : State) (native := true) : State := Id.run do
  let fuel := state.allowance
  let mut state := state
  for _ in [:fuel] do
    if state.phase == .done then break
    state := if native then advance state (max 1 quantum)
      else advancePortable state (max 1 quantum)
  return state

/-- Return the completed continuation's result and exact charged statistics.
The optional result retains the internal-invariant fallback. -/
def finishWith (quantum : Nat) (state : State) (native := true) :
    Except MatrixError (Echelon × Array RemainderRow) × MatrixStats :=
  let out := finishState quantum state native
  (out.result.getD (.error .rowUpdate),out.stats)

/-- The completion loop returns its final state's exact result and statistics,
including the internal-invariant fallback. -/
theorem finishWith_loop (quantum : Nat) (state : State) (native : Bool) :
    finishWith quantum state native = Id.run (do
      let fuel := state.allowance
      let mut state := state
      for _ in [:fuel] do
        if state.phase == .done then break
        state := if native then advance state (max 1 quantum)
          else advancePortable state (max 1 quantum)
      return (state.result.getD (.error .rowUpdate),state.stats)) := by rfl

/-- Selecting the native scheduler preserves the Lean model's complete result
and counters. Agreement of C with that model is a separately audited and tested
native obligation; this theorem does not verify C machine code. -/
theorem finish_spec (quantum : Nat) (state : State) (native : Bool) :
    finishWith quantum state native = finishWith quantum state false := by
  simp only [finishWith,finishState,advance_spec]
  cases native <;> rfl

/-- Complete the continuation in native batches of 64 phases. -/
def finish (state : State) := finishWith 64 state

/-- Validation preserves the exact successful or failed charged prefix. -/
private theorem next_validate (state : State) (stats : MatrixStats)
    (outcome : Except MatrixError Unit)
    (hphase : state.phase = .validate)
    (hcursor : state.validation < state.reducers.size + state.targets.size)
    (hvalidate :
      (Matrix.validate state.field state.limits state.columns state.validation
        (if state.validation < state.reducers.size then state.reducers[state.validation]!
          else state.targets[state.validation-state.reducers.size]!)).run state.stats =
        (outcome, stats)) :
    next state = match outcome with
      | .ok _ => { state with validation := state.validation + 1, stats := stats }
      | .error e => { state with stats := stats, phase := .done, result := some (.error e) } := by
  cases outcome
  all_goals
    simp only [next, advancePhase, hphase]
    dsimp [step, liftWork, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
      ExceptT.mk, StateT.bind, StateT.get, StateT.set, StateT.pure,
      Bind.bind, MonadState.get, MonadStateOf.get, MonadStateOf.set,
      MonadExcept.throw, MonadExceptOf.throw, liftM,
      MonadLiftT.monadLift, MonadLift.monadLift, getThe, throwThe,
      StateT.map, StateT.mk, Functor.map, Pure.pure]
    simp only [hphase, show (Phase.validate == Phase.done) = false from rfl,
      Bool.false_eq_true, ite_false, Nat.not_le_of_lt hcursor]
    dsimp [StateT.bind, ExceptT.bindCont, Id.run]
    simp only [ExceptT.run] at hvalidate
    rw [hvalidate]
    dsimp [modify, modifyThe, MonadStateOf.modifyGet, liftM,
      MonadLiftT.monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk,
      StateT.modifyGet, StateT.map, Functor.map, Pure.pure]
    simp only [hphase]
    rfl

/-- Workspace setup preserves the exact work-charge outcome after its byte
allowance succeeds. Buffer allocation follows only successful work charging. -/
private theorem next_workspace (state : State) (packedStats stats : MatrixStats)
    (outcome : Except MatrixError Unit)
    (hphase : state.phase = .workspace)
    (hsize : state.columns*(state.field.width.bytes+4) < USize.size)
    (hpacked : (Matrix.packedBytes state.limits
      (state.columns*(state.field.width.bytes+4))).run state.stats = (.ok (),packedStats))
    (hwork : (Matrix.work state.limits
      (state.columns*(state.field.width.bytes+4))).run packedStats = (outcome,stats)) :
    next state = match outcome with
      | .ok _ => { state with
          phase := .input
          dense := Matrix.zeros (state.columns*state.field.width.bytes)
          slots := Matrix.zeros (state.columns*4)
          stats := stats }
      | .error error => { state with phase := .done,stats := stats,result := some (.error error) } := by
  cases outcome
  all_goals
    simp only [next,advancePhase,hphase]
    dsimp [step,liftWork,work,ExceptT.run,ExceptT.bind,ExceptT.bindCont,ExceptT.lift,
      ExceptT.mk,StateT.bind,StateT.get,StateT.set,StateT.pure,
      Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,
      MonadExcept.throw,MonadExceptOf.throw,liftM,
      MonadLiftT.monadLift,MonadLift.monadLift,getThe,throwThe,
      StateT.map,StateT.mk,Functor.map,Pure.pure]
    simp only [hphase,show (Phase.workspace == Phase.done) = false from rfl,
      Bool.false_eq_true,ite_false,Nat.not_le_of_lt hsize]
    dsimp [StateT.bind,ExceptT.bindCont,Id.run]
    simp only [ExceptT.run] at hpacked hwork
    rw [hpacked]
    dsimp [modify,modifyThe,MonadStateOf.modifyGet,liftM,
      MonadLiftT.monadLift,MonadLift.monadLift,ExceptT.lift,ExceptT.mk,
      ExceptT.bind,ExceptT.bindCont,StateT.bind,StateT.get,StateT.set,StateT.pure,
      Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,getThe,
      StateT.modifyGet,StateT.map,Functor.map,Pure.pure]
    rw [hwork]
    dsimp [modify,modifyThe,MonadStateOf.modifyGet,liftM,
      MonadLiftT.monadLift,MonadLift.monadLift,ExceptT.lift,ExceptT.mk,
      ExceptT.bind,ExceptT.bindCont,StateT.bind,StateT.get,StateT.set,StateT.pure,
      Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,getThe,
      StateT.modifyGet,StateT.map,Functor.map,Pure.pure]
  all_goals rfl

/-- A failed byte reservation returns before work charging or allocation. -/
private theorem next_workspace_bytes (state : State) (stats : MatrixStats) (error : MatrixError)
    (hphase : state.phase = .workspace)
    (hsize : state.columns*(state.field.width.bytes+4) < USize.size)
    (hpacked : (Matrix.packedBytes state.limits
      (state.columns*(state.field.width.bytes+4))).run state.stats = (.error error,stats)) :
    next state = { state with phase := .done,stats := stats,result := some (.error error) } := by
  simp only [next,advancePhase,hphase]
  dsimp [step,liftWork,work,ExceptT.run,ExceptT.bind,ExceptT.bindCont,ExceptT.lift,
    ExceptT.mk,StateT.bind,StateT.get,StateT.set,StateT.pure,
    Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,
    MonadExcept.throw,MonadExceptOf.throw,liftM,
    MonadLiftT.monadLift,MonadLift.monadLift,getThe,throwThe,
    StateT.map,StateT.mk,Functor.map,Pure.pure]
  simp only [hphase,show (Phase.workspace == Phase.done) = false from rfl,
    Bool.false_eq_true,ite_false,Nat.not_le_of_lt hsize]
  dsimp [StateT.bind,ExceptT.bindCont,Id.run]
  simp only [ExceptT.run] at hpacked
  rw [hpacked]
  dsimp [modify,modifyThe,MonadStateOf.modifyGet,liftM,
    MonadLiftT.monadLift,MonadLift.monadLift,ExceptT.lift,ExceptT.mk,
    ExceptT.bind,ExceptT.bindCont,StateT.bind,StateT.get,StateT.set,StateT.pure,
    Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,getThe,
    StateT.modifyGet,StateT.map,Functor.map,Pure.pure]

/-- Unaddressable workspaces fail before either charge or allocation. -/
private theorem next_workspace_size (state : State)
    (hphase : state.phase = .workspace)
    (hsize : USize.size ≤ state.columns*(state.field.width.bytes+4)) :
    next state = { state with phase := .done,result := some (.error .dimensions) } := by
  simp only [next,advancePhase,hphase]
  dsimp [step,liftWork,work,ExceptT.run,ExceptT.bind,ExceptT.bindCont,ExceptT.lift,
    ExceptT.mk,StateT.bind,StateT.get,StateT.set,StateT.pure,
    Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,
    MonadExcept.throw,MonadExceptOf.throw,liftM,
    MonadLiftT.monadLift,MonadLift.monadLift,getThe,throwThe,
    StateT.map,StateT.mk,Functor.map,Pure.pure]
  simp only [hphase,show (Phase.workspace == Phase.done) = false from rfl,
    Bool.false_eq_true,ite_false,hsize,ite_true]
  rfl

/-- Read-only contents preserved by validation. Phase, validation cursor, result
and charged statistics are stated separately by the transition lemmas. -/
def State.contents (state : State) :=
  (state.field,state.limits,state.columns,state.reducers,state.targets,state.sugars,
    state.independent,state.input,state.dense,state.slots,state.pivots,state.nativePivots,
    state.remainders,state.rank,state.scan,state.gather,state.leading,state.sugar,
    state.inverse,state.quanta)

/-- Fields preserved by workspace setup. Buffer contents, phase, result and
charged statistics are stated separately by its transition contracts. -/
def State.workspaceFrame (state : State) :=
  (state.field,state.limits,state.columns,state.reducers,state.targets,state.sugars,
    state.independent,state.validation,state.input,state.pivots,state.nativePivots,
    state.remainders,state.rank,state.scan,state.gather,state.leading,state.sugar,
    state.inverse,state.quanta)

/-- Workspace setup installs the charged buffers and preserves every other
state field after byte and work charges succeed. -/
theorem workspace_ok (state : State) (packedStats stats : MatrixStats)
    (hphase : state.phase = .workspace)
    (hsize : state.columns*(state.field.width.bytes+4) < USize.size)
    (hpacked : (Matrix.packedBytes state.limits
      (state.columns*(state.field.width.bytes+4))).run state.stats = (.ok (),packedStats))
    (hwork : (Matrix.work state.limits
      (state.columns*(state.field.width.bytes+4))).run packedStats = (.ok (),stats)) :
    let out := next state
    out.phase = .input ∧ out.dense = Matrix.zeros (state.columns*state.field.width.bytes) ∧
      out.slots = Matrix.zeros (state.columns*4) ∧ out.stats = stats ∧
      out.result = state.result ∧ out.workspaceFrame = state.workspaceFrame := by
  rw [next_workspace state packedStats stats (.ok ()) hphase hsize hpacked hwork]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- A work-charge failure after reserving bytes preserves both existing
buffers and the full returned charge prefix in a terminal continuation. -/
theorem workspace_work_error (state : State) (packedStats stats : MatrixStats) (error : MatrixError)
    (hphase : state.phase = .workspace)
    (hsize : state.columns*(state.field.width.bytes+4) < USize.size)
    (hpacked : (Matrix.packedBytes state.limits
      (state.columns*(state.field.width.bytes+4))).run state.stats = (.ok (),packedStats))
    (hwork : (Matrix.work state.limits
      (state.columns*(state.field.width.bytes+4))).run packedStats = (.error error,stats)) :
    let out := next state
    out.phase = .done ∧ out.result = some (.error error) ∧ out.stats = stats ∧
      out.dense = state.dense ∧ out.slots = state.slots ∧
      out.workspaceFrame = state.workspaceFrame := by
  rw [next_workspace state packedStats stats (.error error) hphase hsize hpacked hwork]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- A failed packed-byte allowance preserves existing workspace buffers and
returns the validator's exact terminal charged prefix. -/
theorem workspace_bytes_error (state : State) (stats : MatrixStats) (error : MatrixError)
    (hphase : state.phase = .workspace)
    (hsize : state.columns*(state.field.width.bytes+4) < USize.size)
    (hpacked : (Matrix.packedBytes state.limits
      (state.columns*(state.field.width.bytes+4))).run state.stats = (.error error,stats)) :
    let out := next state
    out.phase = .done ∧ out.result = some (.error error) ∧ out.stats = stats ∧
      out.dense = state.dense ∧ out.slots = state.slots ∧
      out.workspaceFrame = state.workspaceFrame := by
  rw [next_workspace_bytes state stats error hphase hsize hpacked]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Addressability failure preserves every buffer, field and statistic. -/
theorem workspace_size_error (state : State)
    (hphase : state.phase = .workspace)
    (hsize : USize.size ≤ state.columns*(state.field.width.bytes+4)) :
    let out := next state
    out.phase = .done ∧ out.result = some (.error .dimensions) ∧ out.stats = state.stats ∧
      out.dense = state.dense ∧ out.slots = state.slots ∧
      out.workspaceFrame = state.workspaceFrame := by
  rw [next_workspace_size state hphase hsize]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Hex.Groebner.MatrixState.workspace_work_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms workspace_work_error
/-- info: 'Hex.Groebner.MatrixState.workspace_bytes_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms workspace_bytes_error
/-- info: 'Hex.Groebner.MatrixState.workspace_size_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms workspace_size_error

/-- info: 'Hex.Groebner.MatrixState.workspace_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms workspace_ok

/-- A successful validator advances one cursor and preserves its exact charges.
This is an equation for the Lean phase model. -/
theorem validate_ok (state : State) (stats : MatrixStats)
    (hphase : state.phase = .validate)
    (hcursor : state.validation < state.reducers.size + state.targets.size)
    (hvalidate :
      (Matrix.validate state.field state.limits state.columns state.validation
        (if state.validation < state.reducers.size then state.reducers[state.validation]!
          else state.targets[state.validation-state.reducers.size]!)).run state.stats =
        (.ok (), stats)) :
    let out := next state
    out.validation = state.validation + 1 ∧ out.phase = .validate ∧ out.stats = stats ∧
      out.contents = state.contents ∧ out.result = state.result := by
  rw [next_validate state stats (.ok ()) hphase hcursor hvalidate]
  exact ⟨rfl, hphase, rfl, rfl, rfl⟩

/-- A failed validator retains its exact error and charged prefix in a terminal state.
This is an equation for the Lean phase model. -/
theorem validate_error (state : State) (stats : MatrixStats) (error : MatrixError)
    (hphase : state.phase = .validate)
    (hcursor : state.validation < state.reducers.size + state.targets.size)
    (hvalidate :
      (Matrix.validate state.field state.limits state.columns state.validation
        (if state.validation < state.reducers.size then state.reducers[state.validation]!
          else state.targets[state.validation-state.reducers.size]!)).run state.stats =
        (.error error, stats)) :
    let out := next state
    out.phase = .done ∧ out.result = some (.error error) ∧ out.stats = stats ∧
      out.validation = state.validation ∧
      out.contents = state.contents := by
  rw [next_validate state stats (.error error) hphase hcursor hvalidate]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Advancing by zero phases preserves the complete continuation. -/
@[simp] theorem advance_zero (state : State) : advance state 0 = state := by
  rw [advance_spec]
  simp [advancePortable, advanceWith, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]

/-- Taking a phase of a terminal continuation preserves its complete state. -/
theorem next_done (state : State) (h : state.phase = .done) : next state = state := by
  simp only [next, advancePhase, h]
  rfl

/-- A terminal continuation is immutable under every subsequent advance. -/
theorem advance_done (state : State) (steps : Nat) (h : state.phase = .done) :
    advance state steps = state := by
  rw [advance_spec]
  simp only [advancePortable, advanceWith, Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  generalize hx : List.range' _ _ _ = xs
  cases xs <;> simp [h] <;> rfl

/-- Completing an already terminal continuation preserves its result and charges. -/
theorem finish_done (quantum : Nat) (state : State) (native : Bool)
    (h : state.phase = .done) :
    finishWith quantum state native =
      (state.result.getD (.error .rowUpdate), state.stats) := by
  simp only [finishWith,finishState,State.allowance,Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  generalize hx : List.range' _ _ _ = xs
  cases xs <;> simp [h,show (Phase.done == Phase.done) = true from rfl,
    Pure.pure,Bind.bind]



end Hex.Groebner.MatrixState
