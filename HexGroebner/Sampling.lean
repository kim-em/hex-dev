/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Matrix
public import HexGroebner.NativeScan
public import HexGroebner.NativeGather
public import HexBasic.Rand

public section

namespace Hex.Groebner.Sampling

/-- Full-field random combinations in consecutive target blocks. Stopping
counts total zero reductions within a block, without resetting after a pivot.
This is an unchecked row-space candidate, with no pseudorandom error bound. -/
structure Config where
  blockRows : Nat := 32
  zeroTests : Nat := 3
  deriving BEq, Inhabited

/-- Matrix work plus explicit random-word and combination counters. Failed
attempts retain consumed words, including rejected full-field draws. -/
structure Statistics where
  matrix : MatrixStats := {}
  randomWords : Nat := 0
  combinations : Nat := 0
  combinationEntries : Nat := 0
  completedBlocks : Nat := 0
  deriving BEq, Repr, Inhabited

inductive Phase where
  | check | validate | workspace | install | block | draw | combine | scan | inverse | gather | done
  deriving BEq, Inhabited

/-- Owned resumable sampling state. Field, input, configuration and native mode
are fixed by `start`; only absolute cumulative allowances may change on resume.
Known reducers must be monic with distinct leading columns. Targets are sampled
with full-field coefficients using `Hex.Rand.nat` rejection draws. A completed
state does not assert preservation of rank or the Gröbner property. The row
allowance counts supplied reducers, original targets and generated combinations. -/
structure State where
  private mk ::
  field : PrimeField
  columns : Nat
  reducers : Array SparseRow
  targets : Array SparseRow
  sugars : Array Nat
  config : Config
  native : Bool
  random : Hex.Rand
  statistics : Statistics := {}
  phase : Phase := .check
  validation : Nat := 0
  installed : Nat := 0
  slots : ByteArray := {}
  pivots : Array Native.Scan.Pivot := #[]
  rows : Array Pivot := #[]
  dense : ByteArray := {}
  start : Nat := 0
  stop : Nat := 0
  zeros : Nat := 0
  trials : Nat := 0
  row : Nat := 0
  offset : Nat := 0
  multiplier : UInt64 := 0
  sugar : Nat := 0
  scan : Native.Scan.State := { dense := {},column := 0,last := 0,chargedUntil := 0 }
  gather : Native.Gather.State := ⟨{},{},{},0⟩
  inverse : UInt64 := 1
  failure : Option MatrixError := none

/-- Begin an unchecked matrix computation. Even an exhausted computation exposes
its advanced random state and pending multiplier through its sealed state. -/
def start (field : PrimeField) (columns : Nat) (reducers targets : Array SparseRow)
    (random : Hex.Rand) (config : Config := {}) (sugars : Array Nat := #[])
    (native := true) : State :=
  { field,columns,reducers,targets,random,config,sugars,native }

end Hex.Groebner.Sampling
