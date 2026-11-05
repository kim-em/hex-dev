/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGroebner.Elimination
import HexGroebnerEliminationNative
import LeanBench

namespace Hex.Groebner.Bench

private def sparseField : PrimeField :=
  ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

structure SparseInput where
  columns : Nat
  reducers : Array SparseRow
  targets : Array SparseRow
  expected : Array SparseRow
  deriving Hashable

/-- Distinct known heads share a dense tail. Eight identical targets use every
known pivot; the first installs a new remainder pivot and seven reduce to zero.
The final column is outside the common tail. All polynomial coefficients are F₂. -/
def prepareSparseAt (columns n : Nat) : SparseInput := Id.run do
  let half := n/2
  let tail := (Array.range half).map fun i => (columns-half-1+i,(1:UInt64))
  let reducers := (Array.range half).map fun i =>
    (SparseRow.ofEntries sparseField columns (#[(i,(1:UInt64))] ++ tail)).getD {}
  let target := (SparseRow.ofEntries sparseField columns
    (((Array.range half).map (·,(1:UInt64))) ++ #[(columns-1,1)])).getD {}
  let remainder := (SparseRow.ofEntries sparseField columns
    ((if half%2 == 0 then #[] else tail) ++ #[(columns-1,1)])).getD {}
  return ⟨columns,reducers,Array.replicate 8 target,reducers.push remainder⟩

/-- The fixed width crosses the packed backend's dimension ceiling. Preparation
and expected rows are outside timing; native admission, initialization, updates,
complete output comparison/decoding and all eight counters remain inside. -/
def prepareSparseBinary (n : Nat) : SparseInput := prepareSparseAt 131073 n

private def sparseResult (input : SparseInput) (native : Bool) :
    Bool × Array (Bool × Array (Nat × UInt64) × Nat) × Array Nat := Id.run do
  let limits : MatrixLimits := { work := 1000000000,binaryPivots := true }
  let result := if native then
      Elimination.attempt sparseField limits input.columns input.reducers input.targets #[] false
    else Elimination.attemptSparsePortable sparseField limits input.columns input.reducers input.targets #[] false
  let some result := result | return (false,#[],#[])
  let .ok (e,r) := result.result | return (false,#[],#[])
  let s := result.stats
  let mut valid := e.reducerRank == input.reducers.size && e.rows.size == input.expected.size &&
    e.trace.isEmpty && r.isEmpty && s.processedRows == input.reducers.size+8 &&
    s.reductions == 8*input.reducers.size+7 && s.zeroRows == 7
  for (row,i) in e.rows.zipIdx do
    let expected := input.expected[i]!
    valid := valid && row.row.columns == expected.columns &&
      row.row.coefficients == expected.coefficients && row.sugar == 0 &&
      row.multiplier == 1 && row.derivation.isNone &&
      row.fromTarget == (i == input.reducers.size)
  return (valid,e.rows.map (fun row => (row.fromTarget,row.row.entries sparseField,row.sugar)),
    #[s.work,s.inputEntries,s.outputEntries,s.packedBytes,s.traceNodes,
      s.processedRows,s.reductions,s.zeroRows])

private def checkedSparse (input : SparseInput) (native : Bool) :
    IO (Bool × Array (Bool × Array (Nat × UInt64) × Nat) × Array Nat) := do
  let result := sparseResult input native
  unless result.1 do throw (IO.userError "sparse matrix benchmark declined or returned invalid output")
  return result

def sparseBinary (input : SparseInput) := checkedSparse input true
def sparseBinaryReference (input : SparseInput) := checkedSparse input false

#guard (#[2,4,8,16].all fun n =>
  let input := prepareSparseAt (4*n+7) n
  (sparseResult input true).1 && sparseResult input true == sparseResult input false)

#guard Elimination.selectSparse sparseField { binaryPivots := true } 131073
  (prepareSparseBinary 2).reducers (prepareSparseBinary 2).targets

initialize do
  let input := prepareSparseBinary 2
  let native ← sparseBinary input
  let reference ← sparseBinaryReference input
  unless native == reference do
    throw (IO.userError "wide sparse matrix benchmark initialization differs")
  for native in [false,true] do
    let rejected ← try
      let _ ← checkedSparse { input with columns := 0 } native
      pure false
    catch _ => pure true
    unless rejected do throw (IO.userError "sparse matrix benchmark accepted invalid dimensions")

-- Fixed workspace width C=131073 plus O(n²) input, updates and output handling.
setup_benchmark sparseBinary n => 131073+n*n
  with prep := prepareSparseBinary
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64,128,256,512,1024,2048]
    targetInnerNanos := 1000000000
    maxSecondsPerCall := 32.0
  }

-- Same O(C+n²) workspace, sparse updates and output handling as sparseBinary.
setup_benchmark sparseBinaryReference n => 131073+n*n
  with prep := prepareSparseBinary
  where {
    paramFloor := 64
    paramCeiling := 256
    paramSchedule := .custom #[64,128,256]
    targetInnerNanos := 1000000000
    maxSecondsPerCall := 32.0
  }

end Hex.Groebner.Bench
