/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Bench.Cauchy
import HexGroebnerEliminationNative
import LeanBench

namespace Hex.Groebner.Bench

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

private def bytePrime : PrimeField :=
  ⟨251,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
private def shortPrime : PrimeField :=
  ⟨32003,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
private def wordPrime : PrimeField :=
  ⟨2147483647,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

/-- Distinct monic known heads followed by dense tails and eight shared targets.
Every target uses every known reducer; no reducer cancels another known head. -/
def prepareBulk (field : PrimeField) (n : Nat) : Input := Id.run do
  let half := n/2
  let tail := (Array.range (n-half)).map fun j => (half+j,(1:UInt64))
  let reducers := (Array.range half).map fun i =>
    (SparseRow.ofEntries field n (#[(i,(1:UInt64))] ++ tail)).getD {}
  let target := (SparseRow.ofEntries field n
    ((Array.range n).map (·,(1:UInt64)))).getD {}
  return ⟨n,reducers,Array.replicate 8 target⟩

/-- Validation, installation, elimination and every output entry/counter are timed. -/
def bulkOver (field : PrimeField) (input : Input) (native : Bool := true) :
    Bool × Array (Array (Nat × UInt64) × Bool × UInt64 × Nat) × Array Nat :=
  let limits : MatrixLimits := { work := 1000000000 }
  let result := if native then
      Elimination.run field limits input.columns input.reducers input.targets false #[] true false
    else Elimination.reference field limits input.columns input.reducers input.targets #[] false
  match result.result with
  | .error _ => (false,#[],#[])
  | .ok (e,r) =>
    (e.reducerRank == input.reducers.size && e.rows.size == input.reducers.size+1 &&
      e.trace.isEmpty && r.isEmpty,
      e.rows.map fun row => (row.row.entries field,row.fromTarget,row.multiplier,row.sugar),
      let s := result.stats
      #[s.work,s.inputEntries,s.outputEntries,s.packedBytes,s.traceNodes,
        s.processedRows,s.reductions,s.zeroRows])

def prepareBulkByte (n : Nat) := prepareBulk bytePrime n
def prepareBulkShort (n : Nat) := prepareBulk shortPrime n
def prepareBulkWord (n : Nat) := prepareBulk wordPrime n

def bulkByte (input : Input) := bulkOver bytePrime input
def bulkShort (input : Input) := bulkOver shortPrime input
def bulkWord (input : Input) := bulkOver wordPrime input

#guard ([bytePrime,shortPrime,wordPrime].all fun field =>
  #[128,256,512].all fun n =>
    let input := prepareBulk field n
    let actual := bulkOver field input
    Elimination.fits field { work := 1000000000 } n input.reducers input.targets #[] &&
      actual.1 && actual == bulkOver field input false)

-- There are n/2 known rows with n/2+1 entries, and eight targets. Sparse
-- updates, input validation, installation and complete output hashing are O(n²).
setup_benchmark bulkByte n => n*n
  with prep := prepareBulkByte
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128,256,512]
    targetInnerNanos := 4000000000
  }

-- Each of eight targets visits n/2 tails of length n/2+1; two-byte
-- coefficients preserve O(n²) updates, validation and complete output hashing.
setup_benchmark bulkShort n => n*n
  with prep := prepareBulkShort
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128,256,512]
    targetInnerNanos := 4000000000
  }

-- Four-byte coefficients likewise require eight*(n/2)*(n/2+1) sparse updates,
-- plus O(n²) input validation, installation and complete output hashing.
setup_benchmark bulkWord n => n*n
  with prep := prepareBulkWord
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128,256,512]
    targetInnerNanos := 4000000000
  }

end Hex.Groebner.Bench
