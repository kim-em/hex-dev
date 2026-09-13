/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexModularMatrix.Fixtures
import Hex.BenchOracle.Flint
import LeanBench

/-!
Fixed determinant comparisons for the structured, dense random and unimodular
families. Matrix construction and FLINT request encoding precede the timed
closures. These are comparator anchors for the bounded modular route; the
Dixon/divisor performance goal belongs to its later implementation.
-/

namespace Hex.ModularMatrixBench

/-- Select a deterministic family, dimension and entry width. -/
def input (family : String) (n bits : Nat) : Matrix Int n n :=
  if family = "structured" then ModularMatrixFixtures.structured n
  else if family = "dense" then ModularMatrixFixtures.dense n bits
  else ModularMatrixFixtures.unimodular n bits

/-- The production modular route, failing the measurement if it falls back. -/
def runModularAt (family : String) (n bits : Nat) : Unit → IO Int :=
  let A := input family n bits
  fun _ => do
    let result := ModularMatrix.detWith A (ModularMatrix.defaultFuel A)
    if result.rest.isEmpty then return result.value
    throw <| IO.userError "unexpected Bareiss fallback in modular benchmark"

/-- The direct Bareiss comparator on the identical input. -/
def runBareissAt (family : String) (n bits : Nat) : Unit → IO Int :=
  let A := input family n bits
  fun _ => return A.bareiss

/-- FLINT request data prepared outside the timed closure. -/
def rowsJson (A : Matrix Int n n) : Lean.Json :=
  Lean.Json.arr (A.rows.toArray.map fun r =>
    Hex.BenchOracle.Flint.intsToJson r.toList)

/-- FLINT's integer determinant through the shared persistent oracle process. -/
def runFlintAt (family : String) (n bits : Nat) : Unit → IO Int :=
  let rows := rowsJson (input family n bits)
  fun _ => do
    let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "det" #[("rows", rows)]
    match result.getInt? with
    | .ok d => return d
    | .error message => throw <| IO.userError message

/-- Calibrate framing and dispatch without matrix work. -/
def runFlintOverhead (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "overhead" #[]
  match result.getInt? with
  | .ok d => return d
  | .error message => throw <| IO.userError message

/-- Scientific comparator settings; these anchors are collected manually. -/
def compareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, minTotalSeconds := 0.2, warmupFirstIter := true,
    maxSecondsPerCall := 10.0, tags := #["scheduled"] }

setup_fixed_benchmark runFlintOverhead where compareConfig

-- Small independent hash anchors keep CI's verification cost bounded.
def smokeStructured := runModularAt "structured" 4 8
def smokeDense := runModularAt "dense" 4 64
def smokeUnimodular := runModularAt "unimodular" 4 64
setup_fixed_benchmark smokeStructured where { expectedHash := some 0xda }
setup_fixed_benchmark smokeDense where { expectedHash := some 0xe9be599fac7e5bc0 }
setup_fixed_benchmark smokeUnimodular where { expectedHash := some 0x2 }

def runModularStructuredN16B8 := runModularAt "structured" 16 8
setup_fixed_benchmark runModularStructuredN16B8 where compareConfig
def runBareissStructuredN16B8 := runBareissAt "structured" 16 8
setup_fixed_benchmark runBareissStructuredN16B8 where compareConfig
def runFlintStructuredN16B8 := runFlintAt "structured" 16 8
setup_fixed_benchmark runFlintStructuredN16B8 where compareConfig
def runModularStructuredN24B8 := runModularAt "structured" 24 8
setup_fixed_benchmark runModularStructuredN24B8 where compareConfig
def runBareissStructuredN24B8 := runBareissAt "structured" 24 8
setup_fixed_benchmark runBareissStructuredN24B8 where compareConfig
def runFlintStructuredN24B8 := runFlintAt "structured" 24 8
setup_fixed_benchmark runFlintStructuredN24B8 where compareConfig
def runModularStructuredN32B8 := runModularAt "structured" 32 8
setup_fixed_benchmark runModularStructuredN32B8 where compareConfig
def runBareissStructuredN32B8 := runBareissAt "structured" 32 8
setup_fixed_benchmark runBareissStructuredN32B8 where compareConfig
def runFlintStructuredN32B8 := runFlintAt "structured" 32 8
setup_fixed_benchmark runFlintStructuredN32B8 where compareConfig
def runModularStructuredN48B8 := runModularAt "structured" 48 8
setup_fixed_benchmark runModularStructuredN48B8 where compareConfig
def runBareissStructuredN48B8 := runBareissAt "structured" 48 8
setup_fixed_benchmark runBareissStructuredN48B8 where compareConfig
def runFlintStructuredN48B8 := runFlintAt "structured" 48 8
setup_fixed_benchmark runFlintStructuredN48B8 where compareConfig
def runModularStructuredN64B8 := runModularAt "structured" 64 8
setup_fixed_benchmark runModularStructuredN64B8 where compareConfig
def runBareissStructuredN64B8 := runBareissAt "structured" 64 8
setup_fixed_benchmark runBareissStructuredN64B8 where compareConfig
def runFlintStructuredN64B8 := runFlintAt "structured" 64 8
setup_fixed_benchmark runFlintStructuredN64B8 where compareConfig
def runModularStructuredN96B8 := runModularAt "structured" 96 8
setup_fixed_benchmark runModularStructuredN96B8 where compareConfig
def runBareissStructuredN96B8 := runBareissAt "structured" 96 8
setup_fixed_benchmark runBareissStructuredN96B8 where compareConfig
def runFlintStructuredN96B8 := runFlintAt "structured" 96 8
setup_fixed_benchmark runFlintStructuredN96B8 where compareConfig
def runModularStructuredN128B8 := runModularAt "structured" 128 8
setup_fixed_benchmark runModularStructuredN128B8 where compareConfig
def runBareissStructuredN128B8 := runBareissAt "structured" 128 8
setup_fixed_benchmark runBareissStructuredN128B8 where compareConfig
def runFlintStructuredN128B8 := runFlintAt "structured" 128 8
setup_fixed_benchmark runFlintStructuredN128B8 where compareConfig
def runModularStructuredN192B8 := runModularAt "structured" 192 8
setup_fixed_benchmark runModularStructuredN192B8 where compareConfig
def runBareissStructuredN192B8 := runBareissAt "structured" 192 8
setup_fixed_benchmark runBareissStructuredN192B8 where compareConfig
def runFlintStructuredN192B8 := runFlintAt "structured" 192 8
setup_fixed_benchmark runFlintStructuredN192B8 where compareConfig
def runModularStructuredN256B8 := runModularAt "structured" 256 8
setup_fixed_benchmark runModularStructuredN256B8 where compareConfig
def runBareissStructuredN256B8 := runBareissAt "structured" 256 8
setup_fixed_benchmark runBareissStructuredN256B8 where compareConfig
def runFlintStructuredN256B8 := runFlintAt "structured" 256 8
setup_fixed_benchmark runFlintStructuredN256B8 where compareConfig
def runModularStructuredN320B8 := runModularAt "structured" 320 8
setup_fixed_benchmark runModularStructuredN320B8 where compareConfig
def runBareissStructuredN320B8 := runBareissAt "structured" 320 8
setup_fixed_benchmark runBareissStructuredN320B8 where compareConfig
def runFlintStructuredN320B8 := runFlintAt "structured" 320 8
setup_fixed_benchmark runFlintStructuredN320B8 where compareConfig
def runModularStructuredN384B8 := runModularAt "structured" 384 8
setup_fixed_benchmark runModularStructuredN384B8 where compareConfig
def runBareissStructuredN384B8 := runBareissAt "structured" 384 8
setup_fixed_benchmark runBareissStructuredN384B8 where compareConfig
def runFlintStructuredN384B8 := runFlintAt "structured" 384 8
setup_fixed_benchmark runFlintStructuredN384B8 where compareConfig
def runModularStructuredN512B8 := runModularAt "structured" 512 8
setup_fixed_benchmark runModularStructuredN512B8 where compareConfig
def runBareissStructuredN512B8 := runBareissAt "structured" 512 8
setup_fixed_benchmark runBareissStructuredN512B8 where compareConfig
def runFlintStructuredN512B8 := runFlintAt "structured" 512 8
setup_fixed_benchmark runFlintStructuredN512B8 where compareConfig
def runModularDenseN32B8 := runModularAt "dense" 32 8
setup_fixed_benchmark runModularDenseN32B8 where compareConfig
def runBareissDenseN32B8 := runBareissAt "dense" 32 8
setup_fixed_benchmark runBareissDenseN32B8 where compareConfig
def runFlintDenseN32B8 := runFlintAt "dense" 32 8
setup_fixed_benchmark runFlintDenseN32B8 where compareConfig
def runModularDenseN64B8 := runModularAt "dense" 64 8
setup_fixed_benchmark runModularDenseN64B8 where compareConfig
def runBareissDenseN64B8 := runBareissAt "dense" 64 8
setup_fixed_benchmark runBareissDenseN64B8 where compareConfig
def runFlintDenseN64B8 := runFlintAt "dense" 64 8
setup_fixed_benchmark runFlintDenseN64B8 where compareConfig
def runModularDenseN96B8 := runModularAt "dense" 96 8
setup_fixed_benchmark runModularDenseN96B8 where compareConfig
def runBareissDenseN96B8 := runBareissAt "dense" 96 8
setup_fixed_benchmark runBareissDenseN96B8 where compareConfig
def runFlintDenseN96B8 := runFlintAt "dense" 96 8
setup_fixed_benchmark runFlintDenseN96B8 where compareConfig
def runModularDenseN128B8 := runModularAt "dense" 128 8
setup_fixed_benchmark runModularDenseN128B8 where compareConfig
def runBareissDenseN128B8 := runBareissAt "dense" 128 8
setup_fixed_benchmark runBareissDenseN128B8 where compareConfig
def runFlintDenseN128B8 := runFlintAt "dense" 128 8
setup_fixed_benchmark runFlintDenseN128B8 where compareConfig
def runModularDenseN192B8 := runModularAt "dense" 192 8
setup_fixed_benchmark runModularDenseN192B8 where compareConfig
def runBareissDenseN192B8 := runBareissAt "dense" 192 8
setup_fixed_benchmark runBareissDenseN192B8 where compareConfig
def runFlintDenseN192B8 := runFlintAt "dense" 192 8
setup_fixed_benchmark runFlintDenseN192B8 where compareConfig
def runModularDenseN256B8 := runModularAt "dense" 256 8
setup_fixed_benchmark runModularDenseN256B8 where compareConfig
def runBareissDenseN256B8 := runBareissAt "dense" 256 8
setup_fixed_benchmark runBareissDenseN256B8 where compareConfig
def runFlintDenseN256B8 := runFlintAt "dense" 256 8
setup_fixed_benchmark runFlintDenseN256B8 where compareConfig
def runModularDenseN32B64 := runModularAt "dense" 32 64
setup_fixed_benchmark runModularDenseN32B64 where compareConfig
def runBareissDenseN32B64 := runBareissAt "dense" 32 64
setup_fixed_benchmark runBareissDenseN32B64 where compareConfig
def runFlintDenseN32B64 := runFlintAt "dense" 32 64
setup_fixed_benchmark runFlintDenseN32B64 where compareConfig
def runModularDenseN64B64 := runModularAt "dense" 64 64
setup_fixed_benchmark runModularDenseN64B64 where compareConfig
def runBareissDenseN64B64 := runBareissAt "dense" 64 64
setup_fixed_benchmark runBareissDenseN64B64 where compareConfig
def runFlintDenseN64B64 := runFlintAt "dense" 64 64
setup_fixed_benchmark runFlintDenseN64B64 where compareConfig
def runModularDenseN96B64 := runModularAt "dense" 96 64
setup_fixed_benchmark runModularDenseN96B64 where compareConfig
def runBareissDenseN96B64 := runBareissAt "dense" 96 64
setup_fixed_benchmark runBareissDenseN96B64 where compareConfig
def runFlintDenseN96B64 := runFlintAt "dense" 96 64
setup_fixed_benchmark runFlintDenseN96B64 where compareConfig
def runModularDenseN128B64 := runModularAt "dense" 128 64
setup_fixed_benchmark runModularDenseN128B64 where compareConfig
def runBareissDenseN128B64 := runBareissAt "dense" 128 64
setup_fixed_benchmark runBareissDenseN128B64 where compareConfig
def runFlintDenseN128B64 := runFlintAt "dense" 128 64
setup_fixed_benchmark runFlintDenseN128B64 where compareConfig
def runModularDenseN192B64 := runModularAt "dense" 192 64
setup_fixed_benchmark runModularDenseN192B64 where compareConfig
def runBareissDenseN192B64 := runBareissAt "dense" 192 64
setup_fixed_benchmark runBareissDenseN192B64 where compareConfig
def runFlintDenseN192B64 := runFlintAt "dense" 192 64
setup_fixed_benchmark runFlintDenseN192B64 where compareConfig
def runModularDenseN256B64 := runModularAt "dense" 256 64
setup_fixed_benchmark runModularDenseN256B64 where compareConfig
def runBareissDenseN256B64 := runBareissAt "dense" 256 64
setup_fixed_benchmark runBareissDenseN256B64 where compareConfig
def runFlintDenseN256B64 := runFlintAt "dense" 256 64
setup_fixed_benchmark runFlintDenseN256B64 where compareConfig
def runModularDenseN32B1024 := runModularAt "dense" 32 1024
setup_fixed_benchmark runModularDenseN32B1024 where compareConfig
def runBareissDenseN32B1024 := runBareissAt "dense" 32 1024
setup_fixed_benchmark runBareissDenseN32B1024 where compareConfig
def runFlintDenseN32B1024 := runFlintAt "dense" 32 1024
setup_fixed_benchmark runFlintDenseN32B1024 where compareConfig
def runModularDenseN64B1024 := runModularAt "dense" 64 1024
setup_fixed_benchmark runModularDenseN64B1024 where compareConfig
def runBareissDenseN64B1024 := runBareissAt "dense" 64 1024
setup_fixed_benchmark runBareissDenseN64B1024 where compareConfig
def runFlintDenseN64B1024 := runFlintAt "dense" 64 1024
setup_fixed_benchmark runFlintDenseN64B1024 where compareConfig
def runModularDenseN96B1024 := runModularAt "dense" 96 1024
setup_fixed_benchmark runModularDenseN96B1024 where compareConfig
def runBareissDenseN96B1024 := runBareissAt "dense" 96 1024
setup_fixed_benchmark runBareissDenseN96B1024 where compareConfig
def runFlintDenseN96B1024 := runFlintAt "dense" 96 1024
setup_fixed_benchmark runFlintDenseN96B1024 where compareConfig
def runModularDenseN128B1024 := runModularAt "dense" 128 1024
setup_fixed_benchmark runModularDenseN128B1024 where compareConfig
def runBareissDenseN128B1024 := runBareissAt "dense" 128 1024
setup_fixed_benchmark runBareissDenseN128B1024 where compareConfig
def runFlintDenseN128B1024 := runFlintAt "dense" 128 1024
setup_fixed_benchmark runFlintDenseN128B1024 where compareConfig
def runModularDenseN192B1024 := runModularAt "dense" 192 1024
setup_fixed_benchmark runModularDenseN192B1024 where compareConfig
def runBareissDenseN192B1024 := runBareissAt "dense" 192 1024
setup_fixed_benchmark runBareissDenseN192B1024 where compareConfig
def runFlintDenseN192B1024 := runFlintAt "dense" 192 1024
setup_fixed_benchmark runFlintDenseN192B1024 where compareConfig
def runModularDenseN256B1024 := runModularAt "dense" 256 1024
setup_fixed_benchmark runModularDenseN256B1024 where compareConfig
def runBareissDenseN256B1024 := runBareissAt "dense" 256 1024
setup_fixed_benchmark runBareissDenseN256B1024 where compareConfig
def runFlintDenseN256B1024 := runFlintAt "dense" 256 1024
setup_fixed_benchmark runFlintDenseN256B1024 where compareConfig
def runModularUnimodularN32B64 := runModularAt "unimodular" 32 64
setup_fixed_benchmark runModularUnimodularN32B64 where compareConfig
def runBareissUnimodularN32B64 := runBareissAt "unimodular" 32 64
setup_fixed_benchmark runBareissUnimodularN32B64 where compareConfig
def runFlintUnimodularN32B64 := runFlintAt "unimodular" 32 64
setup_fixed_benchmark runFlintUnimodularN32B64 where compareConfig
def runModularUnimodularN64B64 := runModularAt "unimodular" 64 64
setup_fixed_benchmark runModularUnimodularN64B64 where compareConfig
def runBareissUnimodularN64B64 := runBareissAt "unimodular" 64 64
setup_fixed_benchmark runBareissUnimodularN64B64 where compareConfig
def runFlintUnimodularN64B64 := runFlintAt "unimodular" 64 64
setup_fixed_benchmark runFlintUnimodularN64B64 where compareConfig
def runModularUnimodularN96B64 := runModularAt "unimodular" 96 64
setup_fixed_benchmark runModularUnimodularN96B64 where compareConfig
def runBareissUnimodularN96B64 := runBareissAt "unimodular" 96 64
setup_fixed_benchmark runBareissUnimodularN96B64 where compareConfig
def runFlintUnimodularN96B64 := runFlintAt "unimodular" 96 64
setup_fixed_benchmark runFlintUnimodularN96B64 where compareConfig
def runModularUnimodularN128B64 := runModularAt "unimodular" 128 64
setup_fixed_benchmark runModularUnimodularN128B64 where compareConfig
def runBareissUnimodularN128B64 := runBareissAt "unimodular" 128 64
setup_fixed_benchmark runBareissUnimodularN128B64 where compareConfig
def runFlintUnimodularN128B64 := runFlintAt "unimodular" 128 64
setup_fixed_benchmark runFlintUnimodularN128B64 where compareConfig
def runModularUnimodularN192B64 := runModularAt "unimodular" 192 64
setup_fixed_benchmark runModularUnimodularN192B64 where compareConfig
def runBareissUnimodularN192B64 := runBareissAt "unimodular" 192 64
setup_fixed_benchmark runBareissUnimodularN192B64 where compareConfig
def runFlintUnimodularN192B64 := runFlintAt "unimodular" 192 64
setup_fixed_benchmark runFlintUnimodularN192B64 where compareConfig
def runModularUnimodularN256B64 := runModularAt "unimodular" 256 64
setup_fixed_benchmark runModularUnimodularN256B64 where compareConfig
def runBareissUnimodularN256B64 := runBareissAt "unimodular" 256 64
setup_fixed_benchmark runBareissUnimodularN256B64 where compareConfig
def runFlintUnimodularN256B64 := runFlintAt "unimodular" 256 64
setup_fixed_benchmark runFlintUnimodularN256B64 where compareConfig

/-- Run the small hash anchors in CI; the full comparator ladder is scheduled. -/
def verifySmoke : IO UInt32 := do
  let reports ← LeanBench.verify [`Hex.ModularMatrixBench.smokeStructured,
    `Hex.ModularMatrixBench.smokeDense, `Hex.ModularMatrixBench.smokeUnimodular]
  IO.println (LeanBench.Format.fmtCombinedVerify reports)
  return if reports.passed then 0 else 1

end Hex.ModularMatrixBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["verify"] => Hex.ModularMatrixBench.verifySmoke
  | _ => LeanBench.Cli.dispatch args
