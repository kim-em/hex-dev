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
Dixon inverse, lifting and repeated-solve arms report their costs separately.
-/

namespace Hex.ModularMatrixBench

/-- Select a deterministic family, dimension and entry width. -/
def input (family : String) (n bits : Nat) : Matrix Int n n :=
  if family = "structured" then ModularMatrixFixtures.structured n
  else if family = "dense" then ModularMatrixFixtures.dense n bits
  else ModularMatrixFixtures.unimodular n bits

/-- The production modular route, failing the measurement if it falls back. -/
def runModular (A : Matrix Int n n) (_ : Unit) : IO Int := do
  let result := ModularMatrix.detWith A (ModularMatrix.defaultFuel A)
  if result.rest.isEmpty then return result.value
  throw <| IO.userError "unexpected Bareiss fallback in modular benchmark"

def runBareiss (A : Matrix Int n n) (_ : Unit) : IO Int := return A.bareiss

/-- FLINT request data prepared outside the timed closure. -/
def rowsJson (A : Matrix Int n m) : Lean.Json :=
  Lean.Json.arr (A.rows.toArray.map fun r =>
    Hex.BenchOracle.Flint.intsToJson r.toList)

def runFlint (rows : Lean.Json) (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "det" #[("rows", rows)]
  match result.getInt? with
  | .ok d => return d
  | .error message => throw <| IO.userError message

/-- Seeded divisor route; fallback is a benchmark failure. -/
def runDivisor (A : Matrix Int n n) (_ : Unit) : IO Int := do
  let result := ModularMatrix.detWith A (ModularMatrix.defaultFuel A) 10220 true
  if result.rest.isEmpty then return result.value
  throw <| IO.userError "unexpected fallback in divisor benchmark"

def runModularAt (family : String) (n bits : Nat) := runModular (input family n bits)
def runDivisorAt (family : String) (n bits : Nat) := runDivisor (input family n bits)

def solveInput (n : Nat) : Matrix Int n n := ModularMatrixFixtures.dense n 8 10220

def rhsInput (A : Matrix Int n n) (integral : Bool) (r : Nat) : Matrix Int n r :=
  let C := Matrix.ofFn fun i j => ((i.val + 3 * j.val) % 17 : Int) - 8
  if integral then A * C else C

def checksum (X : Matrix Int n m) (d : Int) : Int :=
  (Matrix.Dixon.flatten X).foldl (· + ·) d

def runDecomp (A : Matrix Int n n) (_ : Unit) : IO Int := do
  match A.decomp? A.solveFuel with
  | none => throw <| IO.userError "decomposition failed"
  | some D => return D.detImage

/-- Prepared as a closed value: Lean's arity expansion must not move the inverse
into the timed `Unit → IO Int` function. The discarded warmup forces this value. -/
structure SolveCase (n : Nat) where
  decomp : Option (Matrix.Decomp n)
  rhs : Vector Int n

def prepareSolve (n : Nat) (integral : Bool) : SolveCase n :=
  let A := solveInput n
  ⟨A.decomp? A.solveFuel, (rhsInput A integral 1).col 0⟩

def runSolve (data : SolveCase n) (_ : Unit) : IO Int := do
  match data.decomp with
  | none => throw <| IO.userError "decomposition failed"
  | some D =>
    match Matrix.solveWith D data.rhs with
    | none => throw <| IO.userError "solveWith failed"
    | some (y, d) => return y.foldl (· + ·) d

def runSolveAt (n : Nat) (integral : Bool) := runSolve (prepareSolve n integral)

/-- The timed work includes one decomposition and one simultaneous solve, or
one decomposition per independent right-hand side. -/
def runRepeated (A : Matrix Int n n) (C : Matrix Int n r) (reuse : Bool)
    (_ : Unit) : IO Int := do
  if reuse then
    match (A.decomp? A.solveFuel).bind (Matrix.solveMatWith · C) with
    | none => throw <| IO.userError "solveMatWith failed"
    | some (X, d) => return checksum X d
  else
    let mut ys : Array (Vector Int n × Int) := #[]
    let mut common : Nat := 1
    for j in List.finRange r do
      match A.solve? (C.col j) A.solveFuel with
      | none => throw <| IO.userError "independent solve failed"
      | some (y, d) =>
        ys := ys.push (y, d)
        common := Nat.lcm common d.natAbs
    return ys.foldl (fun acc (y, d) => acc +
      (common : Int) / d * y.foldl (· + ·) 0) common

def runRepeatedAt (n r : Nat) (reuse : Bool) :=
  let A := solveInput n
  runRepeated A (rhsInput A false r) reuse

/-- Informational FLINT fmpq_mat_solve comparator on the same integer system. -/
def runFlintSolve (rows rhs : Lean.Json) (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_mat" "dixon_solve"
    #[("rows", rows), ("rhs", rhs)]
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

-- Memoised fixture values are forced by warmup and shared by comparator arms.
private def dataStructuredN16B8 := Thunk.mk fun _ => input "structured" 16 8
private def dataStructuredN16B8Json := Thunk.mk fun _ => rowsJson dataStructuredN16B8.get
private def dataStructuredN24B8 := Thunk.mk fun _ => input "structured" 24 8
private def dataStructuredN24B8Json := Thunk.mk fun _ => rowsJson dataStructuredN24B8.get
private def dataStructuredN32B8 := Thunk.mk fun _ => input "structured" 32 8
private def dataStructuredN32B8Json := Thunk.mk fun _ => rowsJson dataStructuredN32B8.get
private def dataStructuredN48B8 := Thunk.mk fun _ => input "structured" 48 8
private def dataStructuredN48B8Json := Thunk.mk fun _ => rowsJson dataStructuredN48B8.get
private def dataStructuredN64B8 := Thunk.mk fun _ => input "structured" 64 8
private def dataStructuredN64B8Json := Thunk.mk fun _ => rowsJson dataStructuredN64B8.get
private def dataStructuredN96B8 := Thunk.mk fun _ => input "structured" 96 8
private def dataStructuredN96B8Json := Thunk.mk fun _ => rowsJson dataStructuredN96B8.get
private def dataStructuredN128B8 := Thunk.mk fun _ => input "structured" 128 8
private def dataStructuredN128B8Json := Thunk.mk fun _ => rowsJson dataStructuredN128B8.get
private def dataStructuredN192B8 := Thunk.mk fun _ => input "structured" 192 8
private def dataStructuredN192B8Json := Thunk.mk fun _ => rowsJson dataStructuredN192B8.get
private def dataStructuredN256B8 := Thunk.mk fun _ => input "structured" 256 8
private def dataStructuredN256B8Json := Thunk.mk fun _ => rowsJson dataStructuredN256B8.get
private def dataStructuredN320B8 := Thunk.mk fun _ => input "structured" 320 8
private def dataStructuredN320B8Json := Thunk.mk fun _ => rowsJson dataStructuredN320B8.get
private def dataStructuredN384B8 := Thunk.mk fun _ => input "structured" 384 8
private def dataStructuredN384B8Json := Thunk.mk fun _ => rowsJson dataStructuredN384B8.get
private def dataStructuredN512B8 := Thunk.mk fun _ => input "structured" 512 8
private def dataStructuredN512B8Json := Thunk.mk fun _ => rowsJson dataStructuredN512B8.get
private def dataDenseN32B8 := Thunk.mk fun _ => input "dense" 32 8
private def dataDenseN32B8Json := Thunk.mk fun _ => rowsJson dataDenseN32B8.get
private def dataDenseN64B8 := Thunk.mk fun _ => input "dense" 64 8
private def dataDenseN64B8Json := Thunk.mk fun _ => rowsJson dataDenseN64B8.get
private def dataDenseN96B8 := Thunk.mk fun _ => input "dense" 96 8
private def dataDenseN96B8Json := Thunk.mk fun _ => rowsJson dataDenseN96B8.get
private def dataDenseN128B8 := Thunk.mk fun _ => input "dense" 128 8
private def dataDenseN128B8Json := Thunk.mk fun _ => rowsJson dataDenseN128B8.get
private def dataDenseN192B8 := Thunk.mk fun _ => input "dense" 192 8
private def dataDenseN192B8Json := Thunk.mk fun _ => rowsJson dataDenseN192B8.get
private def dataDenseN256B8 := Thunk.mk fun _ => input "dense" 256 8
private def dataDenseN256B8Json := Thunk.mk fun _ => rowsJson dataDenseN256B8.get
private def dataDenseN32B64 := Thunk.mk fun _ => input "dense" 32 64
private def dataDenseN32B64Json := Thunk.mk fun _ => rowsJson dataDenseN32B64.get
private def dataDenseN64B64 := Thunk.mk fun _ => input "dense" 64 64
private def dataDenseN64B64Json := Thunk.mk fun _ => rowsJson dataDenseN64B64.get
private def dataDenseN96B64 := Thunk.mk fun _ => input "dense" 96 64
private def dataDenseN96B64Json := Thunk.mk fun _ => rowsJson dataDenseN96B64.get
private def dataDenseN128B64 := Thunk.mk fun _ => input "dense" 128 64
private def dataDenseN128B64Json := Thunk.mk fun _ => rowsJson dataDenseN128B64.get
private def dataDenseN192B64 := Thunk.mk fun _ => input "dense" 192 64
private def dataDenseN192B64Json := Thunk.mk fun _ => rowsJson dataDenseN192B64.get
private def dataDenseN256B64 := Thunk.mk fun _ => input "dense" 256 64
private def dataDenseN256B64Json := Thunk.mk fun _ => rowsJson dataDenseN256B64.get
private def dataDenseN32B1024 := Thunk.mk fun _ => input "dense" 32 1024
private def dataDenseN32B1024Json := Thunk.mk fun _ => rowsJson dataDenseN32B1024.get
private def dataDenseN64B1024 := Thunk.mk fun _ => input "dense" 64 1024
private def dataDenseN64B1024Json := Thunk.mk fun _ => rowsJson dataDenseN64B1024.get
private def dataDenseN96B1024 := Thunk.mk fun _ => input "dense" 96 1024
private def dataDenseN96B1024Json := Thunk.mk fun _ => rowsJson dataDenseN96B1024.get
private def dataDenseN128B1024 := Thunk.mk fun _ => input "dense" 128 1024
private def dataDenseN128B1024Json := Thunk.mk fun _ => rowsJson dataDenseN128B1024.get
private def dataDenseN192B1024 := Thunk.mk fun _ => input "dense" 192 1024
private def dataDenseN192B1024Json := Thunk.mk fun _ => rowsJson dataDenseN192B1024.get
private def dataDenseN256B1024 := Thunk.mk fun _ => input "dense" 256 1024
private def dataDenseN256B1024Json := Thunk.mk fun _ => rowsJson dataDenseN256B1024.get
private def dataUnimodularN32B64 := Thunk.mk fun _ => input "unimodular" 32 64
private def dataUnimodularN32B64Json := Thunk.mk fun _ => rowsJson dataUnimodularN32B64.get
private def dataUnimodularN64B64 := Thunk.mk fun _ => input "unimodular" 64 64
private def dataUnimodularN64B64Json := Thunk.mk fun _ => rowsJson dataUnimodularN64B64.get
private def dataUnimodularN96B64 := Thunk.mk fun _ => input "unimodular" 96 64
private def dataUnimodularN96B64Json := Thunk.mk fun _ => rowsJson dataUnimodularN96B64.get
private def dataUnimodularN128B64 := Thunk.mk fun _ => input "unimodular" 128 64
private def dataUnimodularN128B64Json := Thunk.mk fun _ => rowsJson dataUnimodularN128B64.get
private def dataUnimodularN192B64 := Thunk.mk fun _ => input "unimodular" 192 64
private def dataUnimodularN192B64Json := Thunk.mk fun _ => rowsJson dataUnimodularN192B64.get
private def dataUnimodularN256B64 := Thunk.mk fun _ => input "unimodular" 256 64
private def dataUnimodularN256B64Json := Thunk.mk fun _ => rowsJson dataUnimodularN256B64.get
private def solveA32 := Thunk.mk fun _ => solveInput 32
private def solveA32Json := Thunk.mk fun _ => rowsJson solveA32.get
private def solveIntegral32 := Thunk.mk fun _ => prepareSolve 32 true
private def solveIntegral32Json := Thunk.mk fun _ => rowsJson (rhsInput solveA32.get true 1)
private def solveRational32 := Thunk.mk fun _ => prepareSolve 32 false
private def solveRational32Json := Thunk.mk fun _ => rowsJson (rhsInput solveA32.get false 1)
private def repeatedN32R1 := Thunk.mk fun _ => rhsInput solveA32.get false 1
private def repeatedN32R8 := Thunk.mk fun _ => rhsInput solveA32.get false 8
private def repeatedN32R32 := Thunk.mk fun _ => rhsInput solveA32.get false 32
private def solveA64 := Thunk.mk fun _ => solveInput 64
private def solveA64Json := Thunk.mk fun _ => rowsJson solveA64.get
private def solveIntegral64 := Thunk.mk fun _ => prepareSolve 64 true
private def solveIntegral64Json := Thunk.mk fun _ => rowsJson (rhsInput solveA64.get true 1)
private def solveRational64 := Thunk.mk fun _ => prepareSolve 64 false
private def solveRational64Json := Thunk.mk fun _ => rowsJson (rhsInput solveA64.get false 1)
private def repeatedN64R1 := Thunk.mk fun _ => rhsInput solveA64.get false 1
private def repeatedN64R8 := Thunk.mk fun _ => rhsInput solveA64.get false 8
private def repeatedN64R64 := Thunk.mk fun _ => rhsInput solveA64.get false 64
private def solveA96 := Thunk.mk fun _ => solveInput 96
private def solveA96Json := Thunk.mk fun _ => rowsJson solveA96.get
private def solveIntegral96 := Thunk.mk fun _ => prepareSolve 96 true
private def solveIntegral96Json := Thunk.mk fun _ => rowsJson (rhsInput solveA96.get true 1)
private def solveRational96 := Thunk.mk fun _ => prepareSolve 96 false
private def solveRational96Json := Thunk.mk fun _ => rowsJson (rhsInput solveA96.get false 1)
private def repeatedN96R1 := Thunk.mk fun _ => rhsInput solveA96.get false 1
private def repeatedN96R8 := Thunk.mk fun _ => rhsInput solveA96.get false 8
private def repeatedN96R96 := Thunk.mk fun _ => rhsInput solveA96.get false 96
private def solveA128 := Thunk.mk fun _ => solveInput 128
private def solveA128Json := Thunk.mk fun _ => rowsJson solveA128.get
private def solveIntegral128 := Thunk.mk fun _ => prepareSolve 128 true
private def solveIntegral128Json := Thunk.mk fun _ => rowsJson (rhsInput solveA128.get true 1)
private def solveRational128 := Thunk.mk fun _ => prepareSolve 128 false
private def solveRational128Json := Thunk.mk fun _ => rowsJson (rhsInput solveA128.get false 1)
private def repeatedN128R1 := Thunk.mk fun _ => rhsInput solveA128.get false 1
private def repeatedN128R8 := Thunk.mk fun _ => rhsInput solveA128.get false 8
private def repeatedN128R128 := Thunk.mk fun _ => rhsInput solveA128.get false 128
private def solveA192 := Thunk.mk fun _ => solveInput 192
private def solveA192Json := Thunk.mk fun _ => rowsJson solveA192.get
private def solveIntegral192 := Thunk.mk fun _ => prepareSolve 192 true
private def solveIntegral192Json := Thunk.mk fun _ => rowsJson (rhsInput solveA192.get true 1)
private def solveRational192 := Thunk.mk fun _ => prepareSolve 192 false
private def solveRational192Json := Thunk.mk fun _ => rowsJson (rhsInput solveA192.get false 1)
private def repeatedN192R1 := Thunk.mk fun _ => rhsInput solveA192.get false 1
private def repeatedN192R8 := Thunk.mk fun _ => rhsInput solveA192.get false 8
private def repeatedN192R192 := Thunk.mk fun _ => rhsInput solveA192.get false 192
private def solveA256 := Thunk.mk fun _ => solveInput 256
private def solveA256Json := Thunk.mk fun _ => rowsJson solveA256.get
private def solveIntegral256 := Thunk.mk fun _ => prepareSolve 256 true
private def solveIntegral256Json := Thunk.mk fun _ => rowsJson (rhsInput solveA256.get true 1)
private def solveRational256 := Thunk.mk fun _ => prepareSolve 256 false
private def solveRational256Json := Thunk.mk fun _ => rowsJson (rhsInput solveA256.get false 1)
private def repeatedN256R1 := Thunk.mk fun _ => rhsInput solveA256.get false 1
private def repeatedN256R8 := Thunk.mk fun _ => rhsInput solveA256.get false 8
private def repeatedN256R256 := Thunk.mk fun _ => rhsInput solveA256.get false 256

def runModularStructuredN16B8 := runModular dataStructuredN16B8.get
setup_fixed_benchmark runModularStructuredN16B8 where compareConfig
def runBareissStructuredN16B8 := runBareiss dataStructuredN16B8.get
setup_fixed_benchmark runBareissStructuredN16B8 where compareConfig
def runFlintStructuredN16B8 := runFlint dataStructuredN16B8Json.get
setup_fixed_benchmark runFlintStructuredN16B8 where compareConfig
def runModularStructuredN24B8 := runModular dataStructuredN24B8.get
setup_fixed_benchmark runModularStructuredN24B8 where compareConfig
def runBareissStructuredN24B8 := runBareiss dataStructuredN24B8.get
setup_fixed_benchmark runBareissStructuredN24B8 where compareConfig
def runFlintStructuredN24B8 := runFlint dataStructuredN24B8Json.get
setup_fixed_benchmark runFlintStructuredN24B8 where compareConfig
def runModularStructuredN32B8 := runModular dataStructuredN32B8.get
setup_fixed_benchmark runModularStructuredN32B8 where compareConfig
def runBareissStructuredN32B8 := runBareiss dataStructuredN32B8.get
setup_fixed_benchmark runBareissStructuredN32B8 where compareConfig
def runFlintStructuredN32B8 := runFlint dataStructuredN32B8Json.get
setup_fixed_benchmark runFlintStructuredN32B8 where compareConfig
def runModularStructuredN48B8 := runModular dataStructuredN48B8.get
setup_fixed_benchmark runModularStructuredN48B8 where compareConfig
def runBareissStructuredN48B8 := runBareiss dataStructuredN48B8.get
setup_fixed_benchmark runBareissStructuredN48B8 where compareConfig
def runFlintStructuredN48B8 := runFlint dataStructuredN48B8Json.get
setup_fixed_benchmark runFlintStructuredN48B8 where compareConfig
def runModularStructuredN64B8 := runModular dataStructuredN64B8.get
setup_fixed_benchmark runModularStructuredN64B8 where compareConfig
def runBareissStructuredN64B8 := runBareiss dataStructuredN64B8.get
setup_fixed_benchmark runBareissStructuredN64B8 where compareConfig
def runFlintStructuredN64B8 := runFlint dataStructuredN64B8Json.get
setup_fixed_benchmark runFlintStructuredN64B8 where compareConfig
def runModularStructuredN96B8 := runModular dataStructuredN96B8.get
setup_fixed_benchmark runModularStructuredN96B8 where compareConfig
def runBareissStructuredN96B8 := runBareiss dataStructuredN96B8.get
setup_fixed_benchmark runBareissStructuredN96B8 where compareConfig
def runFlintStructuredN96B8 := runFlint dataStructuredN96B8Json.get
setup_fixed_benchmark runFlintStructuredN96B8 where compareConfig
def runModularStructuredN128B8 := runModular dataStructuredN128B8.get
setup_fixed_benchmark runModularStructuredN128B8 where compareConfig
def runBareissStructuredN128B8 := runBareiss dataStructuredN128B8.get
setup_fixed_benchmark runBareissStructuredN128B8 where compareConfig
def runFlintStructuredN128B8 := runFlint dataStructuredN128B8Json.get
setup_fixed_benchmark runFlintStructuredN128B8 where compareConfig
def runModularStructuredN192B8 := runModular dataStructuredN192B8.get
setup_fixed_benchmark runModularStructuredN192B8 where compareConfig
def runBareissStructuredN192B8 := runBareiss dataStructuredN192B8.get
setup_fixed_benchmark runBareissStructuredN192B8 where compareConfig
def runFlintStructuredN192B8 := runFlint dataStructuredN192B8Json.get
setup_fixed_benchmark runFlintStructuredN192B8 where compareConfig
def runModularStructuredN256B8 := runModular dataStructuredN256B8.get
setup_fixed_benchmark runModularStructuredN256B8 where compareConfig
def runBareissStructuredN256B8 := runBareiss dataStructuredN256B8.get
setup_fixed_benchmark runBareissStructuredN256B8 where compareConfig
def runFlintStructuredN256B8 := runFlint dataStructuredN256B8Json.get
setup_fixed_benchmark runFlintStructuredN256B8 where compareConfig
def runModularStructuredN320B8 := runModular dataStructuredN320B8.get
setup_fixed_benchmark runModularStructuredN320B8 where compareConfig
def runBareissStructuredN320B8 := runBareiss dataStructuredN320B8.get
setup_fixed_benchmark runBareissStructuredN320B8 where compareConfig
def runFlintStructuredN320B8 := runFlint dataStructuredN320B8Json.get
setup_fixed_benchmark runFlintStructuredN320B8 where compareConfig
def runModularStructuredN384B8 := runModular dataStructuredN384B8.get
setup_fixed_benchmark runModularStructuredN384B8 where compareConfig
def runBareissStructuredN384B8 := runBareiss dataStructuredN384B8.get
setup_fixed_benchmark runBareissStructuredN384B8 where compareConfig
def runFlintStructuredN384B8 := runFlint dataStructuredN384B8Json.get
setup_fixed_benchmark runFlintStructuredN384B8 where compareConfig
def runModularStructuredN512B8 := runModular dataStructuredN512B8.get
setup_fixed_benchmark runModularStructuredN512B8 where compareConfig
def runBareissStructuredN512B8 := runBareiss dataStructuredN512B8.get
setup_fixed_benchmark runBareissStructuredN512B8 where compareConfig
def runFlintStructuredN512B8 := runFlint dataStructuredN512B8Json.get
setup_fixed_benchmark runFlintStructuredN512B8 where compareConfig
def runModularDenseN32B8 := runModular dataDenseN32B8.get
setup_fixed_benchmark runModularDenseN32B8 where compareConfig
def runBareissDenseN32B8 := runBareiss dataDenseN32B8.get
setup_fixed_benchmark runBareissDenseN32B8 where compareConfig
def runFlintDenseN32B8 := runFlint dataDenseN32B8Json.get
setup_fixed_benchmark runFlintDenseN32B8 where compareConfig
def runModularDenseN64B8 := runModular dataDenseN64B8.get
setup_fixed_benchmark runModularDenseN64B8 where compareConfig
def runBareissDenseN64B8 := runBareiss dataDenseN64B8.get
setup_fixed_benchmark runBareissDenseN64B8 where compareConfig
def runFlintDenseN64B8 := runFlint dataDenseN64B8Json.get
setup_fixed_benchmark runFlintDenseN64B8 where compareConfig
def runModularDenseN96B8 := runModular dataDenseN96B8.get
setup_fixed_benchmark runModularDenseN96B8 where compareConfig
def runBareissDenseN96B8 := runBareiss dataDenseN96B8.get
setup_fixed_benchmark runBareissDenseN96B8 where compareConfig
def runFlintDenseN96B8 := runFlint dataDenseN96B8Json.get
setup_fixed_benchmark runFlintDenseN96B8 where compareConfig
def runModularDenseN128B8 := runModular dataDenseN128B8.get
setup_fixed_benchmark runModularDenseN128B8 where compareConfig
def runBareissDenseN128B8 := runBareiss dataDenseN128B8.get
setup_fixed_benchmark runBareissDenseN128B8 where compareConfig
def runFlintDenseN128B8 := runFlint dataDenseN128B8Json.get
setup_fixed_benchmark runFlintDenseN128B8 where compareConfig
def runModularDenseN192B8 := runModular dataDenseN192B8.get
setup_fixed_benchmark runModularDenseN192B8 where compareConfig
def runBareissDenseN192B8 := runBareiss dataDenseN192B8.get
setup_fixed_benchmark runBareissDenseN192B8 where compareConfig
def runFlintDenseN192B8 := runFlint dataDenseN192B8Json.get
setup_fixed_benchmark runFlintDenseN192B8 where compareConfig
def runModularDenseN256B8 := runModular dataDenseN256B8.get
setup_fixed_benchmark runModularDenseN256B8 where compareConfig
def runBareissDenseN256B8 := runBareiss dataDenseN256B8.get
setup_fixed_benchmark runBareissDenseN256B8 where compareConfig
def runFlintDenseN256B8 := runFlint dataDenseN256B8Json.get
setup_fixed_benchmark runFlintDenseN256B8 where compareConfig
def runModularDenseN32B64 := runModular dataDenseN32B64.get
setup_fixed_benchmark runModularDenseN32B64 where compareConfig
def runBareissDenseN32B64 := runBareiss dataDenseN32B64.get
setup_fixed_benchmark runBareissDenseN32B64 where compareConfig
def runFlintDenseN32B64 := runFlint dataDenseN32B64Json.get
setup_fixed_benchmark runFlintDenseN32B64 where compareConfig
def runModularDenseN64B64 := runModular dataDenseN64B64.get
setup_fixed_benchmark runModularDenseN64B64 where compareConfig
def runBareissDenseN64B64 := runBareiss dataDenseN64B64.get
setup_fixed_benchmark runBareissDenseN64B64 where compareConfig
def runFlintDenseN64B64 := runFlint dataDenseN64B64Json.get
setup_fixed_benchmark runFlintDenseN64B64 where compareConfig
def runModularDenseN96B64 := runModular dataDenseN96B64.get
setup_fixed_benchmark runModularDenseN96B64 where compareConfig
def runBareissDenseN96B64 := runBareiss dataDenseN96B64.get
setup_fixed_benchmark runBareissDenseN96B64 where compareConfig
def runFlintDenseN96B64 := runFlint dataDenseN96B64Json.get
setup_fixed_benchmark runFlintDenseN96B64 where compareConfig
def runModularDenseN128B64 := runModular dataDenseN128B64.get
setup_fixed_benchmark runModularDenseN128B64 where compareConfig
def runBareissDenseN128B64 := runBareiss dataDenseN128B64.get
setup_fixed_benchmark runBareissDenseN128B64 where compareConfig
def runFlintDenseN128B64 := runFlint dataDenseN128B64Json.get
setup_fixed_benchmark runFlintDenseN128B64 where compareConfig
def runModularDenseN192B64 := runModular dataDenseN192B64.get
setup_fixed_benchmark runModularDenseN192B64 where compareConfig
def runBareissDenseN192B64 := runBareiss dataDenseN192B64.get
setup_fixed_benchmark runBareissDenseN192B64 where compareConfig
def runFlintDenseN192B64 := runFlint dataDenseN192B64Json.get
setup_fixed_benchmark runFlintDenseN192B64 where compareConfig
def runModularDenseN256B64 := runModular dataDenseN256B64.get
setup_fixed_benchmark runModularDenseN256B64 where compareConfig
def runBareissDenseN256B64 := runBareiss dataDenseN256B64.get
setup_fixed_benchmark runBareissDenseN256B64 where compareConfig
def runFlintDenseN256B64 := runFlint dataDenseN256B64Json.get
setup_fixed_benchmark runFlintDenseN256B64 where compareConfig
def runModularDenseN32B1024 := runModular dataDenseN32B1024.get
setup_fixed_benchmark runModularDenseN32B1024 where compareConfig
def runBareissDenseN32B1024 := runBareiss dataDenseN32B1024.get
setup_fixed_benchmark runBareissDenseN32B1024 where compareConfig
def runFlintDenseN32B1024 := runFlint dataDenseN32B1024Json.get
setup_fixed_benchmark runFlintDenseN32B1024 where compareConfig
def runModularDenseN64B1024 := runModular dataDenseN64B1024.get
setup_fixed_benchmark runModularDenseN64B1024 where compareConfig
def runBareissDenseN64B1024 := runBareiss dataDenseN64B1024.get
setup_fixed_benchmark runBareissDenseN64B1024 where compareConfig
def runFlintDenseN64B1024 := runFlint dataDenseN64B1024Json.get
setup_fixed_benchmark runFlintDenseN64B1024 where compareConfig
def runModularDenseN96B1024 := runModular dataDenseN96B1024.get
setup_fixed_benchmark runModularDenseN96B1024 where compareConfig
def runBareissDenseN96B1024 := runBareiss dataDenseN96B1024.get
setup_fixed_benchmark runBareissDenseN96B1024 where compareConfig
def runFlintDenseN96B1024 := runFlint dataDenseN96B1024Json.get
setup_fixed_benchmark runFlintDenseN96B1024 where compareConfig
def runModularDenseN128B1024 := runModular dataDenseN128B1024.get
setup_fixed_benchmark runModularDenseN128B1024 where compareConfig
def runBareissDenseN128B1024 := runBareiss dataDenseN128B1024.get
setup_fixed_benchmark runBareissDenseN128B1024 where compareConfig
def runFlintDenseN128B1024 := runFlint dataDenseN128B1024Json.get
setup_fixed_benchmark runFlintDenseN128B1024 where compareConfig
def runModularDenseN192B1024 := runModular dataDenseN192B1024.get
setup_fixed_benchmark runModularDenseN192B1024 where compareConfig
def runBareissDenseN192B1024 := runBareiss dataDenseN192B1024.get
setup_fixed_benchmark runBareissDenseN192B1024 where compareConfig
def runFlintDenseN192B1024 := runFlint dataDenseN192B1024Json.get
setup_fixed_benchmark runFlintDenseN192B1024 where compareConfig
def runModularDenseN256B1024 := runModular dataDenseN256B1024.get
setup_fixed_benchmark runModularDenseN256B1024 where compareConfig
def runBareissDenseN256B1024 := runBareiss dataDenseN256B1024.get
setup_fixed_benchmark runBareissDenseN256B1024 where compareConfig
def runFlintDenseN256B1024 := runFlint dataDenseN256B1024Json.get
setup_fixed_benchmark runFlintDenseN256B1024 where compareConfig
def runModularUnimodularN32B64 := runModular dataUnimodularN32B64.get
setup_fixed_benchmark runModularUnimodularN32B64 where compareConfig
def runBareissUnimodularN32B64 := runBareiss dataUnimodularN32B64.get
setup_fixed_benchmark runBareissUnimodularN32B64 where compareConfig
def runFlintUnimodularN32B64 := runFlint dataUnimodularN32B64Json.get
setup_fixed_benchmark runFlintUnimodularN32B64 where compareConfig
def runModularUnimodularN64B64 := runModular dataUnimodularN64B64.get
setup_fixed_benchmark runModularUnimodularN64B64 where compareConfig
def runBareissUnimodularN64B64 := runBareiss dataUnimodularN64B64.get
setup_fixed_benchmark runBareissUnimodularN64B64 where compareConfig
def runFlintUnimodularN64B64 := runFlint dataUnimodularN64B64Json.get
setup_fixed_benchmark runFlintUnimodularN64B64 where compareConfig
def runModularUnimodularN96B64 := runModular dataUnimodularN96B64.get
setup_fixed_benchmark runModularUnimodularN96B64 where compareConfig
def runBareissUnimodularN96B64 := runBareiss dataUnimodularN96B64.get
setup_fixed_benchmark runBareissUnimodularN96B64 where compareConfig
def runFlintUnimodularN96B64 := runFlint dataUnimodularN96B64Json.get
setup_fixed_benchmark runFlintUnimodularN96B64 where compareConfig
def runModularUnimodularN128B64 := runModular dataUnimodularN128B64.get
setup_fixed_benchmark runModularUnimodularN128B64 where compareConfig
def runBareissUnimodularN128B64 := runBareiss dataUnimodularN128B64.get
setup_fixed_benchmark runBareissUnimodularN128B64 where compareConfig
def runFlintUnimodularN128B64 := runFlint dataUnimodularN128B64Json.get
setup_fixed_benchmark runFlintUnimodularN128B64 where compareConfig
def runModularUnimodularN192B64 := runModular dataUnimodularN192B64.get
setup_fixed_benchmark runModularUnimodularN192B64 where compareConfig
def runBareissUnimodularN192B64 := runBareiss dataUnimodularN192B64.get
setup_fixed_benchmark runBareissUnimodularN192B64 where compareConfig
def runFlintUnimodularN192B64 := runFlint dataUnimodularN192B64Json.get
setup_fixed_benchmark runFlintUnimodularN192B64 where compareConfig
def runModularUnimodularN256B64 := runModular dataUnimodularN256B64.get
setup_fixed_benchmark runModularUnimodularN256B64 where compareConfig
def runBareissUnimodularN256B64 := runBareiss dataUnimodularN256B64.get
setup_fixed_benchmark runBareissUnimodularN256B64 where compareConfig
def runFlintUnimodularN256B64 := runFlint dataUnimodularN256B64Json.get
setup_fixed_benchmark runFlintUnimodularN256B64 where compareConfig

def runDivisorStructuredN16B8 := runDivisor dataStructuredN16B8.get
setup_fixed_benchmark runDivisorStructuredN16B8 where compareConfig
def runDivisorStructuredN24B8 := runDivisor dataStructuredN24B8.get
setup_fixed_benchmark runDivisorStructuredN24B8 where compareConfig
def runDivisorStructuredN32B8 := runDivisor dataStructuredN32B8.get
setup_fixed_benchmark runDivisorStructuredN32B8 where compareConfig
def runDivisorStructuredN48B8 := runDivisor dataStructuredN48B8.get
setup_fixed_benchmark runDivisorStructuredN48B8 where compareConfig
def runDivisorStructuredN64B8 := runDivisor dataStructuredN64B8.get
setup_fixed_benchmark runDivisorStructuredN64B8 where compareConfig
def runDivisorStructuredN96B8 := runDivisor dataStructuredN96B8.get
setup_fixed_benchmark runDivisorStructuredN96B8 where compareConfig
def runDivisorStructuredN128B8 := runDivisor dataStructuredN128B8.get
setup_fixed_benchmark runDivisorStructuredN128B8 where compareConfig
def runDivisorStructuredN192B8 := runDivisor dataStructuredN192B8.get
setup_fixed_benchmark runDivisorStructuredN192B8 where compareConfig
def runDivisorStructuredN256B8 := runDivisor dataStructuredN256B8.get
setup_fixed_benchmark runDivisorStructuredN256B8 where compareConfig
def runDivisorStructuredN320B8 := runDivisor dataStructuredN320B8.get
setup_fixed_benchmark runDivisorStructuredN320B8 where compareConfig
def runDivisorStructuredN384B8 := runDivisor dataStructuredN384B8.get
setup_fixed_benchmark runDivisorStructuredN384B8 where compareConfig
def runDivisorStructuredN512B8 := runDivisor dataStructuredN512B8.get
setup_fixed_benchmark runDivisorStructuredN512B8 where compareConfig
def runDivisorDenseN32B8 := runDivisor dataDenseN32B8.get
setup_fixed_benchmark runDivisorDenseN32B8 where compareConfig
def runDivisorDenseN64B8 := runDivisor dataDenseN64B8.get
setup_fixed_benchmark runDivisorDenseN64B8 where compareConfig
def runDivisorDenseN96B8 := runDivisor dataDenseN96B8.get
setup_fixed_benchmark runDivisorDenseN96B8 where compareConfig
def runDivisorDenseN128B8 := runDivisor dataDenseN128B8.get
setup_fixed_benchmark runDivisorDenseN128B8 where compareConfig
def runDivisorDenseN192B8 := runDivisor dataDenseN192B8.get
setup_fixed_benchmark runDivisorDenseN192B8 where compareConfig
def runDivisorDenseN256B8 := runDivisor dataDenseN256B8.get
setup_fixed_benchmark runDivisorDenseN256B8 where compareConfig
def runDivisorDenseN32B64 := runDivisor dataDenseN32B64.get
setup_fixed_benchmark runDivisorDenseN32B64 where compareConfig
def runDivisorDenseN64B64 := runDivisor dataDenseN64B64.get
setup_fixed_benchmark runDivisorDenseN64B64 where compareConfig
def runDivisorDenseN96B64 := runDivisor dataDenseN96B64.get
setup_fixed_benchmark runDivisorDenseN96B64 where compareConfig
def runDivisorDenseN128B64 := runDivisor dataDenseN128B64.get
setup_fixed_benchmark runDivisorDenseN128B64 where compareConfig
def runDivisorDenseN192B64 := runDivisor dataDenseN192B64.get
setup_fixed_benchmark runDivisorDenseN192B64 where compareConfig
def runDivisorDenseN256B64 := runDivisor dataDenseN256B64.get
setup_fixed_benchmark runDivisorDenseN256B64 where compareConfig
def runDivisorDenseN32B1024 := runDivisor dataDenseN32B1024.get
setup_fixed_benchmark runDivisorDenseN32B1024 where compareConfig
def runDivisorDenseN64B1024 := runDivisor dataDenseN64B1024.get
setup_fixed_benchmark runDivisorDenseN64B1024 where compareConfig
def runDivisorDenseN96B1024 := runDivisor dataDenseN96B1024.get
setup_fixed_benchmark runDivisorDenseN96B1024 where compareConfig
def runDivisorDenseN128B1024 := runDivisor dataDenseN128B1024.get
setup_fixed_benchmark runDivisorDenseN128B1024 where compareConfig
def runDivisorDenseN192B1024 := runDivisor dataDenseN192B1024.get
setup_fixed_benchmark runDivisorDenseN192B1024 where compareConfig
def runDivisorDenseN256B1024 := runDivisor dataDenseN256B1024.get
setup_fixed_benchmark runDivisorDenseN256B1024 where compareConfig
def runDivisorUnimodularN32B64 := runDivisor dataUnimodularN32B64.get
setup_fixed_benchmark runDivisorUnimodularN32B64 where compareConfig
def runDivisorUnimodularN64B64 := runDivisor dataUnimodularN64B64.get
setup_fixed_benchmark runDivisorUnimodularN64B64 where compareConfig
def runDivisorUnimodularN96B64 := runDivisor dataUnimodularN96B64.get
setup_fixed_benchmark runDivisorUnimodularN96B64 where compareConfig
def runDivisorUnimodularN128B64 := runDivisor dataUnimodularN128B64.get
setup_fixed_benchmark runDivisorUnimodularN128B64 where compareConfig
def runDivisorUnimodularN192B64 := runDivisor dataUnimodularN192B64.get
setup_fixed_benchmark runDivisorUnimodularN192B64 where compareConfig
def runDivisorUnimodularN256B64 := runDivisor dataUnimodularN256B64.get
setup_fixed_benchmark runDivisorUnimodularN256B64 where compareConfig
def runDecompN32 := runDecomp solveA32.get
setup_fixed_benchmark runDecompN32 where compareConfig
def runSolveIntegralN32 := runSolve solveIntegral32.get
setup_fixed_benchmark runSolveIntegralN32 where compareConfig
def runFlintSolveIntegralN32 := runFlintSolve solveA32Json.get solveIntegral32Json.get
setup_fixed_benchmark runFlintSolveIntegralN32 where compareConfig
def runSolveRationalN32 := runSolve solveRational32.get
setup_fixed_benchmark runSolveRationalN32 where compareConfig
def runFlintSolveRationalN32 := runFlintSolve solveA32Json.get solveRational32Json.get
setup_fixed_benchmark runFlintSolveRationalN32 where compareConfig
def runRepeatedN32R1 := runRepeated solveA32.get repeatedN32R1.get true
setup_fixed_benchmark runRepeatedN32R1 where compareConfig
def runIndependentN32R1 := runRepeated solveA32.get repeatedN32R1.get false
setup_fixed_benchmark runIndependentN32R1 where compareConfig
def runRepeatedN32R8 := runRepeated solveA32.get repeatedN32R8.get true
setup_fixed_benchmark runRepeatedN32R8 where compareConfig
def runIndependentN32R8 := runRepeated solveA32.get repeatedN32R8.get false
setup_fixed_benchmark runIndependentN32R8 where compareConfig
def runRepeatedN32R32 := runRepeated solveA32.get repeatedN32R32.get true
setup_fixed_benchmark runRepeatedN32R32 where compareConfig
def runIndependentN32R32 := runRepeated solveA32.get repeatedN32R32.get false
setup_fixed_benchmark runIndependentN32R32 where compareConfig
def runDecompN64 := runDecomp solveA64.get
setup_fixed_benchmark runDecompN64 where compareConfig
def runSolveIntegralN64 := runSolve solveIntegral64.get
setup_fixed_benchmark runSolveIntegralN64 where compareConfig
def runFlintSolveIntegralN64 := runFlintSolve solveA64Json.get solveIntegral64Json.get
setup_fixed_benchmark runFlintSolveIntegralN64 where compareConfig
def runSolveRationalN64 := runSolve solveRational64.get
setup_fixed_benchmark runSolveRationalN64 where compareConfig
def runFlintSolveRationalN64 := runFlintSolve solveA64Json.get solveRational64Json.get
setup_fixed_benchmark runFlintSolveRationalN64 where compareConfig
def runRepeatedN64R1 := runRepeated solveA64.get repeatedN64R1.get true
setup_fixed_benchmark runRepeatedN64R1 where compareConfig
def runIndependentN64R1 := runRepeated solveA64.get repeatedN64R1.get false
setup_fixed_benchmark runIndependentN64R1 where compareConfig
def runRepeatedN64R8 := runRepeated solveA64.get repeatedN64R8.get true
setup_fixed_benchmark runRepeatedN64R8 where compareConfig
def runIndependentN64R8 := runRepeated solveA64.get repeatedN64R8.get false
setup_fixed_benchmark runIndependentN64R8 where compareConfig
def runRepeatedN64R64 := runRepeated solveA64.get repeatedN64R64.get true
setup_fixed_benchmark runRepeatedN64R64 where compareConfig
def runIndependentN64R64 := runRepeated solveA64.get repeatedN64R64.get false
setup_fixed_benchmark runIndependentN64R64 where compareConfig
def runDecompN96 := runDecomp solveA96.get
setup_fixed_benchmark runDecompN96 where compareConfig
def runSolveIntegralN96 := runSolve solveIntegral96.get
setup_fixed_benchmark runSolveIntegralN96 where compareConfig
def runFlintSolveIntegralN96 := runFlintSolve solveA96Json.get solveIntegral96Json.get
setup_fixed_benchmark runFlintSolveIntegralN96 where compareConfig
def runSolveRationalN96 := runSolve solveRational96.get
setup_fixed_benchmark runSolveRationalN96 where compareConfig
def runFlintSolveRationalN96 := runFlintSolve solveA96Json.get solveRational96Json.get
setup_fixed_benchmark runFlintSolveRationalN96 where compareConfig
def runRepeatedN96R1 := runRepeated solveA96.get repeatedN96R1.get true
setup_fixed_benchmark runRepeatedN96R1 where compareConfig
def runIndependentN96R1 := runRepeated solveA96.get repeatedN96R1.get false
setup_fixed_benchmark runIndependentN96R1 where compareConfig
def runRepeatedN96R8 := runRepeated solveA96.get repeatedN96R8.get true
setup_fixed_benchmark runRepeatedN96R8 where compareConfig
def runIndependentN96R8 := runRepeated solveA96.get repeatedN96R8.get false
setup_fixed_benchmark runIndependentN96R8 where compareConfig
def runRepeatedN96R96 := runRepeated solveA96.get repeatedN96R96.get true
setup_fixed_benchmark runRepeatedN96R96 where compareConfig
def runIndependentN96R96 := runRepeated solveA96.get repeatedN96R96.get false
setup_fixed_benchmark runIndependentN96R96 where compareConfig
def runDecompN128 := runDecomp solveA128.get
setup_fixed_benchmark runDecompN128 where compareConfig
def runSolveIntegralN128 := runSolve solveIntegral128.get
setup_fixed_benchmark runSolveIntegralN128 where compareConfig
def runFlintSolveIntegralN128 := runFlintSolve solveA128Json.get solveIntegral128Json.get
setup_fixed_benchmark runFlintSolveIntegralN128 where compareConfig
def runSolveRationalN128 := runSolve solveRational128.get
setup_fixed_benchmark runSolveRationalN128 where compareConfig
def runFlintSolveRationalN128 := runFlintSolve solveA128Json.get solveRational128Json.get
setup_fixed_benchmark runFlintSolveRationalN128 where compareConfig
def runRepeatedN128R1 := runRepeated solveA128.get repeatedN128R1.get true
setup_fixed_benchmark runRepeatedN128R1 where compareConfig
def runIndependentN128R1 := runRepeated solveA128.get repeatedN128R1.get false
setup_fixed_benchmark runIndependentN128R1 where compareConfig
def runRepeatedN128R8 := runRepeated solveA128.get repeatedN128R8.get true
setup_fixed_benchmark runRepeatedN128R8 where compareConfig
def runIndependentN128R8 := runRepeated solveA128.get repeatedN128R8.get false
setup_fixed_benchmark runIndependentN128R8 where compareConfig
def runRepeatedN128R128 := runRepeated solveA128.get repeatedN128R128.get true
setup_fixed_benchmark runRepeatedN128R128 where compareConfig
def runIndependentN128R128 := runRepeated solveA128.get repeatedN128R128.get false
setup_fixed_benchmark runIndependentN128R128 where compareConfig
def runDecompN192 := runDecomp solveA192.get
setup_fixed_benchmark runDecompN192 where compareConfig
def runSolveIntegralN192 := runSolve solveIntegral192.get
setup_fixed_benchmark runSolveIntegralN192 where compareConfig
def runFlintSolveIntegralN192 := runFlintSolve solveA192Json.get solveIntegral192Json.get
setup_fixed_benchmark runFlintSolveIntegralN192 where compareConfig
def runSolveRationalN192 := runSolve solveRational192.get
setup_fixed_benchmark runSolveRationalN192 where compareConfig
def runFlintSolveRationalN192 := runFlintSolve solveA192Json.get solveRational192Json.get
setup_fixed_benchmark runFlintSolveRationalN192 where compareConfig
def runRepeatedN192R1 := runRepeated solveA192.get repeatedN192R1.get true
setup_fixed_benchmark runRepeatedN192R1 where compareConfig
def runIndependentN192R1 := runRepeated solveA192.get repeatedN192R1.get false
setup_fixed_benchmark runIndependentN192R1 where compareConfig
def runRepeatedN192R8 := runRepeated solveA192.get repeatedN192R8.get true
setup_fixed_benchmark runRepeatedN192R8 where compareConfig
def runIndependentN192R8 := runRepeated solveA192.get repeatedN192R8.get false
setup_fixed_benchmark runIndependentN192R8 where compareConfig
def runRepeatedN192R192 := runRepeated solveA192.get repeatedN192R192.get true
setup_fixed_benchmark runRepeatedN192R192 where compareConfig
def runIndependentN192R192 := runRepeated solveA192.get repeatedN192R192.get false
setup_fixed_benchmark runIndependentN192R192 where compareConfig
def runDecompN256 := runDecomp solveA256.get
setup_fixed_benchmark runDecompN256 where compareConfig
def runSolveIntegralN256 := runSolve solveIntegral256.get
setup_fixed_benchmark runSolveIntegralN256 where compareConfig
def runFlintSolveIntegralN256 := runFlintSolve solveA256Json.get solveIntegral256Json.get
setup_fixed_benchmark runFlintSolveIntegralN256 where compareConfig
def runSolveRationalN256 := runSolve solveRational256.get
setup_fixed_benchmark runSolveRationalN256 where compareConfig
def runFlintSolveRationalN256 := runFlintSolve solveA256Json.get solveRational256Json.get
setup_fixed_benchmark runFlintSolveRationalN256 where compareConfig
def runRepeatedN256R1 := runRepeated solveA256.get repeatedN256R1.get true
setup_fixed_benchmark runRepeatedN256R1 where compareConfig
def runIndependentN256R1 := runRepeated solveA256.get repeatedN256R1.get false
setup_fixed_benchmark runIndependentN256R1 where compareConfig
def runRepeatedN256R8 := runRepeated solveA256.get repeatedN256R8.get true
setup_fixed_benchmark runRepeatedN256R8 where compareConfig
def runIndependentN256R8 := runRepeated solveA256.get repeatedN256R8.get false
setup_fixed_benchmark runIndependentN256R8 where compareConfig
def runRepeatedN256R256 := runRepeated solveA256.get repeatedN256R256.get true
setup_fixed_benchmark runRepeatedN256R256 where compareConfig
def runIndependentN256R256 := runRepeated solveA256.get repeatedN256R256.get false
setup_fixed_benchmark runIndependentN256R256 where compareConfig

def smokeDivisor := runDivisorAt "structured" 4 8
def smokeIntegral := runSolveAt 4 true
def smokeRational := runSolveAt 4 false
def smokeRepeated := runRepeatedAt 4 4 true
def smokeIndependent := runRepeatedAt 4 4 false
setup_fixed_benchmark smokeDivisor where { expectedHash := some 218 }
setup_fixed_benchmark smokeIntegral where { expectedHash := some 49 }
setup_fixed_benchmark smokeRational where { expectedHash := some 55142488 }
setup_fixed_benchmark smokeRepeated where { expectedHash := some 1765801 }
setup_fixed_benchmark smokeIndependent where { expectedHash := some 1765801 }

/-- Attribute the structured divisor route, including its lifting and image counts. -/
def diagnose (n : Nat) : IO UInt32 := do
  let A := input "structured" n 8
  let pre ← IO.monoNanosNow
  let fuel := A.solveFuel
  if fuel == 0 then throw <| IO.userError "empty diagnostic budget"
  let afterBound ← IO.monoNanosNow
  let qs := ZMod64.primesBelow (2 ^ 31 - 1) fuel
  if qs.isEmpty then throw <| IO.userError "empty diagnostic supply"
  let afterSupply ← IO.monoNanosNow
  IO.println s!"bound_ns={afterBound - pre} supply_ns={afterSupply - afterBound} prime_count={qs.size}"
  let start ← IO.monoNanosNow
  let some D := A.decomp? A.solveFuel | throw <| IO.userError "decomposition failed"
  let afterDecomp ← IO.monoNanosNow
  let b := (Matrix.Dixon.draw n (Rand.ofSeed 10220)).1
  let some (y, d) := Matrix.solveWith D b | throw <| IO.userError "solve failed"
  let afterSolve ← IO.monoNanosNow
  let bound := A.hadamardBound / d.natAbs
  let some state := Matrix.Dixon.cofactorCrt? D d bound (ModularMatrix.defaultFuel A)
    | throw <| IO.userError "cofactor reconstruction failed"
  let finish ← IO.monoNanosNow
  IO.println s!"decomp_ns={afterDecomp - start} solve_ns={afterSolve - afterDecomp} cofactor_ns={finish - afterSolve}"
  IO.println s!"den_bits={d.natAbs.log2 + 1} cofactor_bound_bits={bound.log2 + 1} modulus_bits={state.modulus.log2 + 1} digits={Matrix.Dixon.digits D (Matrix.numeratorBound A b) A.hadamardBound}"
  IO.println s!"det_hash={hash (d * state.value[0])} solution_hash={hash (y.foldl (· + ·) d)}"
  return 0

/-- Run the small hash anchors in CI; the full comparator ladder is scheduled. -/
def verifySmoke : IO UInt32 := do
  let reports ← LeanBench.verify [`Hex.ModularMatrixBench.smokeStructured,
    `Hex.ModularMatrixBench.smokeDense, `Hex.ModularMatrixBench.smokeUnimodular,
    `Hex.ModularMatrixBench.smokeDivisor, `Hex.ModularMatrixBench.smokeIntegral,
    `Hex.ModularMatrixBench.smokeRational, `Hex.ModularMatrixBench.smokeRepeated,
    `Hex.ModularMatrixBench.smokeIndependent]
  IO.println (LeanBench.Format.fmtCombinedVerify reports)
  return if reports.passed then 0 else 1

end Hex.ModularMatrixBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["verify"] => Hex.ModularMatrixBench.verifySmoke
  | ["diagnose", n] => Hex.ModularMatrixBench.diagnose (n.toNat?.getD 128)
  | _ => LeanBench.Cli.dispatch args
