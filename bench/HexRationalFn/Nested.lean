/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRationalFn
import LeanBench
import Lean.Data.Json

namespace Hex.RationalFnBench.Nested

private structure Coefficients where
  Carrier : Type
  field : Lean.Grind.Field Carrier
  equality : DecidableEq Carrier
  encode : Carrier → Lean.Json
  digest : Carrier → UInt64

private def coefficients : Nat → Coefficients
  | 0 => ⟨Rat, inferInstance, inferInstance,
      fun q => Lean.toJson #[q.num, (q.den : Int)], hash⟩
  | depth + 1 =>
    let base := coefficients depth
    letI := base.field
    letI := base.equality
    { Carrier := RationalFn base.Carrier
      field := inferInstance
      equality := inferInstance
      encode := fun f => Lean.Json.mkObj [
        ("num", Lean.Json.arr (f.num.toArray.map base.encode)),
        ("den", Lean.Json.arr (f.den.toArray.map base.encode))]
      digest := fun f => hash (f.num.toArray.map base.digest, f.den.toArray.map base.digest) }

/-- Force the constructed pair to cross a function boundary without timing recursive hashing. -/
@[noinline] private def sizes {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (f : RationalFn K) : Nat × Nat := (f.num.size, f.den.size)

/-- The literal input and independently checked output are prepared outside timing. -/
structure Input where
  depth : Nat
  literal : String
  seed : Nat
  evaluate : Nat → UInt64
  inspect : Unit → Lean.Json

instance : Hashable Input := ⟨fun i => hash (i.depth, i.literal, i.seed)⟩

/-- Cast the runtime input zero and its successor in an existing field dictionary.
The runtime argument prevents construction from moving into preparation. -/
def units (depth : Nat) : Input :=
  let base := coefficients (depth - 1)
  letI := base.field
  letI := base.equality
  let encode := fun (f : RationalFn base.Carrier) => Lean.Json.mkObj [
    ("num", Lean.Json.arr (f.num.toArray.map base.encode)),
    ("den", Lean.Json.arr (f.den.toArray.map base.encode))]
  let literal := (Lean.Json.mkObj [("zero", encode 0), ("one", encode 1)]).compress
  ⟨depth, literal, 0, fun n => hash (sizes (Nat.cast n : RationalFn base.Carrier),
      sizes (Nat.cast (n + 1) : RationalFn base.Carrier)),
    fun _ => Lean.Json.mkObj [("zero", encode 0), ("one", encode 1)]⟩

/-- A representative arithmetic consumer uses a prepared nonconstant fraction. -/
def arithmetic (depth : Nat) : Input :=
  let base := coefficients (depth - 1)
  letI := base.field
  letI := base.equality
  let x : RationalFn base.Carrier := RationalFn.X
  let f := (x + 1) / (x - 1)
  let encode := fun (g : RationalFn base.Carrier) => Lean.Json.mkObj [
    ("num", Lean.Json.arr (g.num.toArray.map base.encode)),
    ("den", Lean.Json.arr (g.den.toArray.map base.encode))]
  let digest := fun (g : RationalFn base.Carrier) =>
    hash (g.num.toArray.map base.digest, g.den.toArray.map base.digest)
  ⟨depth, (encode f).compress, 0,
    fun _ => digest (f * 1 + 0), fun _ => encode (f * 1 + 0)⟩

@[noinline] def runUnits (i : Input) : UInt64 := i.evaluate i.seed
@[noinline] def runArithmetic (i : Input) : UInt64 := i.evaluate i.seed

/-- Short schedules; sharing removes the branching constructor recurrence. -/
def config : LeanBench.BenchmarkConfig :=
  { paramSchedule := .custom #[2, 6, 10], paramFloor := 2, paramCeiling := 10,
    outerTrials := 6, targetInnerNanos := 100000000,
    signalFloorMultiplier := 1, maxSecondsPerCall := 30 }

/- Linear timing model for the repaired constructors: each level constructs one lower
one and shares it, without constructing lower zeros or testing normalization.
Construction and destruction of the resulting shared chain both take Θ(d). -/
setup_benchmark runUnits d => d + 1 with prep := units where config

/- Descriptive complexity formula, representative timings only: count the two outer field
operations. Coefficient arithmetic and recursive output hashing vary with depth;
the descriptive harness verdict makes no timing-scaling claim for them. -/
setup_benchmark runArithmetic _d => 2 with prep := arithmetic
  where { config with paramSchedule := .custom #[1, 2, 3], paramFloor := 1, paramCeiling := 3 }

/-- Complete canonical outputs are checked outside the timed constructor path. -/
def inspect : IO Unit := do
  for (label, prepare, depths) in #[
      ("units", units, #[2, 6, 10]), ("arithmetic", arithmetic, #[1, 2, 3])] do
    for depth in depths do
      let i := prepare depth
      let result := (i.inspect ()).compress
      unless result == i.literal do
        throw (IO.userError s!"nested {label} output differs at depth {depth}")
      IO.println <| (Lean.Json.mkObj [
        ("operation", Lean.toJson label), ("depth", Lean.toJson depth),
        ("input", Lean.toJson i.literal), ("output", Lean.toJson result),
        ("resultHash", Lean.toJson (i.evaluate i.seed).toNat)]).compress

end Hex.RationalFnBench.Nested
