/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Input
import LeanBench
import Lean.Data.Json

namespace Hex.SignDetBench
open Hex.SignDet

/-- Actual nodes and coefficient operands retained outside the measured phases. -/
structure PhaseInput where
  base : Input
  members : List (Node Rat Nat)
  moments : List (TarskiCertificate Rat Rat Nat)
  coefficients : List Rat

instance : Hashable PhaseInput where
  hash i := hash (hash i.base, i.coefficients)

def phaseInput (s : Nat) : PhaseInput :=
  let base := input s
  let members := base.tree.map nodes |>.getD []
  let moments := members.flatMap fun n => n.moments.toList
  let coefficients := moments.flatMap fun c =>
    c.remainders.chain.toList.flatMap fun p => p.toArray.toList
  ⟨base, members, moments, coefficients⟩

/-- Prepared-query calls on the exact representatives used in the tree. -/
@[noinline] def runQueries (i : PhaseInput) : Option UInt64 := do
  let domain ← i.base.domain
  return hash (i.moments.map fun c =>
    (Sturm.certifyPrepared (10377 : Nat) domain c.queryPoly).value)

/-- Actual modulo-head moment construction from retained query preprocessing. -/
@[noinline] def runProducts (i : PhaseInput) : Option UInt64 := do
  let domain ← i.base.domain
  return hash (i.members.map fun n =>
    let operands := QueryReduction.operands n.queries n.preparation
    n.system.rows.toList.map fun row =>
      (nodeReduction true domain operands row).map fun r => polyHash r.result)

/-- Integer moment matrices, including their ordered sign-word scans. -/
@[noinline] def runMatrices (i : PhaseInput) : Option UInt64 := do
  let _ ← i.base.domain
  return hash (i.members.map fun n => matrixHash (momentMatrix n.system.rows n.system.columns))

/-- Actual leaf/parent solvers, including their complete system checks.
The matrix construction inside those checks remains part of this operation. -/
@[noinline] def runSolvers (i : PhaseInput) : Option UInt64 := do
  let _ ← i.base.domain
  let result : Except BuildError (List UInt64) := i.members.mapM fun n => do
    let s ←
      if n.queries.length ≤ 1 then
        solveSystem n.queries.length n.system.rows n.system.columns n.system.values
      else
        solveScaled n.queries.length n.system.rows n.system.columns n.system.values
          n.system.denominator n.system.inverse
    return hash s.counts.toList
  match result with
  | .error _ => none
  | .ok counts => some (hash counts)

/-- Rational coefficient-sign callbacks on the actual stored remainder
coefficients. Mapping and result hashing are included, with linear cost. -/
@[noinline] def runSigns (i : PhaseInput) : Option UInt64 := do
  let _ ← i.base.domain
  return hash (i.coefficients.map Sturm.orderSign)

-- Declared cost-model: Θ(s), there are 7s−4 prepared queries of bounded degree and coefficient size.
setup_benchmark runQueries s => s
  with prep := phaseInput
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    paramFloor := 64
    paramCeiling := 2048
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 10
  }

-- Declared cost-model: Θ(s log s), each balanced node scans its k exponent slots; nonzero factors are bounded.
setup_benchmark runProducts s => s * (Nat.log2 s + 1)
  with prep := phaseInput
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    paramFloor := 64
    paramCeiling := 2048
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 10
  }

-- Declared cost-model: Θ(s log s), bounded matrix dimensions still require Θ(k) sign/exponent slot scans per node.
setup_benchmark runMatrices s => s * (Nat.log2 s + 1)
  with prep := phaseInput
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    paramFloor := 64
    paramCeiling := 2048
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 10
  }

-- Declared cost-model: Θ(s log s), bounded scalar solves include System.check with Θ(k) matrix slot scans per node.
setup_benchmark runSolvers s => s * (Nat.log2 s + 1)
  with prep := phaseInput
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    paramFloor := 64
    paramCeiling := 2048
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 10
  }

-- Declared cost-model: Θ(s), there are Θ(s) stored remainder coefficients of bounded size.
setup_benchmark runSigns s => s
  with prep := phaseInput
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    paramFloor := 64
    paramCeiling := 2048
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 10
  }

/-- Bind phase outputs to the already checked fixture's literal witnesses.
This is output validation, not an independent semantics theorem. -/
def inspectPhases : IO UInt32 := do
  for s in #[64, 128, 256, 512, 1024, 2048] do
    let i := phaseInput s
    unless i.base.domain.isSome && i.base.tree.isSome && !i.members.isEmpty do
      throw (IO.userError s!"missing checked phase input at {s}")
    let expected : List (String × Option UInt64 × Option UInt64) := [
      ("runQueries", runQueries i, some (hash (i.moments.map (·.value)))),
      ("runProducts", runProducts i, some (hash (i.members.map fun n =>
        n.reductions.toList.map fun r => r.map fun r => polyHash r.result))),
      ("runMatrices", runMatrices i, some (hash (i.members.map fun n =>
        matrixHash (momentMatrix n.system.rows n.system.columns)))),
      ("runSolvers", runSolvers i, some (hash (i.members.map fun n => hash n.system.counts.toList))),
      ("runSigns", runSigns i, some (hash (i.coefficients.map fun q =>
        if q.num > 0 then (1 : Int) else if q.num < 0 then -1 else 0)))]
    let mut fields := [("queries", Lean.toJson s),
      ("inputHash", Lean.toJson (hash i).toNat),
      ("nodes", Lean.toJson i.members.length),
      ("preparedQueries", Lean.toJson i.moments.length),
      ("coefficientSigns", Lean.toJson i.coefficients.length)]
    for (name, actual, wanted) in expected do
      unless actual == wanted do throw (IO.userError s!"phase output mismatch: {name} at {s}")
      fields := fields ++ [(name, Lean.toJson (hash wanted).toNat)]
    IO.println (Lean.Json.mkObj fields).compress
  return 0

end Hex.SignDetBench
