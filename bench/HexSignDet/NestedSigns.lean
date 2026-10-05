/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRationalFn
import HexOrderedFn.Infinitesimal
import LeanBench
import Lean.Data.Json

namespace Hex.SignDetBench.NestedSigns

/-- Existing canonical fields and their ordinary positive-infinitesimal sign.
No altered arithmetic instance is introduced for measurement. -/
private structure Coefficients where
  Carrier : Type
  field : Lean.Grind.Field Carrier
  equality : DecidableEq Carrier
  sign : Carrier → Int
  encode : Carrier → Lean.Json

private def coefficients : Nat → Coefficients
  | 0 => ⟨Rat, inferInstance, inferInstance, OrderedFn.orderSign,
      fun q => Lean.toJson #[q.num, (q.den : Int)]⟩
  | depth + 1 =>
    let base := coefficients depth
    letI := base.field
    letI := base.equality
    { Carrier := RationalFn base.Carrier
      field := inferInstance
      equality := inferInstance
      sign := OrderedFn.Infinitesimal.sign base.sign
      encode := fun f => Lean.Json.mkObj [
        ("num", Lean.Json.arr (f.num.toArray.map base.encode)),
        ("den", Lean.Json.arr (f.den.toArray.map base.encode))] }

/-- Capture the actual typed coefficient and sign operation in the closure;
its complete literal encoding, rather than the closure, binds the input hash. -/
structure Input where
  depth : Nat
  literal : String
  evaluate : Unit → Int

instance : Hashable Input where
  hash i := hash (i.depth, i.literal)

/-- At positive depth the input is the newest infinitesimal. Every selected
numerator/denominator coefficient below that level is exactly one. -/
def input (depth : Nat) : Input :=
  match depth with
  | 0 => ⟨0, "[1,1]", fun _ => OrderedFn.orderSign (1 : Rat)⟩
  | baseDepth + 1 =>
    let base := coefficients baseDepth
    letI := base.field
    letI := base.equality
    let epsilon : RationalFn base.Carrier := RationalFn.X
    let literal := (Lean.Json.mkObj [
      ("num", Lean.Json.arr (epsilon.num.toArray.map base.encode)),
      ("den", Lean.Json.arr (epsilon.den.toArray.map base.encode))]).compress
    ⟨depth, literal, fun _ => OrderedFn.Infinitesimal.sign base.sign epsilon⟩

/-- Only the existing coefficient sign is timed. Field and value construction,
coefficient serialization and input hashing happen during preparation. -/
@[noinline] def runSign (i : Input) : Int := i.evaluate ()

def depths : Array Nat := #[2, 4, 6, 8, 10, 12]

/-- Source-derived constructor recurrence: at one level, zero builds two
lower zeros and one lower one; one builds two of each. This counts fixed-size
constructor work, not just the rational signs at the leaves. -/
def numeralCosts : Nat → Nat × Nat
  | 0 => (1, 1)
  | depth + 1 =>
    let (zeros, ones) := numeralCosts depth
    (2*zeros + ones + 1, 2*zeros + 2*ones + 1)

def numeralCost (depth : Nat) : Nat := (numeralCosts depth).1

/- Declared cost-model: Θ((2+√2)^d) for the actual compiled coefficient sign.
The field dictionary rebuilds numerals during zero checks and lowest-coefficient
scans. Constructor costs follow the recurrence above, whose dominant eigenvalue
is 2+√2. The 2^d lower sign calls and the top zero-equality scan are cheaper.
The model counts actual constant construction, not arbitrary arithmetic, BKR
production or lower-level proof-certificate dependencies. -/
setup_benchmark runSign d => numeralCost d
  with prep := input
  where {
    paramSchedule := .custom depths
    paramFloor := 2
    paramCeiling := 12
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 30
  }

/-- Validate each result and retain its complete recursive coefficient input.
These are input checks, not scientific timing observations. -/
def inspect : IO UInt32 := do
  for depth in depths do
    let i := input depth
    unless runSign i == 1 do
      throw (IO.userError s!"positive infinitesimal sign failed at depth {depth}")
    IO.println <| (Lean.Json.mkObj [
      ("depth", Lean.toJson depth), ("coefficient", Lean.toJson i.literal),
      ("encodedBytes", Lean.toJson i.literal.utf8ByteSize),
      ("predictedBaseSigns", Lean.toJson (2^depth)),
      ("resultHash", Lean.toJson (hash (runSign i)).toNat)]).compress
  return 0

end Hex.SignDetBench.NestedSigns
