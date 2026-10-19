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
its complete literal encoding, rather than the closure, supplies Hashable input. -/
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

def depths : Array Nat := #[4, 6, 9, 12]

/-- The sign visits two predecessor signs at each level. Direct, shared
unit constructors cost O(j) at level j; summing that work over the sign tree
is O(2^d). The top structural comparison of two nested zeros also costs O(2^d).
No arbitrary nested arithmetic is covered by this model. -/
def signCost (depth : Nat) : Nat := 2^depth

/- Independently derived timing model: Θ(2^d). In the ordinary upstream field,
zero has an empty numerator and direct unit denominator; one shares the same
direct polynomial between its numerator and denominator. Their construction
costs are u(j)=u(j-1)+O(1), z(j)=u(j-1)+O(1), hence O(j).
Below the top level S(j)=2*S(j-1)+O(j). Its geometric sum is Θ(2^j).
The top zero-coefficient equality traverses an unshared logical tree of at most
Θ(2^d) coefficient pairs and does not increase that bound. -/
setup_benchmark runSign d => signCost d
  with prep := input
  where {
    paramSchedule := .custom depths
    paramFloor := 4
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
