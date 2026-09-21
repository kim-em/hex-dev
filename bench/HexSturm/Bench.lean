/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSturm
import LeanBench
import Lean.Data.Json

/-!
Shared query stage measurements and rational/integer comparison.
Computational performance owners: `HexRealRoots`, `HexSturm`, `HexPolyZ`.
The HexPolyZ denominator-clearing stage measures the rational/integer adapter
used by the Sturm frontend; its arithmetic remains owned by HexPolyZ.

The degree family is `T_n` with query `1` on `(-2,2)`. Its derivative signed
chain is normal, with one degree lost per step. A division between consecutive
degrees makes two cancellations, each visiting O(n) stored coefficients; the
whole chain and both endpoint Horner passes therefore take O(n²) coefficient
operations. This is a family-specific bound within the SPEC's conservative
O(n³) query bound. `inspect` records stored certificate sizes and coefficient
bit lengths. Its 60-bit bound does not bound intermediate arithmetic or imply
that Lean stores every coefficient unboxed; wall-time consistency with the
coefficient-operation model must be checked separately.

The query-degree family fixes `P=x²-2` and uses `F=x^m+1`. Initial reduction
uses the shared dynamic coefficient recurrence with O(m) entries and at most
two correction terms per entry. It takes O(m) coefficient operations. Replay
multiplies a degree-O(m) quotient by the fixed quadratic and also takes O(m)
operations. The returned integer coefficients have O(m) bits and stay
below 64 bits on the declared ladder; neither intermediate bit sizes nor a
uniform bit-complexity bound follow from this observation.

Input preparation and metadata collection are outside timed bodies. Output
hashes include actual coefficients and certificate scalars, not just dimensions.
These tracks do not supply the missing root-sum theorem or extension-depth
proof evidence required for complete Phase 4.
-/

namespace Hex.SturmBench

open Hex DensePoly

instance [Hashable R] [Zero R] [DecidableEq R] : Hashable (DensePoly R) where
  hash p := hash p.toArray

def interval : DyadicInterval := ⟨Dyadic.ofInt (-2), Dyadic.ofInt 2, by decide⟩

def chebyshev (n : Nat) : ZPoly :=
  let twoX : ZPoly := ofCoeffs #[0, 2]
  let rec go : Nat → ZPoly → ZPoly → ZPoly
    | 0, prev, _ => prev
    | k + 1, prev, cur => go k cur (twoX * cur - prev)
  go n 1 (ofCoeffs #[0, 1])

def chainHash (c : SignedRemainderChain Int) : UInt64 :=
  hash (c.chain, c.degrees, c.initial.leftScale, c.initial.quotient,
    c.initial.rightScale, c.steps.map (fun s => (s.leftScale, s.quotient, s.rightScale)), c.terminal)

def certHash (c : TarskiReplay) : UInt64 :=
  hash (c.head, c.queryPoly, c.lowerSigns, c.upperSigns, c.lowerVariations,
    c.upperVariations, c.value, chainHash c.squarefree, chainHash c.remainders)

structure Input where
  p : ZPoly
  f : ZPoly
  rp : DensePoly Rat
  rf : DensePoly Rat
  cert : Option TarskiReplay

instance : Hashable Input where
  hash i := hash (i.p, i.f, i.rp, i.rf, i.cert.map certHash)

def input (p f : ZPoly) : Input :=
  ⟨p, f, ZPoly.toRatPoly p, ZPoly.toRatPoly f, TarskiReplay.certify p f interval⟩

def degreeInput (n : Nat) : Input := input (chebyshev n) 1

def queryInput (n : Nat) : Input :=
  input (ofCoeffs #[-2, 0, 1]) (ofCoeffs ((Array.replicate (n + 1) (0 : Int)).set! 0 1 |>.set! n 1))

def runInteger (i : Input) : Option Int := ZPoly.tarskiQuery i.p i.f interval

def runRational (i : Input) : Option Int :=
  Sturm.query Sturm.orderSign i.rp i.rf (.finite (-2)) (.finite 2)

def runDomain (i : Input) : Bool :=
  (Sturm.prepare Sturm.orderSign i.rp (.finite (-2)) (.finite 2)).isSome

def runInitial (i : Input) : UInt64 :=
  let r := positivePseudoDiv Int.sign (i.f * i.p.derivative) i.p
  hash (r.multiplier, r.quotient, r.remainder)

def runChain (i : Input) : UInt64 :=
  chainHash (SignedRemainderChain.build Int.sign ZPoly.queryNormalize i.p i.f)

def runEndpoints (i : Input) : Array Int × Array Int :=
  match i.cert with
  | none => (#[], #[])
  | some c => (QueryReplay.signs Int.sign ZPoly.queryAdapter c.remainders.chain (.finite interval.lower),
      QueryReplay.signs Int.sign ZPoly.queryAdapter c.remainders.chain (.finite interval.upper))

def runSigns (i : Input) : Array (Array Int) :=
  match i.cert with
  | none => #[]
  | some c => c.remainders.chain.map (fun p => p.toArray.map Int.sign)

def runReplay (i : Input) : Bool :=
  match i.cert with
  | none => false
  | some c => TarskiReplay.check i.p i.f interval c.value c

def runClearing (i : Input) : Nat × ZPoly :=
  ZPoly.clearDenominators (scale (1 / 6 : Rat) i.rp)

-- Distinct names retain each input-family registration's declared model.
def runIntegerHigh := runInteger
def runRationalHigh := runRational
def runInitialHigh := runInitial
def runReplayHigh := runReplay

-- Declared cost-model: O(n²), two normal derivative chains and endpoint Horner passes.
setup_benchmark runInteger n => n ^ 2
  with prep := degreeInput
  where {
    paramSchedule := .custom #[8, 10, 12, 16, 20]
    paramFloor := 8
    paramCeiling := 20
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(n²), the same normal chains with positive field normalization.
setup_benchmark runRational n => n ^ 2
  with prep := degreeInput
  where {
    paramSchedule := .custom #[8, 10, 12, 16, 20]
    paramFloor := 8
    paramCeiling := 20
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(n²), one normal derivative chain for squarefreeness.
setup_benchmark runDomain n => n ^ 2
  with prep := degreeInput
  where {
    paramSchedule := .custom #[8, 10, 12, 16, 20]
    paramFloor := 8
    paramCeiling := 20
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(n), F=1 needs no initial cancellation; derivative and hashing visit n coefficients.
setup_benchmark runInitial n => n
  with prep := degreeInput
  where {
    paramSchedule := .custom #[8, 10, 12, 16, 20]
    paramFloor := 8
    paramCeiling := 20
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(n²), two cancellations per normal-chain step; coefficient hashing is O(n²).
setup_benchmark runChain n => n ^ 2
  with prep := degreeInput
  where {
    paramSchedule := .custom #[8, 10, 12, 16, 20]
    paramFloor := 8
    paramCeiling := 20
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(n²), the sum of normal-chain entry lengths, at two fixed endpoints.
setup_benchmark runEndpoints n => n ^ 2
  with prep := degreeInput
  where {
    paramSchedule := .custom #[8, 10, 12, 16, 20]
    paramFloor := 8
    paramCeiling := 20
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(n²), one sign and one hash visit per stored chain coefficient.
setup_benchmark runSigns n => n ^ 2
  with prep := degreeInput
  where {
    paramSchedule := .custom #[8, 10, 12, 16, 20]
    paramFloor := 8
    paramCeiling := 20
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(n²), normal-chain quotients are linear and every recurrence visits O(n) coefficients.
setup_benchmark runReplay n => n ^ 2
  with prep := degreeInput
  where {
    paramSchedule := .custom #[8, 10, 12, 16, 20]
    paramFloor := 8
    paramCeiling := 20
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(n), a fixed denominator (six) bounds each scalar lcm and division.
setup_benchmark runClearing n => n
  with prep := degreeInput
  where {
    paramSchedule := .custom #[8, 10, 12, 16, 20]
    paramFloor := 8
    paramCeiling := 20
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(m), initial reduction has at most two correction terms per entry.
setup_benchmark runIntegerHigh m => m
  with prep := queryInput
  where {
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    paramFloor := 16
    paramCeiling := 96
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(m), the same recurrence with bounded-word rational coefficients.
setup_benchmark runRationalHigh m => m
  with prep := queryInput
  where {
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    paramFloor := 16
    paramCeiling := 96
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(m), the shared recurrence has at most two correction terms per entry.
setup_benchmark runInitialHigh m => m
  with prep := queryInput
  where {
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    paramFloor := 16
    paramCeiling := 96
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }
-- Declared cost-model: O(m), replay multiplies its supplied quotient by a fixed quadratic.
setup_benchmark runReplayHigh m => m
  with prep := queryInput
  where {
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    paramFloor := 16
    paramCeiling := 96
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }

private def intBits (z : Int) : Nat := if z = 0 then 0 else z.natAbs.log2 + 1
private def ratBits (q : Rat) : Nat := max (intBits q.num) (q.den.log2 + 1)

private def polyBits [Zero D] [DecidableEq D] (bits : D → Nat) (p : DensePoly D) : Nat :=
  p.toArray.foldl (fun m c => max m (bits c)) 0

private def chainBits [Zero D] [DecidableEq D] (bits : D → Nat) (c : SignedRemainderChain D) : Nat :=
  let initial := max (bits c.initial.leftScale)
    (max (bits c.initial.rightScale) (polyBits bits c.initial.quotient))
  let entries := c.chain.foldl (fun m p => max m (polyBits bits p)) initial
  let steps := c.steps.foldl (fun m s => max m
    (max (bits s.leftScale) (max (bits s.rightScale) (polyBits bits s.quotient)))) entries
  match c.terminal with
  | none => steps
  | some (u, q) => max steps (max (bits u) (polyBits bits q))

private def chainJson (c : SignedRemainderChain Int) : Lean.Json :=
  Lean.Json.mkObj [
    ("chain", Lean.toJson (c.chain.map DensePoly.toArray)),
    ("degrees", Lean.toJson c.degrees),
    ("initial", Lean.toJson (c.initial.leftScale, c.initial.quotient.toArray, c.initial.rightScale)),
    ("steps", Lean.toJson (c.steps.map (fun s => (s.leftScale, s.quotient.toArray, s.rightScale)))),
    ("terminal", Lean.toJson (c.terminal.map (fun (u, q) => (u, q.toArray))))]

private def endpointJson : Endpoint Dyadic → Lean.Json
  | .negInf => Lean.toJson "negInf"
  | .posInf => Lean.toJson "posInf"
  | .finite .zero => Lean.toJson ((0 : Int), (0 : Int))
  | .finite (.ofOdd n k _) => Lean.toJson (n, k)

private def certJson (c : TarskiReplay) : Lean.Json :=
  Lean.Json.mkObj [
    ("context", Lean.Json.null), ("head", Lean.toJson c.head.toArray),
    ("query", Lean.toJson c.queryPoly.toArray), ("lower", endpointJson c.lower),
    ("upper", endpointJson c.upper), ("squarefree", chainJson c.squarefree),
    ("remainders", chainJson c.remainders), ("lowerSigns", Lean.toJson c.lowerSigns),
    ("upperSigns", Lean.toJson c.upperSigns), ("lowerVariations", Lean.toJson c.lowerVariations),
    ("upperVariations", Lean.toJson c.upperVariations), ("value", Lean.toJson c.value)]

private def inspectCase (family : String) (n : Nat) (i : Input) (expected : Int) : IO Unit := do
  let some cert := i.cert | throw (IO.userError s!"{family}/{n}: invalid integer domain")
  let some ratCert := Sturm.certify Sturm.orderSign () i.rp i.rf (.finite (-2)) (.finite 2)
    | throw (IO.userError s!"{family}/{n}: invalid rational domain")
  unless runInteger i == some expected && runRational i == some expected && runReplay i &&
      Sturm.Replay.check Sturm.orderSign () i.rp i.rf (.finite (-2)) (.finite 2) expected ratCert do
    throw (IO.userError s!"{family}/{n}: query or replay disagreement")
  let integerBits := max (chainBits intBits cert.squarefree) (chainBits intBits cert.remainders)
  let rationalBits := max (chainBits ratBits ratCert.squarefree) (chainBits ratBits ratCert.remainders)
  if integerBits > 60 || rationalBits > 60 then
    throw (IO.userError s!"{family}/{n}: exceeds declared small-coefficient regime ({integerBits}, {rationalBits})")
  IO.println <| (Lean.Json.mkObj [
    ("family", Lean.toJson family), ("parameter", Lean.toJson n),
    ("degreeP", Lean.toJson i.p.natDegree), ("degreeF", Lean.toJson i.f.natDegree),
    ("chainLength", Lean.toJson cert.remainders.chain.size),
    ("chainDegrees", Lean.toJson cert.remainders.degrees),
    ("integerCoefficientBits", Lean.toJson integerBits),
    ("rationalCoefficientBits", Lean.toJson rationalBits),
    ("certificateBytes", Lean.toJson (certJson cert).compress.utf8ByteSize),
    ("certificate", certJson cert)]).compress

def inspect : IO UInt32 := do
  for n in #[8, 10, 12, 16, 20] do
    inspectCase "head-degree" n (degreeInput n) n
  for n in #[16, 24, 32, 48, 64, 96] do
    inspectCase "query-degree" n (queryInput n) 2
  return 0

end Hex.SturmBench

def main (args : List String) : IO UInt32 :=
  if args == ["inspect"] then Hex.SturmBench.inspect else LeanBench.Cli.dispatch args
