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
The HexPolyZ denominator-clearing stage measures the rational/integer denominator clearing
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
operations. For even m=2r the quotient is
`2 * sum (j=0..r-1) 2^j X^(2(r-j)-1)`: its nonzero coefficients occupy
r(r+3)/2 bits. Big-by-small arithmetic in the recurrence and replay therefore
costs Θ(m²) bits, including materialization of that quotient. The corrected
integer and rational query-degree registrations use multiword coefficients.

Input preparation and metadata collection are outside timed bodies. Output
hashes include actual coefficients and certificate scalars, not just dimensions.
These tracks do not supply the missing root-sum theorem or extension-depth
proof evidence required for complete Phase 4.
-/

/-! Untimed observations of the actual generic kernel instantiated with integer
coefficients. Instrumentation is confined to this benchmark executable; it is
not proof evidence or a replacement polynomial algorithm. -/
namespace Hex.SturmDiagnostics
open Hex DensePoly

structure Counters where
  add : Nat := 0
  sub : Nat := 0
  mul : Nat := 0
  neg : Nat := 0
  sign : Nat := 0
  peakBits : Nat := 0
  normalizationCalls : Nat := 0
  normalizationCoefficients : Nat := 0
  normalizationBits : Nat := 0
  deriving Lean.ToJson, Inhabited

initialize counters : IO.Ref Counters ← IO.mkRef {}

def bits (z : Int) : Nat := if z = 0 then 0 else z.natAbs.log2 + 1

structure Coeff where
  value : Int
  deriving DecidableEq

instance : OfNat Coeff n := ⟨⟨n⟩⟩
instance : NatCast Coeff := ⟨fun n => ⟨n⟩⟩

@[noinline] unsafe def observe (kind : Nat) (a b result : Int) : Coeff := unsafeBaseIO do
  counters.modify fun c => { c with
    add := c.add + if kind = 0 then 1 else 0
    sub := c.sub + if kind = 1 then 1 else 0
    mul := c.mul + if kind = 2 then 1 else 0
    neg := c.neg + if kind = 3 then 1 else 0
    peakBits := max c.peakBits (max (bits a) (max (bits b) (bits result))) }
  return ⟨result⟩

unsafe instance : Add Coeff := ⟨fun a b => observe 0 a.value b.value (a.value + b.value)⟩
unsafe instance : Sub Coeff := ⟨fun a b => observe 1 a.value b.value (a.value - b.value)⟩
unsafe instance : Mul Coeff := ⟨fun a b => observe 2 a.value b.value (a.value * b.value)⟩
unsafe instance : Neg Coeff := ⟨fun a => observe 3 a.value 0 (-a.value)⟩

@[noinline] unsafe def sign (a : Coeff) : Int := unsafeBaseIO do
  counters.modify fun c => { c with sign := c.sign + 1, peakBits := max c.peakBits (bits a.value) }
  return a.value.sign

def wrap (p : ZPoly) : DensePoly Coeff := ofCoeffs (p.toArray.map fun z => ⟨z⟩)
def unwrap (p : DensePoly Coeff) : ZPoly := ofCoeffs (p.toArray.map Coeff.value)

/-- Delegates to the production integer normalizer. The gcd-input volume is
recorded separately from ring-operation counts; gcd internals are not timed or
counted as ring operations. Its two content folds each visit every coefficient. -/
@[noinline] unsafe def normalize (p : DensePoly Coeff) : Coeff × DensePoly Coeff := unsafeBaseIO do
  let z := unwrap p
  let maxBits := z.toArray.foldl (fun n c => max n (bits c)) 0
  counters.modify fun c => { c with
    normalizationCalls := c.normalizationCalls + 1
    normalizationCoefficients := c.normalizationCoefficients + 2 * z.size
    normalizationBits := c.normalizationBits + 2 * z.toArray.foldl (fun n c => n + bits c) 0
    peakBits := max c.peakBits maxBits }
  let (scale, q) := ZPoly.normalizeContent z
  return (⟨scale⟩, wrap q)

unsafe def endpoints : EndpointSigns Coeff Int where
  compare a b := (a - b).sign
  evalSign p a := sign (p.eval ⟨a⟩)

/-- Compare an instrumented call with the production result before recording it. -/
unsafe def inspect (family : String) (parameter : Nat) (p f : ZPoly) (a b : Int) : IO Lean.Json := do
  let some expected := TarskiCertificate.certify Int.sign EndpointSigns.intDyadic
      ZPoly.normalizeContent () p f (.finite (Dyadic.ofInt a)) (.finite (Dyadic.ofInt b))
    | throw (IO.userError "invalid diagnostic domain")
  counters.set {}
  let some cert := TarskiCertificate.certify sign endpoints normalize () (wrap p) (wrap f)
      (.finite a) (.finite b) | throw (IO.userError "instrumented domain mismatch")
  unless cert.value == expected.value && cert.remainders.chain.map unwrap == expected.remainders.chain do
    throw (IO.userError "instrumented producer differs")
  let producer ← counters.get
  counters.set {}
  unless TarskiCertificate.check sign endpoints () (wrap p) (wrap f) (.finite a) (.finite b) cert.value cert do
    throw (IO.userError "instrumented certificate rejected")
  let replay ← counters.get
  return Lean.Json.mkObj [
    ("family", Lean.toJson family), ("parameter", Lean.toJson parameter),
    ("degreeP", Lean.toJson p.natDegree), ("degreeF", Lean.toJson f.natDegree),
    ("chainLength", Lean.toJson cert.remainders.chain.size),
    ("endpointBits", Lean.toJson (max (bits a) (bits b))),
    ("value", Lean.toJson cert.value), ("producer", Lean.toJson producer), ("replay", Lean.toJson replay)]

end Hex.SturmDiagnostics

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

def certHash (c : IntTarskiCertificate) : UInt64 :=
  hash (c.head, c.queryPoly, c.lowerSigns, c.upperSigns, c.lowerVariations,
    c.upperVariations, c.value, chainHash c.squarefree, chainHash c.remainders)

structure Input where
  p : ZPoly
  f : ZPoly
  rp : DensePoly Rat
  rf : DensePoly Rat
  cert : Option IntTarskiCertificate

instance : Hashable Input where
  hash i := hash (i.p, i.f, i.rp, i.rf, i.cert.map certHash)

def input (p f : ZPoly) : Input :=
  ⟨p, f, ZPoly.toRatPoly p, ZPoly.toRatPoly f, IntTarskiCertificate.certify p f interval⟩

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
  chainHash (SignedRemainderChain.build Int.sign ZPoly.normalizeContent i.p i.f)

def runEndpoints (i : Input) : Array Int × Array Int :=
  match i.cert with
  | none => (#[], #[])
  | some c => (TarskiCertificate.signs Int.sign EndpointSigns.intDyadic c.remainders.chain (.finite interval.lower),
      TarskiCertificate.signs Int.sign EndpointSigns.intDyadic c.remainders.chain (.finite interval.upper))

def runSigns (i : Input) : Array (Array Int) :=
  match i.cert with
  | none => #[]
  | some c => c.remainders.chain.map (fun p => p.toArray.map Int.sign)

def runReplay (i : Input) : Bool :=
  match i.cert with
  | none => false
  | some c => IntTarskiCertificate.check i.p i.f interval c.value c

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
-- Declared cost-model: cubic normalization-iteration work, with bounded
-- limb counts on this ladder. Total binary work remains Θ(n⁴); this declaration
-- does not extend to an unbounded-degree bit-time claim. The source count and
-- cost-model derivation is in reports/sturm-bit-cost-models.md.
setup_benchmark runReplay n => n ^ 3
  with prep := degreeInput
  where {
    paramSchedule := .custom #[256, 512, 1024, 2048]
    paramFloor := 256
    paramCeiling := 2048
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 1800
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
-- Declared cost-model: Θ(m²) bit work: the producer materializes the quadratic-bit initial quotient; the remaining chain has fixed degree.
setup_benchmark runIntegerHigh m => m ^ 2
  with prep := queryInput
  where {
    paramSchedule := .custom #[131072, 262144, 524288, 1048576]
    paramFloor := 131072
    paramCeiling := 1048576
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 120
  }
-- Declared cost-model: Θ(m²) bit work: fixed-quadratic rational division
-- constructs the same growing integer numerators; denominators remain one.
setup_benchmark runRationalHigh m => m ^ 2
  with prep := queryInput
  where {
    paramSchedule := .custom #[131072, 262144, 524288, 1048576]
    paramFloor := 131072
    paramCeiling := 1048576
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 120
  }
-- Declared cost-model: Θ(m²) bit work: O(m) big-by-small recurrence operations on growing O(m)-bit coefficients; the quotient itself has Θ(m²) bits.
setup_benchmark runInitialHigh m => m ^ 2
  with prep := queryInput
  where {
    paramSchedule := .custom #[131072, 262144, 524288, 1048576]
    paramFloor := 131072
    paramCeiling := 1048576
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 120
  }
-- Declared cost-model: Θ(m²) bit work: convolution of the Θ(m²)-bit supplied quotient with a fixed quadratic, plus fixed-degree checks.
setup_benchmark runReplayHigh m => m ^ 2
  with prep := queryInput
  where {
    paramSchedule := .custom #[131072, 262144, 524288, 1048576]
    paramFloor := 131072
    paramCeiling := 1048576
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 120
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

private def certJson (c : IntTarskiCertificate) : Lean.Json :=
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
      Sturm.check Sturm.orderSign () i.rp i.rf (.finite (-2)) (.finite 2) expected ratCert do
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


structure AxisInput where
  family : String
  parameter : Nat
  p : ZPoly
  f : ZPoly
  a : Int
  b : Int

private def axisInputs : Array AxisInput := Id.run do
  let mut inputs := #[]
  for n in #[8, 32, 128, 512, 2048] do
    inputs := inputs.push ⟨"coefficient-bits", n, ofCoeffs #[-2, 0, 2 ^ n + 1],
      ofCoeffs #[1, 1], -2, 2⟩
  for n in #[2, 8, 32, 128, 512] do
    inputs := inputs.push ⟨"endpoint-bits", n, chebyshev 8, 1, -(2 ^ n), 2 ^ n⟩
  let x : ZPoly := ofCoeffs #[0, 1]
  let p := natPow x 32 - 1
  for n in #[1, 2, 4, 8, 12, 16, 24, 30] do
    inputs := inputs.push ⟨"chain-length", n, p, p * natPow x 8 + x * chebyshev n, -2, 2⟩
  return inputs

/-- Fixed trial-major observations for independent size axes. These report raw
costs, not a fitted asymptotic verdict. Input conversion and certificates are
prepared outside the measured calls; each call consumes its actual result. -/
unsafe def axes (control : Bool := false) : IO UInt32 := do
  let mut fixtures := #[]
  let inputs := if control then
    #[8, 32, 128, 512, 2048].map fun n =>
      (⟨"coefficient-control", n, ofCoeffs #[-2, 0, 2 ^ n + 1],
        ofCoeffs #[2, 1], -2, 2⟩ : AxisInput)
    else axisInputs
  for i in inputs do
    let a := Endpoint.finite (Dyadic.ofInt i.a)
    let b := Endpoint.finite (Dyadic.ofInt i.b)
    let some c := TarskiCertificate.certify Int.sign EndpointSigns.intDyadic
        ZPoly.normalizeContent () i.p i.f a b | throw (IO.userError "invalid axis domain")
    let rp := ZPoly.toRatPoly i.p
    let rf := ZPoly.toRatPoly i.f
    let ra := Endpoint.finite (i.a : Rat)
    let rb := Endpoint.finite (i.b : Rat)
    unless Sturm.query Sturm.orderSign rp rf ra rb == some c.value do
      throw (IO.userError "axis backends disagree")
    IO.println <| (Lean.Json.mkObj [("kind", Lean.toJson "fixture"),
      ("family", Lean.toJson i.family), ("parameter", Lean.toJson i.parameter),
      ("certificate", certJson c), ("certificateBytes", Lean.toJson (certJson c).compress.utf8ByteSize),
      ("diagnostics", ← SturmDiagnostics.inspect i.family i.parameter i.p i.f i.a i.b)]).compress
    fixtures := fixtures.push (i, c, rp, rf, ra, rb, a, b)
  let some first := fixtures[0]? | throw (IO.userError "empty axis fixtures")
  let inputRef ← IO.mkRef first
  let sink ← IO.mkRef (0 : UInt64)
  for trial in [:4] do
    for fixture in fixtures do
      inputRef.set fixture
      let stages := if trial % 2 = 0 then
        #["integer", "rational", "domain", "initial", "chain", "endpoints", "signs", "replay"]
        else #["rational", "integer", "domain", "initial", "chain", "endpoints", "signs", "replay"]
      for stage in stages do
        let start ← IO.monoNanosNow
        for _ in [:32] do
          let (i, c, rp, rf, ra, rb, a, b) ← inputRef.get
          let result := match stage with
            | "integer" => hash (TarskiCertificate.query Int.sign EndpointSigns.intDyadic
                ZPoly.normalizeContent i.p i.f a b)
            | "rational" => hash (Sturm.query Sturm.orderSign rp rf ra rb)
            | "domain" => hash (Sturm.prepare Sturm.orderSign rp ra rb).isSome
            | "initial" => let r := positivePseudoDiv Int.sign (i.f * i.p.derivative) i.p
                           hash (r.multiplier, r.quotient, r.remainder)
            | "chain" => chainHash (SignedRemainderChain.build Int.sign ZPoly.normalizeContent i.p i.f)
            | "endpoints" => hash (TarskiCertificate.signs Int.sign EndpointSigns.intDyadic c.remainders.chain a,
                TarskiCertificate.signs Int.sign EndpointSigns.intDyadic c.remainders.chain b)
            | "signs" => hash (c.remainders.chain.map fun p => p.toArray.map Int.sign)
            | _ => hash (TarskiCertificate.check Int.sign EndpointSigns.intDyadic () i.p i.f a b c.value c)
          sink.modify (· + result)
        let elapsed := (← IO.monoNanosNow) - start
        IO.println <| (Lean.Json.mkObj [("kind", Lean.toJson "sample"),
          ("trial", Lean.toJson trial), ("family", Lean.toJson fixture.1.family),
          ("parameter", Lean.toJson fixture.1.parameter), ("stage", Lean.toJson stage),
          ("repetitions", Lean.toJson (32 : Nat)), ("nanos", Lean.toJson elapsed),
          ("sink", Lean.toJson (← sink.get))]).compress
  return 0

unsafe def diagnostics : IO UInt32 := do
  for n in #[8, 16, 32, 64, 128] do
    IO.println (← SturmDiagnostics.inspect "head-degree" n (chebyshev n) 1 (-2) 2).compress
  for n in #[16, 32, 64, 128, 256, 512, 1024] do
    let i := queryInput n
    IO.println (← SturmDiagnostics.inspect "query-degree" n i.p i.f (-2) 2).compress
  return 0

end Hex.SturmBench

unsafe def main (args : List String) : IO UInt32 :=
  if args == ["diagnostics"] then Hex.SturmBench.diagnostics else
  if args == ["coefficient-control"] then Hex.SturmBench.axes true else
  if args == ["axes"] then Hex.SturmBench.axes false else
  if args == ["inspect"] then Hex.SturmBench.inspect else LeanBench.Cli.dispatch args
