/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.BenchHash
import LeanBench

/-!
Benchmark registrations for the Mathlib-free compiled HexRCF decision and
certificate-replay pipeline.

All fixture construction is hoisted through `with prep := ...`. In particular,
the replay targets time only `Certificate.replay?` on already accepted `.cells`
certificates; they never rebuild witnesses in the timed region.
-/

namespace Hex.RCFBench

open Hex Hex.RCF

/-! ## Controlled fixture families -/

private def one : ZPoly := DensePoly.ofCoeffs #[(1 : Int)]

private def x : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]

private def linearFactor (root : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-root, 1]

/-- `prod_{i=1}^k (x-i)`, with exactly `k` unit-separated integer roots. -/
def wellSeparated (k : Nat) : ZPoly :=
  (List.range k).foldl
    (fun acc i => acc * linearFactor (Int.ofNat (i + 1))) one

private def positiveParam (n : Nat) : Nat := max 1 n

/-- Ceiling base-2 logarithm, clamped to one, used by the bit-cost models. -/
def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then 1 else (n - 1).log2 + 1

def prepDecisionCarrierDegree (n : Nat) : Sentence :=
  let p := wellSeparated (positiveParam n)
  .existsReal (.atom ⟨p, .eq⟩)

def runDecisionCarrierDegree (sentence : Sentence) : Option Bool :=
  Hex.RCF.decide sentence

def prepDedupRepeated (n : Nat) : List ZPoly :=
  List.replicate (positiveParam n) x

private def distinctPoly (i : Nat) : ZPoly :=
  DensePoly.ofCoeffs #[Int.ofNat (1024 + i), 1, 1]

def prepDedupDistinct (n : Nat) : List ZPoly :=
  (List.range (positiveParam n)).map distinctPoly

def runDedupRepeated (polys : List ZPoly) : List ZPoly :=
  dedupPolys polys

def runDedupDistinct (polys : List ZPoly) : List ZPoly :=
  dedupPolys polys

inductive CommonCase where
  | coprime
  | shared
  | repeated

structure CommonInput where
  carrier : ZPoly
  atoms : List ZPoly

instance : Hashable CommonInput where
  hash input := hash (input.carrier, input.atoms)

private def commonAtom (kind : CommonCase) (i : Nat) : ZPoly :=
  match kind with
  | .coprime => linearFactor (Int.ofNat (1024 + i))
  | .shared => DensePoly.ofCoeffs #[(0 : Int), Int.ofNat (1024 + i)]
  | .repeated => x

private def prepCommon (kind : CommonCase) (n : Nat) : CommonInput :=
  { carrier := x
    atoms := (List.range (positiveParam n)).map (commonAtom kind) }

def prepCommonCoprime : Nat → CommonInput := prepCommon .coprime
def prepCommonShared : Nat → CommonInput := prepCommon .shared
def prepCommonRepeated : Nat → CommonInput := prepCommon .repeated

private def buildCommonBatch (carrier : ZPoly) :
    List ZPoly → Option (List CommonRootCert)
  | [] => some []
  | atom :: atoms => do
      let cert ← buildCommonRoot? atom carrier
      let rest ← buildCommonBatch carrier atoms
      pure (cert :: rest)

def runCommonCoprime (input : CommonInput) : Option (List CommonRootCert) :=
  buildCommonBatch input.carrier input.atoms

def runCommonShared (input : CommonInput) : Option (List CommonRootCert) :=
  buildCommonBatch input.carrier input.atoms

def runCommonRepeated (input : CommonInput) : Option (List CommonRootCert) :=
  buildCommonBatch input.carrier input.atoms

structure SeparationInput where
  carrier : ZPoly
  replay : SturmReplay
  raw : IsolationCert

instance : Hashable SeparationInput where
  hash input := hash (input.carrier, input.replay, input.raw)

private def closePairCarrier (b : Nat) : ZPoly :=
  DensePoly.ofCoeffs #[(-1 : Int), 0, (2 : Int) ^ (2 * b)]

private def touchingPair : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-1)) 0 (by decide),
  DyadicInterval.mk 0 (Dyadic.ofInt 1) (by decide)]⟩

def prepSeparationDepth (n : Nat) : Option SeparationInput :=
  let carrier := closePairCarrier (positiveParam n)
  (buildSturmReplay? carrier).map fun replay =>
    { carrier, replay, raw := touchingPair }

def runSeparationDepth (input : Option SeparationInput) :
    Option IsolationCert := do
  let data ← input
  Separation.separate? data.carrier data.replay data.raw

structure ReplayInput where
  sentence : Sentence
  certificate : Certificate

instance : Hashable ReplayInput where
  hash input := hash (input.sentence, input.certificate)

private def acceptedCells (sentence : Sentence) : Option ReplayInput := do
  let result ← build? sentence
  if result.certificate.check sentence then
    match result.certificate with
    | .cells _ => some { sentence, certificate := result.certificate }
    | _ => none
  else none

def prepReplayCells (n : Nat) : Option ReplayInput :=
  let p := wellSeparated (positiveParam n)
  acceptedCells (.existsReal (.atom ⟨p, .eq⟩))

private def andAll : List Formula → Formula
  | [] => .tt
  | φ :: formulas => .and φ (andAll formulas)

def prepReplaySigns (n : Nat) : Option ReplayInput :=
  let formulas := (List.range (positiveParam n)).map fun i =>
    Formula.atom ⟨DensePoly.ofCoeffs #[(0 : Int), Int.ofNat (1024 + i)], .eq⟩
  acceptedCells (.existsReal (andAll formulas))

private def addLiteralNodes : Nat → Formula → Formula
  | 0, φ => φ
  | n + 1, φ =>
      if n % 2 = 0 then addLiteralNodes n (.and φ .tt)
      else addLiteralNodes n (.or φ .ff)

def prepReplayFormula (n : Nat) : Option ReplayInput :=
  let base := Formula.atom ⟨x, .eq⟩
  acceptedCells (.existsReal (addLiteralNodes n base))

private def replayPrepared (input : Option ReplayInput) : Option Bool := do
  let data ← input
  data.certificate.replay? data.sentence

def runReplayCells : Option ReplayInput → Option Bool := replayPrepared
def runReplaySigns : Option ReplayInput → Option Bool := replayPrepared
def runReplayFormula : Option ReplayInput → Option Bool := replayPrepared

/-! ## Parametric registrations -/

/-
The carrier has `n` active intervals over `n` Descartes levels, each dominated
by a quadratic Möbius transform. The other fixed-shape decision phases are no
worse on this family, giving `O(n^4)` exact-integer operations.
-/
setup_benchmark runDecisionCarrierDegree n => n ^ 4
  with prep := prepDecisionCarrierDegree
  where {
    paramFloor := 16
    paramCeiling := 32
    paramSchedule := .custom #[16, 20, 24, 28, 32]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
After the first occurrence the seen prefix has size one, so each of the `u`
coefficient-equality probes has bounded cost and total work is `O(u)`. The
one-polynomial result has constant structural-hash cost.
-/
setup_benchmark runDedupRepeated u => u
  with prep := prepDedupRepeated
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Every distinct fixed-degree polynomial scans a seen prefix of lengths
`0, ..., u-1`; coefficient widths are bounded by the committed schedule, so
the exact list/coefficient-comparison count is `O(u^2)`. LeanBench's required
structural result hash is `O(u)` and therefore lower-order.
-/
setup_benchmark runDedupDistinct u => u * u
  with prep := prepDedupDistinct
  where {
    paramFloor := 64
    paramCeiling := 1024
    paramSchedule := .custom #[64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
The coprime case performs one bounded-degree gcd, identity package, replay
choice, and checker call for each of `m` independently prepared atoms. The
required hash walks `m` bounded-size certificates, preserving `O(m)`.
-/
setup_benchmark runCommonCoprime m => m
  with prep := prepCommonCoprime
  where {
    paramFloor := 8
    paramCeiling := 128
    paramSchedule := .custom #[8, 16, 32, 64, 128]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
The shared-root case likewise performs one fixed-degree public
`buildCommonRoot?` call per atom; the nonconstant gcd replay remains bounded
because both carrier and atom degrees are fixed. The required structural hash
also walks `m` bounded-size certificates, giving `O(m)` total work.
-/
setup_benchmark runCommonShared m => m
  with prep := prepCommonShared
  where {
    paramFloor := 8
    paramCeiling := 128
    paramSchedule := .custom #[8, 16, 32, 64, 128]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
The repeated case intentionally does not deduplicate: it invokes the public
builder exactly `m` times on the same fixed-degree pair. Hashing the `m`
bounded-size results is also linear, hence `O(m)` total work.
-/
setup_benchmark runCommonRepeated m => m
  with prep := prepCommonRepeated
  where {
    paramFloor := 8
    paramCeiling := 128
    paramSchedule := .custom #[8, 16, 32, 64, 128]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
The two roots `+-2^-b` keep the count-one intervals touching for `Theta(b)`
bisections. Each step performs bounded fixed-degree arithmetic on `Theta(b)`-
bit operands, so the wall contract `O(b M(b))` is represented by the
quasi-linear multiplication proxy `b^2 ceilLog2(b+1)`. The schedule stays in
one multiprecision regime and avoids the immediate-`Int`/GMP seam.
-/
setup_benchmark runSeparationDepth b => b * b * ceilLog2 (b + 1)
  with prep := prepSeparationDepth
  where {
    paramFloor := 36
    paramCeiling := 56
    paramSchedule := .custom #[36, 40, 44, 48, 52, 56]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Isolation validation and the `k` root-cell common-root queries take `O(k^3)`
exact operations. The primitive PRS for `prod_(j<=k)(x-j)` has operand height
`B(k) = O(k^2 log k)`; with quasi-linear multiplication, the wall-cost proxy
for `O(k^3 M(B(k)))` is `k^5 ceilLog2(k+1)^2`. Construction stays in `prep`.
-/
setup_benchmark runReplayCells k => k ^ 5 * (ceilLog2 (k + 1)) ^ 2
  with prep := prepReplayCells
  where {
    paramFloor := 18
    paramCeiling := 28
    paramSchedule := .custom #[18, 20, 22, 24, 26, 28]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
With three carrier cells fixed, product construction, deduplication, aligned
common-root lookup, sign-row construction, and formula lookup scan prefixes of
the `u` distinct scalar-multiple entries, for `O(u^2)` total work.
-/
setup_benchmark runReplaySigns u => u * u
  with prep := prepReplaySigns
  where {
    paramFloor := 64
    paramCeiling := 256
    paramSchedule := .custom #[64, 96, 128, 160, 192, 256]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
The arithmetic payload and atom multiset stay fixed. Polynomial discovery and
the strict option-valued formula fold visit each appended literal/connective
node a bounded number of times, giving `O(s)` structural work.
-/
setup_benchmark runReplayFormula s => s
  with prep := prepReplayFormula
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- The `verify` inputs and small structural representatives must all prepare
accepted evidence. These guards make an accidental `none` fixture a build
failure rather than a misleading constant-time benchmark. -/
#guard (List.range 5).all fun n =>
  runDecisionCarrierDegree (prepDecisionCarrierDegree n) == some true
#guard (List.range 5).all fun n =>
  (runCommonCoprime (prepCommonCoprime n)).isSome
#guard (List.range 5).all fun n =>
  (runCommonShared (prepCommonShared n)).isSome
#guard (List.range 5).all fun n =>
  (runCommonRepeated (prepCommonRepeated n)).isSome
#guard (List.range 5).all fun n => (prepSeparationDepth n).isSome
#guard (List.range 5).all fun n =>
  runSeparationDepth (prepSeparationDepth n) |>.isSome
#guard (List.range 5).all fun n => (prepReplayCells n).isSome
#guard (List.range 5).all fun n => (prepReplaySigns n).isSome
#guard (List.range 5).all fun n => (prepReplayFormula n).isSome
#guard (List.range 5).all fun n =>
  runReplayCells (prepReplayCells n) == some true
#guard (List.range 5).all fun n =>
  runReplaySigns (prepReplaySigns n) == some true
#guard (List.range 5).all fun n =>
  runReplayFormula (prepReplayFormula n) == some true
#guard [16, 20, 24, 28, 32].all fun n =>
  runDecisionCarrierDegree (prepDecisionCarrierDegree n) == some true
#guard [8, 16, 32, 64, 128].all fun n =>
  (runCommonCoprime (prepCommonCoprime n)).isSome &&
  (runCommonShared (prepCommonShared n)).isSome &&
  (runCommonRepeated (prepCommonRepeated n)).isSome
#guard [36, 40, 44, 48, 52, 56].all fun n =>
  runSeparationDepth (prepSeparationDepth n) |>.isSome
#guard [18, 20, 22, 24, 26, 28].all fun n =>
  runReplayCells (prepReplayCells n) == some true
#guard [64, 96, 128, 160, 192, 256].all fun n =>
  runReplaySigns (prepReplaySigns n) == some true
#guard [64, 128, 256, 512, 1024, 2048].all fun n =>
  runReplayFormula (prepReplayFormula n) == some true

end Hex.RCFBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
