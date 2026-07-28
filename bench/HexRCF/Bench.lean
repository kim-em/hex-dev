/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.BenchHash
import Hex.BenchOracle.Flint
import LeanBench

/-!
Benchmark registrations for the Mathlib-free compiled HexRCF decision and
certificate-replay pipeline.

All fixture construction is hoisted through `with prep := ...`. In particular,
the replay targets time only `Certificate.replay?` on already accepted `.cells`
certificates; they never rebuild witnesses in the timed region.

The informational python-flint comparator covers only the compiled
carrier-degree decision family at `n = 16, 20, 24, 28, 32`. Both sides consume
the same precomputed reflected sentence; FLINT receives its precomputed
version-1 JSON encoding through the shared persistent driver protocol:

```text
{"family":"rcf","op":"decide","sentence":<v1 sentence>}
  -> {"ok":true,"result":<bool>}
```

Every outer fixed-benchmark warmup or repeat runs in a fresh Lean child. Both
paired registrations use `warmupFirstIter`, giving a steady-state comparison;
on the FLINT side that call also starts one Python process before timing. The
child then reuses it for its auto-tuned inner-repeat batch. Scheduled-only
release execution and ratio reporting require `python3` with `python-flint`;
routine `verify` still exercises one semantic smoke call for every fixed
registration. This comparator is not proof-producing and supplies no
tactic/elaboration or kernel-replay ratio.
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

/-! ## Informational python-flint decision comparator -/

private def cmpJson : Cmp → Lean.Json
  | .lt => .str "lt"
  | .le => .str "le"
  | .eq => .str "eq"
  | .ge => .str "ge"
  | .gt => .str "gt"
  | .ne => .str "ne"

private def formulaJson : Formula → Lean.Json
  | .atom atom => .mkObj [
      ("tag", .str "atom"),
      ("coeffs", Hex.BenchOracle.Flint.intsToJson atom.p.toArray.toList),
      ("cmp", cmpJson atom.cmp)]
  | .tt => .mkObj [("tag", .str "tt")]
  | .ff => .mkObj [("tag", .str "ff")]
  | .not formula => .mkObj [
      ("tag", .str "not"),
      ("arg", formulaJson formula)]
  | .and left right => .mkObj [
      ("tag", .str "and"),
      ("left", formulaJson left),
      ("right", formulaJson right)]
  | .or left right => .mkObj [
      ("tag", .str "or"),
      ("left", formulaJson left),
      ("right", formulaJson right)]
  | .imp left right => .mkObj [
      ("tag", .str "imp"),
      ("left", formulaJson left),
      ("right", formulaJson right)]

private def dyadicJson : Dyadic → Lean.Json
  | .zero => Hex.BenchOracle.Flint.intsToJson [0, 0]
  | .ofOdd numerator exponent _ =>
      Hex.BenchOracle.Flint.intsToJson [numerator, exponent]

private def boundsJson (lower upper : Dyadic) : Lean.Json :=
  .mkObj [("lower", dyadicJson lower), ("upper", dyadicJson upper)]

private def sentenceJson : Sentence → Lean.Json
  | .forallReal formula => .mkObj [
      ("quantifier", .str "forall_real"),
      ("bounds", .null),
      ("formula", formulaJson formula)]
  | .existsReal formula => .mkObj [
      ("quantifier", .str "exists_real"),
      ("bounds", .null),
      ("formula", formulaJson formula)]
  | .forallIoc lower upper formula => .mkObj [
      ("quantifier", .str "forall_ioc"),
      ("bounds", boundsJson lower upper),
      ("formula", formulaJson formula)]
  | .existsIoc lower upper formula => .mkObj [
      ("quantifier", .str "exists_ioc"),
      ("bounds", boundsJson lower upper),
      ("formula", formulaJson formula)]

private def jsonMatches (actual : Lean.Json) (expected : String) : Bool :=
  match Lean.Json.parse expected with
  | .ok value => actual == value
  | .error _ => false

private def wireX : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]
private def wireAtom (cmp : Cmp) : Formula := .atom ⟨wireX, cmp⟩

/- These guards cover the complete version-1 wire vocabulary, including
constructors not used by the five current comparator inputs. Schema drift is
therefore a build failure rather than a scheduled-host surprise. -/
#guard jsonMatches (cmpJson .lt) "\"lt\""
#guard jsonMatches (cmpJson .le) "\"le\""
#guard jsonMatches (cmpJson .eq) "\"eq\""
#guard jsonMatches (cmpJson .ge) "\"ge\""
#guard jsonMatches (cmpJson .gt) "\"gt\""
#guard jsonMatches (cmpJson .ne) "\"ne\""
#guard jsonMatches (formulaJson (wireAtom .lt))
  "{\"tag\":\"atom\",\"coeffs\":[0,1],\"cmp\":\"lt\"}"
#guard jsonMatches (formulaJson .tt) "{\"tag\":\"tt\"}"
#guard jsonMatches (formulaJson .ff) "{\"tag\":\"ff\"}"
#guard jsonMatches (formulaJson (.not .tt))
  "{\"tag\":\"not\",\"arg\":{\"tag\":\"tt\"}}"
#guard jsonMatches (formulaJson (.and .tt .ff))
  "{\"tag\":\"and\",\"left\":{\"tag\":\"tt\"},\"right\":{\"tag\":\"ff\"}}"
#guard jsonMatches (formulaJson (.or .tt .ff))
  "{\"tag\":\"or\",\"left\":{\"tag\":\"tt\"},\"right\":{\"tag\":\"ff\"}}"
#guard jsonMatches (formulaJson (.imp .tt .ff))
  "{\"tag\":\"imp\",\"left\":{\"tag\":\"tt\"},\"right\":{\"tag\":\"ff\"}}"
#guard jsonMatches (dyadicJson 0) "[0,0]"
#guard jsonMatches (dyadicJson ((Dyadic.ofInt (-1)) >>> (1 : Int))) "[-1,1]"
#guard jsonMatches (sentenceJson (.forallReal .tt))
  "{\"quantifier\":\"forall_real\",\"bounds\":null,\"formula\":{\"tag\":\"tt\"}}"
#guard jsonMatches (sentenceJson (.existsReal .ff))
  "{\"quantifier\":\"exists_real\",\"bounds\":null,\"formula\":{\"tag\":\"ff\"}}"
#guard jsonMatches (sentenceJson (.forallIoc 0 1 .tt))
  "{\"quantifier\":\"forall_ioc\",\"bounds\":{\"lower\":[0,0],\"upper\":[1,0]},\"formula\":{\"tag\":\"tt\"}}"
#guard jsonMatches
  (sentenceJson (.existsIoc ((Dyadic.ofInt (-1)) >>> (1 : Int)) 0 .ff))
  "{\"quantifier\":\"exists_ioc\",\"bounds\":{\"lower\":[-1,1],\"upper\":[0,0]},\"formula\":{\"tag\":\"ff\"}}"

private structure DecisionInput where
  degree : Nat
  sentence : Sentence
  request : String

private def prepDecisionInput (n : Nat) : DecisionInput :=
  let sentence := prepDecisionCarrierDegree n
  let request := Lean.Json.mkObj [
    ("family", .str "rcf"),
    ("op", .str "decide"),
    ("sentence", sentenceJson sentence)]
  { degree := n, sentence, request := request.compress }

/-- The five Sentence/request-line pairs are allocated once at module
initialization. Both timed wrappers read the same degree-keyed record. The
FLINT timing includes pipe transport and Python JSON decoding, but not Lean
request construction or serialization. -/
private initialize decisionInputs : IO.Ref (Array DecisionInput) ←
  IO.mkRef <| #[16, 20, 24, 28, 32].map prepDecisionInput

private def decisionInput (degree : Nat) : IO DecisionInput := do
  let inputs ← decisionInputs.get
  match inputs.find? fun input => input.degree == degree with
  | some input => return input
  | none => throw <| IO.userError s!"HexRCF decision comparator: missing degree {degree}"

private def runLeanDecision (input : DecisionInput) : IO Bool :=
  match runDecisionCarrierDegree input.sentence with
  | some value => return value
  | none => throw <| IO.userError "HexRCF decision comparator: Lean builder failed"

private def runFlintDecision (input : DecisionInput) : IO Bool := do
  let result ← Hex.BenchOracle.Flint.runLine "rcf" "decide" input.request
  match result.getBool? with
  | Except.ok value => return value
  | Except.error message =>
      throw <| IO.userError s!"HexRCF decision comparator: FLINT result was not Boolean: {message}"

private def runLeanDecisionAt (degree : Nat) : Unit → IO Bool := fun _ => do
  runLeanDecision (← decisionInput degree)

private def runFlintDecisionAt (degree : Nat) : Unit → IO Bool := fun _ => do
  runFlintDecision (← decisionInput degree)

def runLeanDecision16 : Unit → IO Bool := runLeanDecisionAt 16
def runFlintDecision16 : Unit → IO Bool := runFlintDecisionAt 16
def runLeanDecision20 : Unit → IO Bool := runLeanDecisionAt 20
def runFlintDecision20 : Unit → IO Bool := runFlintDecisionAt 20
def runLeanDecision24 : Unit → IO Bool := runLeanDecisionAt 24
def runFlintDecision24 : Unit → IO Bool := runFlintDecisionAt 24
def runLeanDecision28 : Unit → IO Bool := runLeanDecisionAt 28
def runFlintDecision28 : Unit → IO Bool := runFlintDecisionAt 28
def runLeanDecision32 : Unit → IO Bool := runLeanDecisionAt 32
def runFlintDecision32 : Unit → IO Bool := runFlintDecisionAt 32

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

/-- Shared steady-state timing shape. The discarded first call warms the Lean
decision path on both sides and starts the persistent driver on the FLINT side. -/
def decisionConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5
    maxSecondsPerCall := 8.0
    minTotalSeconds := 0.2
    warmupFirstIter := true
    expectedHash := some (Hashable.hash true) }

#guard decisionConfig.repeats == 5
#guard decisionConfig.minTotalSeconds == 0.2
#guard decisionConfig.warmupFirstIter
#guard decisionConfig.expectedHash == some (Hashable.hash true)

setup_fixed_benchmark runLeanDecision16 where decisionConfig
setup_fixed_benchmark runFlintDecision16 where decisionConfig
setup_fixed_benchmark runLeanDecision20 where decisionConfig
setup_fixed_benchmark runFlintDecision20 where decisionConfig
setup_fixed_benchmark runLeanDecision24 where decisionConfig
setup_fixed_benchmark runFlintDecision24 where decisionConfig
setup_fixed_benchmark runLeanDecision28 where decisionConfig
setup_fixed_benchmark runFlintDecision28 where decisionConfig
setup_fixed_benchmark runLeanDecision32 where decisionConfig
setup_fixed_benchmark runFlintDecision32 where decisionConfig

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
