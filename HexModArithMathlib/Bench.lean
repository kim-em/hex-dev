import HexModArithMathlib.Basic
import LeanBench

/-!
Benchmark registrations for the `HexModArithMathlib` `ZMod64`/`ZMod` bridge.

This Phase 4 infrastructure slice measures the public conversion and ring
equivalence surfaces over deterministic unit, small, and large word-sized
moduli.

Scientific registrations:

* `runToZModChecksum`: convert executable `ZMod64` residues to Mathlib `ZMod`
  and checksum canonical representatives, `O(n)`.
* `runOfZModChecksum`: rebuild executable `ZMod64` residues from Mathlib
  `ZMod` inputs and checksum canonical representatives, `O(n)`.
* `runRoundTripChecksum`: exercise both conversion round trips over generated
  representatives, `O(n)`.
* `runEquivChecksum`: exercise `ZMod64.equiv` and `ZMod64.equiv.symm` on the
  same representatives, `O(n)`.
* `runAddTransportChecksum`: compare executable addition transported through
  the bridge against Mathlib-side addition, `O(n)`.
* `runMulTransportChecksum`: compare executable multiplication transported
  through the bridge against Mathlib-side multiplication, `O(n)`.
-/

namespace HexModArithMathlib.ModArithBridgeBench

open Hex

private abbrev SmallMod : Nat := 7
private abbrev LargeMod : Nat := 2 ^ 63 + 29

private instance benchBoundsOne : Hex.ZMod64.Bounds 1 := ⟨by decide, by decide⟩
private instance benchBoundsSmall : Hex.ZMod64.Bounds SmallMod := ⟨by decide, by decide⟩
private instance benchBoundsLarge : Hex.ZMod64.Bounds LargeMod := ⟨by decide, by decide⟩

/-- Prepared natural representatives shared by conversion benchmarks. -/
structure UnaryInput where
  values : Array Nat
  deriving Hashable

/-- Prepared representative pairs shared by operation-transport benchmarks. -/
structure BinaryInput where
  lhs : Array Nat
  rhs : Array Nat
  deriving Hashable

/-- Deterministic representative generator, intentionally spanning many wraps. -/
def rawValueAt (i salt : Nat) : Nat :=
  ((i + 1) * 1_103_515_245 +
    (i + 17) * 12_345 +
    (salt + 97) * 65_537 +
    i * i * 31) % 4_294_967_291

/-- Deterministic wrapping mix for compact benchmark result summaries. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Include a natural representative in a stable machine-word checksum. -/
def checksumNat (acc : UInt64) (n : Nat) : UInt64 :=
  mixWord acc (hash n)

/-- Include an executable residue in a stable checksum. -/
def checksumZMod64 {p : Nat} [Hex.ZMod64.Bounds p] (acc : UInt64)
    (x : Hex.ZMod64 p) : UInt64 :=
  checksumNat acc x.toNat

/-- Include a Mathlib residue in a stable checksum. -/
def checksumZMod (p : Nat) [NeZero p] (acc : UInt64) (x : ZMod p) : UInt64 :=
  checksumNat acc x.val

/-- Per-parameter fixture for unary conversion benchmarks. -/
def prepUnaryInput (n : Nat) : UnaryInput :=
  { values := (Array.range n).map fun i => rawValueAt i 31 }

/-- Per-parameter fixture for binary operation-transport benchmarks. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  { lhs := (Array.range n).map fun i => rawValueAt i 43
    rhs := (Array.range n).map fun i => rawValueAt i 71 }

/-- Fold a unary checksum target over the unit, small, and large modulus families. -/
def foldUnaryModuli (values : Array Nat)
    (target : {p : Nat} → [Hex.ZMod64.Bounds p] → Nat → UInt64 → UInt64) : UInt64 :=
  let acc := values.foldl (fun acc n => target (p := 1) n acc) 0
  let acc := values.foldl (fun acc n => target (p := SmallMod) n acc) acc
  values.foldl (fun acc n => target (p := LargeMod) n acc) acc

/-- Fold a binary checksum target over the unit, small, and large modulus families. -/
def foldBinaryModuli (input : BinaryInput)
    (target : {p : Nat} → [Hex.ZMod64.Bounds p] → Nat → Nat → UInt64 → UInt64) :
    UInt64 :=
  let foldForMod {p : Nat} [Hex.ZMod64.Bounds p] (acc : UInt64) : UInt64 :=
    input.lhs.zip input.rhs |>.foldl (fun acc pair => target (p := p) pair.1 pair.2 acc) acc
  let acc := foldForMod (p := 1) 0
  let acc := foldForMod (p := SmallMod) acc
  foldForMod (p := LargeMod) acc

/-- One `toZMod` checksum step at a fixed modulus. -/
def toZModStep {p : Nat} [Hex.ZMod64.Bounds p] (n : Nat) (acc : UInt64) : UInt64 :=
  let residue : Hex.ZMod64 p := Hex.ZMod64.ofNat p n
  checksumZMod p acc (HexModArithMathlib.ZMod64.toZMod residue)

/-- One `ofZMod` checksum step at a fixed modulus. -/
def ofZModStep {p : Nat} [Hex.ZMod64.Bounds p] (n : Nat) (acc : UInt64) : UInt64 :=
  let residue : ZMod p := (n : ZMod p)
  checksumZMod64 acc (HexModArithMathlib.ZMod64.ofZMod residue)

/-- One bidirectional round-trip checksum step at a fixed modulus. -/
def roundTripStep {p : Nat} [Hex.ZMod64.Bounds p] (n : Nat) (acc : UInt64) : UInt64 :=
  let executable : Hex.ZMod64 p := Hex.ZMod64.ofNat p n
  let mathlib : ZMod p := (rawValueAt n 103 : ZMod p)
  let acc := checksumZMod64 acc
    (HexModArithMathlib.ZMod64.ofZMod (HexModArithMathlib.ZMod64.toZMod executable))
  checksumZMod p acc
    (HexModArithMathlib.ZMod64.toZMod (HexModArithMathlib.ZMod64.ofZMod mathlib))

/-- One ring-equivalence checksum step at a fixed modulus. -/
def equivStep {p : Nat} [Hex.ZMod64.Bounds p] (n : Nat) (acc : UInt64) : UInt64 :=
  let executable : Hex.ZMod64 p := Hex.ZMod64.ofNat p n
  let mathlib : ZMod p := (rawValueAt n 109 : ZMod p)
  let equiv := (HexModArithMathlib.ZMod64.equiv : Hex.ZMod64 p ≃+* ZMod p)
  let acc := checksumZMod p acc (equiv executable)
  checksumZMod64 acc (equiv.symm mathlib)

/-- One addition-transport checksum step at a fixed modulus. -/
def addTransportStep {p : Nat} [Hex.ZMod64.Bounds p] (a b : Nat) (acc : UInt64) :
    UInt64 :=
  let lhs : Hex.ZMod64 p := Hex.ZMod64.ofNat p a
  let rhs : Hex.ZMod64 p := Hex.ZMod64.ofNat p b
  let transported := HexModArithMathlib.ZMod64.toZMod (lhs + rhs)
  let mathlibSide :=
    HexModArithMathlib.ZMod64.toZMod lhs + HexModArithMathlib.ZMod64.toZMod rhs
  checksumZMod p (checksumZMod p acc transported) mathlibSide

/-- One multiplication-transport checksum step at a fixed modulus. -/
def mulTransportStep {p : Nat} [Hex.ZMod64.Bounds p] (a b : Nat) (acc : UInt64) :
    UInt64 :=
  let lhs : Hex.ZMod64 p := Hex.ZMod64.ofNat p a
  let rhs : Hex.ZMod64 p := Hex.ZMod64.ofNat p b
  let transported := HexModArithMathlib.ZMod64.toZMod (lhs * rhs)
  let mathlibSide :=
    HexModArithMathlib.ZMod64.toZMod lhs * HexModArithMathlib.ZMod64.toZMod rhs
  checksumZMod p (checksumZMod p acc transported) mathlibSide

/-- Benchmark target: executable-to-Mathlib bridge conversion. -/
def runToZModChecksum (input : UnaryInput) : UInt64 :=
  foldUnaryModuli input.values
    (fun {p} [Hex.ZMod64.Bounds p] n acc => toZModStep (p := p) n acc)

/-- Benchmark target: Mathlib-to-executable bridge conversion. -/
def runOfZModChecksum (input : UnaryInput) : UInt64 :=
  foldUnaryModuli input.values
    (fun {p} [Hex.ZMod64.Bounds p] n acc => ofZModStep (p := p) n acc)

/-- Benchmark target: both bridge round trips. -/
def runRoundTripChecksum (input : UnaryInput) : UInt64 :=
  foldUnaryModuli input.values
    (fun {p} [Hex.ZMod64.Bounds p] n acc => roundTripStep (p := p) n acc)

/-- Benchmark target: ring equivalence and inverse equivalence applications. -/
def runEquivChecksum (input : UnaryInput) : UInt64 :=
  foldUnaryModuli input.values
    (fun {p} [Hex.ZMod64.Bounds p] n acc => equivStep (p := p) n acc)

/-- Benchmark target: addition transported across the bridge. -/
def runAddTransportChecksum (input : BinaryInput) : UInt64 :=
  foldBinaryModuli input
    (fun {p} [Hex.ZMod64.Bounds p] a b acc => addTransportStep (p := p) a b acc)

/-- Benchmark target: multiplication transported across the bridge. -/
def runMulTransportChecksum (input : BinaryInput) : UInt64 :=
  foldBinaryModuli input
    (fun {p} [Hex.ZMod64.Bounds p] a b acc => mulTransportStep (p := p) a b acc)

/- Cost model: each target performs a fixed number of constant-time bridge
operations for each generated representative across the fixed modulus set. -/
setup_benchmark runToZModChecksum n => n
  with prep := prepUnaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: each target performs a fixed number of constant-time bridge
operations for each generated representative across the fixed modulus set. -/
setup_benchmark runOfZModChecksum n => n
  with prep := prepUnaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: each target performs a fixed number of constant-time bridge
operations for each generated representative across the fixed modulus set. -/
setup_benchmark runRoundTripChecksum n => n
  with prep := prepUnaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: each target performs a fixed number of constant-time bridge
operations for each generated representative across the fixed modulus set. -/
setup_benchmark runEquivChecksum n => n
  with prep := prepUnaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: each target performs a fixed number of constant-time executable
and Mathlib additions for each generated pair across the fixed modulus set. -/
setup_benchmark runAddTransportChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: each target performs a fixed number of constant-time executable
and Mathlib multiplications for each generated pair across the fixed modulus set. -/
setup_benchmark runMulTransportChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
    signalFloorMultiplier := 1.0
  }

end HexModArithMathlib.ModArithBridgeBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
