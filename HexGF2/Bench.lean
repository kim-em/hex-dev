import HexGF2
import LeanBench

/-!
Benchmark registrations for `hex-gf2`.

This Phase 4 packed-core slice measures deterministic `GF2Poly` word-level
operations and packed extension-field wrappers. Input construction is hoisted
into `prep`, and polynomial-valued targets return compact checksums over
normalized packed words.

Scientific registrations:

* `runPureClmulChecksum`: pure Lean carry-less word multiplication, `O(n)`.
* `runClmulChecksum`: extern-backed carry-less word multiplication, `O(n)`.
* `runAddChecksum`: packed polynomial XOR addition, `O(n)`.
* `runMulChecksum`: packed schoolbook carry-less multiplication, `O(n^2)`.
* `runShiftLeftChecksum`: packed left shift by a size-proportional amount,
  `O(n)`.
* `runShiftRightChecksum`: packed right shift by a size-proportional amount,
  `O(n)`.
* `runDivChecksum`: packed long-division quotient extraction, `O(n^2)`.
* `runModChecksum`: packed long-division remainder extraction, `O(n^2)`.
* `runGcdChecksum`: packed Euclidean gcd, `O(n^2)` on deterministic
  same-size fixtures.
* `runXGcdChecksum`: packed extended Euclidean algorithm, `O(n^2)` on
  deterministic same-size fixtures.
* `runGF2nAddChecksum`: AES-modulus single-word field addition chains, `O(n)`.
* `runGF2nMulChecksum`: AES-modulus single-word field multiplication chains,
  `O(n)`.
* `runGF2nInvChecksum`: AES-modulus single-word field inversion chains, `O(n)`.
* `runGF2nDivChecksum`: AES-modulus single-word field division chains, `O(n)`.
* `runGF2nPowChecksum`: AES-modulus single-word square-and-multiply powering,
  `O(log k)`.
* `runGF2nPolyMulChecksum`: packed quotient-field multiplication chains over a
  deterministic degree-128 modulus, `O(n)`.
* `runGF2nPolyInvChecksum`: packed quotient-field inversion chains over that
  modulus, `O(n)`.
* `runGF2nPolyDivChecksum`: packed quotient-field division chains over that
  modulus, `O(n)`.
* `runGF2nPolyPowChecksum`: packed quotient-field square-and-multiply powering
  over that modulus, `O(log k)`.
The `hexgf2_bench` executable root additionally imports `HexGF2Bench`, which
registers cross-library `GF2Poly` versus `FpPoly 2` comparison workloads outside
the `HexGF2` library ownership boundary.
-/

namespace Hex.GF2Bench

/-- Hash packed polynomials by their normalized word arrays in benchmark inputs. -/
instance : Hashable GF2Poly where
  hash p := hash p.toWords

/-- One prepared carry-less word-multiply sample. -/
structure WordSample where
  lhs : UInt64
  rhs : UInt64
  deriving Hashable

/-- Prepared word samples for `pureClmul` and extern `clmul`. -/
structure WordInput where
  samples : Array WordSample
  deriving Hashable

/-- Prepared binary polynomial-operation input. -/
structure BinaryInput where
  lhs : GF2Poly
  rhs : GF2Poly
  deriving Hashable

/-- Prepared polynomial plus a shift amount. -/
structure ShiftInput where
  poly : GF2Poly
  shift : Nat
  deriving Hashable

private theorem aesIrreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x1B 8) :=
  GF2Poly.aes_modulus_irreducible

private abbrev AESField : Type :=
  GF2n 8 0x1B (by decide) (by decide) aesIrreducible

private def aesField (w : UInt64) : AESField :=
  GF2n.reduce w

instance : Hashable AESField where
  hash a := hash a.val

/-- Prepared single-word extension-field samples. -/
structure GF2nInput where
  samples : Array (AESField × AESField)
  deriving Hashable

/-- Prepared single-word extension-field power input. -/
structure GF2nPowInput where
  base : AESField
  exponent : Nat
  deriving Hashable

/-- Deterministic degree-128 packed quotient-field modulus fixture. -/
def gf2nPolyModulus : GF2Poly :=
  GF2Poly.ofWords #[0x87, 0, 1]

private theorem gf2nPolyIrreducible :
    GF2Poly.Irreducible gf2nPolyModulus :=
  GF2Poly.gf2nPoly_modulus_irreducible

private abbrev PolyField : Type :=
  GF2nPoly gf2nPolyModulus gf2nPolyIrreducible

private def polyField (p : GF2Poly) : PolyField :=
  GF2nPoly.reducePoly p

instance : Hashable PolyField where
  hash a := hash a.val

/-- Prepared packed quotient-field samples. -/
structure GF2nPolyInput where
  samples : Array (PolyField × PolyField)
  deriving Hashable

/-- Prepared packed quotient-field power input. -/
structure GF2nPolyPowInput where
  base : PolyField
  exponent : Nat
  deriving Hashable

/-- Deterministic mixing over machine words for compact benchmark observables. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Stable checksum for one carry-less 128-bit product. -/
def checksumClmulPair (acc : UInt64) (pair : UInt64 × UInt64) : UInt64 :=
  mixWord (mixWord acc pair.1) pair.2

/-- Stable checksum for a packed polynomial's normalized words. -/
def checksumPoly (p : GF2Poly) : UInt64 :=
  p.toWords.foldl mixWord 0

/-- Stable checksum for two packed polynomial outputs. -/
def checksumPolyPair (p q : GF2Poly) : UInt64 :=
  mixWord (checksumPoly p) (checksumPoly q)

/-- Stable checksum for a single-word extension-field element. -/
def checksumGF2n (a : AESField) : UInt64 :=
  a.val

/-- Stable checksum for a packed quotient-field element. -/
def checksumGF2nPoly (a : PolyField) : UInt64 :=
  checksumPoly a.val

/-- Deterministic nonzero-ish packed word generator keyed by index and salt. -/
def wordValue (i salt : Nat) : UInt64 :=
  UInt64.ofNat <|
    ((i + 1) * 1_103_515_245 +
      (i + 17) * 12_345 +
      (salt + 97) * 65_537 +
      i * i * 31) % 18_446_744_073_709_551_557

/-- Deterministic normalized packed polynomial with `n` machine words. -/
def packedPoly (n salt : Nat) : GF2Poly :=
  if n = 0 then
    0
  else
    let words :=
      (Array.range n).map fun i =>
        let w := wordValue i salt
        if i + 1 = n then w ||| 1 else w
    GF2Poly.ofWords words

/-- Per-parameter fixture for word carry-less multiplication. -/
def prepWordInput (n : Nat) : WordInput :=
  { samples := (Array.range n).map fun i =>
      { lhs := wordValue i 11
        rhs := wordValue i 37 } }

/-- Per-parameter fixture for same-size binary polynomial operations. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  { lhs := packedPoly n 53
    rhs := packedPoly n 89 }

/-- Per-parameter fixture for division-style operations. -/
def prepDivInput (n : Nat) : BinaryInput :=
  { lhs := packedPoly (2 * n + 1) 131
    rhs := packedPoly (n + 1) 173 }

/-- Per-parameter fixture for same-size Euclidean operations. -/
def prepGcdInput (n : Nat) : BinaryInput :=
  { lhs := packedPoly (n + 1) 197
    rhs := packedPoly (n + 1) 229 }

/-- Per-parameter fixture for left shifts by a size-proportional amount. -/
def prepShiftLeftInput (n : Nat) : ShiftInput :=
  { poly := packedPoly n 251
    shift := 32 * n + 13 }

/-- Per-parameter fixture for right shifts by a size-proportional amount. -/
def prepShiftRightInput (n : Nat) : ShiftInput :=
  { poly := packedPoly (2 * n + 1) 283
    shift := 32 * n + 13 }

/-- Per-parameter fixture for AES-modulus single-word field operations. -/
def prepGF2nInput (n : Nat) : GF2nInput :=
  { samples := (Array.range n).map fun i =>
      (aesField (wordValue i 311), aesField (wordValue i 347)) }

/-- Per-parameter fixture for AES-modulus powering by a growing exponent. -/
def prepGF2nPowInput (n : Nat) : GF2nPowInput :=
  { base := aesField (wordValue n 383)
    exponent := n + 1 }

/-- Per-parameter fixture for packed quotient-field operations. -/
def prepGF2nPolyInput (n : Nat) : GF2nPolyInput :=
  { samples := (Array.range n).map fun i =>
      (polyField (packedPoly 2 (419 + i)), polyField (packedPoly 2 (467 + i))) }

/-- Per-parameter fixture for packed quotient-field powering. -/
def prepGF2nPolyPowInput (n : Nat) : GF2nPolyPowInput :=
  { base := polyField (packedPoly 2 (503 + n))
    exponent := n + 1 }

/-- Benchmark target: pure Lean carry-less word multiplication. -/
def runPureClmulChecksum (input : WordInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => checksumClmulPair acc (pureClmul sample.lhs sample.rhs))
    0

/-- Benchmark target: extern-backed carry-less word multiplication. -/
def runClmulChecksum (input : WordInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => checksumClmulPair acc (clmul sample.lhs sample.rhs))
    0

/-- Benchmark target: add two prepared packed polynomials and checksum the result. -/
def runAddChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (input.lhs + input.rhs)

/-- Benchmark target: multiply two prepared packed polynomials and checksum the result. -/
def runMulChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (input.lhs * input.rhs)

/-- Benchmark target: shift a prepared packed polynomial left. -/
def runShiftLeftChecksum (input : ShiftInput) : UInt64 :=
  checksumPoly (input.poly.shiftLeft input.shift)

/-- Benchmark target: shift a prepared packed polynomial right. -/
def runShiftRightChecksum (input : ShiftInput) : UInt64 :=
  checksumPoly (input.poly.shiftRight input.shift)

/-- Benchmark target: compute the quotient from packed long division. -/
def runDivChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (input.lhs / input.rhs)

/-- Benchmark target: compute the remainder from packed long division. -/
def runModChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (input.lhs % input.rhs)

/-- Benchmark target: compute packed polynomial gcd. -/
def runGcdChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (GF2Poly.gcd input.lhs input.rhs)

/-- Benchmark target: compute packed extended gcd and checksum all outputs. -/
def runXGcdChecksum (input : BinaryInput) : UInt64 :=
  let result := GF2Poly.xgcd input.lhs input.rhs
  mixWord (checksumPoly result.gcd) (checksumPolyPair result.left result.right)

/-- Benchmark target: add AES-modulus single-word field sample pairs. -/
def runGF2nAddChecksum (input : GF2nInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => mixWord acc (checksumGF2n (sample.1 + sample.2)))
    0

/-- Benchmark target: multiply AES-modulus single-word field sample pairs. -/
def runGF2nMulChecksum (input : GF2nInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => mixWord acc (checksumGF2n (sample.1 * sample.2)))
    0

/-- Benchmark target: invert AES-modulus single-word field samples. -/
def runGF2nInvChecksum (input : GF2nInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => mixWord acc (checksumGF2n sample.1⁻¹))
    0

/-- Benchmark target: divide AES-modulus single-word field sample pairs. -/
def runGF2nDivChecksum (input : GF2nInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => mixWord acc (checksumGF2n (sample.1 / sample.2)))
    0

/-- Benchmark target: power one AES-modulus single-word field element. -/
def runGF2nPowChecksum (input : GF2nPowInput) : UInt64 :=
  checksumGF2n (input.base ^ input.exponent)

/-- Benchmark target: multiply packed quotient-field sample pairs. -/
def runGF2nPolyMulChecksum (input : GF2nPolyInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => mixWord acc (checksumGF2nPoly (sample.1 * sample.2)))
    0

/-- Benchmark target: invert packed quotient-field samples. -/
def runGF2nPolyInvChecksum (input : GF2nPolyInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => mixWord acc (checksumGF2nPoly sample.1⁻¹))
    0

/-- Benchmark target: divide packed quotient-field sample pairs. -/
def runGF2nPolyDivChecksum (input : GF2nPolyInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => mixWord acc (checksumGF2nPoly (sample.1 / sample.2)))
    0

/-- Benchmark target: power one packed quotient-field element. -/
def runGF2nPolyPowChecksum (input : GF2nPolyPowInput) : UInt64 :=
  checksumGF2nPoly (input.base ^ input.exponent)

setup_benchmark runPureClmulChecksum n => n
  with prep := prepWordInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runClmulChecksum n => n
  with prep := prepWordInput
  where {
    paramFloor := 65536
    paramCeiling := 1048576
    paramSchedule := .custom #[65536, 131072, 262144, 524288, 1048576]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runAddChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 4096
    paramCeiling := 65536
    paramSchedule := .custom #[4096, 8192, 16384, 32768, 65536]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runMulChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runShiftLeftChecksum n => n
  with prep := prepShiftLeftInput
  where {
    paramFloor := 4096
    paramCeiling := 65536
    paramSchedule := .custom #[4096, 8192, 16384, 32768, 65536]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runShiftRightChecksum n => n
  with prep := prepShiftRightInput
  where {
    paramFloor := 4096
    paramCeiling := 65536
    paramSchedule := .custom #[4096, 8192, 16384, 32768, 65536]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runDivChecksum n => n * n
  with prep := prepDivInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runModChecksum n => n * n
  with prep := prepDivInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGcdChecksum n => n * n
  with prep := prepGcdInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runXGcdChecksum n => n * n
  with prep := prepGcdInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGF2nAddChecksum n => n
  with prep := prepGF2nInput
  where {
    paramFloor := 4096
    paramCeiling := 65536
    paramSchedule := .custom #[4096, 8192, 16384, 32768, 65536]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGF2nMulChecksum n => n
  with prep := prepGF2nInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGF2nInvChecksum n => n
  with prep := prepGF2nInput
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGF2nDivChecksum n => n
  with prep := prepGF2nInput
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGF2nPowChecksum n => Nat.log2 (n + 1)
  with prep := prepGF2nPowInput
  where {
    paramFloor := 1048576
    paramCeiling := 268435456
    paramSchedule := .custom #[1048576, 4194304, 16777216, 67108864, 268435456]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGF2nPolyMulChecksum n => n
  with prep := prepGF2nPolyInput
  where {
    paramFloor := 64
    paramCeiling := 1024
    paramSchedule := .custom #[64, 128, 256, 512, 1024]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGF2nPolyInvChecksum n => n
  with prep := prepGF2nPolyInput
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGF2nPolyDivChecksum n => n
  with prep := prepGF2nPolyInput
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGF2nPolyPowChecksum n => Nat.log2 (n + 1)
  with prep := prepGF2nPolyPowInput
  where {
    paramFloor := 1048576
    paramCeiling := 268435456
    paramSchedule := .custom #[1048576, 4194304, 16777216, 67108864, 268435456]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end Hex.GF2Bench
