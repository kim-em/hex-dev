/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

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

Informational external comparator:

* `NTL GF2X` (via the persistent C++ subprocess driver
  `scripts/oracle/gf2_ntl_bench_driver.cc`): paired Hex/NTL
  `setup_fixed_benchmark` registrations record raw and overhead-adjusted
  wall-time ratios on the SPEC-named packed-word GF(2)[x] operations
  (`add`, `mul`, `div` quotient, `rem` modular reduction, `gcd`). The
  comparator is classified `informational` in
  `SPEC/Libraries/hex-gf2.md §"External comparators"`: NTL ships
  hand-tuned word-level inner loops while Hex's `GF2Poly` is the
  verified algorithmic surface, so the constant-factor gap is
  structural; ratios are recorded for orientation but do not block
  Phase 4.

## NTL comparator-call protocol (persistent subprocess)

Per `SPEC/benchmarking.md` (post-#3657) §"External comparators" §"Process
call", the NTL comparator uses a persistent subprocess: one
`gf2_ntl_bench_driver` binary is spawned per `lake exe hexgf2_bench run`
invocation, and each measured call sends one framed request to its stdin
and reads one framed reply from its stdout.

The wiring shape (persistent-subprocess via a C++ NTL driver) is the HO-27
choice from the two SPEC-permitted options. FFI would require an
`extern_lib hexgf2ntlffi` block in `lakefile.lean` linking against `libntl`
at every Hex bench build; the persistent-subprocess driver compiles
on-demand the first time a bench touches the NTL comparator and lets a
fresh `lake build` succeed on hosts where NTL is not installed (NTL is only
required when the bench actually runs the comparator paths).

**Framing.** Each request is one line of plain ASCII:

  - `add  <hex_lhs> <hex_rhs>`         packed XOR
  - `mul  <hex_lhs> <hex_rhs>`         packed schoolbook / Karatsuba-style mul
  - `div  <hex_lhs> <hex_rhs>`         packed long-division quotient
  - `rem  <hex_lhs> <hex_rhs>`         packed long-division remainder
  - `gcd  <hex_lhs> <hex_rhs>`         packed Euclidean gcd
  - `shl  <hex_lhs> <decimal_shift>`   packed left shift
  - `shr  <hex_lhs> <decimal_shift>`   packed right shift
  - `ping`                             protocol-overhead probe

`<hex_*>` is the `GF2Poly`'s normalized byte representation in
little-endian byte order, uppercase hex, with `0` denoting the zero
polynomial (matching `gf2PolyToHexBytes`). The reply is exactly 16
lowercase hex digits + `\n`: the `mixWord` checksum of the result's
normalized `UInt64` word array, matching `checksumPoly` in Lean.

**Lifetime.** The driver is spawned lazily on first use into
`ntlChildRef : IO.Ref (Option NtlPersistentComparator)` and reused for
every subsequent call in the same `hexgf2_bench` process. The child's
stdin is held by the bench process via `Child.takeStdin`; on process
exit, the OS reaps the driver via EOF on stdin.

**Error handling.** If `requestLine` raises any `IO` error, the bench
wiring drops the cached child handle, re-spawns the driver from
`scripts/oracle/setup_gf2_ntl_driver.sh`, and retries the request once.
Persistent failure (e.g. setup-script failure or repeated driver crash)
surfaces as an `IO.userError`.

**Interaction with `setup_fixed_benchmark`.** `lean-bench` spawns one
fresh `hexgf2_bench` child process per measured repeat of a fixed
benchmark, so each repeat starts with a cold `ntlChildRef`. The
per-call protocol overhead figure shown in the headline report
includes one process startup per fixed-benchmark repeat at this shape.
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

/-! ## NTL `GF2X` persistent-subprocess driver

Wires `scripts/oracle/gf2_ntl_bench_driver.cc` (built on-demand by
`scripts/oracle/setup_gf2_ntl_driver.sh`) as the informational external
comparator for the SPEC-named packed-word GF(2)[x] operations. Per-rung
paired Hex/NTL `setup_fixed_benchmark` registrations populate the
headline report's Comparator Ratios subsection at densified rungs of
each parametric ladder. -/

/-- Persistent child process for the NTL bench driver. `stdin` is the
writable handle returned by `Child.takeStdin`; `child` is the
post-`takeStdin` `Child` (its `stdin` field is `Stdio.null`), kept so
the process is not reaped while the bench harness holds the
comparator. -/
structure NtlPersistentComparator where
  stdin : IO.FS.Handle
  child : IO.Process.Child
    { stdin := .null, stdout := .piped, stderr := .piped }

namespace NtlPersistentComparator

/-- Spawn the driver with piped stdio and detach its stdin handle. -/
def spawn (cmd : String) (args : Array String := #[]) :
    IO NtlPersistentComparator := do
  let raw ← IO.Process.spawn
    { cmd := cmd, args := args,
      stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← raw.takeStdin
  return { stdin := stdin, child := child }

/-- Write one request line and read one reply line. Appends `'\n'`,
flushes stdin, then blocks on `getLine`. The bench wiring inserts a
retry layer above this helper that respawns on `IO` error. -/
def requestLine (c : NtlPersistentComparator) (request : String) : IO String := do
  c.stdin.putStr (request ++ "\n")
  c.stdin.flush
  c.child.stdout.getLine

end NtlPersistentComparator

/-- Cached absolute path of the compiled NTL driver. Resolved lazily on
first use via `HEX_GF2_NTL_DRIVER` or `setup_gf2_ntl_driver.sh`. -/
initialize ntlBinaryRef : IO.Ref (Option String) ← IO.mkRef none

/-- Cached running NTL driver. Reset to `none` on `IO` error so the next
request respawns the driver. -/
initialize ntlChildRef : IO.Ref (Option NtlPersistentComparator) ←
  IO.mkRef none

private def checkedNtlOutput (cmd : String) (args : Array String := #[]) :
    IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"process failed ({cmd}):\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}"
  return out.stdout.trimAscii.toString

/-- Resolve the absolute path of the NTL driver binary, honouring the
`HEX_GF2_NTL_DRIVER` env override or delegating to the setup script. -/
def resolveNtlBinary : IO String := do
  if let some cached ← ntlBinaryRef.get then
    return cached
  let path ←
    match (← IO.getEnv "HEX_GF2_NTL_DRIVER") with
    | some p => pure p
    | none => checkedNtlOutput "scripts/oracle/setup_gf2_ntl_driver.sh"
  ntlBinaryRef.set (some path)
  return path

/-- Lazily spawn the persistent NTL driver, or return the cached handle. -/
def resolveNtlChild : IO NtlPersistentComparator := do
  if let some ch ← ntlChildRef.get then
    return ch
  let binary ← resolveNtlBinary
  let ch ← NtlPersistentComparator.spawn binary
  ntlChildRef.set (some ch)
  return ch

/-- Send one request to the persistent driver and parse its reply. On
process death, EOF before a reply line, or any IO error from the
protocol, the cached handle is dropped, a fresh driver is spawned, and
the call retried once. Persistent failure surfaces as an `IO.userError`
from the retry path. -/
def requestNtlLineWithRetry (request : String) : Nat → IO String
  | 0 => do
    let reply ← (← resolveNtlChild).requestLine request
    if reply.isEmpty then
      throw <| IO.userError "gf2_ntl_bench_driver closed stdout before replying"
    return reply
  | Nat.succ remaining => do
    try
      let reply ← (← resolveNtlChild).requestLine request
      if reply.isEmpty then
        throw <| IO.userError "gf2_ntl_bench_driver closed stdout before replying"
      return reply
    catch _ =>
      ntlChildRef.set none
      requestNtlLineWithRetry request remaining

/-- Hex digit (uppercase). Used for the driver's input encoding; the
driver's output uses lowercase, which `parseNtlHexReply` accepts via
`UInt8.ofHexChar`-equivalent matching. -/
@[inline] private def hexNibbleUpper (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat)
  else Char.ofNat (n - 10 + 'A'.toNat)

@[inline] private def hexNibbleValue : Char → Option Nat
  | c =>
    let v := c.toNat
    if '0'.toNat ≤ v ∧ v ≤ '9'.toNat then some (v - '0'.toNat)
    else if 'a'.toNat ≤ v ∧ v ≤ 'f'.toNat then some (10 + v - 'a'.toNat)
    else if 'A'.toNat ≤ v ∧ v ≤ 'F'.toNat then some (10 + v - 'A'.toNat)
    else none

/-- Serialize a `GF2Poly` to its NTL byte-encoding hex string. Each
normalized word emits exactly 16 uppercase hex digits in little-endian
byte order. The empty (zero) polynomial maps to the literal `0` so the
driver can short-circuit a zero parse. -/
def gf2PolyToHexBytes (p : GF2Poly) : String := Id.run do
  let words := p.toWords
  if words.isEmpty then return "0"
  let mut out : Array Char := Array.mkEmpty (words.size * 16)
  for word in words do
    let mut i : Nat := 0
    while i < 8 do
      let shifted := word >>> (UInt64.ofNat (i * 8))
      let byteVal : Nat := (shifted &&& (0xff : UInt64)).toNat
      out := out.push (hexNibbleUpper (byteVal / 16))
      out := out.push (hexNibbleUpper (byteVal % 16))
      i := i + 1
  return String.ofList out.toList

/-- Parse a `UInt64` from the driver's 16-char lowercase hex reply
(plus optional trailing whitespace / newline that `Handle.getLine`
preserves). Raises `IO.userError` on invalid hex. -/
def parseNtlHexReply (reply : String) : IO UInt64 := do
  let trimmed := reply.trimAscii.toString
  if trimmed == "ERROR" then
    throw <| IO.userError "gf2_ntl_bench_driver reported parse error"
  let chars := trimmed.toList
  if chars.length != 16 then
    throw <| IO.userError s!"gf2_ntl_bench_driver reply not 16 hex chars: {trimmed}"
  let mut acc : UInt64 := 0
  for c in chars do
    match hexNibbleValue c with
    | some v => acc := acc * 16 + UInt64.ofNat v
    | none =>
      throw <| IO.userError s!"gf2_ntl_bench_driver reply contains non-hex char: {trimmed}"
  return acc

/-- Send one binary-operand request (`add`, `mul`, `div`, `rem`, `gcd`)
to the NTL driver and return the result's `mixWord` checksum. -/
def runNtlBinaryOp (op : String) (lhs rhs : GF2Poly) : IO UInt64 := do
  let request := s!"{op} {gf2PolyToHexBytes lhs} {gf2PolyToHexBytes rhs}"
  parseNtlHexReply (← requestNtlLineWithRetry request 1)

/-- NTL `GF2X` packed-XOR addition checksum. -/
def runNtlAddChecksum (input : BinaryInput) : IO UInt64 :=
  runNtlBinaryOp "add" input.lhs input.rhs

/-- NTL `GF2X` packed multiplication checksum. -/
def runNtlMulChecksum (input : BinaryInput) : IO UInt64 :=
  runNtlBinaryOp "mul" input.lhs input.rhs

/-- NTL `GF2X` packed long-division quotient checksum. -/
def runNtlDivChecksum (input : BinaryInput) : IO UInt64 :=
  runNtlBinaryOp "div" input.lhs input.rhs

/-- NTL `GF2X` packed long-division remainder checksum. -/
def runNtlModChecksum (input : BinaryInput) : IO UInt64 :=
  runNtlBinaryOp "rem" input.lhs input.rhs

/-- NTL `GF2X` packed Euclidean gcd checksum. -/
def runNtlGcdChecksum (input : BinaryInput) : IO UInt64 :=
  runNtlBinaryOp "gcd" input.lhs input.rhs

/-! ### Per-rung wrappers for paired Hex/NTL fixed registrations

The Hex parametric `setup_benchmark` ladders above own the algorithmic
verdict; the per-rung wrappers below replay one rung of the prep
function so paired `setup_fixed_benchmark` entries compare Hex and NTL
on the same deterministic fixture per rung. Each `runHexFooAt n` is the
Hex target lifted to `Unit → IO UInt64` so it shares a registration
shape with its `runNtlFooAt n` counterpart. -/

def runAddAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runAddChecksum (prepBinaryInput n)
def runNtlAddAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runNtlAddChecksum (prepBinaryInput n)

def runMulAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runMulChecksum (prepBinaryInput n)
def runNtlMulAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runNtlMulChecksum (prepBinaryInput n)

def runDivAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runDivChecksum (prepDivInput n)
def runNtlDivAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runNtlDivChecksum (prepDivInput n)

def runModAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runModChecksum (prepDivInput n)
def runNtlModAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runNtlModChecksum (prepDivInput n)

def runGcdAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runGcdChecksum (prepGcdInput n)
def runNtlGcdAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runNtlGcdChecksum (prepGcdInput n)

/-! Per-rung concrete bindings used by the paired `setup_fixed_benchmark`
registrations.

Add ladder: in-fill of the parametric `[4096, 8192, 16384, 32768, 65536]`
schedule pushed up to `262144` so NTL's per-call wall time clears the
persistent-subprocess startup floor.

Mul/Div/Mod/Gcd ladders: in-fill of the parametric
`[16, 24, 32, 48, 64, 96, 128]` schedule pushed up to `256` for the
same reason. -/

def runAdd4096 : Unit → IO UInt64 := runAddAt 4096
def runNtlAdd4096 : Unit → IO UInt64 := runNtlAddAt 4096
def runAdd8192 : Unit → IO UInt64 := runAddAt 8192
def runNtlAdd8192 : Unit → IO UInt64 := runNtlAddAt 8192
def runAdd16384 : Unit → IO UInt64 := runAddAt 16384
def runNtlAdd16384 : Unit → IO UInt64 := runNtlAddAt 16384
def runAdd32768 : Unit → IO UInt64 := runAddAt 32768
def runNtlAdd32768 : Unit → IO UInt64 := runNtlAddAt 32768
def runAdd65536 : Unit → IO UInt64 := runAddAt 65536
def runNtlAdd65536 : Unit → IO UInt64 := runNtlAddAt 65536
def runAdd131072 : Unit → IO UInt64 := runAddAt 131072
def runNtlAdd131072 : Unit → IO UInt64 := runNtlAddAt 131072
def runAdd262144 : Unit → IO UInt64 := runAddAt 262144
def runNtlAdd262144 : Unit → IO UInt64 := runNtlAddAt 262144

def runMul16 : Unit → IO UInt64 := runMulAt 16
def runNtlMul16 : Unit → IO UInt64 := runNtlMulAt 16
def runMul24 : Unit → IO UInt64 := runMulAt 24
def runNtlMul24 : Unit → IO UInt64 := runNtlMulAt 24
def runMul32 : Unit → IO UInt64 := runMulAt 32
def runNtlMul32 : Unit → IO UInt64 := runNtlMulAt 32
def runMul48 : Unit → IO UInt64 := runMulAt 48
def runNtlMul48 : Unit → IO UInt64 := runNtlMulAt 48
def runMul64 : Unit → IO UInt64 := runMulAt 64
def runNtlMul64 : Unit → IO UInt64 := runNtlMulAt 64
def runMul96 : Unit → IO UInt64 := runMulAt 96
def runNtlMul96 : Unit → IO UInt64 := runNtlMulAt 96
def runMul128 : Unit → IO UInt64 := runMulAt 128
def runNtlMul128 : Unit → IO UInt64 := runNtlMulAt 128
def runMul192 : Unit → IO UInt64 := runMulAt 192
def runNtlMul192 : Unit → IO UInt64 := runNtlMulAt 192
def runMul256 : Unit → IO UInt64 := runMulAt 256
def runNtlMul256 : Unit → IO UInt64 := runNtlMulAt 256
def runMul384 : Unit → IO UInt64 := runMulAt 384
def runNtlMul384 : Unit → IO UInt64 := runNtlMulAt 384
def runMul512 : Unit → IO UInt64 := runMulAt 512
def runNtlMul512 : Unit → IO UInt64 := runNtlMulAt 512
def runMul768 : Unit → IO UInt64 := runMulAt 768
def runNtlMul768 : Unit → IO UInt64 := runNtlMulAt 768
def runMul1024 : Unit → IO UInt64 := runMulAt 1024
def runNtlMul1024 : Unit → IO UInt64 := runNtlMulAt 1024
def runMul1536 : Unit → IO UInt64 := runMulAt 1536
def runNtlMul1536 : Unit → IO UInt64 := runNtlMulAt 1536
def runMul2048 : Unit → IO UInt64 := runMulAt 2048
def runNtlMul2048 : Unit → IO UInt64 := runNtlMulAt 2048

def runDiv16 : Unit → IO UInt64 := runDivAt 16
def runNtlDiv16 : Unit → IO UInt64 := runNtlDivAt 16
def runDiv24 : Unit → IO UInt64 := runDivAt 24
def runNtlDiv24 : Unit → IO UInt64 := runNtlDivAt 24
def runDiv32 : Unit → IO UInt64 := runDivAt 32
def runNtlDiv32 : Unit → IO UInt64 := runNtlDivAt 32
def runDiv48 : Unit → IO UInt64 := runDivAt 48
def runNtlDiv48 : Unit → IO UInt64 := runNtlDivAt 48
def runDiv64 : Unit → IO UInt64 := runDivAt 64
def runNtlDiv64 : Unit → IO UInt64 := runNtlDivAt 64
def runDiv96 : Unit → IO UInt64 := runDivAt 96
def runNtlDiv96 : Unit → IO UInt64 := runNtlDivAt 96
def runDiv128 : Unit → IO UInt64 := runDivAt 128
def runNtlDiv128 : Unit → IO UInt64 := runNtlDivAt 128
def runDiv192 : Unit → IO UInt64 := runDivAt 192
def runNtlDiv192 : Unit → IO UInt64 := runNtlDivAt 192
def runDiv256 : Unit → IO UInt64 := runDivAt 256
def runNtlDiv256 : Unit → IO UInt64 := runNtlDivAt 256
def runDiv384 : Unit → IO UInt64 := runDivAt 384
def runNtlDiv384 : Unit → IO UInt64 := runNtlDivAt 384
def runDiv512 : Unit → IO UInt64 := runDivAt 512
def runNtlDiv512 : Unit → IO UInt64 := runNtlDivAt 512
def runDiv768 : Unit → IO UInt64 := runDivAt 768
def runNtlDiv768 : Unit → IO UInt64 := runNtlDivAt 768
def runDiv1024 : Unit → IO UInt64 := runDivAt 1024
def runNtlDiv1024 : Unit → IO UInt64 := runNtlDivAt 1024

def runMod16 : Unit → IO UInt64 := runModAt 16
def runNtlMod16 : Unit → IO UInt64 := runNtlModAt 16
def runMod24 : Unit → IO UInt64 := runModAt 24
def runNtlMod24 : Unit → IO UInt64 := runNtlModAt 24
def runMod32 : Unit → IO UInt64 := runModAt 32
def runNtlMod32 : Unit → IO UInt64 := runNtlModAt 32
def runMod48 : Unit → IO UInt64 := runModAt 48
def runNtlMod48 : Unit → IO UInt64 := runNtlModAt 48
def runMod64 : Unit → IO UInt64 := runModAt 64
def runNtlMod64 : Unit → IO UInt64 := runNtlModAt 64
def runMod96 : Unit → IO UInt64 := runModAt 96
def runNtlMod96 : Unit → IO UInt64 := runNtlModAt 96
def runMod128 : Unit → IO UInt64 := runModAt 128
def runNtlMod128 : Unit → IO UInt64 := runNtlModAt 128
def runMod192 : Unit → IO UInt64 := runModAt 192
def runNtlMod192 : Unit → IO UInt64 := runNtlModAt 192
def runMod256 : Unit → IO UInt64 := runModAt 256
def runNtlMod256 : Unit → IO UInt64 := runNtlModAt 256
def runMod384 : Unit → IO UInt64 := runModAt 384
def runNtlMod384 : Unit → IO UInt64 := runNtlModAt 384
def runMod512 : Unit → IO UInt64 := runModAt 512
def runNtlMod512 : Unit → IO UInt64 := runNtlModAt 512
def runMod768 : Unit → IO UInt64 := runModAt 768
def runNtlMod768 : Unit → IO UInt64 := runNtlModAt 768
def runMod1024 : Unit → IO UInt64 := runModAt 1024
def runNtlMod1024 : Unit → IO UInt64 := runNtlModAt 1024

def runGcd16 : Unit → IO UInt64 := runGcdAt 16
def runNtlGcd16 : Unit → IO UInt64 := runNtlGcdAt 16
def runGcd24 : Unit → IO UInt64 := runGcdAt 24
def runNtlGcd24 : Unit → IO UInt64 := runNtlGcdAt 24
def runGcd32 : Unit → IO UInt64 := runGcdAt 32
def runNtlGcd32 : Unit → IO UInt64 := runNtlGcdAt 32
def runGcd48 : Unit → IO UInt64 := runGcdAt 48
def runNtlGcd48 : Unit → IO UInt64 := runNtlGcdAt 48
def runGcd64 : Unit → IO UInt64 := runGcdAt 64
def runNtlGcd64 : Unit → IO UInt64 := runNtlGcdAt 64
def runGcd96 : Unit → IO UInt64 := runGcdAt 96
def runNtlGcd96 : Unit → IO UInt64 := runNtlGcdAt 96
def runGcd128 : Unit → IO UInt64 := runGcdAt 128
def runNtlGcd128 : Unit → IO UInt64 := runNtlGcdAt 128
def runGcd192 : Unit → IO UInt64 := runGcdAt 192
def runNtlGcd192 : Unit → IO UInt64 := runNtlGcdAt 192
def runGcd256 : Unit → IO UInt64 := runGcdAt 256
def runNtlGcd256 : Unit → IO UInt64 := runNtlGcdAt 256
def runGcd384 : Unit → IO UInt64 := runGcdAt 384
def runNtlGcd384 : Unit → IO UInt64 := runNtlGcdAt 384
def runGcd512 : Unit → IO UInt64 := runGcdAt 512
def runNtlGcd512 : Unit → IO UInt64 := runNtlGcdAt 512
def runGcd768 : Unit → IO UInt64 := runGcdAt 768
def runNtlGcd768 : Unit → IO UInt64 := runNtlGcdAt 768
def runGcd1024 : Unit → IO UInt64 := runGcdAt 1024
def runNtlGcd1024 : Unit → IO UInt64 := runNtlGcdAt 1024
def runGcd1536 : Unit → IO UInt64 := runGcdAt 1536
def runNtlGcd1536 : Unit → IO UInt64 := runNtlGcdAt 1536

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

/-! ## NTL `GF2X` informational comparator fixed registrations

Paired Hex/NTL `setup_fixed_benchmark` rungs feed the headline report's
Comparator Ratios subsection at densified rungs of each SPEC-named
parametric ladder. `lean-bench` reports each pair's observed hashes and
median wall time; per `SPEC/Libraries/hex-gf2.md §"External
comparators"` the comparator is `informational` and no gating-goal
verdict is required. -/

setup_fixed_benchmark runAdd4096 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlAdd4096 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runAdd8192 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlAdd8192 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runAdd16384 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlAdd16384 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runAdd32768 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlAdd32768 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runAdd65536 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlAdd65536 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runAdd131072 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlAdd131072 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runAdd262144 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlAdd262144 where { repeats := 5, maxSecondsPerCall := 5.0 }

setup_fixed_benchmark runMul16 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMul16 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMul24 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMul24 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMul32 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMul32 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMul48 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMul48 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMul64 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMul64 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMul96 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMul96 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMul128 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMul128 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMul192 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlMul192 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runMul256 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlMul256 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runMul384 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlMul384 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runMul512 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runNtlMul512 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runMul768 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runNtlMul768 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runMul1024 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runNtlMul1024 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runMul1536 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runNtlMul1536 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runMul2048 where { repeats := 3, maxSecondsPerCall := 30.0 }
setup_fixed_benchmark runNtlMul2048 where { repeats := 3, maxSecondsPerCall := 30.0 }

setup_fixed_benchmark runDiv16 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlDiv16 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runDiv24 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlDiv24 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runDiv32 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlDiv32 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runDiv48 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlDiv48 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runDiv64 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlDiv64 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runDiv96 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlDiv96 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runDiv128 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlDiv128 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runDiv192 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlDiv192 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runDiv256 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlDiv256 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runDiv384 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlDiv384 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runDiv512 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runNtlDiv512 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runDiv768 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runNtlDiv768 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runDiv1024 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runNtlDiv1024 where { repeats := 3, maxSecondsPerCall := 20.0 }

setup_fixed_benchmark runMod16 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMod16 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMod24 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMod24 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMod32 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMod32 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMod48 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMod48 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMod64 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMod64 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMod96 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMod96 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMod128 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlMod128 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runMod192 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlMod192 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runMod256 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlMod256 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runMod384 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlMod384 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runMod512 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runNtlMod512 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runMod768 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runNtlMod768 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runMod1024 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runNtlMod1024 where { repeats := 3, maxSecondsPerCall := 20.0 }

setup_fixed_benchmark runGcd16 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlGcd16 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runGcd24 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlGcd24 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runGcd32 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlGcd32 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runGcd48 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlGcd48 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runGcd64 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlGcd64 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runGcd96 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlGcd96 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runGcd128 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runNtlGcd128 where { repeats := 5, maxSecondsPerCall := 5.0 }
setup_fixed_benchmark runGcd192 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlGcd192 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runGcd256 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlGcd256 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runGcd384 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runNtlGcd384 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runGcd512 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runNtlGcd512 where { repeats := 3, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runGcd768 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runNtlGcd768 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runGcd1024 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runNtlGcd1024 where { repeats := 3, maxSecondsPerCall := 20.0 }
setup_fixed_benchmark runGcd1536 where { repeats := 3, maxSecondsPerCall := 30.0 }
setup_fixed_benchmark runNtlGcd1536 where { repeats := 3, maxSecondsPerCall := 30.0 }

end Hex.GF2Bench
