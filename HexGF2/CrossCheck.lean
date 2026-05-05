import HexGF2.Clmul

/-!
Extern-vs-pure-Lean cross-check for `Hex.clmul`.

`Hex.clmul` carries an `@[extern "lean_hex_clmul_u64"]` attribute, so
compiled code may call into a C wrapper that dispatches to a CPU
intrinsic (`_mm_clmulepi64_si128` on x86, `vmull_p64` on aarch64) or a
portable shift-and-XOR fallback. The Lean reference implementation is
`Hex.pureClmul`. The hex-gf2 SPEC explicitly flags this extern boundary
as a divergence risk and requires that the compiled wrapper agree with
`pureClmul` on a stream of inputs.

The stream below is a deterministic 64-bit LCG (Knuth's MMIX
constants, multiplier `6364136223846793005`, increment
`1442695040888963407`) seeded from a fixed start state. Successive
draws supply `(a, b)` pairs; the cross-check passes iff every pair
satisfies `clmul a b = pureClmul a b`.

Mode: `always` (Lean-only, no oracle).
Profile: `core`.
-/

namespace Hex
namespace ClmulCrossCheck

/-- One step of a 64-bit linear congruential generator using the MMIX
constants. The `UInt64` arithmetic wraps modulo `2^64`, which is
exactly the LCG modulus. -/
private def stepLCG (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

/-- True iff the extern-backed `clmul` agrees with `pureClmul` on the
first `n` pairs `(a, b)` produced by `stepLCG` starting from `s`.
Each pair consumes two consecutive draws so that `a` and `b` are
independent within the stream. -/
private def streamAgreesAux (s : UInt64) : Nat → Bool
  | 0 => true
  | n + 1 =>
    let a := s
    let s₁ := stepLCG s
    let b := s₁
    let s₂ := stepLCG s₁
    if clmul a b == pureClmul a b then
      streamAgreesAux s₂ n
    else
      false

@[inline] private def streamAgrees (seed : UInt64) (n : Nat) : Bool :=
  streamAgreesAux seed n

/-- Production stream length required by the SPEC cross-check. -/
private def streamLength : Nat := 10000

/-- Fixed seed for the production cross-check. Chosen to be nonzero in
both halves so the very first draws exercise carries past bit 32. -/
private def streamSeed : UInt64 := 0xCAFEBABEDEADBEEF

-- Sanity: the LCG is not stuck on the seed.
#guard stepLCG streamSeed != streamSeed

-- Sanity: agreement on the empty prefix is vacuous.
#guard streamAgrees streamSeed 0 = true

-- Sanity: agreement on a single pair matches the direct check.
#guard streamAgrees streamSeed 1 =
  (clmul streamSeed (stepLCG streamSeed) == pureClmul streamSeed (stepLCG streamSeed))

-- The SPEC cross-check: `clmul` agrees with `pureClmul` on
-- `streamLength` pseudorandom 64-bit pairs.
#guard streamAgrees streamSeed streamLength

/-- Discriminator self-test: replace `clmul` with a deliberately flipped
reference whose low word is XORed with `1`, and confirm that the same
stream rejects it. Without this guard, `streamAgrees` returning `true`
on the production stream would not by itself prove the loop ever
performs a meaningful comparison. -/
private def streamAgreesFlippedAux (s : UInt64) : Nat → Bool
  | 0 => true
  | n + 1 =>
    let a := s
    let s₁ := stepLCG s
    let b := s₁
    let s₂ := stepLCG s₁
    let (hi, lo) := pureClmul a b
    if clmul a b == (hi, lo ^^^ 1) then
      streamAgreesFlippedAux s₂ n
    else
      false

#guard streamAgreesFlippedAux streamSeed streamLength = false

end ClmulCrossCheck
end Hex
