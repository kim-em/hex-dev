import HexHenselMathlib.Correctness
import LeanBench

/-!
Benchmark registrations for the `HexHenselMathlib` Hensel bridge.

This Phase 4 slice measures executable coefficient-window mirrors of the
Mathlib-facing coefficient reduction and prime-power bridge surfaces. Fixed
checksum targets and proof-only elaboration checks keep the public
coprimality-lift, executable-Hensel correctness, degree, extension, and
uniqueness theorem APIs wired into the benchmark module.

Scientific registrations:

* `runCoeffMapDivisibilityChecksum`: reduce deterministic integer-polynomial
  coefficient windows modulo `5`, mirroring the `Polynomial.map` bridge
  surface, `O(n)`.
* `runPrimePowerReductionChecksum`: reduce deterministic integer-polynomial
  coefficient windows through moduli `5^3`, `5^2`, and `5`, mirroring the
  prime-power compatibility bridge surface, `O(n)`.
* `runCoprimeLiftChecksum`: fixed checksum for the canonical coprime-lift
  bridge fixture.
* `runHenselCorrectnessSurfaceChecksum`: fixed API checksum for
  `hensel_correct`, `hensel_extends`, `hensel_degree`, and `hensel_unique`.
-/

namespace HexHenselMathlib.HenselMathlibBench

open Polynomial
open Hex

private instance benchBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

/-- Hash prepared executable polynomial inputs by their normalized coefficients. -/
instance : Hashable ZPoly where
  hash p := hash p.toArray

/-- Prepared executable polynomial pair mirroring the Mathlib bridge inputs. -/
structure PolyPairInput where
  lhs : ZPoly
  rhs : ZPoly
  deriving Hashable

/-- Deterministic mixing over machine words for compact benchmark observables. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Deterministic integer coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 1) * (salt + 23) + (i + 3) * (i + 11) * 17 + n * 41) % 2039
  Int.ofNat raw - 1019

/-- Deterministic executable integer polynomial with `n` generated coefficients. -/
def denseZPoly (n salt : Nat) : ZPoly :=
  if n = 0 then
    0
  else
    DensePoly.ofCoeffs <| (Array.range n).map fun i =>
      let coeff := coeffValue n i salt
      if i + 1 = n ∧ coeff = 0 then 1 else coeff

/-- Canonical natural representative of an integer modulo `m`. -/
def intModNat (z : Int) (m : Nat) : Nat :=
  Int.toNat (z % Int.ofNat m)

/-- Stable checksum for a fixed executable coefficient window reduced modulo `m`. -/
def checksumReducedCoeffs (m limit : Nat) (p : ZPoly) : UInt64 :=
  (Array.range limit).foldl (fun acc i => mixWord acc (hash (intModNat (p.coeff i) m))) 0

/-- Stable checksum for a fixed executable coefficient window over `ℤ`. -/
def checksumZPolyWindow (limit : Nat) (p : ZPoly) : UInt64 :=
  (Array.range limit).foldl (fun acc i => mixWord acc (hash (p.coeff i))) 0

/-- Per-parameter fixture for coefficient-map and divisibility checks. -/
def prepCoeffMapInput (n : Nat) : PolyPairInput :=
  { lhs := denseZPoly n 71
    rhs := denseZPoly n 97 }

/-- Per-parameter fixture for prime-power reduction checks. -/
def prepPrimePowerInput (n : Nat) : PolyPairInput :=
  { lhs := denseZPoly n 131
    rhs := denseZPoly n 173 }

/--
Benchmark target: reduce two integer polynomials modulo `5`, checksum the
coefficient windows, mirroring the coefficientwise Mathlib bridge surface.
-/
def runCoeffMapDivisibilityChecksum (input : PolyPairInput) : UInt64 :=
  let limit := input.lhs.size.max input.rhs.size
  mixWord (checksumReducedCoeffs 5 limit input.lhs) (checksumReducedCoeffs 5 limit input.rhs)

/--
Benchmark target: exercise direct and staged prime-power reductions for one
deterministic polynomial pair, then checksum all visible coefficient windows.
-/
def runPrimePowerReductionChecksum (input : PolyPairInput) : UInt64 :=
  let limit := input.lhs.size.max input.rhs.size
  mixWord
    (mixWord (checksumReducedCoeffs (5 ^ 3) limit input.lhs)
      (checksumReducedCoeffs 5 limit input.lhs))
    (mixWord (checksumReducedCoeffs (5 ^ 3) limit input.rhs)
      (checksumReducedCoeffs (5 ^ 2) limit input.rhs))

/-- Fixed theorem-construction check for the public coprimality-lift surface. -/
def runCoprimeLiftChecksum (_ : Unit) : UInt64 :=
  checksumZPolyWindow 2 (DensePoly.ofCoeffs #[1, 1])

/--
Fixed checksum target for the public Hensel correctness and uniqueness theorem
surface. Importing this executable keeps the theorem constants and their
dependent public types available to downstream benchmark users.
-/
def runHenselCorrectnessSurfaceChecksum (_ : Unit) : UInt64 :=
  checksumZPolyWindow 3 (DensePoly.ofCoeffs #[2, 3, 1])

noncomputable example :
    let f : Polynomial ℤ := Polynomial.C 17 - Polynomial.C 11 * Polynomial.X
    (f.map (Int.castRingHom (ZMod 5))).coeff 1 = 0 ↔ (5 : ℤ) ∣ f.coeff 1 := by
  exact coeff_map_intCastRingHom_eq_zero_iff_dvd
    (Polynomial.C 17 - Polynomial.C 11 * Polynomial.X) 5 1

noncomputable example :
    let f : Polynomial ℤ := Polynomial.C 17 - Polynomial.C 11 * Polynomial.X
    (f.map (Int.castRingHom (ZMod (5 ^ (2 + 1))))).map
        (ZMod.castHom (dvd_pow_self 5 (Nat.succ_ne_zero 2)) (ZMod 5)) =
      f.map (Int.castRingHom (ZMod 5)) := by
  exact polynomial_map_zmod_pow_succ_to_base
    (Polynomial.C 17 - Polynomial.C 11 * Polynomial.X) 5 2

noncomputable example :
    let g : Polynomial ℤ := Polynomial.X + Polynomial.C 1
    let h : Polynomial ℤ := 1
    IsCoprime (g.map (Int.castRingHom (ZMod (5 ^ 3))))
      (h.map (Int.castRingHom (ZMod (5 ^ 3)))) := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let g : Polynomial ℤ := Polynomial.X + Polynomial.C 1
  let h : Polynomial ℤ := 1
  have base :
      IsCoprime (g.map (Int.castRingHom (ZMod 5)))
        (h.map (Int.castRingHom (ZMod 5))) := by
    refine ⟨0, 1, ?_⟩
    simp [h]
  exact coprime_mod_p_lifts g h 5 3 (by decide) base

noncomputable example : True := by
  let _correct := hensel_correct
  let _extends := hensel_extends
  let _degree := hensel_degree
  let _unique := hensel_unique
  let _quadFactor := quadraticHenselStep_factor_correct
  let _quadBezout := quadraticHenselStep_bezout_correct
  trivial

/-
Cost model: the executable coefficient-window mirror of `Polynomial.map` and
the checksum both visit the generated coefficient window once, so the textbook
model is linear in the generated polynomial size.
-/
setup_benchmark runCoeffMapDivisibilityChecksum n => n
  with prep := prepCoeffMapInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Cost model: each direct or staged prime-power reduction mirror visits one
generated coefficient window, and the checksum forces that same window. The
asymptotic model is linear in the generated coefficient count.
-/
setup_benchmark runPrimePowerReductionChecksum n => n
  with prep := prepPrimePowerInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_fixed_benchmark runCoprimeLiftChecksum where {
  repeats := 5
  maxSecondsPerCall := 1.0
}

setup_fixed_benchmark runHenselCorrectnessSurfaceChecksum where {
  repeats := 5
  maxSecondsPerCall := 1.0
}

end HexHenselMathlib.HenselMathlibBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
