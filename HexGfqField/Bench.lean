import HexGfqField.Operations
import LeanBench

/-!
Benchmark registrations for `hex-gfq-field`.

This Phase 4 smoke surface measures the executable finite-field wrapper over
`F_8191[x] / (f)`. The benchmark prime is a Mersenne prime, so the Frobenius
exponent has dense binary representation and exercises the square-and-multiply
multiply branch throughout the timed path. Inputs use deterministic dense
moduli of degree `n + 1`; construction is hoisted through `prep`, and timed
targets return compact polynomial checksums.

Scientific registrations:

* `runOfPolyReprChecksum`: field construction followed by projection,
  `O(n^2)`.
* `runAddChecksum`: field addition on canonical representatives, `O(n)`.
* `runMulChecksum`: field multiplication on canonical representatives,
  `O(n^2)`.
* `runNegSubChecksum`: field negation and subtraction, `O(n)`.
* `runPowChecksum`: square-and-multiply exponentiation, `O(n^2 log n)`.
* `runInvDivChecksum`: extended-gcd inversion and division, `O(n^2)`.
* `runZPowChecksum`: signed square-and-multiply exponentiation,
  `O(n^2 log n)`.
* `runFrobChecksum`: Frobenius as the `p`-th power, `O(n^2 log p)`.
-/

namespace Hex
namespace GFqFieldBench

open GFqField

private instance benchBoundsMersenne : ZMod64.Bounds 8191 := ⟨by decide, by decide⟩

private theorem one_ne_zero_mersenne : (1 : ZMod64 8191) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 8191) 1 0).mp h
  simp at hm

private def noNontrivialDivisors (p : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
      noNontrivialDivisors p k &&
        if k + 1 = 1 ∨ k + 1 = p then true else p % (k + 1) != 0

private theorem noNontrivialDivisors_sound {p n m : Nat} (hp0 : 0 < p)
    (hcheck : noNontrivialDivisors p n = true) (hmn : m ≤ n) (hm : m ∣ p) :
    m = 1 ∨ m = p := by
  induction n generalizing m with
  | zero =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      rcases hm with ⟨c, hc⟩
      omega
  | succ n ih =>
      have hparts :
          noNontrivialDivisors p n = true ∧
            ((n = 0 ∨ n + 1 = p) ∨ ¬p % (n + 1) = 0) := by
        simpa [noNontrivialDivisors] using hcheck
      by_cases hmle : m ≤ n
      · exact ih hparts.1 hmle hm
      · have hmEq : m = n + 1 := by omega
        subst m
        rcases hparts.2 with hleft | hnmod
        · rcases hleft with hn0 | hnp
          · left
            omega
          · exact Or.inr hnp
        · have hmod : p % (n + 1) = 0 := Nat.mod_eq_zero_of_dvd hm
          contradiction

set_option maxRecDepth 100000 in
private theorem prime_mersenne : Hex.Nat.Prime 8191 := by
  constructor
  · decide
  · intro m hm
    exact noNontrivialDivisors_sound (p := 8191) (n := 8191) (m := m)
      (by decide) (by decide) (Nat.le_of_dvd (by decide : 0 < 8191) hm) hm

instance : Hashable (ZMod64 8191) where
  hash a := hash a.toNat

instance : Hashable (FpPoly 8191) where
  hash f := hash f.toArray

/-- Deterministic large-prime coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : ZMod64 8191 :=
  ZMod64.ofNat 8191 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 8191

/-- Deterministic dense polynomial over the benchmark prime field. -/
def densePoly (n salt : Nat) : FpPoly 8191 :=
  FpPoly.ofCoeffs <| (Array.range n).map fun i => coeffValue n i salt

/-- Deterministic nonconstant modulus of degree `degree + 1`. -/
def modulus (degree : Nat) : FpPoly 8191 :=
  { coeffs := ((Array.range degree).map fun i => coeffValue degree i 503).push 1
    normalized := by
      right
      intro hback
      have hlast :
          (((Array.range degree).map fun i => coeffValue degree i 503).push
              (1 : ZMod64 8191)).back? = some 1 := by
        simp
      rw [hlast] at hback
      exact one_ne_zero_mersenne (Option.some.inj hback) }

/-- Generated moduli are nonconstant, so field representatives are meaningful. -/
theorem modulus_pos_degree (degree : Nat) : 0 < FpPoly.degree (modulus (degree + 1)) := by
  unfold FpPoly.degree DensePoly.degree? DensePoly.size modulus
  simp

/-! ## Per-degree irreducibility placeholders

The deterministic `modulus` generator is not designed to produce
irreducible polynomials at every degree, so a universally quantified
`FpPoly.Irreducible (modulus degree)` claim is unsound.  Instead, we
sorry irreducibility one degree at a time, restricted to the finite
set of degrees actually exercised by `paramSchedule` entries below.
Each such sorry is a *concrete* claim about a specific deterministic
polynomial: still unverified, but no longer universally quantified
over arbitrary degrees.

The fallback at degree 2 covers any benchmark `n` not in the
schedule (none today; included only to keep `bundleForN` total).

These per-degree sorries can be discharged later by checking each
specific polynomial against an external tool (e.g. python-flint) or
by replacing the deterministic generator with a known-irreducible
sparse family.  Until then they remain `sorry` to keep the residual
unsoundness grep-able. -/

private theorem modulus_2_irreducible : FpPoly.Irreducible (modulus 2) := by sorry
private theorem modulus_33_irreducible : FpPoly.Irreducible (modulus 33) := by sorry
private theorem modulus_49_irreducible : FpPoly.Irreducible (modulus 49) := by sorry
private theorem modulus_65_irreducible : FpPoly.Irreducible (modulus 65) := by sorry
private theorem modulus_97_irreducible : FpPoly.Irreducible (modulus 97) := by sorry
private theorem modulus_129_irreducible : FpPoly.Irreducible (modulus 129) := by sorry
private theorem modulus_193_irreducible : FpPoly.Irreducible (modulus 193) := by sorry
private theorem modulus_257_irreducible : FpPoly.Irreducible (modulus 257) := by sorry
private theorem modulus_513_irreducible : FpPoly.Irreducible (modulus 513) := by sorry
private theorem modulus_1025_irreducible : FpPoly.Irreducible (modulus 1025) := by sorry
private theorem modulus_2049_irreducible : FpPoly.Irreducible (modulus 2049) := by sorry
private theorem modulus_4097_irreducible : FpPoly.Irreducible (modulus 4097) := by sorry
private theorem modulus_8193_irreducible : FpPoly.Irreducible (modulus 8193) := by sorry
private theorem modulus_16385_irreducible : FpPoly.Irreducible (modulus 16385) := by sorry

/-- A modulus together with its positive-degree and irreducibility
witnesses, used by the benchmark prep functions to dispatch on the
parameter `n` and select the correct per-degree fixture. -/
private structure ModulusBundle where
  modulus : FpPoly 8191
  pos : 0 < FpPoly.degree modulus
  irr : FpPoly.Irreducible modulus

/-- Look up the per-degree modulus fixture for benchmark parameter `n`.
The match enumerates the union of `paramSchedule` entries used by the
registrations below; any `n` outside that schedule falls back to a
degree-2 fixture so that the function remains total. -/
private def bundleForN (n : Nat) : ModulusBundle :=
  match n with
  | 32 => ⟨modulus 33, modulus_pos_degree 32, modulus_33_irreducible⟩
  | 48 => ⟨modulus 49, modulus_pos_degree 48, modulus_49_irreducible⟩
  | 64 => ⟨modulus 65, modulus_pos_degree 64, modulus_65_irreducible⟩
  | 96 => ⟨modulus 97, modulus_pos_degree 96, modulus_97_irreducible⟩
  | 128 => ⟨modulus 129, modulus_pos_degree 128, modulus_129_irreducible⟩
  | 192 => ⟨modulus 193, modulus_pos_degree 192, modulus_193_irreducible⟩
  | 256 => ⟨modulus 257, modulus_pos_degree 256, modulus_257_irreducible⟩
  | 512 => ⟨modulus 513, modulus_pos_degree 512, modulus_513_irreducible⟩
  | 1024 => ⟨modulus 1025, modulus_pos_degree 1024, modulus_1025_irreducible⟩
  | 2048 => ⟨modulus 2049, modulus_pos_degree 2048, modulus_2049_irreducible⟩
  | 4096 => ⟨modulus 4097, modulus_pos_degree 4096, modulus_4097_irreducible⟩
  | 8192 => ⟨modulus 8193, modulus_pos_degree 8192, modulus_8193_irreducible⟩
  | 16384 => ⟨modulus 16385, modulus_pos_degree 16384, modulus_16385_irreducible⟩
  | _ => ⟨modulus 2, modulus_pos_degree 1, modulus_2_irreducible⟩

/-- Stable checksum for polynomial-valued benchmark results. -/
def checksumPoly (f : FpPoly 8191) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Prepared input for field construction/projection benchmarks. -/
structure OfPolyInput where
  modulus : FpPoly 8191
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  poly : FpPoly 8191

/-- Prepared input for binary field operations. -/
structure BinaryInput where
  modulus : FpPoly 8191
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  lhs : FiniteField modulus modulusDegreePos prime_mersenne modulusIrreducible
  rhs : FiniteField modulus modulusDegreePos prime_mersenne modulusIrreducible

/-- Prepared input for unary field operations. -/
structure UnaryInput where
  modulus : FpPoly 8191
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  value : FiniteField modulus modulusDegreePos prime_mersenne modulusIrreducible

/-- Prepared input for field exponentiation. -/
structure PowInput where
  modulus : FpPoly 8191
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  value : FiniteField modulus modulusDegreePos prime_mersenne modulusIrreducible
  exponent : Nat

/-- Prepared input for signed field exponentiation. -/
structure ZPowInput where
  modulus : FpPoly 8191
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  value : FiniteField modulus modulusDegreePos prime_mersenne modulusIrreducible
  exponent : Int

instance : Hashable OfPolyInput where
  hash input := mixHash (hash input.modulus) (hash input.poly)

instance : Hashable BinaryInput where
  hash input :=
    mixHash
      (mixHash (hash input.modulus) (hash <| repr input.lhs))
      (hash <| repr input.rhs)

instance : Hashable UnaryInput where
  hash input := mixHash (hash input.modulus) (hash <| repr input.value)

instance : Hashable PowInput where
  hash input :=
    mixHash (mixHash (hash input.modulus) (hash <| repr input.value)) (hash input.exponent)

instance : Hashable ZPowInput where
  hash input :=
    mixHash (mixHash (hash input.modulus) (hash <| repr input.value)) (hash input.exponent)

/-- Per-parameter fixture for field construction. -/
def prepOfPolyInput (n : Nat) : OfPolyInput :=
  let b := bundleForN n
  { modulus := b.modulus
    modulusDegreePos := b.pos
    modulusIrreducible := b.irr
    poly := densePoly (2 * (n + 1) + 1) 23 }

/-- Per-parameter fixture for field binary operations. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  let b := bundleForN n
  { modulus := b.modulus
    modulusDegreePos := b.pos
    modulusIrreducible := b.irr
    lhs := ofPoly b.modulus b.pos prime_mersenne b.irr (densePoly (n + 1) 37)
    rhs := ofPoly b.modulus b.pos prime_mersenne b.irr (densePoly (n + 1) 71) }

/-- Per-parameter fixture for field unary operations. -/
def prepUnaryInput (n : Nat) : UnaryInput :=
  let input := prepBinaryInput n
  { modulus := input.modulus
    modulusDegreePos := input.modulusDegreePos
    modulusIrreducible := input.modulusIrreducible
    value := input.lhs }

/-- Exponent with all bits set at the benchmark parameter's bit length. -/
def denseExponent (n : Nat) : Nat :=
  2 ^ (Nat.log2 (n + 1) + 1) - 1

/-- Per-parameter fixture for field exponentiation. -/
def prepPowInput (n : Nat) : PowInput :=
  let input := prepUnaryInput n
  { modulus := input.modulus
    modulusDegreePos := input.modulusDegreePos
    modulusIrreducible := input.modulusIrreducible
    value := input.value
    exponent := denseExponent n }

/-- Per-parameter fixture for signed field exponentiation. -/
def prepZPowInput (n : Nat) : ZPowInput :=
  let input := prepUnaryInput n
  { modulus := input.modulus
    modulusDegreePos := input.modulusDegreePos
    modulusIrreducible := input.modulusIrreducible
    value := input.value
    exponent := -Int.ofNat (denseExponent n) }

/-- Benchmark target: construct and project a finite-field representative. -/
def runOfPolyReprChecksum (input : OfPolyInput) : UInt64 :=
  checksumPoly <| repr <| ofPoly input.modulus input.modulusDegreePos
    prime_mersenne input.modulusIrreducible input.poly

/-- Benchmark target: field addition checksum. -/
def runAddChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly <| repr (input.lhs + input.rhs)

/-- Benchmark target: field multiplication checksum. -/
def runMulChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly <| repr (input.lhs * input.rhs)

/-- Benchmark target: field negation and subtraction checksum. -/
def runNegSubChecksum (input : BinaryInput) : UInt64 :=
  mixHash (checksumPoly <| repr (-input.lhs)) (checksumPoly <| repr (input.lhs - input.rhs))

/-- Benchmark target: field exponentiation checksum. -/
def runPowChecksum (input : PowInput) : UInt64 :=
  checksumPoly <| repr (input.value ^ input.exponent)

/-- Benchmark target: field inverse and division checksum. -/
def runInvDivChecksum (input : BinaryInput) : UInt64 :=
  mixHash (checksumPoly <| repr input.lhs⁻¹) (checksumPoly <| repr (input.lhs / input.rhs))

/-- Benchmark target: signed field exponentiation checksum. -/
def runZPowChecksum (input : ZPowInput) : UInt64 :=
  checksumPoly <| repr (zpow input.value input.exponent)

/-- Benchmark target: Frobenius checksum. -/
def runFrobChecksum (input : UnaryInput) : UInt64 :=
  checksumPoly <| repr (frob input.value)

/-
`ofPoly` normalizes through degree-`n` quotient-ring reduction, giving
quadratic work; `repr` is only the projection of the stored canonical
representative.
-/
setup_benchmark runOfPolyReprChecksum n => n * n
  with prep := prepOfPolyInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Field addition delegates to quotient-ring addition on canonical
degree-bounded representatives, followed by linear degree-bounded
normalization.
-/
setup_benchmark runAddChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Field multiplication delegates to quotient-ring multiplication: multiply two
degree-bounded dense representatives and reduce modulo a degree-`n` modulus,
giving the same quadratic model as quotient-ring multiplication.
-/
setup_benchmark runMulChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Negation and subtraction are linear coefficientwise operations on canonical
degree-bounded representatives, followed by degree-bounded normalization.
-/
setup_benchmark runNegSubChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The prepared all-ones exponent has Theta(log n) bits and exercises both the
square and multiply-by-base branch on every bit. Each field multiplication
delegates to a quadratic quotient-ring multiplication.
-/
setup_benchmark runPowChecksum n => n * n * Nat.log2 (n + 1)
  with prep := prepPowInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Inversion computes one polynomial extended gcd against a degree-`n` modulus and
reduces the inverse candidate. Division adds one quadratic field
multiplication after that inverse. The wider doubling ladder keeps the small
extended-gcd constants from dominating the fitted quadratic slope.
-/
setup_benchmark runInvDivChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 32
    paramCeiling := 1024
    paramSchedule := .custom #[32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Negative signed powers compute a natural power with Theta(log n) dense bits and
then invert the result. The quadratic multiplications in the power dominate the
single quadratic inverse at these parameters.
-/
setup_benchmark runZPowChecksum n => n * n * Nat.log2 (n + 1)
  with prep := prepZPowInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Frobenius is implemented as the fixed `p`-th power. The benchmark prime
`p = 8191` has all binary exponent bits set, so the square-and-multiply path
performs Theta(log p) quadratic field multiplications.
-/
setup_benchmark runFrobChecksum n => n * n * Nat.log2 8191
  with prep := prepUnaryInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end GFqFieldBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
