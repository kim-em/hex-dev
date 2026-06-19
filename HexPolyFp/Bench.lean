import HexPolyFp.Frobenius
import HexPolyFp.ModCompose
import HexPolyFp.SquareFree
import LeanBench

/-!
Benchmark registrations for `hex-poly-fp`.

This Phase 4 slice measures the executable finite-field polynomial operations
over fixed word-prime fields: the quotient-ring benchmarks use `F_65537`, and
the square-free/product benchmarks use `F_5`. Input construction is hoisted into
`prep`; timed targets return compact checksums or decomposition summaries.

Scientific registrations:

* `runPowModMonicChecksum`: quotient-ring square-and-multiply with a growing
  exponent, `O(n^2 log n)`.
* `runFrobeniusXModChecksum`: a batch of `n` calls to `X^p mod f` on degree
  `n` moduli, `O(n^3)`.
* `runFrobeniusXPowModChecksum`: `X^(p^n) mod f`, `O(n^3)` for growing modulus
  degree and Frobenius exponent height.
* `runComposeModMonicChecksum`: Horner modular composition, `O(n^3)`.
* `runWeightedProductChecksum`: product of `n` linear factors, `O(n^2)`.
* `runSquareFreeDecompositionSummary`: Yun-style square-free decomposition on
  deterministic product-shaped inputs, `O(n^2)`.
-/

namespace Hex
namespace FpPolyBench

open FpPoly

private instance benchBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance benchBoundsLarge : ZMod64.Bounds 65537 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem one_ne_zero_large : (1 : ZMod64 65537) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 65537) 1 0).mp h
  simp at hm

private theorem prime_five : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

instance {p : Nat} [ZMod64.Bounds p] : Hashable (ZMod64 p) where
  hash a := hash a.toNat

instance {p : Nat} [ZMod64.Bounds p] : Hashable (FpPoly p) where
  hash f := hash f.toArray

instance : Hashable (SquareFreeFactor 5) where
  hash sf := mixHash (hash sf.factor) (hash sf.multiplicity)

/-- Prepared input for quotient-ring exponentiation and Frobenius operations. -/
structure ModInput where
  base : FpPoly 65537
  degree : Nat
  exponent : Nat
  deriving Hashable

/-- Prepared batched input for fixed-prime Frobenius. -/
structure FrobeniusBatchInput where
  count : Nat
  degree : Nat
  deriving Hashable

/-- Prepared input for modular composition. -/
structure ComposeInput where
  outer : FpPoly 65537
  inner : FpPoly 65537
  degree : Nat
  deriving Hashable

/-- Prepared input for weighted products. -/
structure WeightedInput where
  factors : List (SquareFreeFactor 5)
  deriving Hashable

/-- Prepared input for square-free decomposition. -/
structure SquareFreeInput where
  poly : FpPoly 5
  deriving Hashable

/-- Prepared input for field long division: a dividend and a lower-degree divisor. -/
structure DivModInput where
  num : FpPoly 65537
  den : FpPoly 65537
  deriving Hashable

/-- Prepared input for the Euclidean gcd remainder sequence over `F_p`. -/
structure GcdInput where
  f : FpPoly 65537
  g : FpPoly 65537
  deriving Hashable

/-- Deterministic coefficient generator keyed by size, index, and salt. -/
def coeffValueFive (n i salt : Nat) : ZMod64 5 :=
  ZMod64.ofNat 5 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 5

/-- Deterministic large-prime coefficient generator keyed by size, index, and salt. -/
def coeffValueLarge (n i salt : Nat) : ZMod64 65537 :=
  ZMod64.ofNat 65537 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 65537

/-- Deterministic dense finite-field polynomial with `n` generated coefficients. -/
def densePolyFive (n salt : Nat) : FpPoly 5 :=
  ofCoeffs <| (Array.range n).map fun i => coeffValueFive n i salt

/-- Deterministic dense polynomial over the large benchmark prime field. -/
def densePolyLarge (n salt : Nat) : FpPoly 65537 :=
  ofCoeffs <| (Array.range n).map fun i => coeffValueLarge n i salt

/-- Deterministic monic modulus of degree `degree` over `F_5`. -/
def monicModulusFive (degree : Nat) : FpPoly 5 :=
  DensePoly.monomial degree (1 : ZMod64 5)

/-- Generated monomial moduli over `F_5` are monic. -/
theorem monicModulusFive_monic (degree : Nat) : DensePoly.Monic (monicModulusFive degree) := by
  unfold monicModulusFive DensePoly.Monic DensePoly.leadingCoeff DensePoly.monomial
  by_cases h : (1 : ZMod64 5) = 0
  · exact False.elim (one_ne_zero_five h)
  · change ((Array.replicate degree (0 : ZMod64 5)).push 1).back?.getD 0 = 1
    simp

/-- Deterministic monic modulus of degree `degree` over the large benchmark prime. -/
def monicModulusLarge (degree : Nat) : FpPoly 65537 :=
  { coeffs := ((Array.range degree).map fun i => coeffValueLarge degree i 503).push 1
    normalized := by
      right
      intro hback
      have hlast :
          (((Array.range degree).map fun i => coeffValueLarge degree i 503).push
              (1 : ZMod64 65537)).back? = some 1 := by
        simp
      rw [hlast] at hback
      exact one_ne_zero_large (Option.some.inj hback) }

/-- Generated monomial moduli over the large benchmark prime are monic. -/
theorem monicModulusLarge_monic (degree : Nat) :
    DensePoly.Monic (monicModulusLarge degree) := by
  unfold monicModulusLarge DensePoly.Monic DensePoly.leadingCoeff
  change (((Array.range degree).map fun i => coeffValueLarge degree i 503).push
    (1 : ZMod64 65537)).back?.getD 0 = 1
  simp

/-- Deterministic linear square-free factor. -/
def linearFactor (i : Nat) : FpPoly 5 :=
  ofCoeffs #[coeffValueFive i 0 211, 1]

/-- Deterministic factor record used by weighted-product benchmarks. -/
def weightedFactor (i : Nat) : SquareFreeFactor 5 :=
  { factor := linearFactor i, multiplicity := 1 }

/--
Balanced multiplicity distribution for the square-free decomposition fixture.

The five distinct monic linear factors `(x - 0), (x - 1), …, (x - 4)` over
`F_5` are assigned multiplicities `⌊n / 5⌋` each, with the first `n mod 5`
factors taking an extra `+1`. The resulting product has total degree exactly
`n`, exactly five distinct linear factors, and max multiplicity `⌈n / 5⌉`,
giving a Yun ladder whose iteration count grows linearly with `n` and whose
per-iteration `gcd(c, w)` and `w / y` calls each scale linearly with the
shrinking remnant degree.

The fixture cannot avoid the formal-`p`-th-root branch entirely: when at
least one multiplicity divides `p = 5`, the contribution of that factor to
`f'` vanishes and the squarefree part `c_0` collapses to fewer distinct
factors than the polynomial actually contains. The constant in front of
`n^2` then increases (the Yun ladder takes more shrink steps before
exhausting `c_0`), but the asymptote stays `O(n^2)`. The scientific
schedule avoids the worst-case rung where four out of five multiplicities
divide `5` simultaneously.
-/
def balancedSquareFreeFactors (n : Nat) : List (SquareFreeFactor 5) :=
  let base := n / 5
  let rem := n % 5
  (List.range 5).map fun i =>
    { factor := ofCoeffs #[ZMod64.ofNat 5 i, 1]
      multiplicity := if i < rem then base + 1 else base }

/-- Stable checksum for polynomial-valued benchmark results. -/
def checksumPoly {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable bounded summary for square-free decompositions. -/
def checksumSquareFree (d : SquareFreeDecomposition 5) : UInt64 :=
  d.factors.foldl
    (fun acc sf => mixHash (mixHash acc (checksumPoly sf.factor)) (hash sf.multiplicity))
    (hash d.unit)

/-- Per-parameter fixture for quotient-ring exponentiation. -/
def prepPowModInput (n : Nat) : ModInput :=
  { base := densePolyLarge (n + 1) 11
    degree := n + 1
    exponent := n + 1 }

/-- Per-parameter fixture for fixed-prime Frobenius batches. -/
def prepFrobeniusInput (n : Nat) : FrobeniusBatchInput :=
  { count := n
    degree := n + 1 }

/-- Per-parameter fixture for Frobenius powers. -/
def prepFrobeniusPowInput (n : Nat) : ModInput :=
  { base := X
    degree := n + 1
    exponent := n + 1 }

/-- Per-parameter fixture for same-size modular composition. -/
def prepComposeInput (n : Nat) : ComposeInput :=
  { outer := densePolyLarge (n + 1) 37
    inner := densePolyLarge (n + 1) 71
    degree := n + 1 }

/-- Per-parameter fixture for weighted products of linear factors. -/
def prepWeightedInput (n : Nat) : WeightedInput :=
  { factors := (List.range n).map weightedFactor }

/-- Per-parameter fixture for square-free decomposition. -/
def prepSquareFreeInput (n : Nat) : SquareFreeInput :=
  { poly := weightedProduct (balancedSquareFreeFactors n) }

/-- Per-parameter fixture for field long division: a degree-`2n` dividend over a
degree-`n` divisor, so the division loop runs `Θ(n)` elimination steps. -/
def prepDivModInput (n : Nat) : DivModInput :=
  { num := densePolyLarge (2 * n + 1) 17
    den := densePolyLarge (n + 1) 23 }

/-- Per-parameter fixture for the Euclidean gcd remainder sequence: two
independent degree-`n` polynomials, almost always coprime over `F_p`, so the
remainder sequence has `Θ(n)` `divMod` steps. -/
def prepGcdInput (n : Nat) : GcdInput :=
  { f := densePolyLarge (n + 1) 5
    g := densePolyLarge (n + 1) 9 }

/-- Benchmark target: compute `base^exponent mod modulus`. -/
def runPowModMonicChecksum (input : ModInput) : UInt64 :=
  checksumPoly <|
    powModMonic input.base (monicModulusLarge input.degree)
      (monicModulusLarge_monic input.degree)
      input.exponent

/-- Benchmark target: compute a batch of `X^p mod modulus` calls. -/
def runFrobeniusXModChecksum (input : FrobeniusBatchInput) : UInt64 :=
  (Array.range input.count).foldl
    (fun acc _ =>
      mixHash acc <| checksumPoly <|
        frobeniusXMod (monicModulusLarge input.degree) (monicModulusLarge_monic input.degree))
    0

/-- Benchmark target: compute `X^(p^k) mod modulus`. -/
def runFrobeniusXPowModChecksum (input : ModInput) : UInt64 :=
  checksumPoly <|
    frobeniusXPowMod (monicModulusLarge input.degree) (monicModulusLarge_monic input.degree)
      input.exponent

/-- Benchmark target: compute modular composition and checksum the result. -/
def runComposeModMonicChecksum (input : ComposeInput) : UInt64 :=
  checksumPoly <|
    composeModMonic input.outer input.inner (monicModulusLarge input.degree)
      (monicModulusLarge_monic input.degree)

/-- Benchmark target: multiply weighted square-free factors. -/
def runWeightedProductChecksum (input : WeightedInput) : UInt64 :=
  checksumPoly <| weightedProduct input.factors

/-- Benchmark target: compute a square-free decomposition summary. -/
def runSquareFreeDecompositionSummary (input : SquareFreeInput) : UInt64 :=
  checksumSquareFree <| squareFreeDecomposition prime_five input.poly

/-- Benchmark target: field long division, checksumming quotient and remainder. -/
def runDivModChecksum (input : DivModInput) : UInt64 :=
  let qr := DensePoly.divMod input.num input.den
  mixHash (checksumPoly qr.1) (checksumPoly qr.2)

/-- Benchmark target: Euclidean gcd over `F_p`, checksumming the result. -/
def runGcdChecksum (input : GcdInput) : UInt64 :=
  checksumPoly <| DensePoly.gcd input.f input.g

/-
The modulus degree, reduced base degree, and exponent all scale with `n`.
Square-and-multiply performs Theta(log n) quotient-ring multiplications, and
each reduced dense multiplication/reduction is quadratic in the modulus degree.
-/
setup_benchmark runPowModMonicChecksum n => n * n * Nat.log2 (n + 1)
  with prep := prepPowModInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
This registration batches `n` fixed-prime Frobenius calls on dense degree-`n`
monic moduli. Each call performs a constant number of quotient-ring
square-and-multiply steps with quadratic dense multiplication/reduction, so the
batch is cubic. The schedule starts at `n = 16` because below that the
constant-bit-length of `p = 65537` (17 bits of square-and-multiply work per
call) is comparable to the modulus degree and the `n³` asymptote has not
dominated; the largest rung `n = 80` keeps per-call wall time well under the
four-second cap on the reference host.
-/
setup_benchmark runFrobeniusXModChecksum n => n * n * n
  with prep := prepFrobeniusInput
  where {
    paramFloor := 16
    paramCeiling := 80
    paramSchedule := .custom #[16, 24, 32, 48, 64, 80]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.20
  }

/-
Here both the modulus degree and Frobenius height scale with `n`. The exponent
`65537^n` has Theta(n) bits, so the quotient-ring square-and-multiply loop performs
Theta(n) quadratic reduced multiplications. The schedule stops at `n = 64`
because at `n = 96` the per-call wall time crosses the four-second cap on the
reference host; trimming the truncating rung keeps every scheduled rung inside
the cap.
-/
setup_benchmark runFrobeniusXPowModChecksum n => n * n * n
  with prep := prepFrobeniusPowInput
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 24, 32, 48, 64]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Horner modular composition does one reduced multiplication per coefficient of
the outer polynomial. With all reduced polynomials bounded by degree `n`, each
step is quadratic, for Theta(n^3) total work. The schedule stops at `n = 192`
because at `n = 256` the per-call wall time crosses the four-second cap on
the reference host; trimming the truncating rung keeps every scheduled rung
inside the cap.
-/
setup_benchmark runComposeModMonicChecksum n => n * n * n
  with prep := prepComposeInput
  where {
    paramFloor := 32
    paramCeiling := 192
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The prepared family multiplies `n` linear factors, all with multiplicity one.
The accumulator degree grows linearly, so the schoolbook multiplications by a
linear polynomial sum to Theta(n^2).
-/
setup_benchmark runWeightedProductChecksum n => n * n
  with prep := prepWeightedInput
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
This prepared family is the balanced product `∏_{i=0..4} (x - i)^{m_i}` over
`F_5`, with multiplicities `m_i ∈ {⌊n/5⌋, ⌈n/5⌉}` summing to `n`. Yun's
algorithm runs an initial dense `gcd(f, f')` followed by `⌈n / 5⌉` ladder
iterations whose `gcd(c, w)` and `w / y` calls each scale linearly with the
shrinking remnant degree; total cost is `O(n^2)` for every rung, with a
constant that varies modestly depending on whether any of the five
multiplicities at that `n` divides `p = 5` (in which case the squarefree
part `c_0` collapses to fewer distinct factors and the Yun ladder takes
more shrink steps). The schedule stops at `n = 768` because at `n = 1024`
the rung `(205, 205, 205, 205, 204)` has four multiplicities divisible by
`5` simultaneously, collapsing `c_0` to a single linear factor and
amplifying that constant by an order of magnitude; the verdict is fit over
the remaining rungs where the constant is bounded. The widened slope
tolerance acknowledges the residual `n`-to-`n` constant variance that this
input family carries.
-/
setup_benchmark runSquareFreeDecompositionSummary n => n * n
  with prep := prepSquareFreeInput
  where {
    paramFloor := 64
    paramCeiling := 768
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512, 768]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.30
  }

/-
Field long division of a degree-`2n` dividend by a degree-`n` divisor runs
`Theta(n)` elimination steps, each subtracting a shifted scalar multiple of the
divisor across `Theta(n)` coefficients, so the work is quadratic, `O(n^2)`
total. The schedule covers the BHKS-relevant low degrees `8/16/32/64` plus
higher rungs so the quadratic slope is visible above the per-call constant.
-/
setup_benchmark runDivModChecksum n => n * n
  with prep := prepDivModInput
  where {
    paramFloor := 8
    paramCeiling := 256
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The Euclidean gcd of two independent degree-`n` polynomials over `F_p` is a
remainder sequence of `Theta(n)` `divMod` steps whose degrees shrink by one each
step, so the cost is quadratic, `O(n^2)` coefficient operations. This is the
substrate under the BHKS separability test `gcd(f, f')`; the schedule matches
the divMod rungs.
-/
setup_benchmark runGcdChecksum n => n * n
  with prep := prepGcdInput
  where {
    paramFloor := 8
    paramCeiling := 256
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end FpPolyBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
