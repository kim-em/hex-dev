import HexBerlekamp.DistinctDegree
import LeanBench

/-!
Benchmark registrations for `hex-berlekamp`.

This Phase 4 infrastructure slice measures Berlekamp matrix construction,
Rabin irreducibility testing, split-step Berlekamp factorization, and
distinct-degree factorization over the fixed small prime `5`. Inputs are
deterministic and monic where the API requires monicity; timed targets return
compact checksums or summaries of the computed structures.

Scientific registrations:

* `runBerlekampMatrixChecksum`: build `Q_f` for a degree-`n` input,
  `O(n^2)` for fixed small `p` (sparse `X^p mod f`).
* `runRabinTestChecksum`: Rabin irreducibility test on a degree-`n` input,
  `O(n^3)`.
* `runBerlekampFactorChecksum`: Berlekamp split-step factorization,
  `O(n^2)`.
* `runDistinctDegreeChecksum`: distinct-degree factorization, `O(n^3)`.
-/

namespace Hex
namespace BerlekampBench

open Berlekamp

private instance benchBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

instance : Hashable (ZMod64 5) where
  hash a := hash a.toNat

instance : Hashable (FpPoly 5) where
  hash f := hash f.toArray

/-- Prepared monic input shared by Berlekamp matrix, Rabin, and DDF surfaces. -/
structure MonicInput where
  poly : FpPoly 5
  monic : DensePoly.Monic poly

instance : Hashable MonicInput where
  hash input := hash input.poly

/-- Prepared input for the Berlekamp split-step factoring surface.

Both `poly` and `witness` are dense polynomials of comparable degree so each
`gcd(poly, witness - c)` attempt exercises a representative quadratic Euclidean
gcd, rather than the `O(n)` shortcut a low-degree witness would expose. -/
structure SplitInput where
  poly : FpPoly 5
  witness : FpPoly 5

instance : Hashable SplitInput where
  hash input := mixHash (hash input.poly) (hash input.witness)

/-- Deterministic `F_5` coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : ZMod64 5 :=
  ZMod64.ofNat 5 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 5

/-- Deterministic monic polynomial of degree `degree`. -/
def monicPoly (degree salt : Nat) : FpPoly 5 :=
  { coeffs := ((Array.range degree).map fun i => coeffValue degree i salt).push 1
    normalized := by
      right
      intro hback
      have hlast :
          (((Array.range degree).map fun i => coeffValue degree i salt).push
              (1 : ZMod64 5)).back? = some 1 := by
        simp
      rw [hlast] at hback
      exact one_ne_zero_five (Option.some.inj hback) }

/-- Generated monic polynomials have leading coefficient one. -/
theorem monicPoly_monic (degree salt : Nat) : DensePoly.Monic (monicPoly degree salt) := by
  unfold monicPoly DensePoly.Monic DensePoly.leadingCoeff
  change (((Array.range degree).map fun i => coeffValue degree i salt).push
    (1 : ZMod64 5)).back?.getD 0 = 1
  simp

/-- Stable checksum for polynomial-valued benchmark results. -/
def checksumPoly (f : FpPoly 5) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum for square matrices over `F_5`. -/
def checksumMatrix {n : Nat} (M : Matrix (ZMod64 5) n n) : UInt64 :=
  M.toArray.foldl
    (fun acc row =>
      mixHash acc <| row.toArray.foldl (fun rowAcc coeff => mixHash rowAcc (hash coeff)) 0)
    0

/-- Stable checksum for distinct-degree factorization results. -/
def checksumDistinctDegree (result : DistinctDegreeFactorization 5) : UInt64 :=
  let buckets :=
    result.buckets.foldl
      (fun acc bucket => mixHash (mixHash acc (hash bucket.degree)) (checksumPoly bucket.factor))
      0
  mixHash buckets (checksumPoly result.residual)

/-- Tail-recursive helper for `fibPoly`. -/
private def fibPolyAux : Nat → FpPoly 5 → FpPoly 5 → FpPoly 5
  | 0, prev, _ => prev
  | k + 1, prev, curr => fibPolyAux k curr (FpPoly.X * curr + prev)

/-- Fibonacci-like polynomial family `f_0 = 1`, `f_1 = X`, `f_k = X * f_{k-1} + f_{k-2}`.
Each `f_k` is monic of degree `k`; the pair `(f_n, f_{n-1})` is the textbook
worst-case Euclidean gcd on which `gcd(f_n, f_{n-1}) = 1` takes `n` steps with
quadratic total cost. -/
def fibPoly (n : Nat) : FpPoly 5 := fibPolyAux n 1 FpPoly.X

/-- Per-parameter fixture for Berlekamp matrix and Rabin paths. -/
def prepLinearProductInput (n : Nat) : MonicInput :=
  { poly := monicPoly (n + 1) 101
    monic := monicPoly_monic (n + 1) 101 }

/-- Per-parameter fixture with both linear and quadratic distinct-degree buckets. -/
def prepMixedDegreeInput (n : Nat) : MonicInput :=
  { poly := monicPoly (n + 3) 211
    monic := monicPoly_monic (n + 3) 211 }

/-- Per-parameter fixture for one Berlekamp split-step factoring search.

`poly = fibPoly (n + 2)`, `witness = fibPoly (n + 1)` is the textbook Euclidean
worst case: `gcd(f_{n+2}, f_{n+1} - c)` runs `Θ(n)` Euclidean steps for each
`c`, giving the declared `O(n^2)` cost rather than the `O(n)` short-circuit a
random-input fixture would expose. -/
def prepSplitInput (n : Nat) : SplitInput :=
  { poly := fibPoly (n + 2)
    witness := fibPoly (n + 1) }

/-- Benchmark target: build and checksum the Berlekamp matrix. -/
def runBerlekampMatrixChecksum (input : MonicInput) : UInt64 :=
  checksumMatrix <| berlekampMatrix input.poly input.monic

/-- Benchmark target: run Rabin's irreducibility test. -/
def runRabinTestChecksum (input : MonicInput) : UInt64 :=
  hash <| rabinTest input.poly input.monic

/-- Benchmark target: run all `p` Berlekamp split candidates `gcd(f, h - c)` and
checksum them together. The full sweep avoids the variable-cost early exit of
`kernelWitnessSplit?` and exercises a fixed `p` quadratic gcd attempts. -/
def runBerlekampFactorChecksum (input : SplitInput) : UInt64 :=
  (List.range 5).foldl
    (fun acc c =>
      mixHash acc <|
        checksumPoly (splitFactorAt input.poly input.witness (ZMod64.ofNat 5 c)))
    0

/-- Benchmark target: run distinct-degree factorization and checksum its buckets. -/
def runDistinctDegreeChecksum (input : MonicInput) : UInt64 :=
  checksumDistinctDegree <| distinctDegreeFactor input.poly input.monic

/-
The implementation constructs one Frobenius column for each basis vector via
the iterative recurrence `column (j + 1) = column j * (X^p mod f) mod f`.
For fixed small `p = 5` and `n > p`, `X^p mod f = X^p` is the sparse single
monomial `X^5`, so each iterative step costs `O(p * n)` (shift by `p`
positions plus at most `p` monic reductions, each `O(n)`); over `n` columns
the total is `O(p * n^2) = O(n^2)` for fixed `p`.
-/
setup_benchmark runBerlekampMatrixChecksum n => n * n
  with prep := prepLinearProductInput
  where {
    paramFloor := 16
    paramCeiling := 192
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-
Rabin's test computes the degree-`n` Frobenius remainder and a bounded list of
gcd checks. The Frobenius power dominates for these dense inputs, giving cubic
work in the polynomial degree.
-/
setup_benchmark runRabinTestChecksum n => n * n * n
  with prep := prepLinearProductInput
  where {
    paramFloor := 8
    paramCeiling := 64
    paramSchedule := .custom #[8, 12, 16, 24, 32, 48, 64]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-
The split-step factoring surface computes `gcd(f, witness - c)` for the `p`
field constants `c` until a nontrivial factor is found. With both `f` and
`witness` dense and of degree `~n`, each Euclidean gcd is `O(n^2)`, and the
constant-bounded loop over `c` gives `O(p * n^2) = O(n^2)` per call for
fixed `p`.
-/
setup_benchmark runBerlekampFactorChecksum n => n * n
  with prep := prepSplitInput
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-
Distinct-degree factorization performs increasing Frobenius/gcd steps against
the residual. For the mixed linear/quadratic product family, the Frobenius
updates over degree-`n` inputs dominate, so the declared model is cubic.
-/
setup_benchmark runDistinctDegreeChecksum n => n * n * n
  with prep := prepMixedDegreeInput
  where {
    paramFloor := 12
    paramCeiling := 96
    paramSchedule := .custom #[12, 16, 24, 32, 48, 64, 96]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

end BerlekampBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
