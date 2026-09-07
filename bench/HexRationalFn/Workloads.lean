/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRationalFn.Families
import HexPolyFp.PrimeField

/-!
Complementary degree, output-size, Euclidean-chain, and coefficient-height
axes. Height registrations use the published quadratic coefficient-arithmetic
upper bound, not a two-sided prediction of GMP's data-dependent gcd paths.
The prime-field chain isolates polynomial work from rational height growth.
-/

namespace Hex.RationalFnWorkloads
open DensePoly RationalFn
open RationalFnFamilies (Raw Pair fraction config)
open RationalFnScaling (dense consecutive output)

private instance : Inhabited (RationalFn Rat) := ⟨0⟩
private instance : Hashable (RationalFn Rat) := ⟨fun f => hash (output f)⟩
private instance : Hashable Raw := ⟨fun i => hash (i.p.toArray, i.q.toArray)⟩
private instance : Hashable Pair := ⟨fun i => hash (output i.f, output i.g)⟩

def linearFraction (n : Nat) := fraction (dense (max n 1)) #p[0, 1]
def squareDenominator (n : Nat) := fraction (dense (max n 1)) #p[0, 0, 1]
def polynomial (n : Nat) : RationalFn Rat := ofPoly (dense (max n 1))
def derivative (f : RationalFn Rat) := output (RationalFn.derivative f)
def derivativeCancel (f : RationalFn Rat) := output (RationalFn.derivative f)
def derivativePolynomial (f : RationalFn Rat) := output (RationalFn.derivative f)
def polynomialPart (f : RationalFn Rat) :=
  let (q, r) := split f
  (q.toArray, output r)

-- Cost model: Θ(n): (p/X)' = (Xp'-p)/X², with nonzero constant coefficient -1.
-- Every product/divisor has bounded degree; the gcd chain has bounded length.
-- Coefficients and derivative multipliers remain machine-word-sized on the ladder.
setup_benchmark derivative n => n with prep := linearFraction where { config with tags := #["degree"] }
-- Cost model: Θ(n): the quotient-rule numerator for p/X² has exactly one common factor X
-- with X⁴. Cancelling it leaves (Xp'-2p)/X³; all other work is linear scans.
setup_benchmark derivativeCancel n => n with prep := squareDenominator where { config with tags := #["degree"] }
-- Cost model: Θ(n): polynomial differentiation visits n coefficients, then normalizes over
-- denominator one. This separately covers the polynomial/zero-remainder branch.
setup_benchmark derivativePolynomial n => n with prep := polynomial where { config with tags := #["degree"] }
-- Cost model: Θ(n): division by X scans the input once; the nonzero remainder is its
-- constant coefficient. Constructing the proper part adds no gcd computation.
setup_benchmark polynomialPart n => n with prep := linearFraction where { config with tags := #["degree"] }

/-- Three-way Karatsuba recurrence on the power-of-two scientific ladder. -/
def multiplicationCost (n : Nat) : Nat := 3 ^ Nat.log2 (max n 1)

def balanced (n : Nat) : Pair :=
  ⟨polynomial n, ofPoly (dense (max n 1) + 1)⟩
def multiply (i : Pair) := output (i.f * i.g)
def square (f : RationalFn Rat) := output (f ^ (2 : Nat))

-- Cost model: Θ(n^log₂3): the balanced product obeys T(n)=3T(n/2)+Θ(n).
-- Denominator-one gcd/division and full hashing are linear. Product coefficient
-- heights are O(log n), within machine words across the declared ladder.
setup_benchmark multiply n => multiplicationCost n with prep := balanced where { config with tags := #["degree"] }
-- Cost model: Θ(n^log₂3): exponent two performs one specialized square. Output degree is
-- 2n, so this is an output-size ladder rather than a fixed-output power anchor.
setup_benchmark square n => multiplicationCost n with prep := polynomial where { config with tags := #["degree"] }

/-- Vary the long/short ratio, including an odd short length that pads recursive
Karatsuba blocks. Both lengths exceed the schoolbook dispatch cutoff. -/
def unbalancedInput (n : Nat) : Pair × Pair :=
  let pair := fun m =>
    (⟨ofPoly (dense (m * max n 1 - 1)), ofPoly (dense (m - 1))⟩ : Pair)
  (pair 33, pair 64)

def unbalanced (i : Pair × Pair) := (multiply i.1, multiply i.2)
def unbalancedSchoolbook (i : Pair × Pair) :=
  let product := fun j => output (mulWith schoolbookPlan j.f j.g)
  (product i.1, product i.2)

private def ratioConfig : LeanBench.BenchmarkConfig :=
  { config with
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512]
    tags := #["degree", "ratio"] }

-- Cost model: Θ(n): with fixed short lengths m=33,64 and long length mn,
-- there are n balanced blocks, each costing M(m), and Θ(mn) accumulator updates
-- and output hashing. This tests the SPEC's O(ceil(long/short)*M(short)) bound
-- along its ratio axis, independently of the balanced degree ladder.
setup_benchmark unbalanced n => n with prep := unbalancedInput where ratioConfig
-- Cost model: Θ(n): schoolbook costs Θ((mn)m), with m fixed at 33 and 64.
-- It has the same canonical full output and parameter domain as unbalanced.
setup_benchmark unbalancedSchoolbook n => n with prep := unbalancedInput where ratioConfig

def constructors (n : Nat) :=
  let p : DensePoly Rat := #p[(n : Rat), 1]
  (output (ofPoly p), output (C (n : Rat)), output (X : RationalFn Rat),
    output (n : RationalFn Rat), output (-(n : Int) : RationalFn Rat),
    (toPoly? (ofPoly p)).map DensePoly.toArray)
-- Cost model: Θ(1): these constructors share their input polynomial or build at most two
-- coefficients; projection tests denominator one. n varies coefficient values,
-- not degree, and remains word-sized. Full output consumption is also bounded.
setup_benchmark constructors _n => 1 where { config with tags := #["degree"] }

scoped instance : ZMod64.Bounds 7 := ⟨by decide, by decide⟩
scoped instance : ZMod64.PrimeModulus 7 := ZMod64.primeModulusOfPrime (by decide)
abbrev F := ZMod64 7
private instance : Hashable F := ⟨fun x => hash x.toNat⟩
private instance : Inhabited (RationalFn F) := ⟨0⟩
private instance : Hashable (DensePoly F) := ⟨fun p => hash p.toArray⟩
private instance : Hashable (RationalFn F) := ⟨fun f => hash (f.num.toArray, f.den.toArray)⟩

/-- Consecutive continuants with every Euclidean quotient equal to X+1.
Each recurrence increases degree by one, also in characteristic seven. -/
def continuants (n : Nat) : DensePoly F × DensePoly F := Id.run do
  let mut a : DensePoly F := 1
  let mut b : DensePoly F := #p[1, 1]
  for _ in [0:n] do
    let c := #p[1, 1] * b + a
    a := b
    b := c
  return (b, a)

def normalizeChain (i : DensePoly F × DensePoly F) :=
  if h : i.2 ≠ 0 then
    let f := normalize i.1 i.2 h
    (f.num.toArray, f.den.toArray)
  else (#[], #[])

-- Mode 2: O(M(n) log n) field operations for half-gcd and O(M(n)) divisions,
-- with M(n)=n^log₂3 for the selected Karatsuba plan. All field costs are bounded.
-- Source: van der Hoeven, Optimizing the half-gcd algorithm, introduction,
-- https://www.texmacs.org/joris/gcd/gcd.pdf . A tight family wallclock model is
-- not asserted: finite-characteristic cancellations change matrix supports and
-- admissible high-half blocks, despite the prescribed full Euclidean chain.
setup_benchmark normalizeChain n => multiplicationCost n * (Nat.log2 n + 1)
  with prep := continuants where { config with tags := #["degree", "upper-bound"] }

def powerInput (n : Nat) : Nat × RationalFn F := (n, ofPoly #p[1, 1])
def power (i : Nat × RationalFn F) :=
  let f := i.2 ^ i.1
  (f.num.toArray, f.den.toArray)
-- Cost model: Θ(n^log₂3): exponent n produces degree n. The geometrically increasing
-- specialized squares have total cost Θ(M(n)); raw Karatsuba visits stored
-- zero coefficients too, so modular cancellations do not skip the recurrence.
setup_benchmark power n => multiplicationCost n with prep := powerInput where { config with tags := #["degree"] }

def heightRaw (bits : Nat) : Raw :=
  let k := 2 ^ max bits 1
  let u : Rat := (k + 1 : Nat) / (k + 3 : Nat)
  let v : Rat := (k + 5 : Nat) / (k + 7 : Nat)
  let a := dense 4
  ⟨scale u (a * #p[1, 1]), scale v ((a + 1) * #p[1, 1])⟩

def heightPair (bits : Nat) : Pair :=
  let i := heightRaw bits
  ⟨fraction i.p i.q, fraction i.q i.p⟩
def heightNormalize (i : Raw) := RationalFnFamilies.normalizeDegree i
def heightAdd (i : Pair) := output (i.f + i.g)
def heightMultiply (i : Pair) := output (i.f * i.f)
def heightDerivative (i : Pair) := output (RationalFn.derivative i.f)

def heightConfig : LeanBench.BenchmarkConfig :=
  { config with paramSchedule := .custom #[128, 256, 512, 1024, 2048, 4096, 8192, 16384] }

-- Mode 2 for all four height cases: fixed polynomial degrees bound the number
-- of field operations and all intermediate bit lengths by O(bits). Classical
-- multiplication/division and Lehmer gcd are O(bits²); faster GMP dispatches
-- preserve that upper bound. Source: GNU MP manual, Lehmer's Algorithm,
-- https://gmplib.org/manual/Lehmer_0027s-Algorithm . No tight family model is
-- available across GMP thresholds and data-dependent quotient sequences;
-- degree-only models cannot cover the dominant rational coefficient work.
setup_benchmark heightNormalize n => n ^ 2 with prep := heightRaw where { heightConfig with tags := #["coefficient-height", "upper-bound"] }
-- Same fixed-degree coefficient-arithmetic bound; includes the two gcd phases.
setup_benchmark heightAdd n => n ^ 2 with prep := heightPair where { heightConfig with tags := #["coefficient-height", "upper-bound"] }
-- Same bit bound; squaring a nonconstant canonical fraction forms full products.
setup_benchmark heightMultiply n => n ^ 2 with prep := heightPair where { heightConfig with tags := #["coefficient-height", "upper-bound"] }
-- Same bit bound; quotient-rule products and normalization retain fixed degrees.
setup_benchmark heightDerivative n => n ^ 2 with prep := heightPair where { heightConfig with tags := #["coefficient-height", "upper-bound"] }

end Hex.RationalFnWorkloads
