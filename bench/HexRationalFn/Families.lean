/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRationalFn.Scaling

/-!
Controlled rational-function families. Degree and cancellation are independent
axes: `normalizeDegree` holds the common factor fixed, while `normalizeCancel`
holds the residual degrees fixed. Their Euclidean chains have bounded length;
long Euclidean chains and balanced products are measured separately.
-/

namespace Hex.RationalFnFamilies
open DensePoly RationalFn
open RationalFnScaling (dense consecutive output)

private instance : Inhabited (RationalFn Rat) := ⟨0⟩
private instance : Hashable (RationalFn Rat) := ⟨fun f => hash (output f)⟩

def fraction (p q : DensePoly Rat) : RationalFn Rat :=
  if h : q ≠ 0 then normalize p q h else panic! "zero benchmark denominator"

structure Raw where
  p : DensePoly Rat
  q : DensePoly Rat

private instance : Hashable Raw := ⟨fun i => hash (i.p.toArray, i.q.toArray)⟩

def degreeInput (n : Nat) : Raw :=
  let a := dense (max n 1)
  ⟨scale (3 : Rat) (a * #p[1, 1]), scale (-2) ((a + 1) * #p[1, 1])⟩

def cancelInput (n : Nat) : Raw :=
  let h := dense (max n 1)
  ⟨scale (3 : Rat) (#p[1, 1] * h), scale (-2) (#p[2, 1] * h)⟩

def normalizeDegree (i : Raw) := output (fraction i.p i.q)
def normalizeCancel (i : Raw) := output (fraction i.p i.q)
def checkedFraction (i : Raw) := (ofFraction? i.p i.q).map output
def generate (i : Raw) :=
  if h : i.q ≠ 0 then
    let c := certifyWith defaultPlan i.p i.q h
    (c.num.toArray, c.den.toArray, c.s.toArray, c.t.toArray)
  else (#[], #[], #[], #[])

def config : LeanBench.BenchmarkConfig :=
  { paramSchedule := .custom #[32, 64, 128, 256, 512, 1024, 2048, 4096],
    targetInnerNanos := 2000000000, maxSecondsPerCall := 10, outerTrials := 3 }

-- Cost model: Θ(n): a and a+1 have constant-length Euclidean quotient chains. The fixed
-- linear common factor adds bounded quotient work; exact division by it and
-- final scaling traverse dense length-n arrays with bounded coefficients.
setup_benchmark normalizeDegree n => n with prep := degreeInput where { config with tags := #["degree"] }
-- Cost model: Θ(n): the two residual linear factors are fixed. Euclid cancels their dense
-- common factor in boundedly many linear array operations; final outputs are fixed.
setup_benchmark normalizeCancel n => n with prep := cancelInput where { config with tags := #["degree"] }
-- Cost model: Θ(n): the checked constructor adds a constant-time zero-denominator guard to
-- the same degree-varying normalization; the complete result hash is linear.
setup_benchmark checkedFraction n => n with prep := degreeInput where { config with tags := #["degree"] }
-- Cost model: Θ(n): normalization plus xgcd of consecutive degree-n residuals has a bounded
-- quotient chain and bounded coefficients. All four certificate arrays are hashed.
setup_benchmark generate n => n with prep := degreeInput where { config with tags := #["degree"] }

structure Pair where
  f : RationalFn Rat
  g : RationalFn Rat
  deriving Hashable

def cancelPair (n : Nat) : Pair :=
  let f := consecutive (dense (max n 1))
  ⟨f, f⁻¹⟩

def coprimePair (n : Nat) : Pair :=
  let f := consecutive (dense (max n 1))
  ⟨f, fraction 1 #p[0, 1]⟩

def sharedPair (n : Nat) : Pair :=
  let h := dense (max n 1)
  ⟨fraction 1 (h * #p[0, 1]), fraction (-2) (h * #p[1, 1])⟩

def sharedCancelPair (n : Nat) : Pair :=
  let h := dense (max n 1) * #p[-1, 1]
  ⟨fraction 1 (h * #p[0, 1]), fraction (-2) (h * #p[1, 1])⟩

def zeroSumPair (n : Nat) : Pair :=
  let f := consecutive (dense (max n 1))
  ⟨f, -f⟩

def addCoprime (i : Pair) := output (i.f + i.g)
def addShared (i : Pair) := output (i.f + i.g)
def addCancel (i : Pair) := output (i.f + i.g)
def addTotal (i : Pair) := output (i.f + i.g)
def addEqual (i : Pair) := output (i.f + i.f)
def subtract (i : Pair) := output (i.f - i.g)
def multiply (i : Pair) := output (i.f * i.g)
def cancelMultiply (i : Pair) := output (i.f * i.g)
def divide (i : Pair) := output (i.f / i.g)
def checkedDivide (i : Pair) := (div? i.f i.g).map output

-- Cost model: Θ(n): one degree-n and one fixed linear denominator are coprime; bounded
-- remainder chains, linear unbalanced products, and bounded coefficient arithmetic.
setup_benchmark addCoprime n => n with prep := coprimePair where { config with tags := #["degree"] }
-- Cost model: Θ(n): the shared degree-n factor leaves fixed linear cofactors. The second gcd
-- is against 1-X, whose synthetic-division partial sums have O(log n) bits
-- (machine-word-sized throughout this ladder). Every product has a short factor.
setup_benchmark addShared n => n with prep := sharedPair where { config with tags := #["degree"] }
-- Cost model: Θ(n): here the shared denominator factor includes X-1, so the
-- second gcd really cancels X-1 from the numerator 1-X. All products and exact
-- divisors have bounded short degree; synthetic-division sums stay word-sized.
setup_benchmark addCancel n => n with prep := sharedCancelPair where { config with tags := #["degree"] }
-- Cost model: Θ(n): equal denominators take the direct branch; adding opposite
-- dense numerators visits n coefficients before returning the canonical zero.
setup_benchmark addTotal n => n with prep := zeroSumPair where { config with tags := #["degree"] }
-- Cost model: Θ(n): equal-denominator addition normalizes 2a/(a+1), whose Euclidean chain
-- has bounded length; coefficient scaling and full result hashing are linear.
setup_benchmark addEqual n => n with prep := cancelPair where { config with tags := #["degree"] }
-- Cost model: Θ(n): negation plus the same coprime-denominator addition chain and hash walk.
setup_benchmark subtract n => n with prep := coprimePair where { config with tags := #["degree"] }
-- Cost model: Θ(n): cross gcds with one or X have bounded quotient chains. Products have
-- fixed short factors; this coprime control actually forms a growing numerator/denominator.
setup_benchmark multiply n => n with prep := coprimePair where { config with tags := #["degree"] }
-- Cost model: Θ(n): both cross gcds cancel equal dense polynomials. Exact quotient work scans
-- those arrays; final products are constant. This is maximal cancellation only.
setup_benchmark cancelMultiply n => n with prep := cancelPair where { config with tags := #["degree"] }
-- Cost model: Θ(n): inversion of a fixed linear fraction followed by the same unbalanced
-- cancellation/product work. No rational coefficient height grows with n.
setup_benchmark divide n => n with prep := coprimePair where { config with tags := #["degree"] }
-- Cost model: Θ(n): the nonzero guard is constant; the successful division and full hash dominate.
setup_benchmark checkedDivide n => n with prep := coprimePair where { config with tags := #["degree"] }

def inverseInput (n : Nat) : RationalFn Rat :=
  let f := consecutive (dense (max n 1))
  ofCoprime (scale 2 f.num) f.den f.monic_den
    (f.bezout.scale_left (by decide))

def inverse (f : RationalFn Rat) := output f⁻¹
def checkedInverse (f : RationalFn Rat) := (inv? f).map output

-- Cost model: Θ(n): the numerator leading coefficient is two, so both swapped arrays must
-- be scaled by 1/2. This exercises nonmonic inversion, not the sharing fast path.
setup_benchmark inverse n => n with prep := inverseInput where { config with tags := #["degree"] }
-- Cost model: Θ(n): the checked nonzero guard adds constant work to nonmonic inversion.
setup_benchmark checkedInverse n => n with prep := inverseInput where { config with tags := #["degree"] }

def accept (i : RationalFnScaling.ReplayInput) := (ofCert? i.p i.q i.cert).map output
-- Cost model: Θ(n): validating the degree-n Bezout witnesses dominates; accepted pair degree
-- stays one. This benchmarks construction through the public checked replay API.
setup_benchmark accept n => n with prep := Hex.RationalFnScaling.prepWitness where { config with tags := #["degree"] }

end Hex.RationalFnFamilies
