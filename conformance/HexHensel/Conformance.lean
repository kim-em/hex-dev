/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexHensel.Multifactor
import HexHensel.QuadraticMultifactor

/-!
Core conformance checks for the `HexHensel` conversion and ordered-product surface.

Oracle: Sage or FLINT for external Hensel-lifting profiles; core uses Lean-only
property checks.
Mode: `if_available`
Covered operations:
- `ZPoly.modP`
- `FpPoly.liftToZ`
- `ZPoly.reduceModPow`
- `Array.polyProduct`
- `ZPoly.multifactorLift`
- `ZPoly.multifactorLiftQuadratic`
Covered properties:
- reduction modulo `p` uses canonical representatives coefficientwise
- lifting from `F_p[x]` uses canonical nonnegative integer representatives
- reducing modulo `p^k` preserves coefficientwise congruence on committed inputs
- ordered products use left-fold multiplication with identity `1`
- the multifactor lifters carry the product congruence
  `∏ liftedFactors ≡ f (mod p^k)`
- linear and quadratic multifactor lifts agree on shared inputs after
  canonicalisation by `ZPoly.reduceModPow _ p k` (executable mirror of the
  lift-uniqueness obligation discharged in `hex-hensel-mathlib`)
Covered edge cases:
- zero and empty polynomial inputs
- empty factor arrays and identity products
- modulus exponent `k = 0`
- internal zeros, negative coefficients, and trailing-zero normalization
- multifactor lift at the trivial precision `k = 1`
-/

namespace Hex
namespace HenselConformance

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private def zcoeffs (f : ZPoly) : List Int :=
  f.toArray.toList

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def fpCoeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def coeffMod (z : Int) (m : Nat) : Nat :=
  Int.toNat (z % Int.ofNat m)

private def modPCoeffsMatch (p : Nat) [ZMod64.Bounds p] (f : ZPoly) (bound : Nat) : Bool :=
  (List.range bound).all (fun i =>
    (ZPoly.modP p f).coeff i == ZMod64.ofNat p (coeffMod (f.coeff i) p))

private def liftCoeffsInRange (f : FpPoly 5) (bound : Nat) : Bool :=
  (List.range bound).all (fun i =>
    0 ≤ (FpPoly.liftToZ f).coeff i ∧ (FpPoly.liftToZ f).coeff i < 5)

private def congrAt (f g : ZPoly) (m i : Nat) : Bool :=
  ((f.coeff i - g.coeff i) % (m : Int)) == 0

private def congrOn (f g : ZPoly) (m bound : Nat) : Bool :=
  (List.range bound).all (fun i => congrAt f g m i)

private def modPTypical : ZPoly := DensePoly.ofCoeffs #[7, -1, 12]
private def modPEdge : ZPoly := 0
private def modPAdversarial : ZPoly := DensePoly.ofCoeffs #[-6, 0, 14, 0, 0]

#guard fpCoeffNats (ZPoly.modP 5 modPTypical) = [2, 4, 2]
#guard fpCoeffNats (ZPoly.modP 5 modPEdge) = []
#guard fpCoeffNats (ZPoly.modP 5 modPAdversarial) = [4, 0, 4]

#guard modPCoeffsMatch 5 modPTypical 5
#guard modPCoeffsMatch 5 modPEdge 3
#guard modPCoeffsMatch 5 modPAdversarial 6

private def liftTypical : FpPoly 5 := polyFive #[4, 0, 3]
private def liftEdge : FpPoly 5 := 0
private def liftAdversarial : FpPoly 5 := polyFive #[9, 0, 12, 0, 0]

#guard zcoeffs (FpPoly.liftToZ liftTypical) = [4, 0, 3]
#guard zcoeffs (FpPoly.liftToZ liftEdge) = []
#guard zcoeffs (FpPoly.liftToZ liftAdversarial) = [4, 0, 2]

#guard liftCoeffsInRange liftTypical 5
#guard liftCoeffsInRange liftEdge 3
#guard liftCoeffsInRange liftAdversarial 6

#guard ZPoly.modP 5 (FpPoly.liftToZ liftTypical) = liftTypical
#guard ZPoly.modP 5 (FpPoly.liftToZ liftEdge) = liftEdge
#guard ZPoly.modP 5 (FpPoly.liftToZ liftAdversarial) = liftAdversarial

private def reduceTypical : ZPoly := DensePoly.ofCoeffs #[10, -1, 17]
private def reduceEdge : ZPoly := DensePoly.ofCoeffs #[4, -2, 0, 0]
private def reduceAdversarial : ZPoly := DensePoly.ofCoeffs #[-9, 0, 16, 24, 0, 0]

#guard zcoeffs (ZPoly.reduceModPow reduceTypical 3 2) = [1, 8, 8]
#guard zcoeffs (ZPoly.reduceModPow reduceEdge 7 0) = []
#guard zcoeffs (ZPoly.reduceModPow reduceAdversarial 2 3) = [7]

#guard congrOn (ZPoly.reduceModPow reduceTypical 3 2) reduceTypical (3 ^ 2) 5
#guard congrOn (ZPoly.reduceModPow reduceEdge 7 0) reduceEdge (7 ^ 0) 5
#guard congrOn (ZPoly.reduceModPow reduceAdversarial 2 3) reduceAdversarial (2 ^ 3) 6

private def productTypicalFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[1, 1], DensePoly.ofCoeffs #[2, 1]]

private def productEdgeFactors : Array ZPoly :=
  #[]

private def productAdversarialFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[3, 0, 0], 0, DensePoly.ofCoeffs #[4, 1]]

#guard zcoeffs (Array.polyProduct productTypicalFactors) = [2, 3, 1]
#guard Array.polyProduct productEdgeFactors = (1 : ZPoly)
#guard Array.polyProduct productAdversarialFactors = (0 : ZPoly)

#guard Array.polyProduct productTypicalFactors =
  (DensePoly.ofCoeffs #[1, 1] : ZPoly) * DensePoly.ofCoeffs #[2, 1]
#guard Array.polyProduct productEdgeFactors =
  productEdgeFactors.foldl (· * ·) (1 : ZPoly)
#guard Array.polyProduct productAdversarialFactors =
  productAdversarialFactors.foldl (· * ·) (1 : ZPoly)

/-
Multifactor Hensel lift fixtures.

Each fixture supplies a target polynomial `f` together with an exact
factorisation over `Z` whose factors are pairwise coprime modulo `p = 5`.
Choosing `f := Array.polyProduct factors` keeps the precondition
`∏ factors ≡ f (mod p)` trivially satisfied and lets the conformance
checks below assert the *lift* obligation
`∏ (lifted factors) ≡ f (mod p^k)` for non-trivial `k`.
-/

private def qmTypicalFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[1, 1],
    DensePoly.ofCoeffs #[2, 1],
    DensePoly.ofCoeffs #[3, 1]]

private def qmTypicalF : ZPoly := Array.polyProduct qmTypicalFactors

/-- Edge fixture: precision `k = 1`, where the lift collapses to the
input factors taken modulo `p`. -/
private def qmEdgeFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[2, 1, 1],
    DensePoly.ofCoeffs #[3, 1],
    DensePoly.ofCoeffs #[1, 1]]

private def qmEdgeF : ZPoly := Array.polyProduct qmEdgeFactors

/-- Adversarial fixture: four monic linear factors at `k = 6`. The split
tree has three nontrivial nodes and the doubling loop runs three times
per split; this is the case used for the asymptotic-gap commentary at
the bottom of the file. -/
private def qmAdversarialFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[1, 1],
    DensePoly.ofCoeffs #[2, 1],
    DensePoly.ofCoeffs #[3, 1],
    DensePoly.ofCoeffs #[4, 1]]

private def qmAdversarialF : ZPoly := Array.polyProduct qmAdversarialFactors

private def reduceArrModPow (a : Array ZPoly) (p k : Nat) : Array ZPoly :=
  a.map (fun g => ZPoly.reduceModPow g p k)

-- Product congruence: ∏ (multifactorLiftQuadratic …) ≡ f (mod p^k).

#guard congrOn
  (Array.polyProduct (ZPoly.multifactorLiftQuadratic 5 4 qmTypicalF qmTypicalFactors))
  qmTypicalF (5 ^ 4) 6

#guard congrOn
  (Array.polyProduct (ZPoly.multifactorLiftQuadratic 5 1 qmEdgeF qmEdgeFactors))
  qmEdgeF (5 ^ 1) 8

#guard congrOn
  (Array.polyProduct (ZPoly.multifactorLiftQuadratic 5 6 qmAdversarialF qmAdversarialFactors))
  qmAdversarialF (5 ^ 6) 8

-- Linear/quadratic agreement after canonicalisation modulo `p^k`. This is
-- the executable mirror of the lift-uniqueness statement that lives in
-- `hex-hensel-mathlib`: the two paths produce identical factor arrays
-- once each factor is reduced to its canonical representative in
-- `[0, p^k)` via `ZPoly.reduceModPow`.

/-
The `k = 1` edge fixture checks the trivial path where both algorithms
return the input factors modulo `p`. The `k = 4` typical fixture and
`k = 6` adversarial fixture check the same linear/quadratic agreement at
higher precision, after both paths canonicalise factors modulo `p^k`.
-/
#guard reduceArrModPow (ZPoly.multifactorLift 5 1 qmEdgeF qmEdgeFactors) 5 1
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 1 qmEdgeF qmEdgeFactors) 5 1

#guard reduceArrModPow (ZPoly.multifactorLift 5 4 qmTypicalF qmTypicalFactors) 5 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 4 qmTypicalF qmTypicalFactors) 5 4

#guard reduceArrModPow (ZPoly.multifactorLift 5 6 qmAdversarialF qmAdversarialFactors) 5 6
     = reduceArrModPow
        (ZPoly.multifactorLiftQuadratic 5 6 qmAdversarialF qmAdversarialFactors) 5 6

/-
Canonical-coefficient conformance for the quadratic lift (issue #9131).

The quadratic recursion reaches `p^k` from `p^ceil(k/2)`, so for even `k`
the doubling step lands on `p^k` exactly and its output is already
canonical there; only an odd `k`, whose step overshoots to `p^(k+1)`,
needs the descent. The compiled shapes drop the reductions the even case
makes redundant, and the leaf reduction below the root of the product
tree, so these checks exercise both parities on both sides of the
word-to-bignum boundary. `#guard` runs the compiled code, so it sees the
`@[csimp]` implementations rather than the specifications.

At `p = 5` the word-sized step guard is `m * m < 2^64` for the step's own
modulus `m = 5^ceil(k/2)`, so `5^13` is the last half-exponent that fits.
Targets `k = 26` (even, top step at `5^13`, word path) and `k = 27` (odd,
top step at `5^14`, bignum path) therefore bracket that boundary; `k = 40`
is the high-precision large-coefficient case, whose coefficients run to
`5^40 > 9 * 10^27`.
-/

private def qmParityFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[2, 1, 1],
    DensePoly.ofCoeffs #[3, 1],
    DensePoly.ofCoeffs #[4, 1],
    DensePoly.ofCoeffs #[1, 2, 1]]

private def qmParityF : ZPoly := Array.polyProduct qmParityFactors

-- Even target exponent, both steps inside the word path.
#guard congrOn
  (Array.polyProduct (ZPoly.multifactorLiftQuadratic 5 8 qmParityF qmParityFactors))
  qmParityF (5 ^ 8) 8
#guard reduceArrModPow (ZPoly.multifactorLift 5 8 qmParityF qmParityFactors) 5 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 8 qmParityF qmParityFactors) 5 8

-- Odd target exponent, where the descent from `p^(k+1)` is genuinely needed.
#guard congrOn
  (Array.polyProduct (ZPoly.multifactorLiftQuadratic 5 9 qmParityF qmParityFactors))
  qmParityF (5 ^ 9) 8
#guard reduceArrModPow (ZPoly.multifactorLift 5 9 qmParityF qmParityFactors) 5 9
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 9 qmParityF qmParityFactors) 5 9

-- Even target exponent whose top step is the last one the word path takes.
#guard congrOn
  (Array.polyProduct (ZPoly.multifactorLiftQuadratic 5 26 qmParityF qmParityFactors))
  qmParityF (5 ^ 26) 8
#guard reduceArrModPow (ZPoly.multifactorLift 5 26 qmParityF qmParityFactors) 5 26
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 26 qmParityF qmParityFactors) 5 26

-- Odd target exponent whose top step has crossed into the bignum path.
#guard congrOn
  (Array.polyProduct (ZPoly.multifactorLiftQuadratic 5 27 qmParityF qmParityFactors))
  qmParityF (5 ^ 27) 8
#guard reduceArrModPow (ZPoly.multifactorLift 5 27 qmParityF qmParityFactors) 5 27
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 27 qmParityF qmParityFactors) 5 27

-- High-precision large-coefficient case, whose top steps take the bignum path
-- while the lower recursive steps are still inside the word guard.
#guard congrOn
  (Array.polyProduct (ZPoly.multifactorLiftQuadratic 5 40 qmParityF qmParityFactors))
  qmParityF (5 ^ 40) 8
#guard reduceArrModPow (ZPoly.multifactorLift 5 40 qmParityF qmParityFactors) 5 40
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 40 qmParityF qmParityFactors) 5 40

-- Every lifted factor is canonical in `[0, p^k)`, which is what the dropped
-- reductions used to establish and the invariant now establishes instead.
private def arrCanonical (a : Array ZPoly) (p k : Nat) : Bool :=
  a.all (fun g => g.toArray.all (fun c => 0 ≤ c ∧ c < ((p ^ k : Nat) : Int)))

#guard arrCanonical (ZPoly.multifactorLiftQuadratic 5 8 qmParityF qmParityFactors) 5 8
#guard arrCanonical (ZPoly.multifactorLiftQuadratic 5 9 qmParityF qmParityFactors) 5 9
#guard arrCanonical (ZPoly.multifactorLiftQuadratic 5 26 qmParityF qmParityFactors) 5 26
#guard arrCanonical (ZPoly.multifactorLiftQuadratic 5 27 qmParityF qmParityFactors) 5 27
#guard arrCanonical (ZPoly.multifactorLiftQuadratic 5 40 qmParityF qmParityFactors) 5 40

-- The factor-only last step still agrees with the projection of the full
-- lift, at both parities and on both sides of the word-to-bignum boundary.
private def qmSplitG : ZPoly := DensePoly.ofCoeffs #[2, 1, 1]
private def qmSplitH : ZPoly := DensePoly.ofCoeffs #[3, 1]
private def qmSplitF : ZPoly := qmSplitG * qmSplitH

private def qmSplitS : ZPoly :=
  FpPoly.liftToZ (ZPoly.normalizedXGCD 5 qmSplitG qmSplitH).left
private def qmSplitT : ZPoly :=
  FpPoly.liftToZ (ZPoly.normalizedXGCD 5 qmSplitG qmSplitH).right

private def factorsMatchFullLift (k : Nat) : Bool :=
  let factors := ZPoly.henselLiftFactors 5 k qmSplitF qmSplitG qmSplitH qmSplitS qmSplitT
  let full := ZPoly.henselLiftQuadratic 5 k qmSplitF qmSplitG qmSplitH qmSplitS qmSplitT
  factors.1 == full.g && factors.2 == full.h

#guard factorsMatchFullLift 0
#guard factorsMatchFullLift 1
#guard factorsMatchFullLift 8
#guard factorsMatchFullLift 9
#guard factorsMatchFullLift 26
#guard factorsMatchFullLift 27
#guard factorsMatchFullLift 40

-- The two degenerate precisions the compiled tree walk short-circuits: at
-- `k = 0` the modulus is `1`, so every lifted factor is zero, and at `k = 1`
-- the lift is the input factors taken modulo `p`. Both are cases where the
-- leaf flag is set from a `henselLiftFactors` output, so both are checked
-- against the linear lift and for canonicity.
#guard reduceArrModPow (ZPoly.multifactorLift 5 0 qmParityF qmParityFactors) 5 0
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 0 qmParityF qmParityFactors) 5 0
#guard reduceArrModPow (ZPoly.multifactorLift 5 1 qmParityF qmParityFactors) 5 1
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 1 qmParityF qmParityFactors) 5 1
#guard arrCanonical (ZPoly.multifactorLiftQuadratic 5 1 qmParityF qmParityFactors) 5 1
#guard (ZPoly.multifactorLiftQuadratic 5 0 qmParityF qmParityFactors).all (· == 0)
#guard congrOn
  (Array.polyProduct (ZPoly.multifactorLiftQuadratic 5 1 qmParityF qmParityFactors))
  qmParityF (5 ^ 1) 8

/-
Boundary conformance for the windowed canonical representative.

`ZPoly.intModNatImpl` returns a value already in `[0, m)` untouched, covers
`[-m, 0)` with one addition, and falls back to `Int.emod` elsewhere. The
`@[csimp]` rule means `#guard` evaluates the windowed form, so these cases
pin the branch boundaries -- both signs of the window, the two endpoints
`z = m` and `z = -m`, values outside it, and the degenerate `m = 0`, where
`Int.emod z 0 = z` and the specification returns `Int.toNat z`.
-/
#guard ZPoly.intModNat 0 7 == 0
#guard ZPoly.intModNat 6 7 == 6
#guard ZPoly.intModNat 7 7 == 0
#guard ZPoly.intModNat 8 7 == 1
#guard ZPoly.intModNat 100 7 == 2
#guard ZPoly.intModNat (-1) 7 == 6
#guard ZPoly.intModNat (-7) 7 == 0
#guard ZPoly.intModNat (-8) 7 == 6
#guard ZPoly.intModNat (-100) 7 == 5
#guard ZPoly.intModNat 5 0 == 5
#guard ZPoly.intModNat (-5) 0 == 0
#guard ZPoly.intModNat 0 0 == 0
#guard ZPoly.intModNat (5 ^ 40) (5 ^ 40) == 0
#guard ZPoly.intModNat (5 ^ 40 - 1) (5 ^ 40) == 5 ^ 40 - 1
#guard ZPoly.intModNat (-(5 ^ 40)) (5 ^ 40) == 0

/-
Asymptotic-gap commentary (observation only; no timing assertion).

`multifactorLift` lifts to precision `p^k` via `k - 1` linear steps per
split; `multifactorLiftQuadratic` reaches the same precision via
`⌈log₂ k⌉` doubling steps per split. On the adversarial fixture above
(`p = 5`, `k = 6`, four monic linear factors), the linear path performs
`(k - 1) × (n - 1) = 5 × 3 = 15` per-step `linearHenselStep` invocations
across the recursive split tree; the quadratic path performs only
`⌈log₂ k⌉ × (n - 1) = 3 × 3 = 9` `quadraticHenselStep` invocations. The
gap grows roughly as `k / log₂ k` per split point and is the reason
`hex-berlekamp-zassenhaus` consumes `multifactorLiftQuadratic` rather
than `multifactorLift`. Performance is enforced separately in
`HexHensel/Bench.lean`; conformance only records the algebraic agreement
between the two paths.
-/

/-
Proof-mode conformance for the quadratic Hensel doubling step. Each
`example` witnesses that the `@[grind =>]` annotation on the matching
public theorem closes the natural downstream consumer shape: given the
base-modulus factorisation, Bezout pair, and monicity hypotheses, the
quadratic step delivers a `mod m^2` factorisation, preserves monicity,
and preserves the input factorisation at the base modulus.
-/

example (m : Nat) (f g h s t : ZPoly)
    (hm : 0 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    ZPoly.congr ((ZPoly.quadraticHenselStep m f g h s t).g *
                 (ZPoly.quadraticHenselStep m f g h s t).h) f (m * m) := by
  have := ZPoly.quadraticHenselStep_factor_spec m f g h s t hm hprod hbez hmonic
  grind only

example (m : Nat) (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    ZPoly.congr ((ZPoly.quadraticHenselStep m f g h s t).s *
                   (ZPoly.quadraticHenselStep m f g h s t).g +
                 (ZPoly.quadraticHenselStep m f g h s t).t *
                   (ZPoly.quadraticHenselStep m f g h s t).h) 1 (m * m) := by
  have := ZPoly.quadraticHenselStep_bezout_spec m f g h s t hm hprod hbez hmonic
  grind only

example (m : Nat) (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    ZPoly.congr ((ZPoly.quadraticHenselStep m f g h s t).g *
                 (ZPoly.quadraticHenselStep m f g h s t).h) f (m * m) ∧
      ZPoly.congr ((ZPoly.quadraticHenselStep m f g h s t).s *
                     (ZPoly.quadraticHenselStep m f g h s t).g +
                   (ZPoly.quadraticHenselStep m f g h s t).t *
                     (ZPoly.quadraticHenselStep m f g h s t).h) 1 (m * m) := by
  have := ZPoly.quadraticHenselStep_spec m f g h s t hm hprod hbez hmonic
  grind only

example (m : Nat) (f g h s t : ZPoly)
    (hm : 1 < m)
    (hmonic : DensePoly.Monic g) :
    DensePoly.Monic (ZPoly.quadraticHenselStep m f g h s t).g := by
  have := ZPoly.quadraticHenselStep_monic m f g h s t hm hmonic
  grind only

example (m : Nat) (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m) :
    ZPoly.congr (ZPoly.quadraticHenselStep m f g h s t).g g m ∧
      ZPoly.congr (ZPoly.quadraticHenselStep m f g h s t).h h m := by
  have := ZPoly.quadraticHenselStep_factor_congr_mod_base m f g h s t hm hprod
  grind only

end HenselConformance
end Hex
