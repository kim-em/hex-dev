import HexHensel.Multifactor
import HexHensel.QuadraticMultifactor

/-!
Core conformance checks for the `HexHensel` bridge and ordered-product surface.

Oracle: Sage or FLINT for external Hensel-lifting profiles; core uses Lean-only
property checks.
Mode: if_available
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

end HenselConformance
end Hex
