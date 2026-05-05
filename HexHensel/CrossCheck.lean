import HexHensel.Multifactor
import HexHensel.QuadraticMultifactor

/-!
Linear-vs-quadratic multifactor Hensel lift cross-check at
`k ∈ {2, 4, 8, 16}` for `p ∈ {5, 7, 11}`.

Companion stream to `HexHensel/Conformance.lean`. The conformance file
sanity-checks the algorithmic surface at three hand-picked precisions
(`k = 1, 4, 6` over `p = 5`); this file widens coverage to a deterministic
grid of factor sets per `(p, k)` pair to strengthen the SPEC's
"linear lift is the reference surface" claim
(`SPEC/Libraries/hex-hensel.md`).

Each fixture supplies an array of monic linear factors with pairwise
distinct constants modulo `p` (hence pairwise coprime modulo `p`) and a
target polynomial `f := Array.polyProduct factors + p * shift` where
`shift` is a small fixed integer polynomial. With this choice
`∏ factors ≡ f (mod p)` while `∏ factors ≠ f` over `Z`, so the lift
performs genuine doubling/linear iteration rather than collapsing to an
input-preserving no-op.

The cross-check asserts
`reduceArrModPow (multifactorLift p k f factors) p k`
`= reduceArrModPow (multifactorLiftQuadratic p k f factors) p k`,
i.e. both lifts agree on the canonical representative of each lifted
factor in `[0, p^k)`. Since the lifted factor set is unique modulo `p^k`
under the coprimality precondition, any ±1 perturbation in either lift
step would diverge the two paths and trip the corresponding `#guard`.

Tier-G fast-vs-fast.
-/

namespace Hex
namespace HenselCrossCheck

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance boundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩
private instance boundsEleven : ZMod64.Bounds 11 := ⟨by decide, by decide⟩

private def reduceArrModPow (a : Array ZPoly) (p k : Nat) : Array ZPoly :=
  a.map (fun g => ZPoly.reduceModPow g p k)

private def linearFactor (c : Int) : ZPoly :=
  DensePoly.ofCoeffs #[c, 1]

private def factorsFromConstants (cs : Array Int) : Array ZPoly :=
  cs.map linearFactor

/-- `f := ∏ factors + p`. The constant-term shift by `p` keeps the
precondition `∏ factors ≡ f (mod p)` while ensuring `f ≠ ∏ factors` over
`Z`, so the lift converges to lifted factors that genuinely differ from
the inputs. -/
private def fixtureF (p : Nat) (factors : Array ZPoly) : ZPoly :=
  Array.polyProduct factors + DensePoly.ofCoeffs #[(p : Int)]

-- p = 5 fixtures: 5 factor sets (3, 3, 4, 4, 5 monic linear factors).
private def factors5a : Array ZPoly := factorsFromConstants #[1, 2, 3]
private def factors5b : Array ZPoly := factorsFromConstants #[0, 1, 4]
private def factors5c : Array ZPoly := factorsFromConstants #[1, 2, 3, 4]
private def factors5d : Array ZPoly := factorsFromConstants #[0, 2, 3, 4]
private def factors5e : Array ZPoly := factorsFromConstants #[0, 1, 2, 3, 4]

private def f5a : ZPoly := fixtureF 5 factors5a
private def f5b : ZPoly := fixtureF 5 factors5b
private def f5c : ZPoly := fixtureF 5 factors5c
private def f5d : ZPoly := fixtureF 5 factors5d
private def f5e : ZPoly := fixtureF 5 factors5e

-- DELIBERATE-CORRUPTION SANITY CHECK: perturbing the linear lift output by
-- adding 1 to a constant term must trip the cross-check.
private def perturbedFirstFactor (a : Array ZPoly) : Array ZPoly :=
  if h : 0 < a.size then
    a.set 0 (a[0]'h + DensePoly.ofCoeffs #[1])
  else a

#guard reduceArrModPow (perturbedFirstFactor (ZPoly.multifactorLift 5 2 f5a factors5a)) 5 2
     ≠ reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 2 f5a factors5a) 5 2

-- k = 2 over p = 5
#guard reduceArrModPow (ZPoly.multifactorLift 5 2 f5a factors5a) 5 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 2 f5a factors5a) 5 2
#guard reduceArrModPow (ZPoly.multifactorLift 5 2 f5b factors5b) 5 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 2 f5b factors5b) 5 2
#guard reduceArrModPow (ZPoly.multifactorLift 5 2 f5c factors5c) 5 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 2 f5c factors5c) 5 2
#guard reduceArrModPow (ZPoly.multifactorLift 5 2 f5d factors5d) 5 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 2 f5d factors5d) 5 2
#guard reduceArrModPow (ZPoly.multifactorLift 5 2 f5e factors5e) 5 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 2 f5e factors5e) 5 2

-- k = 4 over p = 5
#guard reduceArrModPow (ZPoly.multifactorLift 5 4 f5a factors5a) 5 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 4 f5a factors5a) 5 4
#guard reduceArrModPow (ZPoly.multifactorLift 5 4 f5b factors5b) 5 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 4 f5b factors5b) 5 4
#guard reduceArrModPow (ZPoly.multifactorLift 5 4 f5c factors5c) 5 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 4 f5c factors5c) 5 4
#guard reduceArrModPow (ZPoly.multifactorLift 5 4 f5d factors5d) 5 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 4 f5d factors5d) 5 4
#guard reduceArrModPow (ZPoly.multifactorLift 5 4 f5e factors5e) 5 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 4 f5e factors5e) 5 4

-- k = 8 over p = 5
#guard reduceArrModPow (ZPoly.multifactorLift 5 8 f5a factors5a) 5 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 8 f5a factors5a) 5 8
#guard reduceArrModPow (ZPoly.multifactorLift 5 8 f5b factors5b) 5 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 8 f5b factors5b) 5 8
#guard reduceArrModPow (ZPoly.multifactorLift 5 8 f5c factors5c) 5 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 8 f5c factors5c) 5 8
#guard reduceArrModPow (ZPoly.multifactorLift 5 8 f5d factors5d) 5 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 8 f5d factors5d) 5 8
#guard reduceArrModPow (ZPoly.multifactorLift 5 8 f5e factors5e) 5 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 8 f5e factors5e) 5 8

-- k = 16 over p = 5
#guard reduceArrModPow (ZPoly.multifactorLift 5 16 f5a factors5a) 5 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 16 f5a factors5a) 5 16
#guard reduceArrModPow (ZPoly.multifactorLift 5 16 f5b factors5b) 5 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 16 f5b factors5b) 5 16
#guard reduceArrModPow (ZPoly.multifactorLift 5 16 f5c factors5c) 5 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 16 f5c factors5c) 5 16
#guard reduceArrModPow (ZPoly.multifactorLift 5 16 f5d factors5d) 5 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 16 f5d factors5d) 5 16
#guard reduceArrModPow (ZPoly.multifactorLift 5 16 f5e factors5e) 5 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 5 16 f5e factors5e) 5 16

-- p = 7 fixtures
private def factors7a : Array ZPoly := factorsFromConstants #[1, 2, 3]
private def factors7b : Array ZPoly := factorsFromConstants #[0, 3, 5]
private def factors7c : Array ZPoly := factorsFromConstants #[1, 2, 3, 4]
private def factors7d : Array ZPoly := factorsFromConstants #[0, 2, 4, 6]
private def factors7e : Array ZPoly := factorsFromConstants #[0, 1, 2, 3, 5]

private def f7a : ZPoly := fixtureF 7 factors7a
private def f7b : ZPoly := fixtureF 7 factors7b
private def f7c : ZPoly := fixtureF 7 factors7c
private def f7d : ZPoly := fixtureF 7 factors7d
private def f7e : ZPoly := fixtureF 7 factors7e

-- k = 2 over p = 7
#guard reduceArrModPow (ZPoly.multifactorLift 7 2 f7a factors7a) 7 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 2 f7a factors7a) 7 2
#guard reduceArrModPow (ZPoly.multifactorLift 7 2 f7b factors7b) 7 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 2 f7b factors7b) 7 2
#guard reduceArrModPow (ZPoly.multifactorLift 7 2 f7c factors7c) 7 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 2 f7c factors7c) 7 2
#guard reduceArrModPow (ZPoly.multifactorLift 7 2 f7d factors7d) 7 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 2 f7d factors7d) 7 2
#guard reduceArrModPow (ZPoly.multifactorLift 7 2 f7e factors7e) 7 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 2 f7e factors7e) 7 2

-- k = 4 over p = 7
#guard reduceArrModPow (ZPoly.multifactorLift 7 4 f7a factors7a) 7 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 4 f7a factors7a) 7 4
#guard reduceArrModPow (ZPoly.multifactorLift 7 4 f7b factors7b) 7 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 4 f7b factors7b) 7 4
#guard reduceArrModPow (ZPoly.multifactorLift 7 4 f7c factors7c) 7 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 4 f7c factors7c) 7 4
#guard reduceArrModPow (ZPoly.multifactorLift 7 4 f7d factors7d) 7 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 4 f7d factors7d) 7 4
#guard reduceArrModPow (ZPoly.multifactorLift 7 4 f7e factors7e) 7 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 4 f7e factors7e) 7 4

-- k = 8 over p = 7
#guard reduceArrModPow (ZPoly.multifactorLift 7 8 f7a factors7a) 7 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 8 f7a factors7a) 7 8
#guard reduceArrModPow (ZPoly.multifactorLift 7 8 f7b factors7b) 7 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 8 f7b factors7b) 7 8
#guard reduceArrModPow (ZPoly.multifactorLift 7 8 f7c factors7c) 7 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 8 f7c factors7c) 7 8
#guard reduceArrModPow (ZPoly.multifactorLift 7 8 f7d factors7d) 7 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 8 f7d factors7d) 7 8
#guard reduceArrModPow (ZPoly.multifactorLift 7 8 f7e factors7e) 7 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 8 f7e factors7e) 7 8

-- k = 16 over p = 7
#guard reduceArrModPow (ZPoly.multifactorLift 7 16 f7a factors7a) 7 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 16 f7a factors7a) 7 16
#guard reduceArrModPow (ZPoly.multifactorLift 7 16 f7b factors7b) 7 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 16 f7b factors7b) 7 16
#guard reduceArrModPow (ZPoly.multifactorLift 7 16 f7c factors7c) 7 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 16 f7c factors7c) 7 16
#guard reduceArrModPow (ZPoly.multifactorLift 7 16 f7d factors7d) 7 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 16 f7d factors7d) 7 16
#guard reduceArrModPow (ZPoly.multifactorLift 7 16 f7e factors7e) 7 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 7 16 f7e factors7e) 7 16

-- p = 11 fixtures
private def factors11a : Array ZPoly := factorsFromConstants #[1, 2, 3]
private def factors11b : Array ZPoly := factorsFromConstants #[0, 5, 9]
private def factors11c : Array ZPoly := factorsFromConstants #[1, 4, 6, 9]
private def factors11d : Array ZPoly := factorsFromConstants #[0, 3, 5, 7]
private def factors11e : Array ZPoly := factorsFromConstants #[0, 2, 4, 6, 8]

private def f11a : ZPoly := fixtureF 11 factors11a
private def f11b : ZPoly := fixtureF 11 factors11b
private def f11c : ZPoly := fixtureF 11 factors11c
private def f11d : ZPoly := fixtureF 11 factors11d
private def f11e : ZPoly := fixtureF 11 factors11e

-- k = 2 over p = 11
#guard reduceArrModPow (ZPoly.multifactorLift 11 2 f11a factors11a) 11 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 2 f11a factors11a) 11 2
#guard reduceArrModPow (ZPoly.multifactorLift 11 2 f11b factors11b) 11 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 2 f11b factors11b) 11 2
#guard reduceArrModPow (ZPoly.multifactorLift 11 2 f11c factors11c) 11 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 2 f11c factors11c) 11 2
#guard reduceArrModPow (ZPoly.multifactorLift 11 2 f11d factors11d) 11 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 2 f11d factors11d) 11 2
#guard reduceArrModPow (ZPoly.multifactorLift 11 2 f11e factors11e) 11 2
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 2 f11e factors11e) 11 2

-- k = 4 over p = 11
#guard reduceArrModPow (ZPoly.multifactorLift 11 4 f11a factors11a) 11 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 4 f11a factors11a) 11 4
#guard reduceArrModPow (ZPoly.multifactorLift 11 4 f11b factors11b) 11 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 4 f11b factors11b) 11 4
#guard reduceArrModPow (ZPoly.multifactorLift 11 4 f11c factors11c) 11 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 4 f11c factors11c) 11 4
#guard reduceArrModPow (ZPoly.multifactorLift 11 4 f11d factors11d) 11 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 4 f11d factors11d) 11 4
#guard reduceArrModPow (ZPoly.multifactorLift 11 4 f11e factors11e) 11 4
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 4 f11e factors11e) 11 4

-- k = 8 over p = 11
#guard reduceArrModPow (ZPoly.multifactorLift 11 8 f11a factors11a) 11 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 8 f11a factors11a) 11 8
#guard reduceArrModPow (ZPoly.multifactorLift 11 8 f11b factors11b) 11 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 8 f11b factors11b) 11 8
#guard reduceArrModPow (ZPoly.multifactorLift 11 8 f11c factors11c) 11 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 8 f11c factors11c) 11 8
#guard reduceArrModPow (ZPoly.multifactorLift 11 8 f11d factors11d) 11 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 8 f11d factors11d) 11 8
#guard reduceArrModPow (ZPoly.multifactorLift 11 8 f11e factors11e) 11 8
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 8 f11e factors11e) 11 8

-- k = 16 over p = 11
#guard reduceArrModPow (ZPoly.multifactorLift 11 16 f11a factors11a) 11 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 16 f11a factors11a) 11 16
#guard reduceArrModPow (ZPoly.multifactorLift 11 16 f11b factors11b) 11 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 16 f11b factors11b) 11 16
#guard reduceArrModPow (ZPoly.multifactorLift 11 16 f11c factors11c) 11 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 16 f11c factors11c) 11 16
#guard reduceArrModPow (ZPoly.multifactorLift 11 16 f11d factors11d) 11 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 16 f11d factors11d) 11 16
#guard reduceArrModPow (ZPoly.multifactorLift 11 16 f11e factors11e) 11 16
     = reduceArrModPow (ZPoly.multifactorLiftQuadratic 11 16 f11e factors11e) 11 16

end HenselCrossCheck
end Hex
