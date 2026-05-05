import HexHensel.Multifactor
import HexHensel.Quadratic

/-!
Quadratic multifactor Hensel lifting.

This module exposes `multifactorLiftQuadratic`, the production multifactor
Hensel lifter named on equal footing with `multifactorLift` in
`hex-hensel`. The implementation reuses the per-step quadratic primitive
`quadraticHenselStep` inside a sequential split tree that mirrors
`multifactorLift`. Iteration to the requested precision `p^k` is handled
by a doubling loop on the Bezout-witnessed `QuadraticLiftResult`.

The companion theorem states the ordered-product congruence contract for
the lifted array. The linear-vs-quadratic agreement obligation lives in
`hex-hensel-mathlib`.
-/

namespace Hex

namespace ZPoly

/-- Iterate `quadraticHenselStep` on a Bezout-witnessed factorisation,
doubling the modulus exponent each time. The first index is the current
modulus exponent; the second is the number of remaining doubling steps. -/
private def iterateQuadraticHensel
    (p : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    Nat → Nat → QuadraticLiftResult → QuadraticLiftResult
  | _current, 0, acc => acc
  | current, fuel + 1, acc =>
      let m := p ^ current
      let next := quadraticHenselStep m f acc.g acc.h acc.s acc.t
      iterateQuadraticHensel p f (2 * current) fuel next

/-- Lift a Bezout-witnessed factorisation modulo `p` to one valid modulo
`p^k` by iterating `quadraticHenselStep`.

`k` doubling steps starting from modulus `p` reach modulus `p^(2^k)`,
which dominates `p^k` for all `k`; the final result is reduced modulo
`p^k` to expose the requested precision. -/
def henselLiftQuadratic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly) : QuadraticLiftResult :=
  let init : QuadraticLiftResult := { g, h, s, t }
  let lifted := iterateQuadraticHensel p f 1 k init
  { g := ZPoly.reduceModPow lifted.g p k
    h := ZPoly.reduceModPow lifted.h p k
    s := ZPoly.reduceModPow lifted.s p k
    t := ZPoly.reduceModPow lifted.t p k }

private def multifactorLiftQuadraticList
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Array ZPoly
  | [] => #[]
  | [_g] => #[ZPoly.reduceModPow f p k]
  | g :: rest =>
      let restFactors := rest.toArray
      let h := Array.polyProduct restFactors
      let xgcd := ZPoly.normalizedXGCD p g h
      let s := FpPoly.liftToZ xgcd.left
      let t := FpPoly.liftToZ xgcd.right
      let lifted := henselLiftQuadratic p k f g h s t
      #[lifted.g] ++ multifactorLiftQuadraticList p k lifted.h rest

/--
Quadratic multifactor Hensel lift.

Lifts an ordered array of factors of `f` from congruence modulo `p` to
congruence modulo `p^k` using the doubling step `quadraticHenselStep`
inside the same sequential split tree as `multifactorLift`.
-/
def multifactorLiftQuadratic
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly) : Array ZPoly :=
  multifactorLiftQuadraticList p k f factors.toList

/-- The proof state carried by one quadratic Hensel loop modulus. -/
def QuadraticLiftLoopInvariant
    (m : Nat) (f : ZPoly) (acc : QuadraticLiftResult) : Prop :=
  ZPoly.congr (acc.g * acc.h) f m ∧
    ZPoly.congr (acc.s * acc.g + acc.t * acc.h) 1 m ∧
    DensePoly.Monic acc.g

/--
One quadratic step preserves the loop invariant while replacing `m` by `m*m`.

This is the local invariant-preservation surface consumed by the quadratic
doubling loop.
-/
theorem quadraticLiftLoopInvariant_step
    (m : Nat) (f : ZPoly) (acc : QuadraticLiftResult)
    (hm : 1 < m)
    (hinv : QuadraticLiftLoopInvariant m f acc) :
    let next := quadraticHenselStep m f acc.g acc.h acc.s acc.t
    QuadraticLiftLoopInvariant (m * m) f next := by
  rcases hinv with ⟨hprod, hbez, hmonic⟩
  intro next
  have hstep :
      ZPoly.congr (next.g * next.h) f (m * m) ∧
        ZPoly.congr (next.s * next.g + next.t * next.h) 1 (m * m) := by
    simpa [next] using
      quadraticHenselStep_spec m f acc.g acc.h acc.s acc.t hm hprod hbez hmonic
  exact
    ⟨hstep.1, hstep.2,
      by
        simpa [next] using
          quadraticHenselStep_monic m f acc.g acc.h acc.s acc.t hm hmonic⟩

/--
Recursive preconditions required by the sequential quadratic multifactor lift.

Each nontrivial split carries the initial quadratic loop invariant needed by
`henselLiftQuadratic`; the recursive tail carries the same contract for the
lifted complementary factor.
-/
def QuadraticMultifactorLiftInvariant
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Prop
  | [] => ZPoly.congr 1 f (p ^ k)
  | [_g] => True
  | g :: rest =>
      let h := Array.polyProduct rest.toArray
      let xgcd := normalizedXGCD p g h
      let s := FpPoly.liftToZ xgcd.left
      let t := FpPoly.liftToZ xgcd.right
      let lifted := henselLiftQuadratic p k f g h s t
      QuadraticLiftLoopInvariant p f { g, h, s, t } ∧
        QuadraticMultifactorLiftInvariant p k lifted.h rest

/--
The product of the lifted factors is congruent to `f` modulo `p^k`,
under the recursive precondition package consumed by the quadratic
multifactor lifting tree.

The lift-uniqueness companion (linear-vs-quadratic agreement after
canonicalisation) lives in `hex-hensel-mathlib`.
-/
theorem multifactorLiftQuadratic_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors.toList) :
    ZPoly.congr (Array.polyProduct (multifactorLiftQuadratic p k f factors))
      f (p ^ k) := by
  sorry

end ZPoly

end Hex
