/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.PMinusOne

public section

/-!
Montgomery-curve ECM stage 1.

The curve arithmetic is deliberately outside the trusted surface. Setup and
stage-boundary gcds distinguish `1`, a dynamically checked proper factor, and
the whole modulus; only the middle case is exposed as a factor.
-/

namespace Hex
namespace Nat

/-- Which modular representation an ECM attempt selects. -/
inductive EcmBackend where
  | word
  | natural
deriving Repr, DecidableEq

/-- Select the word route exactly when an odd modulus fits in one machine word. -/
def ecmBackend (n : Nat) : EcmBackend :=
  if n < 2 ^ 64 ∧ n % 2 = 1 then .word else .natural

/-- Projective Montgomery `x:z` coordinates. -/
structure EcmPoint where
  x : Nat
  z : Nat
deriving Repr, DecidableEq

/-- The three semantically distinct gcd outcomes of an ECM stage. -/
inductive EcmResult where
  | noFactor
  | factor (value : Nat)
  | whole
deriving Repr, DecidableEq

private def addMod (n a b : Nat) : Nat := (a + b) % n
private def subMod (n a b : Nat) : Nat := (a + n - b % n) % n

/-- One Montgomery multiplication after reducing and encoding both operands. -/
private def mulModWordOdd (n a b : Nat) (p : UInt64) (hp : p % 2 = 1) : Nat :=
  let ctx := MontCtx.mk p hp
  let am := ctx.toMont (UInt64.ofNat (a % n))
  let bm := ctx.toMont (UInt64.ofNat (b % n))
  (ctx.fromMont (ctx.mulMont am bm)).toNat

/-- Semantic modular multiplication selected by the explicit arithmetic
dispatch. The word arm is the lowering point for `MontCtx`; large moduli use
GMP-backed `Nat` multiplication and remainder. -/
private def mulMod (backend : EcmBackend) (n a b : Nat) : Nat :=
  match backend with
  | .word =>
      let p := UInt64.ofNat n
      if _hfit : p.toNat = n then
        if hodd : p % 2 = 1 then mulModWordOdd n a b p hodd
        else (a * b) % n
      else (a * b) % n
  | .natural => (a * b) % n

private def sqrMod (backend : EcmBackend) (n a : Nat) : Nat :=
  mulMod backend n a a

/-- Montgomery doubling with `A24 = numerator / denominator`, kept scaled so
setup requires no modular inverse. -/
private def xDouble (backend : EcmBackend) (n a24num a24den : Nat)
    (p : EcmPoint) : EcmPoint :=
  let sum := addMod n p.x p.z
  let difference := subMod n p.x p.z
  let aa := sqrMod backend n sum
  let bb := sqrMod backend n difference
  let c := subMod n aa bb
  ⟨mulMod backend n aa bb,
    mulMod backend n c
      (addMod n (mulMod backend n bb a24den)
        (mulMod backend n a24num c))⟩

/-- Differential Montgomery addition: `difference` represents `p - q`. -/
private def xAdd (backend : EcmBackend) (n : Nat)
    (p q difference : EcmPoint) : EcmPoint :=
  let a := addMod n p.x p.z
  let b := subMod n p.x p.z
  let c := addMod n q.x q.z
  let d := subMod n q.x q.z
  let da := mulMod backend n d a
  let cb := mulMod backend n c b
  ⟨mulMod backend n difference.z (sqrMod backend n (addMod n da cb)),
    mulMod backend n difference.x (sqrMod backend n (subMod n da cb))⟩

private def scalarMul (backend : EcmBackend) (n a24num a24den : Nat)
    (p : EcmPoint) : Nat → EcmPoint
  | 0 => ⟨1, 0⟩
  | 1 => p
  | k + 2 =>
      let scalar := k + 2
      let q := scalarMul backend n a24num a24den p (scalar / 2)
      let twoq := xDouble backend n a24num a24den q
      if scalar % 2 = 0 then twoq else xAdd backend n twoq q p
termination_by scalar => scalar
decreasing_by omega

private def largestPower (q bound : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc =>
      if acc ≤ bound / q then largestPower q bound fuel (acc * q) else acc

private def smoothPower (q bound : Nat) : Nat :=
  largestPower q bound (bound.log2 + 1) q

private def stageMultiply (backend : EcmBackend) (n bound a24num a24den : Nat) :
    List Nat → EcmPoint → EcmPoint
  | [], p => p
  | q :: qs, p =>
      if q ≤ bound then
        stageMultiply backend n bound a24num a24den qs
          (scalarMul backend n a24num a24den p (smoothPower q bound))
      else p

private def classifyGcd (n g : Nat) : EcmResult :=
  if g = 1 then .noFactor
  else if 1 < g ∧ g < n ∧ n % g = 0 then .factor g
  else .whole

/-- One Suyama-parameterized Montgomery ECM stage-1 attempt. -/
def ecmStage1 (n sigma bound : Nat) : EcmResult :=
  if n < 4 ∨ sigma < 6 then .noFactor
  else
    let backend := ecmBackend n
    let u := (sigma * sigma + n - 5) % n
    let v := (4 * sigma) % n
    let u3 := mulMod backend n (sqrMod backend n u) u
    let v3 := mulMod backend n (sqrMod backend n v) v
    let curveNum := mulMod backend n
      (mulMod backend n (sqrMod backend n (subMod n v u)) (subMod n v u))
      (addMod n (3 * u % n) v)
    let curveDen := mulMod backend n (4 * u3 % n) v
    let setup := Nat.gcd curveDen n
    if setup != 1 then classifyGcd n setup
    else
      -- `A24 = curveNum / (4 * curveDen)`.
      let p := stageMultiply backend n bound curveNum (4 * curveDen % n)
        primeTable.toList ⟨u3, v3⟩
      classifyGcd n (Nat.gcd p.z n)

/-- Every ECM factor result is a dynamically validated proper divisor. -/
theorem ecmStage1_spec {n sigma bound d : Nat}
    (h : ecmStage1 n sigma bound = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold ecmStage1 at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · unfold classifyGcd at h
      split at h
      · cases h
      · split at h
        · rename_i _ _ hg
          injection h with heq
          subst d
          exact ⟨hg.1, hg.2.1, Nat.dvd_of_mod_eq_zero hg.2.2⟩
        · cases h
    · unfold classifyGcd at h
      split at h
      · cases h
      · split at h
        · rename_i _ _ hg
          injection h with heq
          subst d
          exact ⟨hg.1, hg.2.1, Nat.dvd_of_mod_eq_zero hg.2.2⟩
        · cases h

end Nat
end Hex
