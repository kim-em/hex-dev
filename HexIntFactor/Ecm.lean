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
  /-- Projective numerator coordinate. -/
  x : Nat
  /-- Projective denominator coordinate. -/
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

private def mulMod (n a b : Nat) : Nat := (a * b) % n
private def sqrMod (n a : Nat) : Nat := mulMod n a a

/-- Montgomery doubling with `A24 = numerator / denominator`, kept scaled so
setup requires no modular inverse. -/
private def xDouble (n a24num a24den : Nat) (p : EcmPoint) : EcmPoint :=
  let sum := addMod n p.x p.z
  let difference := subMod n p.x p.z
  let aa := sqrMod n sum
  let bb := sqrMod n difference
  let c := subMod n aa bb
  ⟨mulMod n (mulMod n aa bb) a24den,
    mulMod n c (addMod n (mulMod n bb a24den) (mulMod n a24num c))⟩

/-- Differential Montgomery addition: `difference` represents `p - q`. -/
private def xAdd (n : Nat) (p q difference : EcmPoint) : EcmPoint :=
  let a := addMod n p.x p.z
  let b := subMod n p.x p.z
  let c := addMod n q.x q.z
  let d := subMod n q.x q.z
  let da := mulMod n d a
  let cb := mulMod n c b
  ⟨mulMod n difference.z (sqrMod n (addMod n da cb)),
    mulMod n difference.x (sqrMod n (subMod n da cb))⟩

private def scalarPair (n a24num a24den : Nat)
    (p : EcmPoint) : Nat → EcmPoint × EcmPoint
  | 0 => (⟨1, 0⟩, p)
  | 1 => (p, xDouble n a24num a24den p)
  | k + 2 =>
      let scalar := k + 2
      let pair := scalarPair n a24num a24den p (scalar / 2)
      let sum := xAdd n pair.1 pair.2 p
      if scalar % 2 = 0 then
        (xDouble n a24num a24den pair.1, sum)
      else
        (sum, xDouble n a24num a24den pair.2)
termination_by scalar => scalar
decreasing_by omega

private def scalarMul (n a24num a24den : Nat)
    (p : EcmPoint) (scalar : Nat) : EcmPoint :=
  if scalar = 0 then ⟨1, 0⟩
  else (scalarPair n a24num a24den p scalar).1

/-- Projective point whose coordinates stay in Montgomery representation. -/
private structure EcmWordPoint where
  x : UInt64
  z : UInt64

private def addWord (p a b : UInt64) : UInt64 :=
  let gap := p - b
  if gap ≤ a then a - gap else a + b

private def subWord (p a b : UInt64) : UInt64 :=
  if b ≤ a then a - b else p - (b - a)

private def xDoubleWord {p : UInt64} (ctx : MontCtx p)
    (a24num a24den : UInt64) (point : EcmWordPoint) : EcmWordPoint :=
  let sum := addWord p point.x point.z
  let difference := subWord p point.x point.z
  let aa := ctx.mulMont sum sum
  let bb := ctx.mulMont difference difference
  let c := subWord p aa bb
  ⟨ctx.mulMont (ctx.mulMont aa bb) a24den,
    ctx.mulMont c (addWord p (ctx.mulMont bb a24den) (ctx.mulMont a24num c))⟩

private def xAddWord {modulus : UInt64} (ctx : MontCtx modulus)
    (p q difference : EcmWordPoint) : EcmWordPoint :=
  let a := addWord modulus p.x p.z
  let b := subWord modulus p.x p.z
  let c := addWord modulus q.x q.z
  let d := subWord modulus q.x q.z
  let da := ctx.mulMont d a
  let cb := ctx.mulMont c b
  let sum := addWord modulus da cb
  let difference' := subWord modulus da cb
  ⟨ctx.mulMont difference.z (ctx.mulMont sum sum),
    ctx.mulMont difference.x (ctx.mulMont difference' difference')⟩

private def scalarPairWord {modulus : UInt64} (ctx : MontCtx modulus)
    (a24num a24den : UInt64) (p : EcmWordPoint) :
    Nat → EcmWordPoint × EcmWordPoint
  | 0 => (⟨ctx.toMont 1, 0⟩, p)
  | 1 => (p, xDoubleWord ctx a24num a24den p)
  | k + 2 =>
      let scalar := k + 2
      let pair := scalarPairWord ctx a24num a24den p (scalar / 2)
      let sum := xAddWord ctx pair.1 pair.2 p
      if scalar % 2 = 0 then
        (xDoubleWord ctx a24num a24den pair.1, sum)
      else
        (sum, xDoubleWord ctx a24num a24den pair.2)
termination_by scalar => scalar
decreasing_by omega

private def scalarMulWord {modulus : UInt64} (ctx : MontCtx modulus)
    (a24num a24den : UInt64) (p : EcmWordPoint) (scalar : Nat) : EcmWordPoint :=
  if scalar = 0 then ⟨ctx.toMont 1, 0⟩
  else (scalarPairWord ctx a24num a24den p scalar).1

private def largestPower (q bound : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc =>
      if acc ≤ bound / q then largestPower q bound fuel (acc * q) else acc

private def smoothPower (q bound : Nat) : Nat :=
  largestPower q bound (bound.log2 + 1) q

private def stageMultiply (n bound a24num a24den : Nat) :
    List Nat → EcmPoint → EcmPoint
  | [], p => p
  | q :: qs, p =>
      if q ≤ bound then
        stageMultiply n bound a24num a24den qs
          (scalarMul n a24num a24den p (smoothPower q bound))
      else p

private def stageMultiplyWord {modulus : UInt64} (ctx : MontCtx modulus)
    (bound : Nat) (a24num a24den : UInt64) :
    List Nat → EcmWordPoint → EcmWordPoint
  | [], p => p
  | q :: qs, p =>
      if q ≤ bound then
        stageMultiplyWord ctx bound a24num a24den qs
          (scalarMulWord ctx a24num a24den p (smoothPower q bound))
      else p

private def classifyGcd (n g : Nat) : EcmResult :=
  if g = 1 then .noFactor
  else if 1 < g ∧ g < n ∧ n % g = 0 then .factor g
  else .whole

private def stageGcdNat (n bound curveNum curveDen u3 v3 : Nat) : Nat :=
  let p := stageMultiply n bound curveNum (4 * curveDen % n)
    primeTable.toList ⟨u3, v3⟩
  Nat.gcd p.z n

private def stageGcd (n bound curveNum curveDen u3 v3 : Nat) : Nat :=
  match ecmBackend n with
  | .natural => stageGcdNat n bound curveNum curveDen u3 v3
  | .word =>
      let modulus := UInt64.ofNat n
      if _hfit : modulus.toNat = n then
        if hodd : modulus % 2 = 1 then
          let ctx := MontCtx.mk modulus hodd
          let a24num := ctx.toMont (UInt64.ofNat curveNum)
          let a24den := ctx.toMont (UInt64.ofNat (4 * curveDen % n))
          let p := stageMultiplyWord ctx bound a24num a24den primeTable.toList
            ⟨ctx.toMont (UInt64.ofNat u3), ctx.toMont (UInt64.ofNat v3)⟩
          Nat.gcd (ctx.fromMont p.z).toNat n
        else
          stageGcdNat n bound curveNum curveDen u3 v3
      else
        stageGcdNat n bound curveNum curveDen u3 v3

namespace Internal

/-- Route-level observations from one ECM attempt. The zero stage gcd means
the attempt stopped before stage multiplication. -/
structure EcmTrace where
  /-- Arithmetic backend selected for the stage. -/
  backend : EcmBackend
  /-- Gcd of the Suyama setup denominator and the modulus. -/
  setupGcd : Nat
  /-- Stage-boundary gcd, or zero when setup stopped the attempt. -/
  stageGcd : Nat
  /-- Public result obtained by classifying the applicable gcd. -/
  result : EcmResult
deriving Repr, DecidableEq

/-- Instrumented ECM attempt used by route-level conformance checks. -/
def ecmTrace (n sigma bound : Nat) : EcmTrace :=
  let backend := ecmBackend n
  if n < 4 ∨ sigma < 6 then
    ⟨backend, 0, 0, .noFactor⟩
  else
    let u := (sigma * sigma + n - 5) % n
    let v := (4 * sigma) % n
    let u3 := mulMod n (sqrMod n u) u
    let v3 := mulMod n (sqrMod n v) v
    let vu := subMod n v u
    let curveNum := mulMod n (mulMod n (sqrMod n vu) vu)
      (addMod n (3 * u % n) v)
    let curveDen := mulMod n (4 * u3 % n) v
    let setup := Nat.gcd curveDen n
    if setup != 1 then
      ⟨backend, setup, 0, classifyGcd n setup⟩
    else
      let stage := stageGcd n bound curveNum curveDen u3 v3
      ⟨backend, setup, stage, classifyGcd n stage⟩

end Internal

/-- One Suyama-parameterized Montgomery ECM stage-1 attempt. -/
def ecmStage1 (n sigma bound : Nat) : EcmResult :=
  (Internal.ecmTrace n sigma bound).result

private theorem classifyGcd_spec {n g d : Nat}
    (h : classifyGcd n g = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold classifyGcd at h
  split at h
  · cases h
  · split at h
    · rename_i _ hg
      injection h with heq
      subst d
      exact ⟨hg.1, hg.2.1, Nat.dvd_of_mod_eq_zero hg.2.2⟩
    · cases h

/-- Every ECM factor result is a dynamically validated proper divisor. -/
theorem ecmStage1_spec {n sigma bound d : Nat}
    (h : ecmStage1 n sigma bound = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold ecmStage1 Internal.ecmTrace at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · exact classifyGcd_spec h
    · exact classifyGcd_spec h

end Nat
end Hex
