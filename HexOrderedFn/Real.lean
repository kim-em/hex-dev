/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn.Search
public import HexOrderedFn.Oracle
public import HexRationalFn

@[expose] public section

namespace Hex.OrderedFn.Real

open Oracle
universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]

/-- Positive requested width at refinement index `n`. -/
def precision (n : Nat) : Rat := 1 / (2 : Rat) ^ n

/-- Exact Horner bounds, refining every coefficient and the argument together. -/
def enclose (a : Approximation K) (p : DensePoly K) (δ : Rat) : Bounds :=
  let x := a.constant δ
  p.coeffs.foldr (fun c acc => (a.coeff c δ).add (x.mul acc)) (.singleton 0)

/-- One total-sign trial. Formal zero does not invoke either provider. -/
def attempt (a : Approximation K) (f : RationalFn K) (n : Nat) : Option Int :=
  if f.num = 0 then some 0 else do
    let s ← (enclose a f.num (precision n)).sign?
    let t ← (enclose a f.den (precision n)).sign?
    pure (s * t)

/-- Total sign for one query, given an erased proof that its refinement terminates.
Semantic correctness additionally needs containment for these exact providers. -/
def sign (a : Approximation K) (f : RationalFn K)
    (h : Acc (Next (attempt a f)) 0) : Int := firstSome (attempt a f) 0 h

/-- One trial for a requested rational-function enclosure. -/
def approxAttempt (a : Approximation K) (f : RationalFn K) (δ : Rat) (n : Nat) :
    Option Bounds :=
  if f.num = 0 then
    if 0 ≤ δ then some (.singleton 0) else none
  else do
    let b ← (enclose a f.num (precision n)).div? (enclose a f.den (precision n))
    if b.width ≤ δ then some b else none

/-- Nonpositive requests ask for a coarse width-one enclosure. -/
def requestWidth (δ : Rat) : Rat := if 0 < δ then δ else 1

/-- Derived approximation for one query. Nonpositive requests run the same
refinement at width one, so every result still encloses the queried value. -/
def approx (a : Approximation K) (f : RationalFn K) (δ : Rat)
    (h : Acc (Next (approxAttempt a f (requestWidth δ))) 0) : Bounds :=
  firstSome (approxAttempt a f (requestWidth δ)) 0 h

/-- Finite evaluation requires a separated denominator even without transcendence.
An exact singleton numerator may certify zero; a zero-containing bound cannot. -/
def finiteAttempt (a : Approximation K) (f : RationalFn K) (n : Nat) : Option Int := do
  let t ← (enclose a f.den (precision n)).sign?
  let s ← (enclose a f.num (precision n)).exactSign?
  pure (s * t)

/-- Optional finite evaluation. Fuel counts trials, beginning at precision zero;
this function is never a coefficient field operation. -/
def sign? (a : Approximation K) (f : RationalFn K) (fuel : Nat) : Option Int :=
  go fuel 0
where
  go : Nat → Nat → Option Int
    | 0, _ => none
    | fuel + 1, n =>
      match finiteAttempt a f n with
      | some s => some s
      | none => go fuel (n + 1)

theorem attempt_zero (a : Approximation K) (n : Nat) : attempt a 0 n = some 0 := by
  simp [attempt, show (0 : RationalFn K).num = 0 from rfl]

theorem sign_zero (a : Approximation K) (h : Acc (Next (attempt a 0)) 0) :
    sign a 0 h = 0 := firstSome_some _ _ _ (attempt_zero a 0)

theorem approxAttempt_width (a : Approximation K) (f : RationalFn K)
    (δ : Rat) (n : Nat) {b : Bounds} (hb : approxAttempt a f δ n = some b) :
    b.width ≤ δ := by
  unfold approxAttempt at hb
  split at hb
  · split at hb
    · cases hb
      simpa using ‹0 ≤ δ›
    · contradiction
  · cases hd : (enclose a f.num (precision n)).div? (enclose a f.den (precision n)) with
    | none => simp [hd] at hb
    | some c =>
      simp [hd] at hb
      exact hb.2 ▸ hb.1

/-- Width is a rational property of the actual search, separate from containment. -/
theorem approx_width (a : Approximation K) (f : RationalFn K) (δ : Rat)
    (h : Acc (Next (approxAttempt a f (requestWidth δ))) 0) (hδ : 0 < δ) :
    (approx a f δ h).width ≤ δ := by
  obtain ⟨n, _, hn⟩ := firstSome_spec (approxAttempt a f (requestWidth δ)) 0 h
  have hw := approxAttempt_width a f (requestWidth δ) n hn
  calc
    (approx a f δ h).width ≤ requestWidth δ := hw
    _ = δ := by simp [requestWidth, hδ]

end Hex.OrderedFn.Real
