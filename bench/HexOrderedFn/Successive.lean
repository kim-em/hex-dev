/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexOrderedFn

/-!
Finite successive-approximation workloads. Every cached entry stores a requested
width and a checked termination witness, not a precomputed approximation result.
The timed coefficient callback executes the inner total search from zero.
These rational subjects are per-query fixtures, not transcendental registrations.
-/

namespace Hex.OrderedFnBench.Successive

open Hex.OrderedFn Hex.OrderedFn.Oracle

abbrev First := RationalFn Rat
abbrev Second := RationalFn First

private def window (q δ : Rat) : Bounds :=
  if h : 0 < δ then ⟨q - δ / 2, q + δ / 2, by grind⟩ else .singleton q

private def inner : Approximation Rat := .ofConstant (window 2)

structure Entry where
  subject : First
  width : Rat
  progress : Acc (Next (Real.approxAttempt inner subject (Real.requestWidth width))) 0

private def entry (f : First) (k : Nat) : IO Entry := do
  let δ := Real.precision k
  match h : Real.approxAttempt inner f (Real.requestWidth δ) (k + 2) with
  | none => throw (IO.userError "successive coefficient witness failed")
  | some b =>
    let value := f.num.eval 2 / f.den.eval 2
    unless b.lower ≤ value && value ≤ b.upper && b.width ≤ δ do
      throw (IO.userError "successive coefficient enclosure failed")
    return ⟨f, δ, acc_of_success _ (k + 2) b h 0 (by omega)⟩

private def execute (q : Entry) : Bounds :=
  Real.approx inner q.subject q.width q.progress

/-- The fixture covers every coefficient and request made before its outer
success witness. The exact fallback defines other requests at the same rational
subject; no global field embedding or width contract is asserted. -/
private def coefficient (entries : Array (Entry × Entry)) (c : First) (δ : Rat) : Bounds :=
  match entries[δ.den.log2]? with
  | some pair =>
    if c = pair.1.subject && δ = pair.1.width then execute pair.1
    else if c = pair.2.subject && δ = pair.2.width then execute pair.2
    else .singleton (c.num.eval 2 / c.den.eval 2)
  | none => .singleton (c.num.eval 2 / c.den.eval 2)

structure Query where
  source : Approximation First
  subject : Second
  width : Rat
  progress : Acc (Next (Real.approxAttempt source subject (Real.requestWidth width))) 0

def run (q : Query) : Rat × Rat :=
  let b := Real.approx q.source q.subject q.width q.progress
  (b.lower, b.upper)

/-- X₂ - X₁ at X₁=2, X₂=2+2⁻ⁿ; approximate it to width 2⁻ⁿ. -/
def prepare (n : Nat) : IO Query := do
  let δ := Real.precision n
  let f : Second := RationalFn.X - RationalFn.C RationalFn.X
  let negativeX : First := -RationalFn.X
  let mut entries := #[]
  for k in [:n + 4] do
    entries := entries.push (← entry negativeX k, ← entry 1 k)
  -- These are all coefficients actually requested by both Horner evaluations.
  unless f.num.coeffs == #[negativeX, 1] && f.den.coeffs == #[1] do
    throw (IO.userError "unexpected successive polynomial coefficients")
  let a : Approximation First := ⟨coefficient entries, window (2 + δ)⟩
  for k in [:n + 4] do
    let width := Real.precision k
    for c in f.num.coeffs ++ f.den.coeffs do
      unless entries[width.den.log2]?.any (fun p =>
          (c == p.1.subject && width == p.1.width) ||
          (c == p.2.subject && width == p.2.width)) do
        throw (IO.userError "successive request lacks an inner search witness")
  unless (Real.approxAttempt a f (Real.requestWidth δ) n).isNone &&
      (Real.approxAttempt a f (Real.requestWidth δ) (n + 1)).isSome do
    throw (IO.userError "unexpected successive separation precision")
  match h : Real.approxAttempt a f (Real.requestWidth δ) (n + 3) with
  | none => throw (IO.userError "successive outer witness failed")
  | some b =>
    unless b.lower ≤ δ && δ ≤ b.upper && b.width ≤ δ do
      throw (IO.userError "successive outer enclosure failed")
    let q : Query := ⟨a, f, δ, acc_of_success _ (n + 3) b h 0 (by omega)⟩
    let (lo, hi) := run q
    unless lo == δ / 2 && hi == 3 * δ / 2 do
      throw (IO.userError "successive total approximation failed")
    return q

end Hex.OrderedFnBench.Successive

-- Preparation checks exact containment and width, and verifies that all requests
-- up to the outer witness execute cached inner searches rather than the fallback.
#eval do
  for n in [0, 1, 4, 8, 16] do
    discard <| Hex.OrderedFnBench.Successive.prepare n
