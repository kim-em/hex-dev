/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Ecm
import all HexIntFactor.Ecm

public section

/-! Bounded Montgomery ECM continuation. Search is untrusted: only a dynamically
validated proper divisor crosses the public boundary. See the HexIntFactor SPEC
and reports/hex-primality-ecm-stage2.md for the interval and work contracts. -/

namespace Hex.Nat.Ecm

structure State where
  n : Nat
  num : Nat
  den : Nat
  point : EcmPoint

-- Setup and stage 1 match the natural-number production backend exactly.
def start (n sigma b₁ : Nat) : EcmResult × Option State := Id.run do
  if n < 4 || sigma < 6 || b₁ > 524288 then return (.noFactor, none)
  let u := (sigma * sigma + n - 5) % n
  let v := 4 * sigma % n
  let u3 := u * u % n * u % n
  let v3 := v * v % n * v % n
  let vu := (v + n - u) % n
  let num := vu * vu % n * vu % n * ((3 * u + v) % n) % n
  let den := 4 * u3 % n * v % n
  let setup := classifyGcd n (Nat.gcd den n)
  if setup != .noFactor then return (setup, none)
  let den := 4 * den % n
  let point := stageMultiply n b₁ num den (primesBelow (b₁ + 1)) ⟨u3, v3⟩
  let result := classifyGcd n (Nat.gcd point.z n)
  return (result, if result == .noFactor then some ⟨n, num, den, point⟩ else none)

structure Trace where
  result : EcmResult := .noFactor
  candidates : Nat := 0
  advances : Nat := 0
  batches : Nat := 0
  recovery : List Nat := []
  lastPrime : Nat := 0
  oracleMismatch : Bool := false
  deriving Repr

-- A whole leaf does not mask a later proper leaf.
def flush (n product : Nat) (terms : Array Nat) : EcmResult × List Nat := Id.run do
  let result := classifyGcd n (Nat.gcd product n)
  if result != .whole then return (result, [])
  let mut recovery := []
  for t in terms do
    let g := Nat.gcd t n
    recovery := recovery ++ [g]
    if let .factor d := classifyGcd n g then return (.factor d, recovery)
  return (.whole, recovery)

/- Every prime in `(b₁,b₂]` is mapped to q = 210*i+j. Cross differences also
admit the opposite sign, but all exits still validate a proper divisor. For
small q (i=0), use `[q]Q.z` directly to avoid the point at infinity. -/
def stage2 (s : State) (b₁ b₂ : Nat) (checkGiants : Bool := false) : Trace := Id.run do
  if s.n < 4 || b₁ > 524288 || b₂ > 4194304 || b₂ ≤ b₁ then return {}
  let primes := (primesBelow (b₂ + 1)).filter (b₁ < ·)
  if primes.isEmpty then return {}
  let mul := scalarMul s.n s.num s.den s.point
  let babies := (List.range 210).toArray.map mul
  let step := mul 210
  let mut previous : EcmPoint := ⟨1, 0⟩
  let mut giant := step
  let mut index := 1
  let mut terms := #[]
  let mut product := 1
  let mut trace : Trace := {}
  for q in primes do
    let i := q / 210
    let j := q % 210
    while index < i do
      let next := if index == 1 then xDouble s.n s.num s.den giant
        else xAdd s.n giant step previous
      previous := giant
      giant := next
      index := index + 1
      trace := { trace with advances := trace.advances + 1 }
    if checkGiants && i > 0 then
      let direct := mul (210 * i)
      if (direct.x * giant.z) % s.n != (giant.x * direct.z) % s.n then
        trace := { trace with oracleMismatch := true }
    let t := if i == 0 then (mul q).z else
      let baby := babies[j]' (by simp [babies, j]; omega)
      (giant.x * baby.z % s.n + s.n - baby.x * giant.z % s.n) % s.n
    product := product * t % s.n
    terms := terms.push t
    trace := { trace with candidates := trace.candidates + 1, lastPrime := q }
    if terms.size == 32 then
      let (result, recovery) := flush s.n product terms
      trace := { trace with batches := trace.batches + 1, result, recovery }
      if result != .noFactor then return trace
      terms := #[]
      product := 1
  if !terms.isEmpty then
    let (result, recovery) := flush s.n product terms
    trace := { trace with batches := trace.batches + 1, result, recovery }
  return trace

-- Requests are rejected rather than silently changed. Stage one has its existing cap.
def validBounds (b₁ b₂ : Nat) : Bool := b₁ ≤ 524288 && b₂ ≤ 4194304

private def searchCore (n sigma b₁ b₂ allowance : Nat) : EcmResult × Nat :=
  if allowance == 0 || !validBounds b₁ b₂ then (.noFactor, 0) else
  let (result, saved) := start n sigma b₁
  match saved with
  | some s => if b₂ > b₁ && allowance > 1 then ((stage2 s b₁ b₂).result, 2)
      else (result, 1)
  | none => (result, 1)

/-- A deterministic curve attempt with at most two semantic charges. Invalid
bounds or zero allowance decline without work; one remaining attempt permits
only stage 1. No random state is consumed. -/
def search (n sigma b₁ b₂ allowance : Nat) : EcmResult × Nat :=
  let (result, work) := searchCore n sigma b₁ b₂ allowance
  (match result with
   | .factor d => classifyGcd n d
   | other => other, work)

/-- A factor from the counted continuation is always a proper divisor. -/
theorem search_spec {n sigma b₁ b₂ allowance d : Nat}
    (h : (search n sigma b₁ b₂ allowance).1 = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  generalize he : searchCore n sigma b₁ b₂ allowance = out
  obtain ⟨result, work⟩ := out
  simp only [search, he] at h
  cases result with
  | factor value => exact classifyGcd_spec h
  | noFactor => cases h
  | whole => cases h

end Hex.Nat.Ecm
