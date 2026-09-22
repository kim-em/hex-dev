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

-- Requests are rejected rather than silently changed.
def validBounds (b₁ b₂ : Nat) : Bool := b₁ ≤ 524288 && b₂ ≤ 4194304

/-- Invocation-local schedules. Only checked preparation can construct a handle;
read-only views support independent conformance checks. Neither schedule is
allocated until its arithmetic stage can execute. -/
structure Tables where
  private mk ::
  b₁ : Nat
  b₂ : Nat
  powers : Option (List Nat) := none
  primes : Option (List Nat) := none

/-- Validate bounds without enumerating primes. -/
def prepare (b₁ b₂ : Nat) : Option Tables :=
  if validBounds b₁ b₂ then some ⟨b₁, b₂, none, none⟩ else none

namespace Internal

private def prepareStage1 (t : Tables) : Tables :=
  if t.powers.isSome then t else
    { t with powers := some ((primesBelow (t.b₁ + 1)).map (smoothPower · t.b₁)) }

private def prepareStage2 (t : Tables) : Tables :=
  if t.primes.isSome then t else
    { t with primes := some ((primesBelow (t.b₂ + 1)).filter (t.b₁ < ·)) }

private def multiplyPowers (n num den : Nat) : List Nat → EcmPoint → EcmPoint
  | [], p => p
  | k :: ks, p => multiplyPowers n num den ks (scalarMul n num den p k)

structure State where
  n : Nat
  num : Nat
  den : Nat
  point : EcmPoint

-- Setup and stage 1 match the natural-number production backend exactly.
private def startPrepared (n sigma : Nat) (t : Tables) :
    (EcmResult × Option State) × Tables := Id.run do
  if n < 4 || sigma < 6 then return ((.noFactor, none), t)
  let u := (sigma * sigma + n - 5) % n
  let v := 4 * sigma % n
  let u3 := u * u % n * u % n
  let v3 := v * v % n * v % n
  let vu := (v + n - u) % n
  let num := vu * vu % n * vu % n * ((3 * u + v) % n) % n
  let den := 4 * u3 % n * v % n
  let setup := classifyGcd n (Nat.gcd den n)
  if setup != .noFactor then return ((setup, none), t)
  let den := 4 * den % n
  let t := prepareStage1 t
  let point := multiplyPowers n num den (t.powers.getD []) ⟨u3, v3⟩
  let result := classifyGcd n (Nat.gcd point.z n)
  return ((result, if result == .noFactor then some ⟨n, num, den, point⟩ else none), t)

-- Diagnostic wrapper uses the same arithmetic and checked preparation.
def start (n sigma b₁ : Nat) : EcmResult × Option State :=
  match prepare b₁ b₁ with
  | none => (.noFactor, none)
  | some t => (startPrepared n sigma t).1

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
private def continueWith (s : State) (primes : List Nat)
    (checkGiants : Bool) : Trace := Id.run do
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

/-- Diagnostic continuation; no preparation for an invalid or empty interval. -/
def stage2 (s : State) (b₁ b₂ : Nat) (checkGiants : Bool := false) : Trace :=
  if s.n < 4 || b₂ ≤ b₁ then {} else
  match prepare b₁ b₂ with
  | none => {}
  | some t => continueWith s ((prepareStage2 t).primes.getD []) checkGiants

/-- Shared entry point. Returns the invocation-local handle for the next curve.
Only bound-dependent schedules are retained; all curve arithmetic remains local. -/
def searchPrepared (n sigma allowance : Nat) (t : Tables) :
    (EcmResult × Nat) × Tables := Id.run do
  if allowance == 0 then return ((.noFactor, 0), t)
  let ((result, saved), t) := startPrepared n sigma t
  let (result, work, t) := match saved with
    | some s => if t.b₂ > t.b₁ && allowance > 1 then
        let t := prepareStage2 t
        ((continueWith s (t.primes.getD []) false).result, 2, t)
      else (result, 1, t)
    | none => (result, 1, t)
  return ((match result with
    | .factor d => classifyGcd n d
    | other => other, work), t)

end Internal

private def searchCore (n sigma b₁ b₂ allowance : Nat) : EcmResult × Nat :=
  if allowance == 0 then (.noFactor, 0) else
  match prepare b₁ b₂ with
  | none => (.noFactor, 0)
  | some t => (Internal.searchPrepared n sigma allowance t).1

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
