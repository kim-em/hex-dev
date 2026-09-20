/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Interval

@[expose] public section

/-!
# Bounded exact point certificates for π and exp(1)

The versioned sources use Machin's identity with a geometric arctangent
remainder, and the exponential factorial sum with its geometric remainder.
All calculations are rational or dyadic. Certificates are untrusted literal
data; the Mathlib companion owns real containment and effective convergence.

The resource model charges conservative bit bounds before any series or
rounding work. For order n, each arctangent term denominator has at most
18*n+9 bits (the larger reciprocal base is 239). Even unreduced accumulation
of n such terms has at most 32*(n+1)^2 bits per rational component. Factorials
and their partial-sum numerators fit this bound too. Reconstruction, radius,
and cross multiplication fit `integerBits` below. Reduction by gcd only
shrinks these bounds. Work units bound schoolbook multiplication/division and
Euclidean normalization by a cubic bit bound per rational operation; allocation
units bound cumulative temporary bits by a quadratic bound per operation.
These are deterministic conservative charges, not host timings or heap bytes.
-/

namespace Hex.Interval.Constants

/-- Source identities bind both the named constant and its exact formula. -/
inductive Source where
  | piMachinV1
  | expOneTaylorV1
  deriving DecidableEq, Repr

/-- Independent caps for series, integer arithmetic, allocation and replay.
The existing interval limits also charge endpoint and rounding work. -/
structure Limits where
  arithmetic : Arithmetic.PrecisionLimits
  maxOrder : Nat
  maxIntegerBits : Nat
  maxIntegerWork : Nat
  maxAllocation : Nat
  maxReplayWork : Nat
  deriving Repr

/-- An exact center and symmetric analytic remainder witness. -/
structure Approximation where
  center : Rat
  radius : Rat
  deriving DecidableEq, Repr

/-- Literal source-bound certificate. Precision is a width request, not a
claim that rounding to that grid alone suffices. -/
structure Certificate where
  source : Source
  bits : Nat
  order : Nat
  approximation : Approximation
  lower : Dyadic
  upper : Dyadic
  deriving DecidableEq

inductive Error where
  | source
  | precision
  | order
  | integerBits
  | integerWork
  | allocation
  | replay
  | witness
  | endpoints
  | width
  | construction (cost : CompareCost)
  | arithmetic (cost : Arithmetic.Cost)
  deriving Repr

/-- Peak bits, total integer work and total temporary-bit allocation charges.
Metadata uses only small arithmetic on already supplied natural numbers. -/
def charges (order bits : Nat) : Nat × Nat × Nat :=
  let b := 256 * (order + 1) ^ 2 + 8 * (bits + 3)
  let steps := 128 * (order + 1)
  (b, steps * b ^ 3, steps * b ^ 2)

/-- Gate every loop, shift and exact arithmetic operation before execution.
Zero order is refused because the exponential remainder divides by order. -/
def preflight (limits : Limits) (bits order : Nat) (replay : Bool) : Except Error Unit := do
  if order == 0 || order > limits.maxOrder then throw .order
  let precision : Int := bits + 2
  match Arithmetic.admitPrecision limits.arithmetic precision with
  | .error cost => throw (.arithmetic cost)
  | .ok _ => pure ()
  let (b, work, allocation) := charges order bits
  if b > limits.maxIntegerBits then throw .integerBits
  if work > limits.maxIntegerWork then throw .integerWork
  if allocation > limits.maxAllocation then throw .allocation
  if replay && work > limits.maxReplayWork then throw .replay

/-- The alternating sum through indices `i < n`, paired with `q^(2*n+1)`.
This helper is unchecked; public callers enter through `preflight`. -/
def arctanState (q : Nat) : Nat → Rat × Nat
  | 0 => (0, q)
  | n + 1 =>
      let (sum, power) := arctanState q n
      let term := mkRat (if n % 2 == 0 then 1 else -1) ((2 * n + 1) * power)
      (sum + term, power * q * q)

/-- The recurrence retains exactly the power used by the geometric tail. -/
theorem arctan_power (q n : Nat) : (arctanState q n).2 = q ^ (2 * n + 1) := by
  induction n with
  | zero => simp [arctanState]
  | succ n ih =>
      change (arctanState q n).2 * q * q = q ^ (2 * (n + 1) + 1)
      rw [ih, show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
      simp only [Nat.pow_succ]

/-- The geometric radius `x*(x²)^n/(1-x²)`, `x=1/q`.
The source fixes q to 5 or 239, so the denominator is positive. -/
def arctanRadius (q power : Nat) : Rat :=
  mkRat (q * q) (power * (q * q - 1))

/-- `S_n*n!` and `n!`, where `S_n = sum(i < n) 1/i!`. -/
def expState : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
      let (numerator, factorial) := expState n
      ((n + 1) * (numerator + 1), (n + 1) * factorial)

/-- Source formulas shared with the companion's analytic theorems.
This unchecked helper must not be used as an untrusted resource boundary. -/
def approximate (source : Source) (order : Nat) : Approximation :=
  match source with
  | .piMachinV1 =>
      let (s, p) := arctanState 5 order
      let (t, q) := arctanState 239 order
      ⟨16 * s - 4 * t, 16 * arctanRadius 5 p + 4 * arctanRadius 239 q⟩
  | .expOneTaylorV1 =>
      let (numerator, factorial) := expState order
      ⟨mkRat numerator factorial, mkRat (order + 1) (factorial * order)⟩

def build : BuildResult → Except Error Hex.Interval
  | .ready value => .ok value
  | .resourceLimit cost => .error (.construction cost)

def compute : Arithmetic.Result → Except Error Hex.Interval
  | .ready value => .ok value
  | .resourceLimit cost => .error (.arithmetic cost)

/-- Construct closed, ordered cuts after admitting their comparison. -/
def buildBounds (limits : Limits) (lo hi : Dyadic) : Except Error Hex.Interval := do
  let cost := CompareCost.ofDyadic lo hi
  if !cost.allowed limits.arithmetic.endpoint then throw (.construction cost)
  if !(lo ≤ hi) then throw .endpoints
  build (betweenWithin limits.arithmetic.endpoint lo false hi false)

/-- Outward rational projection via the existing checked singleton quotient.
The admitted series bit bound applies before the integer singleton conversion. -/
def project (limits : Limits) (precision : Int) (value : Rat) :
    Except Error (Dyadic × Dyadic) := do
  let numerator ← build (singletonWithin limits.arithmetic.endpoint (Dyadic.ofInt value.num))
  let denominator ← build (singletonWithin limits.arithmetic.endpoint (Dyadic.ofInt value.den))
  let interval ← compute (divWithin limits.arithmetic precision numerator denominator)
  match interval.view with
  | .bounds (.finite lo _) (.finite hi _) => pure (lo, hi)
  | _ => throw .endpoints

def widthWithin (limits : Limits) (bits : Nat) (lo hi : Dyadic) :
    Except Error Unit := do
  let a ← build (singletonWithin limits.arithmetic.endpoint lo)
  let b ← build (singletonWithin limits.arithmetic.endpoint hi)
  let difference ← build (subWithin limits.arithmetic.endpoint b a)
  let target := Dyadic.ofIntWithPrec 1 bits
  match difference.view with
  | .bounds (.finite width _) _ =>
      let cost := CompareCost.ofDyadic width target
      if !cost.allowed limits.arithmetic.endpoint then throw (.construction cost)
      if width ≤ target then pure () else throw .width
  | _ => throw .endpoints

def smallRat (limit : Nat) (value : Rat) : Bool :=
  EndpointCost.natBits value.num.natAbs ≤ limit &&
    EndpointCost.natBits value.den ≤ limit

/-- Finish an already preflighted exact approximation. This is an unchecked
internal stage; untrusted requests must use `generate` or `check`. -/
def finish (limits : Limits) (source : Source) (bits order : Nat)
    (approximation : Approximation) : Except Error Certificate := do
  let (b, _, _) := charges order bits
  if !smallRat b approximation.center || !smallRat b approximation.radius then
    throw .integerBits
  let (lo, _) ← project limits (bits + 2) (approximation.center - approximation.radius)
  let (_, hi) ← project limits (bits + 2) (approximation.center + approximation.radius)
  let _ ← buildBounds limits lo hi
  widthWithin limits bits lo hi
  pure ⟨source, bits, order, approximation, lo, hi⟩

/-- Produce a literal certificate at an explicitly supplied approximation order.
Insufficient order is an honest width failure, never a false precision claim. -/
def generate (limits : Limits) (source : Source) (bits order : Nat) :
    Except Error Certificate := do
  preflight limits bits order false
  finish limits source bits order (approximate source order)

/-- Deterministic order schedule for a requested width. It does not search for
an order or silently raise any caller budget. -/
def enclose (limits : Limits) (source : Source) (bits : Nat) : Except Error Certificate :=
  generate limits source bits (bits + 4)

/-- Replay binds the expected subject and precision, admits all literal fields,
recomputes the exact source/remainder and outward cuts, and checks actual width.
An accepted value is computational evidence only; real soundness is companion-owned. -/
def check (limits : Limits) (source : Source) (bits : Nat) (certificate : Certificate) :
    Except Error Hex.Interval := do
  if certificate.source != source then throw .source
  if certificate.bits != bits then throw .precision
  preflight limits bits certificate.order true
  let (b, _, _) := charges certificate.order bits
  if !smallRat b certificate.approximation.center ||
      !smallRat b certificate.approximation.radius then throw .integerBits
  if (EndpointCost.ofDyadic certificate.lower).numeratorBits > b ||
      (EndpointCost.ofDyadic certificate.upper).numeratorBits > b ||
      (EndpointCost.ofDyadic certificate.lower).encodedExponentBits > b ||
      (EndpointCost.ofDyadic certificate.upper).encodedExponentBits > b then throw .integerBits
  if !(EndpointCost.ofDyadic certificate.lower).allowed limits.arithmetic.endpoint ||
      !(EndpointCost.ofDyadic certificate.upper).allowed limits.arithmetic.endpoint then
    throw .endpoints
  let approximation := approximate source certificate.order
  if certificate.approximation != approximation then throw .witness
  let expected ← finish limits source bits certificate.order approximation
  if certificate.lower != expected.lower || certificate.upper != expected.upper then
    throw .endpoints
  buildBounds limits certificate.lower certificate.upper

/-- Explicit conservative budgets for the `bits + 4` order schedule.
This convenience scales every cap with the request; it is not an input
sanitizer. Untrusted requests require independently chosen caller caps. -/
def limitsFor (bits : Nat) : Limits :=
  let (b, work, allocation) := charges (bits + 4) bits
  { arithmetic :=
      { endpoint := ⟨16 * b, 16 * b⟩
        maxPrecisionMagnitude := bits + 2
        maxPrecisionBits := EndpointCost.natBits (bits + 2)
        maxTemporaryBits := 16 * b }
    maxOrder := bits + 4
    maxIntegerBits := b
    maxIntegerWork := work
    maxAllocation := allocation
    maxReplayWork := work }

/-- Accepted certificates name the subject requested by the caller. -/
theorem checked_source {limits source bits certificate interval}
    (h : check limits source bits certificate = .ok interval) :
    certificate.source = source := by
  by_cases hs : certificate.source = source
  · exact hs
  · simp [check, hs, bind, Except.bind, throw] at h

/-- Accepted certificates bind the caller's width request. -/
theorem checked_bits {limits source bits certificate interval}
    (h : check limits source bits certificate = .ok interval) :
    certificate.bits = bits := by
  have hs := checked_source h
  by_cases hb : certificate.bits = bits
  · exact hb
  · simp [check, hs, hb, bind, Except.bind, throw] at h


/-- Replay authenticates the exact rational approximation and remainder. -/
theorem checked_approximation {limits source bits certificate interval}
    (h : check limits source bits certificate = .ok interval) :
    certificate.approximation = approximate source certificate.order := by
  have hs := checked_source h
  have hb := checked_bits h
  by_cases ha : certificate.approximation = approximate source certificate.order
  · exact ha
  · simp [check, hs, hb, ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all


/-- Zero order cannot cross the replay boundary. -/
theorem checked_order {limits source bits certificate interval}
    (h : check limits source bits certificate = .ok interval) :
    0 < certificate.order := by
  have hs := checked_source h
  have hb := checked_bits h
  by_cases hn : certificate.order = 0
  · simp [check, hs, hb, preflight, hn, bind, Except.bind, throw,
      throwThe, MonadExceptOf.throw] at h
  · omega


/-- A successful finite builder exposes the normalized exact input cuts. -/
theorem build_view {limit lower upper interval}
    (h : build (betweenWithin limit lower false upper false) = .ok interval) :
    interval.view =
      (Raw.bounds (.finite lower false) (.finite upper false)).normalizeUnchecked := by
  cases hb : betweenWithin limit lower false upper false with
  | ready value =>
      have hv : value = interval := by simpa [hb, build] using h
      subst value
      exact view_betweenWithin_ready hb
  | resourceLimit cost => simp [hb, build] at h

/-- Successful construction refuses reversed cuts. -/
theorem bounds_ordered {limits lower upper interval}
    (h : buildBounds limits lower upper = .ok interval) : lower ≤ upper := by
  by_cases ho : lower ≤ upper
  · exact ho
  · simp [buildBounds, ho, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h
    split at h <;> simp_all

/-- The ordered builder preserves its literal cuts under normalization. -/
theorem bounds_view {limits lower upper interval}
    (h : buildBounds limits lower upper = .ok interval) :
    interval.view =
      (Raw.bounds (.finite lower false) (.finite upper false)).normalizeUnchecked := by
  apply build_view (limit := limits.arithmetic.endpoint)
  simp [buildBounds, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h <;> try simp_all
  split at h <;> try simp_all

/-- Accepted replay retains the checked ordered builder result. -/
theorem checked_bounds {limits source bits certificate interval}
    (h : check limits source bits certificate = .ok interval) :
    buildBounds limits certificate.lower certificate.upper = .ok interval := by
  have hs := checked_source h
  have hb := checked_bits h
  have ha := checked_approximation h
  simp [check, hs, hb, ha, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h <;> try simp_all
  split at h <;> try simp_all
  split at h <;> try simp_all
  split at h <;> try simp_all
  split at h <;> try simp_all
  split at h <;> try simp_all

/-- Accepted replay has ordered literal cuts. -/
theorem checked_ordered {limits source bits certificate interval}
    (h : check limits source bits certificate = .ok interval) :
    certificate.lower ≤ certificate.upper :=
  bounds_ordered (checked_bounds h)

/-- Replay returns exactly the certificate's two closed, ordered literal cuts. -/
theorem checked_view {limits source bits certificate interval}
    (h : check limits source bits certificate = .ok interval) :
    interval.view = .bounds (.finite certificate.lower false)
      (.finite certificate.upper false) := by
  rw [bounds_view (checked_bounds h)]
  apply Raw.normalizeUnchecked_eq_self
  have ho := checked_ordered h
  by_cases hl : certificate.lower < certificate.upper
  · simp [Raw.CutConsistent, Raw.consistent, hl]
  · have he : certificate.lower = certificate.upper :=
      Dyadic.le_antisymm ho (Dyadic.not_le.mp hl)
    simp [Raw.CutConsistent, Raw.consistent, he]


end Hex.Interval.Constants
