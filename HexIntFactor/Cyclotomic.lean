/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Factor

public section

/-! Checked cyclotomic candidate splits for `b^n ± 1`.  The recursive
producer is untrusted; the public option returns only after checking the final
product against the original input. -/

namespace Hex

namespace Nat

/-- Sign in a difference/sum of powers. -/
inductive Sign where
  | minus
  | plus
deriving Repr, DecidableEq

/-- The natural-number target denoted by a signed power form. -/
def powerTarget (b n : Nat) : Sign → Nat
  | .minus => b ^ n - 1
  | .plus => b ^ n + 1

/-- One candidate cyclotomic value `Φ_index(base)`. -/
structure CyclotomicPart where
  /-- Cyclotomic index `d`. -/
  index : Nat
  /-- Candidate value `Φ_d(b)` at the requested base. -/
  value : Nat
deriving Repr, DecidableEq

private def divisorIndices (n : Nat) : List Nat :=
  (List.range n).map (· + 1) |>.filter fun d => n % d = 0

private def properValueProduct (i : Nat) (prior : List Nat)
    (values : Array Nat) : Nat :=
  prior.foldl (fun acc d =>
    if i % d = 0 then acc * values.getD d 0 else acc) 1

/-- Fill the required divisor-closed indices once, in ascending order. The
array gives constant-time access to every previously computed proper divisor;
`prior` contains exactly the filled indices, in reverse order. -/
private def buildValues (b : Nat) : List Nat → List Nat → Array Nat → Array Nat
  | [], _, values => values
  | i :: rest, prior, values =>
      let denominator := properValueProduct i prior values
      let value := (b ^ i - 1) / denominator
      buildValues b rest (i :: prior) (values.set! i value)

private def valueTable (b : Nat) (indices : List Nat) : Array Nat :=
  let limit := indices.foldl max 0
  buildValues b indices [] (Array.replicate (limit + 1) 0)

private def splitIndices (n : Nat) (sign : Sign) (all : List Nat) : List Nat :=
  match sign with
  | .minus => all
  | .plus => all.filter fun d => n % d ≠ 0

/-- Candidate split of `b^n - 1` or `b^n + 1`, guarded by an exact product
check and rejected on the degenerate domains. -/
def cyclotomicSplit? (b n : Nat) (sign : Sign) :
    Option (List CyclotomicPart) :=
  if b < 2 then none
  else if n = 0 then none
  else
    let limit : Nat := match sign with | .minus => n | .plus => 2 * n
    let all : List Nat := divisorIndices limit
    let values : Array Nat := valueTable b all
    let parts : List CyclotomicPart := (splitIndices n sign all).map fun d =>
      ⟨d, values.getD d 0⟩
    let target := powerTarget b n sign
    if (parts.map (·.value)).prod = target then some parts else none

/-- Every returned cyclotomic candidate has the requested domain and exact
product. -/
theorem cyclotomicSplit?_prod {b n : Nat} {sign : Sign}
    {parts : List CyclotomicPart}
    (h : cyclotomicSplit? b n sign = some parts) :
    2 ≤ b ∧ 0 < n ∧
      (parts.map (·.value)).prod =
        powerTarget b n sign := by
  by_cases hb : b < 2
  · simp [cyclotomicSplit?, hb] at h
  by_cases hn : n = 0
  · simp [cyclotomicSplit?, hb, hn] at h
  cases sign with
  | minus =>
      unfold cyclotomicSplit? at h
      rw [ite_eq_right hb, ite_eq_right hn] at h
      dsimp only at h
      split at h
      · rename_i hp
        injection h with heq
        subst parts
        exact ⟨by omega, Nat.pos_of_ne_zero hn, hp⟩
      · cases h
  | plus =>
      unfold cyclotomicSplit? at h
      rw [ite_eq_right hb, ite_eq_right hn] at h
      dsimp only at h
      split at h
      · rename_i hp
        injection h with heq
        subst parts
        exact ⟨by omega, Nat.pos_of_ne_zero hn, hp⟩
      · cases h

/-- Which top-level route produced a power-form factorization. -/
inductive PowerRoute where
  | cyclotomic
  | generic
deriving Repr, DecidableEq

namespace Internal

/-- Retry a power target only after ordinary subproblem exhaustion. An
invariant rejection is propagated with its original diagnostic scope; a
failed retry adds the earlier and fallback attempt subtotals. -/
def retryPower? (target : Nat) (failure : FactorFailure) (fuel : Nat) :
    Except FactorFailure (CheckedFactorization target × Rand × PowerRoute) :=
  match failure.stop with
  | .rejected => .error failure
  | .zero | .incomplete =>
      match factor? target failure.rand fuel with
      | .ok (F, r') => .ok (F, r', .generic)
      | .error fallback =>
          .error { fallback with
            attempts := failure.attempts + fallback.attempts }

/-- A scoped checker rejection is propagated unchanged and never retried as
generic exhaustion. -/
theorem retryPower?_rejected {target : Nat} {failure : FactorFailure}
    {fuel : Nat} (hstop : failure.stop = .rejected) :
    retryPower? target failure fuel = .error failure := by
  simp [retryPower?, hstop]

/-- A failed generic continuation preserves its diagnostics while adding the
exact earlier part-search subtotal. -/
theorem retryPower?_fallback {target : Nat} {failure fallback : FactorFailure}
    {fuel : Nat} (hstop : failure.stop ≠ .rejected)
    (hfactor : factor? target failure.rand fuel = .error fallback) :
    retryPower? target failure fuel = .error
      { fallback with
        attempts := failure.attempts + fallback.attempts } := by
  cases h : failure.stop <;> simp_all [retryPower?]

end Internal

/-- Canonical merged entries and exact search state for a completed suffix of
cyclotomic parts. -/
private structure PartFactors where
  entries : List PrimePower
  attempts : Nat
  rand : Rand

private def factorParts (fuel : Nat) : List CyclotomicPart → Rand →
    Except FactorFailure PartFactors
  | [], r => .ok ⟨[], 0, r⟩
  | part :: parts, r =>
      match Internal.factorCounted? part.value r fuel with
      | .error failure => .error failure
      | .ok current =>
          match factorParts fuel parts current.rand with
          | .error failure =>
              .error { failure with
                attempts := current.attempts + failure.attempts }
          | .ok rest =>
              .ok ⟨Internal.mergePowers current.factorization.raw.factors
                  rest.entries,
                current.attempts + rest.attempts, rest.rand⟩

private def factorPowerTarget? (target : Nat) (parts? : Option (List CyclotomicPart))
    (r : Rand) (fuel : Nat) :
    Except FactorFailure (CheckedFactorization target × Rand × PowerRoute) :=
  match parts? with
  | some parts =>
      match factorParts fuel parts r with
      | .ok factored =>
          let raw : Factorization := ⟨target, factored.entries⟩
          if h : checkFactorization raw = true then
            .ok (⟨raw, rfl, h⟩, factored.rand, .cyclotomic)
          else .error
            { stop := .rejected
              attempts := factored.attempts
              rand := factored.rand
              culprit := some ⟨target, factored.entries, 1⟩ }
      | .error failure =>
          Internal.retryPower? target failure fuel
  | none =>
      (factor? target r fuel).map fun (F, r') => (F, r', .generic)

/-- Factor a declared `b^n ± 1` form, trying its checked cyclotomic pieces
before the generic dispatch. The route tag makes this ordering testable. -/
def factorPowerWithRoute? (b n : Nat) (sign : Sign) (r : Rand)
    (fuel : Nat := defaultFuel (powerTarget b n sign)) :
    Except FactorFailure
      (CheckedFactorization (powerTarget b n sign) × Rand × PowerRoute) :=
  match sign with
  | .minus => factorPowerTarget? (b ^ n - 1) (cyclotomicSplit? b n .minus) r fuel
  | .plus => factorPowerTarget? (b ^ n + 1) (cyclotomicSplit? b n .plus) r fuel

/-- Convenience projection that hides the diagnostic route tag. -/
def factorPower? (b n : Nat) (sign : Sign) (r : Rand)
    (fuel : Nat := defaultFuel (powerTarget b n sign)) :
    Except FactorFailure
      (CheckedFactorization (powerTarget b n sign) × Rand) :=
  match factorPowerWithRoute? b n sign r fuel with
  | .ok (F, r', _) => .ok (F, r')
  | .error failure => .error failure

/-- The convenience projection preserves every failure unchanged, including
scoped checker rejection and accumulated retry diagnostics. -/
theorem factorPower?_error_iff {b n : Nat} {sign : Sign} {r : Rand}
    {fuel : Nat} {failure : FactorFailure} :
    factorPower? b n sign r fuel = .error failure ↔
      factorPowerWithRoute? b n sign r fuel = .error failure := by
  unfold factorPower?
  split <;> simp_all

/-- A projected success is exactly a routed success with the diagnostic tag
hidden. -/
theorem factorPower?_ok_iff {b n : Nat} {sign : Sign} {r r' : Rand}
    {fuel : Nat} {F : CheckedFactorization (powerTarget b n sign)} :
    factorPower? b n sign r fuel = .ok (F, r') ↔
      ∃ route, factorPowerWithRoute? b n sign r fuel = .ok (F, r', route) := by
  unfold factorPower?
  split <;> simp_all

/-- If no checked cyclotomic candidate exists, the route is exactly the
ordinary generic factorization search tagged as generic. -/
theorem factorPowerWithRoute?_generic {b n : Nat} {sign : Sign} {r : Rand}
    {fuel : Nat} (hparts : cyclotomicSplit? b n sign = none) :
    factorPowerWithRoute? b n sign r fuel =
      (factor? (powerTarget b n sign) r fuel).map fun (F, r') =>
        (F, r', .generic) := by
  cases sign with
  | minus =>
      change factorPowerTarget? (b ^ n - 1) (cyclotomicSplit? b n .minus)
          r fuel = _
      rw [hparts]
      simp only [factorPowerTarget?, powerTarget]
  | plus =>
      change factorPowerTarget? (b ^ n + 1) (cyclotomicSplit? b n .plus)
          r fuel = _
      rw [hparts]
      simp only [factorPowerTarget?, powerTarget]

/-- A cyclotomic-tagged result implies that the checked split was available. -/
theorem factorPowerWithRoute?_cyclotomic {b n : Nat} {sign : Sign} {r r' : Rand}
    {fuel : Nat} {F : CheckedFactorization (powerTarget b n sign)}
    (h : factorPowerWithRoute? b n sign r fuel = .ok (F, r', .cyclotomic)) :
    ∃ parts, cyclotomicSplit? b n sign = some parts := by
  cases hparts : cyclotomicSplit? b n sign with
  | some parts => exact ⟨parts, rfl⟩
  | none =>
      rw [factorPowerWithRoute?_generic hparts] at h
      cases hfactor : factor? (powerTarget b n sign) r fuel with
      | error failure =>
          rw [hfactor] at h
          simp only [Except.map] at h
          cases h
      | ok result =>
          rcases result with ⟨G, s⟩
          rw [hfactor] at h
          simp only [Except.map] at h
          cases h

end Nat

end Hex
