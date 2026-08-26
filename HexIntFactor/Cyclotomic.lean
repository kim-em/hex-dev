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

/-- One candidate cyclotomic value `Φ_index(base)`. -/
structure CyclotomicPart where
  /-- Cyclotomic index `d`. -/
  index : Nat
  /-- Candidate value `Φ_d(b)` at the requested base. -/
  value : Nat
deriving Repr, DecidableEq

private def properValueProduct (i : Nat) (values : List Nat) : Nat :=
  (List.range (i - 1)).foldl (fun acc j =>
    let d := j + 1
    if i % d = 0 then acc * values.getD j 1 else acc) 1

private def buildValues (b : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 =>
      let previous := buildValues b n
      let i := n + 1
      previous ++ [(b ^ i - 1) / properValueProduct i previous]

/-- Recursive Nat candidate for `Φ_d(b)`. -/
def cyclotomicValue (b d : Nat) : Nat :=
  if d = 0 then 0 else (buildValues b d).getD (d - 1) 0

private def splitIndices (n : Nat) (sign : Sign) : List Nat :=
  match sign with
  | .minus =>
      (List.range n).map (· + 1) |>.filter fun d => n % d = 0
  | .plus =>
      (List.range (2 * n)).map (· + 1) |>.filter fun d =>
        2 * n % d = 0 && n % d ≠ 0

/-- Candidate split of `b^n - 1` or `b^n + 1`, guarded by an exact product
check and rejected on the degenerate domains. -/
def cyclotomicSplit? (b n : Nat) (sign : Sign) :
    Option (List CyclotomicPart) :=
  if b < 2 then none
  else if n = 0 then none
  else
    let parts := (splitIndices n sign).map fun d =>
      ⟨d, cyclotomicValue b d⟩
    let target := match sign with
      | .minus => b ^ n - 1
      | .plus => b ^ n + 1
    if (parts.map (·.value)).prod = target then some parts else none

/-- Every returned cyclotomic candidate has the requested domain and exact
product. -/
theorem cyclotomicSplit?_prod {b n : Nat} {sign : Sign}
    {parts : List CyclotomicPart}
    (h : cyclotomicSplit? b n sign = some parts) :
    2 ≤ b ∧ 0 < n ∧
      (parts.map (·.value)).prod =
        match sign with
        | .minus => b ^ n - 1
        | .plus => b ^ n + 1 := by
  by_cases hb : b < 2
  · simp [cyclotomicSplit?, hb] at h
  by_cases hn : n = 0
  · simp [cyclotomicSplit?, hb, hn] at h
  cases sign with
  | minus =>
      unfold cyclotomicSplit? at h
      rw [if_neg hb, if_neg hn] at h
      dsimp only at h
      split at h
      · rename_i hp
        injection h with heq
        subst parts
        exact ⟨by omega, Nat.pos_of_ne_zero hn, hp⟩
      · cases h
  | plus =>
      unfold cyclotomicSplit? at h
      rw [if_neg hb, if_neg hn] at h
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
            attempts := failure.attempts + fallback.attempts
            metered := failure.metered && fallback.metered }

end Internal

private def insertPartPower (entry : PrimePower) : List PrimePower → List PrimePower
  | [] => [entry]
  | current :: rest =>
      if entry.prime < current.prime then entry :: current :: rest
      else if entry.prime = current.prime then
        { current with exponent := current.exponent + entry.exponent } :: rest
      else current :: insertPartPower entry rest

private def mergePartPowers (source target : List PrimePower) : List PrimePower :=
  source.foldl (fun acc entry => insertPartPower entry acc) target

private def factorParts (fuel : Nat) : List CyclotomicPart → Rand →
    Except FactorFailure (List PrimePower × Rand)
  | [], r => .ok ([], r)
  | part :: parts, r =>
      match factor? part.value r fuel with
      | .error failure => .error failure
      | .ok (F, r') =>
          match factorParts fuel parts r' with
          | .error failure => .error failure
          | .ok (entries, r'') => .ok (mergePartPowers F.raw.factors entries, r'')

private def factorPowerTarget? (target : Nat) (parts? : Option (List CyclotomicPart))
    (r : Rand) (fuel : Nat) :
    Except FactorFailure (CheckedFactorization target × Rand × PowerRoute) :=
  match parts? with
  | some parts =>
      match factorParts fuel parts r with
      | .ok (entries, r') =>
          let raw : Factorization := ⟨target, entries⟩
          if h : checkFactorization raw = true then
            .ok (⟨raw, rfl, h⟩, r', .cyclotomic)
          else .error
            { stop := .rejected
              attempts := 0
              rand := r'
              culprit := some ⟨target, entries, 1⟩
              metered := false }
      | .error failure =>
          -- `factor?` does not expose successful-search counts. A failure in
          -- a later part therefore omits the work spent on earlier parts;
          -- retain the diagnostic, but do not advertise that subtotal as
          -- exact when the generic continuation later stops.
          Internal.retryPower? target { failure with metered := false } fuel
  | none =>
      match factor? target r fuel with
      | .ok (F, r') => .ok (F, r', .generic)
      | .error failure => .error failure

/-- Factor a declared `b^n ± 1` form, trying its checked cyclotomic pieces
before the generic dispatch. The route tag makes this ordering testable. -/
def factorPowerWithRoute? (b n : Nat) (sign : Sign) (r : Rand)
    (fuel : Nat := defaultFuel (b ^ n + 1)) :
    Except FactorFailure
      (CheckedFactorization
        (match sign with | .minus => b ^ n - 1 | .plus => b ^ n + 1) ×
       Rand × PowerRoute) :=
  match sign with
  | .minus => factorPowerTarget? (b ^ n - 1) (cyclotomicSplit? b n .minus) r fuel
  | .plus => factorPowerTarget? (b ^ n + 1) (cyclotomicSplit? b n .plus) r fuel

/-- Convenience projection that hides the diagnostic route tag. -/
def factorPower? (b n : Nat) (sign : Sign) (r : Rand)
    (fuel : Nat := defaultFuel (b ^ n + 1)) :
    Except FactorFailure
      (CheckedFactorization
        (match sign with | .minus => b ^ n - 1 | .plus => b ^ n + 1) × Rand) :=
  match factorPowerWithRoute? b n sign r fuel with
  | .ok (F, r', _) => .ok (F, r')
  | .error failure => .error failure

end Nat

end Hex
