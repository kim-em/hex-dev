/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Table
public import HexArith.Montgomery.Context
public import HexBasic.Rand

public section

/-! Pollard `p - 1` stage 1, shared with integer factorization.  This is an
untrusted search primitive; a factor result is checked for range and
divisibility before it is exposed. -/

namespace Hex

namespace Nat

/-- The three semantically distinct stage-1 gcd outcomes. -/
inductive PMinusOneResult where
  | noFactor
  | factor (value : Nat)
  | whole
deriving Repr, DecidableEq

/-- The result of one counted deterministic stage-1 call. A call is one
attempt on every terminal gcd outcome. Pollard `p - 1` draws no randomness,
so the returned generator is exactly the supplied state; carrying it here
lets randomized callers resume through the same boundary as rho. -/
structure PMinusOneAttempt where
  /-- The terminal gcd outcome. -/
  result : PMinusOneResult
  /-- Semantic stage-1 calls executed; always one at this boundary. -/
  attempts : Nat
  /-- The unchanged generator state. -/
  rand : Rand
deriving Repr, DecidableEq

/-- Accepted stage-1 smoothness cap. It remains inside the complete table range,
but is independent of later table-policy growth so search cost and retry-ladder
coverage do not change as a side effect of a larger certification table. -/
def smoothBoundCap : Nat := 9999

/-- Clamp a requested stage-1 bound to the complete committed-table range. -/
def smoothBound (bound : Nat) : Nat := min bound smoothBoundCap

@[simp]
theorem smoothBound_idem (bound : Nat) :
    smoothBound (smoothBound bound) = smoothBound bound := by
  simp [smoothBound, Nat.min_assoc]

private def largestPower (q bound : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc =>
      if acc ≤ bound / q then largestPower q bound fuel (acc * q) else acc

private def stageExponent (q bound : Nat) : Nat :=
  largestPower q bound (bound.log2 + 1) q

private def raiseSmooth (n bound : Nat) : List Nat → Nat → Nat
  | [], x => x
  | q :: qs, x =>
      if q ≤ bound then
        raiseSmooth n bound qs
          (HexArith.powModNat x (stageExponent q bound) n)
      else x

private def pMinusOneStage1Core (n base bound : Nat) : PMinusOneResult :=
  if n < 4 ∨ base ≤ 1 ∨ n ≤ base then .noFactor
  else
    let initial := Nat.gcd base n
    if 1 < initial then
      if initial < n ∧ n % initial = 0 then .factor initial else .whole
    else
      let x := raiseSmooth n bound primeTable.toList (base % n)
      let g := Nat.gcd ((x + n - 1) % n) n
      if g = 1 then .noFactor
      else if 1 < g ∧ g < n ∧ n % g = 0 then .factor g
      else .whole

/-- One deterministic Pollard `p - 1` stage-1 attempt. Invalid bases or
moduli return `noFactor`; a gcd equal to the modulus is reported separately
as `whole`. The effective smoothness bound is `smoothBound bound`, never an
incomplete extension beyond the committed prime table. -/
def pMinusOneStage1 (n base bound : Nat) : PMinusOneResult :=
  pMinusOneStage1Core n base (smoothBound bound)

/-- One counted, resumable Pollard `p - 1` stage-1 attempt. The deterministic
primitive consumes no generator words, but every call costs exactly one search
attempt whether it returns `noFactor`, a proper factor, or `whole`. -/
def pMinusOneStage1Counted (n base bound : Nat) (r : Rand) :
    PMinusOneAttempt :=
  ⟨pMinusOneStage1 n base bound, 1, r⟩

/-- Requests beyond the complete prime-table range are exactly capped. -/
theorem pMinusOneStage1_bound (n base bound : Nat) :
    pMinusOneStage1 n base bound =
      pMinusOneStage1 n base (smoothBound bound) := by
  simp [pMinusOneStage1]

/-- Every reported factor is a dynamically checked proper divisor. -/
theorem pMinusOneStage1_spec {n base bound d : Nat}
    (h : pMinusOneStage1 n base bound = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold pMinusOneStage1 pMinusOneStage1Core at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · split at h
      · rename_i _ hvalid
        injection h with heq
        subst d
        exact ⟨by assumption, hvalid.1,
          Nat.dvd_of_mod_eq_zero hvalid.2⟩
      · cases h
    · split at h
      · cases h
      · split at h
        · rename_i _ hg hvalid
          injection h with heq
          subst d
          exact ⟨hvalid.1, hvalid.2.1,
            Nat.dvd_of_mod_eq_zero hvalid.2.2⟩
        · cases h

/-- A proper factor returned through the counted boundary satisfies the same
dynamically checked contract as the compatibility result. -/
theorem pMinusOneStage1Counted_spec {n base bound d : Nat} {r : Rand}
    (h : (pMinusOneStage1Counted n base bound r).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  exact pMinusOneStage1_spec h

end Nat

end Hex
