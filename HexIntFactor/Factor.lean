/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Ecm
public import HexIntFactor.PMinusOne
public import HexIntFactor.Rho
public import HexIntFactor.Small

public section

/-! Fuel-bounded factorization dispatch.  Search output crosses into the
trusted API only through `checkPartial` or `checkFactorization`. -/

namespace Hex

namespace Nat

/-- Why complete factorization did not return an answer. -/
inductive FactorStop where
  | zero
  | incomplete
  | rejected
deriving Repr, DecidableEq

/-- Checked partial data retained when complete search stops. -/
structure PartialSnapshot where
  raw : PartialFactorization
  valid : checkPartial raw = true
deriving Repr

/-- Resumable factorization failure. -/
structure FactorFailure where
  stop : FactorStop
  attempts : Nat
  rand : Rand
  snapshot : Option PartialSnapshot := none
deriving Repr

/-- Default search budget, scaled by input bit length. -/
def defaultFuel (n : Nat) : Nat := 4 * n.log2 + 32

private structure FactorAttempt (n : Nat) where
  raw : PartialFactorization
  subject_eq : raw.subject = n
  rand : Rand
  attempts : Nat

private def insertPower (entry : PrimePower) : List PrimePower → List PrimePower
  | [] => [entry]
  | current :: rest =>
      if entry.prime < current.prime then entry :: current :: rest
      else if entry.prime = current.prime then
        { current with exponent := current.exponent + entry.exponent } :: rest
      else current :: insertPower entry rest

private def mergePowers (entries : List PrimePower) (into : List PrimePower) :
    List PrimePower :=
  entries.foldl (fun acc entry => insertPower entry acc) into

private structure SearchState where
  factors : List PrimePower
  residual : Nat
  rand : Rand
  attempts : Nat

private def searchGo : Nat → List (Nat × Nat) → List PrimePower → Nat →
    Rand → Nat → SearchState
  | 0, stack, factors, residual, r, attempts =>
      { factors
        residual := stack.foldl (fun acc item => acc * item.1 ^ item.2) residual
        rand := r
        attempts }
  | _fuel + 1, [], factors, residual, r, attempts =>
      ⟨factors, residual, r, attempts⟩
  | fuel + 1, (m, multiplier) :: stack, factors, residual, r, attempts =>
      if m = 1 then searchGo fuel stack factors residual r attempts
      else
        let trial := trialFactors m
        let found := trial.1.map fun e =>
          { e with exponent := e.exponent * multiplier }
        let factors := mergePowers found factors
        let m := trial.2
        if m = 1 then searchGo fuel stack factors residual r attempts
        else
          match primeCert? m r (fuel + 1) with
          | .ok (cert, r') =>
              searchGo fuel stack
                (insertPower ⟨multiplier, cert.raw⟩ factors)
                residual r' attempts
          | .error primeFailure =>
              match rhoSplit? m primeFailure.rand
                  (min 1000000 ((fuel + 1) * (fuel + 1))) with
              | .ok (d, r') =>
                  searchGo fuel ((d, multiplier) :: (m / d, multiplier) :: stack)
                    factors residual r' (attempts + primeFailure.attempts + 1)
              | .error rhoFailure =>
                  match pMinusOneFactor m 2 (min primeTableBound (64 * (fuel + 1))) with
                  | .factor d =>
                      searchGo fuel ((d, multiplier) :: (m / d, multiplier) :: stack)
                        factors residual rhoFailure.rand
                        (attempts + primeFailure.attempts + rhoFailure.attempts + 1)
                  | .noFactor | .whole =>
                      match ecmStage1 m (6 + attempts % 64)
                          (min primeTableBound (64 * (fuel + 1))) with
                      | .factor d =>
                          searchGo fuel
                            ((d, multiplier) :: (m / d, multiplier) :: stack)
                            factors residual rhoFailure.rand
                            (attempts + primeFailure.attempts + rhoFailure.attempts + 1)
                      | .noFactor | .whole =>
                          searchGo fuel stack factors (residual * m ^ multiplier)
                            rhoFailure.rand
                            (attempts + primeFailure.attempts + rhoFailure.attempts + 1)

private def smallAttempt (n : Nat) (r : Rand) (fuel : Nat) :
    FactorAttempt n :=
  let candidate := smallCandidate n
  let result := searchGo fuel
    [(candidate.residualBase, candidate.residualExponent)]
    candidate.factors 1 r 0
  ⟨⟨n, result.factors, result.residual⟩, rfl,
    result.rand, result.attempts⟩

namespace Internal

/-- Check an untrusted partial candidate and tie it to the requested subject.
Checker rejection is an internal search failure, not fuel exhaustion. -/
def acceptPartial? (n : Nat) (hn : 0 < n) (raw : PartialFactorization)
    (r : Rand) (attempts : Nat) :
    Except FactorFailure (CheckedPartialFactorization n × Rand) :=
  let fallback : PartialFactorization := ⟨n, [], n⟩
  have hf : checkPartial fallback = true := by
    dsimp [fallback]
    simp [checkPartial, checkEntries, factorProduct, boundedPowMul, hn]
  let rejected : FactorFailure :=
    { stop := .rejected
      attempts
      rand := r
      snapshot := some ⟨fallback, hf⟩ }
  if hs : raw.subject = n then
    if hv : checkPartial raw = true then
      .ok (⟨raw, hs, hv⟩, r)
    else .error rejected
  else .error rejected

/-- Candidate acceptance never confuses checker rejection with exhaustion. -/
theorem acceptPartial?_error {n hn raw r attempts f}
    (h : acceptPartial? n hn raw r attempts = .error f) :
    f.stop = .rejected ∧
      ∃ saved, f.snapshot = some saved ∧ saved.raw.subject = n := by
  unfold acceptPartial? at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · injection h with h
      subst h
      simp
  · injection h with h
    subst h
    simp

end Internal

/-- Return checked partial data for positive input, or expose a rejected
internal candidate. -/
def factorPartial? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) :
    Except FactorFailure (CheckedPartialFactorization n × Rand) :=
  if hn : n = 0 then .error { stop := .zero, attempts := 0, rand := r }
  else
    let out := smallAttempt n r fuel
    Internal.acceptPartial? n (Nat.pos_of_ne_zero hn) out.raw out.rand out.attempts

/-- Complete factorization when the checked partial residual is `1`. -/
def factor? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) :
    Except FactorFailure (CheckedFactorization n × Rand) :=
  if hn : n = 0 then .error { stop := .zero, attempts := 0, rand := r }
  else
    let out := smallAttempt n r fuel
    match Internal.acceptPartial? n (Nat.pos_of_ne_zero hn) out.raw out.rand
        out.attempts with
    | .error failure => .error failure
    | .ok (F, r') =>
        if _hr : F.raw.residual = 1 then
          let raw : Factorization := ⟨n, F.raw.factors⟩
          if hv : checkFactorization raw = true then
            .ok (⟨raw, rfl, hv⟩, r')
          else .error
            { stop := .rejected
              attempts := out.attempts
              rand := r'
              snapshot := some ⟨F.raw, F.valid⟩ }
        else .error
          { stop := .incomplete
            attempts := out.attempts
            rand := r'
            snapshot := some ⟨F.raw, F.valid⟩ }

/-- Partial search errors are either the distinguished zero input or an
internal candidate rejection. -/
theorem factorPartial?_error {n r fuel f}
    (h : factorPartial? n r fuel = .error f) :
    (f.stop = .zero ∧ n = 0) ∨
      (f.stop = .rejected ∧
        ∃ saved, f.snapshot = some saved ∧ saved.raw.subject = n) := by
  unfold factorPartial? at h
  split at h
  · rename_i hn
    injection h with h
    subst h
    exact Or.inl ⟨rfl, hn⟩
  · dsimp only at h
    exact Or.inr (Internal.acceptPartial?_error h)

/-- Every positive input either has checked partial data or exposes an internal
candidate rejection; rejection is never reported as ordinary exhaustion. -/
theorem factorPartial?_success {n r fuel} (hn : 0 < n) :
    (∃ F r', factorPartial? n r fuel = .ok (F, r')) ∨
      ∃ f saved, factorPartial? n r fuel = .error f ∧
        f.stop = .rejected ∧ f.snapshot = some saved ∧
          saved.raw.subject = n := by
  cases hresult : factorPartial? n r fuel with
  | ok result => exact Or.inl ⟨result.1, result.2, rfl⟩
  | error f =>
      rcases factorPartial?_error hresult with ⟨_, hz⟩ | ⟨hrejected, hsnapshot⟩
      · subst n
        cases hn
      · obtain ⟨saved, hsaved, hsubject⟩ := hsnapshot
        exact Or.inr ⟨f, saved, rfl, hrejected, hsaved, hsubject⟩

end Nat

end Hex
