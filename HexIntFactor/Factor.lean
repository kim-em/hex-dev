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
  /-- Last checked partial aggregate, when the stopped route has one. -/
  snapshot : Option PartialSnapshot := none
  /-- Raw aggregate rejected by a checker, when rejection caused the stop. -/
  culprit : Option PartialFactorization := none
  /-- Whether `attempts` is an exact count for the stopped route. -/
  metered : Bool := true
deriving Repr

/-- Default search budget, scaled by input bit length. -/
def defaultFuel (n : Nat) : Nat := 4 * n.log2 + 32

private structure FactorAttempt (n : Nat) where
  raw : PartialFactorization
  subject_eq : raw.subject = n
  rand : Rand
  attempts : Nat
  powerRoutes : Nat

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
  powerRoutes : Nat

private def searchGo : Nat → List (Nat × Nat) → List PrimePower → Nat →
    Rand → Nat → Nat → SearchState
  | 0, stack, factors, residual, r, attempts, powerRoutes =>
      { factors
        residual := stack.foldl (fun acc item => acc * item.1 ^ item.2) residual
        rand := r
        attempts
        powerRoutes }
  | _fuel + 1, [], factors, residual, r, attempts, powerRoutes =>
      ⟨factors, residual, r, attempts, powerRoutes⟩
  | fuel + 1, (m, multiplier) :: stack, factors, residual, r, attempts,
      powerRoutes =>
      if m = 1 then
        searchGo fuel stack factors residual r attempts powerRoutes
      else
        -- Keep the full structural pipeline here: table-coprimality of stack
        -- entries is an invariant of the current producers, not of their type.
        let candidate := (smallCandidate m).scale multiplier
        let powerRoutes := match candidate.route with
          | .trial => powerRoutes
          | .perfectPower => powerRoutes + 1
        let factors := mergePowers candidate.factors factors
        let m := candidate.residualBase
        let multiplier := candidate.residualExponent
        if m = 1 then
          searchGo fuel stack factors residual r attempts powerRoutes
        else
          match primeCert? m r (fuel + 1) with
          | .ok (cert, r') =>
              searchGo fuel stack
                (insertPower ⟨multiplier, cert.raw⟩ factors)
                residual r' attempts powerRoutes
          | .error primeFailure =>
              match rhoSplit? m primeFailure.rand
                  (min 1000000 ((fuel + 1) * (fuel + 1))) with
              | .ok (d, r') =>
                  searchGo fuel ((d, multiplier) :: (m / d, multiplier) :: stack)
                    factors residual r' (attempts + primeFailure.attempts + 1)
                    powerRoutes
              | .error rhoFailure =>
                  match pMinusOneFactor m 2 (min primeTableBound (64 * (fuel + 1))) with
                  | .factor d =>
                      searchGo fuel ((d, multiplier) :: (m / d, multiplier) :: stack)
                        factors residual rhoFailure.rand
                        (attempts + primeFailure.attempts + rhoFailure.attempts + 1)
                        powerRoutes
                  | .noFactor | .whole =>
                      match ecmStage1 m (6 + attempts % 64)
                          (min primeTableBound (64 * (fuel + 1))) with
                      | .factor d =>
                          searchGo fuel
                            ((d, multiplier) :: (m / d, multiplier) :: stack)
                            factors residual rhoFailure.rand
                            (attempts + primeFailure.attempts + rhoFailure.attempts + 1)
                            powerRoutes
                      | .noFactor | .whole =>
                          searchGo fuel stack factors (residual * m ^ multiplier)
                            rhoFailure.rand
                            (attempts + primeFailure.attempts + rhoFailure.attempts + 1)
                            powerRoutes

private def smallAttempt (n : Nat) (r : Rand) (fuel : Nat) :
    FactorAttempt n :=
  let candidate := smallCandidate n
  let powerRoutes := match candidate.route with
    | .trial => 0
    | .perfectPower => 1
  let result := searchGo fuel
    [(candidate.residualBase, candidate.residualExponent)]
    candidate.factors 1 r 0 powerRoutes
  ⟨⟨n, result.factors, result.residual⟩, rfl,
    result.rand, result.attempts, result.powerRoutes⟩

namespace Internal

/-- Run a full factor search and count its perfect-power reductions. This
diagnostic exists for route-level conformance tests and rejects zero cheaply. -/
def countPowerRoutes (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) : Nat :=
  if n = 0 then 0 else (smallAttempt n r fuel).powerRoutes

/-- Check an untrusted partial candidate and tie it to the requested subject.
Checker rejection is an internal search failure, not fuel exhaustion. -/
def acceptPartial? (n : Nat) (hn : 0 < n) (raw : PartialFactorization)
    (hs : raw.subject = n) (r : Rand) (attempts : Nat) :
    Except FactorFailure (CheckedPartialFactorization n × Rand) :=
  let fallback : PartialFactorization := ⟨n, [], n⟩
  have hf : checkPartial fallback = true := by
    dsimp [fallback]
    simp [checkPartial, checkEntries, factorProduct, boundedPowMul, hn]
  let rejected : FactorFailure :=
    { stop := .rejected
      attempts
      rand := r
      snapshot := some ⟨fallback, hf⟩
      culprit := some raw }
  if hv : checkPartial raw = true then
    .ok (⟨raw, hs, hv⟩, r)
  else .error rejected

/-- Candidate acceptance never confuses checker rejection with exhaustion. -/
theorem acceptPartial?_error {n hn raw hs r attempts f}
    (h : acceptPartial? n hn raw hs r attempts = .error f) :
    f.stop = .rejected ∧ f.culprit = some raw ∧
      checkPartial raw = false ∧
      ∃ saved, f.snapshot = some saved ∧ saved.raw.subject = n := by
  unfold acceptPartial? at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hv
    injection h with h
    subst h
    have hbad : checkPartial raw = false := by
      cases hcheck : checkPartial raw with
      | false => rfl
      | true => exact False.elim (hv hcheck)
    refine ⟨rfl, rfl, hbad, ?_⟩
    simp

end Internal

/-- Return checked partial data for positive input, or expose a rejected
internal candidate. -/
def factorPartial? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) :
    Except FactorFailure (CheckedPartialFactorization n × Rand) :=
  if hn : n = 0 then .error { stop := .zero, attempts := 0, rand := r }
  else
    let out := smallAttempt n r fuel
    Internal.acceptPartial? n (Nat.pos_of_ne_zero hn) out.raw out.subject_eq
      out.rand out.attempts

/-- Complete factorization when the checked partial residual is `1`. -/
def factor? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) :
    Except FactorFailure (CheckedFactorization n × Rand) :=
  if hn : n = 0 then .error { stop := .zero, attempts := 0, rand := r }
  else
    let out := smallAttempt n r fuel
    match Internal.acceptPartial? n (Nat.pos_of_ne_zero hn) out.raw
        out.subject_eq out.rand out.attempts with
    | .error failure => .error failure
    | .ok (F, r') =>
        if _hr : F.raw.residual = 1 then
          let raw : Factorization := ⟨n, F.raw.factors⟩
          have hv : checkFactorization raw = true := by
            simpa [raw, F.subject_eq] using
              checkFactorization_of_checkPartial F.valid _hr
          .ok (⟨raw, rfl, hv⟩, r')
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
        ∃ rejected saved, f.culprit = some rejected ∧
          checkPartial rejected = false ∧ f.snapshot = some saved ∧
            saved.raw.subject = n) := by
  unfold factorPartial? at h
  split at h
  · rename_i hn
    injection h with h
    subst h
    exact Or.inl ⟨rfl, hn⟩
  · dsimp only at h
    obtain ⟨hrejected, hculprit, hbad, saved, hsaved, hsubject⟩ :=
      Internal.acceptPartial?_error h
    exact Or.inr
      ⟨hrejected, _, saved, hculprit, hbad, hsaved, hsubject⟩

/-- Every positive input either has checked partial data or exposes an internal
candidate rejection; rejection is never reported as ordinary exhaustion. -/
theorem factorPartial?_result {n r fuel} (hn : 0 < n) :
    (∃ F r', factorPartial? n r fuel = .ok (F, r')) ∨
      ∃ f rejected saved, factorPartial? n r fuel = .error f ∧
        f.stop = .rejected ∧ f.culprit = some rejected ∧
          checkPartial rejected = false ∧ f.snapshot = some saved ∧
            saved.raw.subject = n := by
  cases hresult : factorPartial? n r fuel with
  | ok result => exact Or.inl ⟨result.1, result.2, rfl⟩
  | error f =>
      rcases factorPartial?_error hresult with ⟨_, hz⟩ | ⟨hrejected, evidence⟩
      · subst n
        cases hn
      · obtain ⟨rejected, saved, hculprit, hbad, hsaved, hsubject⟩ := evidence
        exact Or.inr
          ⟨f, rejected, saved, rfl, hrejected, hculprit, hbad, hsaved,
            hsubject⟩

end Nat

end Hex
