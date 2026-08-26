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
  /-- The retained partial factorization candidate. -/
  raw : PartialFactorization
  valid : checkPartial raw = true
deriving Repr

/-- Resumable factorization failure. -/
structure FactorFailure where
  /-- Semantic reason the complete or partial search stopped. -/
  stop : FactorStop
  /-- Search attempts accumulated before stopping. -/
  attempts : Nat
  /-- Generator state after every randomized attempt that actually ran. -/
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

namespace Internal

/-- Rho restarts allocated by the complete-factorization dispatcher. The cap
keeps Pollard p−1 and ECM reachable after rho exhaustion, while the fuel side
prevents a nearly exhausted search from manufacturing extra attempts. -/
def rhoRestartBudget (fuel : Nat) : Nat :=
  min Hex.Nat.Internal.rhoRestartCap fuel

/-- Maximum combined number of Pollard `p - 1` and ECM attempts at one
dispatcher entry. The caller's fuel may lower this further. -/
def smoothAttemptCap : Nat := 8

/-- One observable attempt made by the smooth-factor routes. -/
inductive SmoothEvent where
  | pMinusOne (base bound : Nat) (result : PMinusOneResult)
  | ecm (sigma bound : Nat) (result : EcmResult)
deriving Repr, DecidableEq

/-- Result and exact attempt trace of the smooth-factor dispatcher. -/
structure SmoothSearch where
  /-- Dynamically validated factor returned by one route, when found. -/
  factor : Option Nat
  /-- Generator state after every attempted randomized curve. -/
  rand : Rand
  /-- Attempts in execution order; its length is the dispatcher's charge. -/
  events : List SmoothEvent
deriving Repr, DecidableEq

private structure SmoothPhase where
  factor : Option Nat
  events : List SmoothEvent

private def pMinusOneAttemptCap : Nat := 4
private def smoothInitialBound : Nat := 64
private def smoothBases : List Nat := [2, 3, 5, 7]
private def ecmSigmaRange : Nat := 256

private def raiseSmoothBound (bound : Nat) : Nat :=
  smoothBound (8 * bound)

private def lowerSmoothBound (bound : Nat) : Nat :=
  max 2 (bound / 8)

private def pMinusOneGo (n : Nat) : Nat → Nat → Nat → SmoothPhase
  | 0, _, _ => ⟨none, []⟩
  | fuel + 1, baseIndex, bound =>
      match smoothBases[baseIndex]? with
      | none => ⟨none, []⟩
      | some base =>
          let result := pMinusOneFactor n base bound
          let event := SmoothEvent.pMinusOne base bound result
          match result with
          | .factor d => ⟨some d, [event]⟩
          | .noFactor =>
              let nextBound := raiseSmoothBound bound
              if nextBound = bound then ⟨none, [event]⟩
              else
                let rest := pMinusOneGo n fuel baseIndex nextBound
                ⟨rest.factor, event :: rest.events⟩
          | .whole =>
              let rest := pMinusOneGo n fuel (baseIndex + 1)
                (lowerSmoothBound bound)
              ⟨rest.factor, event :: rest.events⟩

private def ecmGo (n : Nat) : Nat → Nat → Rand → SmoothSearch
  | 0, _, r => ⟨none, r, []⟩
  | fuel + 1, bound, r =>
      let draw := r.next
      let sigma := 6 + draw.1.toNat % ecmSigmaRange
      let result := ecmStage1 n sigma bound
      let event := SmoothEvent.ecm sigma bound result
      match result with
      | .factor d => ⟨some d, draw.2, [event]⟩
      | .noFactor =>
          let nextBound := raiseSmoothBound bound
          if nextBound = bound then ⟨none, draw.2, [event]⟩
          else
            let rest := ecmGo n fuel nextBound draw.2
            ⟨rest.factor, rest.rand, event :: rest.events⟩
      | .whole =>
          let rest := ecmGo n fuel bound draw.2
          ⟨rest.factor, rest.rand, event :: rest.events⟩

/-- Run the production p−1 base/bound ladder followed by randomized ECM
curves. Gcd one raises the next bound. Whole modulus changes the p−1 base and
lowers its bound, or changes the ECM curve at the retained bound. Total
attempts are bounded by both `fuel` and `smoothAttemptCap`. -/
def smoothSearch (n : Nat) (r : Rand) (fuel : Nat) : SmoothSearch :=
  let budget := min smoothAttemptCap fuel
  let p1 := pMinusOneGo n (min pMinusOneAttemptCap budget) 0
    smoothInitialBound
  match p1.factor with
  | some d => ⟨some d, r, p1.events⟩
  | none =>
      let ecm := ecmGo n (budget - p1.events.length) smoothInitialBound r
      ⟨ecm.factor, ecm.rand, p1.events ++ ecm.events⟩

end Internal

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
          -- Split-produced stack entries are odd; the two-adic cases are
          -- defensive if a future producer weakens that invariant.
          | .trial | .twos => powerRoutes
          | .perfectPower | .twosPower => powerRoutes + 1
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
                  (Internal.rhoRestartBudget (fuel + 1)) with
              | .ok (d, r') =>
                  searchGo fuel ((d, multiplier) :: (m / d, multiplier) :: stack)
                    factors residual r' (attempts + primeFailure.attempts + 1)
                    powerRoutes
              | .error rhoFailure =>
                  let smooth := Internal.smoothSearch m rhoFailure.rand (fuel + 1)
                  match smooth.factor with
                  | some d =>
                      searchGo fuel ((d, multiplier) :: (m / d, multiplier) :: stack)
                        factors residual smooth.rand
                        (attempts + primeFailure.attempts + rhoFailure.attempts +
                          smooth.events.length)
                        powerRoutes
                  | none =>
                      searchGo fuel stack factors (residual * m ^ multiplier)
                        smooth.rand
                        (attempts + primeFailure.attempts + rhoFailure.attempts +
                          smooth.events.length)
                        powerRoutes

private def smallAttempt (n : Nat) (r : Rand) (fuel : Nat) :
    FactorAttempt n :=
  let candidate := smallCandidate n
  let powerRoutes := match candidate.route with
    | .trial | .twos => 0
    | .perfectPower | .twosPower => 1
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
