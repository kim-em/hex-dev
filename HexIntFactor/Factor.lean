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
  /-- Successful replay of the retained partial factorization. -/
  valid : checkPartial raw = true
deriving Repr

/-- Resumable factorization failure. -/
structure FactorFailure where
  /-- Semantic reason the complete or partial search stopped. -/
  stop : FactorStop
  /-- Search attempts accumulated before stopping: rho restarts, certificate
  witness candidates, p−1 calls, and ECM curves, including successful ones. -/
  attempts : Nat
  /-- Generator state after every randomized attempt that actually ran. -/
  rand : Rand
  /-- Last checked partial aggregate, when the stopped route has one. -/
  snapshot : Option PartialSnapshot := none
  /-- Raw aggregate rejected by a checker, when rejection caused the stop. -/
  culprit : Option PartialFactorization := none
  /-- Ordered diagnostics, retained even when search exhausts. -/
  events : List FactorEvent := []
deriving Repr

/-- Default search budget, scaled by input bit length. -/
def defaultFuel (n : Nat) : Nat := 4 * n.log2 + 32

private structure FactorAttempt (n : Nat) where
  raw : PartialFactorization
  subject_eq : raw.subject = n
  rand : Rand
  attempts : Nat
  powerRoutes : Nat
  events : List FactorEvent := []

namespace Internal

/-- Insert one certified prime-power entry into a sorted, duplicate-free list,
adding exponents when the prime is already present. -/
def insertPower (entry : PrimePower) : List PrimePower → List PrimePower
  | [] => [entry]
  | current :: rest =>
      if entry.prime < current.prime then entry :: current :: rest
      else if entry.prime = current.prime then
        { current with exponent := current.exponent + entry.exponent } :: rest
      else current :: insertPower entry rest

/-- Merge certified prime-power entries into the canonical sorted list,
combining every duplicate prime by exponent addition. -/
def mergePowers (entries : List PrimePower) (into : List PrimePower) :
    List PrimePower :=
  entries.foldl (fun acc entry => insertPower entry acc) into

/-- Rho restarts allocated by the complete-factorization dispatcher. The cap
keeps Pollard p−1 and ECM reachable after rho exhaustion, while the fuel side
prevents a nearly exhausted search from manufacturing extra attempts. -/
def rhoRestartBudget (fuel : Nat) : Nat :=
  min Hex.Nat.Internal.rhoRestartCap fuel

/-- Stage-1 and ECM allocation at one dispatcher entry. An enabled
continuation may use one additional attempt if the caller has spare fuel. -/
def smoothAttemptCap : Nat := 8

/-- One observable attempt made by the smooth-factor routes. -/
inductive SmoothEvent where
  | pMinusOne (base bound : Nat) (result : PMinusOneResult)
  | ecm (sigma bound : Nat) (result : EcmResult)
  | pMinusOneTrace (event : PMinusOne.Event)
deriving Repr, DecidableEq

/-- Serialize route diagnostics at the upstream ABI boundary. -/
def SmoothEvent.toFactorEvent (n : Nat) : SmoothEvent → FactorEvent
  | .pMinusOneTrace event => .pMinusOne event
  | .pMinusOne base bound result => .pMinusOne {
      subject := n
      base := some base
      requestedB1 := bound
      effectiveB1 := smoothBound bound
      outcome := result }
  | .ecm sigma bound result =>
      let outcome := match result with
        | .noFactor => "noFactor"
        | .factor _ => "factor"
        | .whole => "whole"
      let factor := match result with
        | .factor d => [("factor", toString d)]
        | _ => []
      .route "ecm" ([("subject", toString n), ("sigma", toString sigma),
        ("requestedBound", toString bound), ("effectiveBound", toString (smoothBound bound)),
        ("outcome", outcome), ("attempts", "1")] ++ factor)

/-- Result and exact attempt trace of the smooth-factor dispatcher. -/
structure SmoothSearch where
  /-- Dynamically validated factor returned by one route, when found. -/
  factor : Option Nat
  /-- Generator state after every attempted randomized curve. -/
  rand : Rand
  /-- Semantic p−1 calls and ECM curves executed. -/
  attempts : Nat
  /-- Attempts in execution order, retained for route diagnostics. -/
  events : List SmoothEvent
deriving Repr, DecidableEq

private structure SmoothPhase where
  factor : Option Nat
  rand : Rand
  attempts : Nat
  events : List SmoothEvent
  continuations : Nat

private def pMinusOneAttemptCap : Nat := 4
private def smoothInitialBound : Nat := 64
private def smoothBases : List Nat := [2, 3, 5, 7]
private def ecmSigmaRange : Nat := 256

private def raiseSmoothBound (bound : Nat) : Nat :=
  min 9999 (8 * bound)

private def lowerSmoothBound (bound : Nat) : Nat :=
  max 2 (bound / 8)

private def pMinusOneGo (n : Nat) (enabled continuation : Bool) : Nat → Nat → Nat → Rand → SmoothPhase
  | 0, _, _, r => ⟨none, r, 0, [], 0⟩
  | fuel + 1, baseIndex, bound, r =>
      match smoothBases[baseIndex]? with
      | none => ⟨none, r, 0, [], 0⟩
      | some base =>
          let first := PMinusOne.start n base bound
          let event := if enabled then SmoothEvent.pMinusOneTrace first.event
            else SmoothEvent.pMinusOne base bound first.result
          match first.result with
          | .factor d => ⟨some d, r, 1, [event], 0⟩
          | .noFactor => Id.run do
              let nextBound := raiseSmoothBound bound
              if enabled && baseIndex == 0 && bound == smoothInitialBound then
                if let some x := first.residue then
                  if !continuation then
                    let skip := SmoothEvent.pMinusOneTrace {
                      subject := n
                      requestedB1 := bound
                      effectiveB1 := smoothBound bound
                      requestedB2 := some 4096
                      effectiveB2 := some 4096
                      reason := "budget" }
                    let rest := pMinusOneGo n enabled false fuel baseIndex nextBound r
                    return ⟨rest.factor, rest.rand, 1 + rest.attempts,
                      event :: skip :: rest.events, rest.continuations⟩
                  else
                    let next := pMinusOneStage2Counted n x bound 4096 r
                    let events := event :: next.events.map SmoothEvent.pMinusOneTrace
                    if let .factor d := next.result then
                      return ⟨some d, next.rand, 1 + next.attempts, events, next.attempts⟩
                    let rest := pMinusOneGo n enabled false fuel baseIndex nextBound next.rand
                    return ⟨rest.factor, rest.rand, 1 + next.attempts + rest.attempts,
                      events ++ rest.events, next.attempts + rest.continuations⟩
              if nextBound = bound then return ⟨none, r, 1, [event], 0⟩
              let rest := pMinusOneGo n enabled continuation fuel baseIndex nextBound r
              return ⟨rest.factor, rest.rand, 1 + rest.attempts, event :: rest.events, rest.continuations⟩
          | .whole =>
              let rest := pMinusOneGo n enabled continuation fuel (baseIndex + 1) (lowerSmoothBound bound) r
              ⟨rest.factor, rest.rand, 1 + rest.attempts, event :: rest.events, rest.continuations⟩
termination_by fuel => fuel

private def ecmGo (n : Nat) : Nat → Nat → Rand → SmoothSearch
  | 0, _, r => ⟨none, r, 0, []⟩
  | fuel + 1, bound, r =>
      let draw := r.next
      let sigma := 6 + draw.1.toNat % ecmSigmaRange
      let result := ecmStage1 n sigma bound
      let event := SmoothEvent.ecm sigma bound result
      match result with
      | .factor d => ⟨some d, draw.2, 1, [event]⟩
      | .noFactor =>
          let nextBound := raiseSmoothBound bound
          if nextBound = bound then ⟨none, draw.2, 1, [event]⟩
          else
            let rest := ecmGo n fuel nextBound draw.2
            ⟨rest.factor, rest.rand, rest.attempts + 1, event :: rest.events⟩
      | .whole =>
          let rest := ecmGo n fuel bound draw.2
          ⟨rest.factor, rest.rand, rest.attempts + 1, event :: rest.events⟩

/-- Run the production p−1 base/bound ladder followed by randomized ECM
curves. Gcd one raises the next bound. Whole modulus changes the p−1 base and
lowers its bound, or changes the ECM curve at the retained bound. Total
attempts never exceed `fuel`. Stage 1 and ECM share `smoothAttemptCap`;
continuation uses at most one extra slot, reserved only when fuel exceeds
that cap, so it cannot displace any stage-1 call or randomized curve. -/
def smoothSearch (n : Nat) (r : Rand) (fuel : Nat)
    (pMinusOneStage2 : Bool := false) : SmoothSearch :=
  let budget := min smoothAttemptCap fuel
  let continuation := pMinusOneStage2 && smoothAttemptCap < fuel
  let p1 := pMinusOneGo n pMinusOneStage2 continuation (min pMinusOneAttemptCap budget) 0
    smoothInitialBound r
  match p1.factor with
  | some d => ⟨some d, p1.rand, p1.attempts, p1.events⟩
  | none =>
      let ecm := ecmGo n (budget - (p1.attempts - p1.continuations)) smoothInitialBound p1.rand
      ⟨ecm.factor, ecm.rand, p1.attempts + ecm.attempts,
        p1.events ++ ecm.events⟩

end Internal

private structure SearchState where
  factors : List PrimePower
  residual : Nat
  rand : Rand
  attempts : Nat
  powerRoutes : Nat
  events : List FactorEvent := []

private def searchGo (budget : PrimeCertBudget) (primeFuel : Nat) (stage2 : Bool) :
    Nat → List (Nat × Nat) → List PrimePower → Nat → Rand → Nat → Nat →
      List FactorEvent →
      SearchState
  | 0, stack, factors, residual, r, attempts, powerRoutes, events =>
      { factors
        residual := stack.foldl (fun acc item => acc * item.1 ^ item.2) residual
        rand := r
        attempts
        powerRoutes
        events }
  | _fuel + 1, [], factors, residual, r, attempts, powerRoutes, events =>
      ⟨factors, residual, r, attempts, powerRoutes, events⟩
  | fuel + 1, (m, multiplier) :: stack, factors, residual, r, attempts,
      powerRoutes, events =>
      if m = 1 then
        searchGo budget primeFuel stage2 fuel stack factors residual r attempts powerRoutes events
      else
        -- Keep the full structural pipeline here: table-coprimality of stack
        -- entries is an invariant of the current producers, not of their type.
        let candidate := (smallCandidate m).scale multiplier
        let powerRoutes := match candidate.route with
          -- Split-produced stack entries are odd; the two-adic cases are
          -- defensive if a future producer weakens that invariant.
          | .trial | .twos => powerRoutes
          | .perfectPower | .twosPower => powerRoutes + 1
        let factors := Internal.mergePowers candidate.factors factors
        let m := candidate.residualBase
        let multiplier := candidate.residualExponent
        if m = 1 then
          searchGo budget primeFuel stage2 fuel stack factors residual r attempts powerRoutes events
        else
          match Internal.primeCertCountedWith? budget m r
              (min primeFuel (fuel + 1)) with
          | .ok certified =>
              searchGo budget primeFuel stage2 fuel stack
                (Internal.insertPower ⟨multiplier, certified.cert.raw⟩ factors)
                residual certified.rand (attempts + certified.attempts) powerRoutes events
          | .error primeFailure =>
              match Internal.rhoSplitCountedWith? m primeFailure.rand
                  (min budget.rhoRestarts (Internal.rhoRestartBudget (fuel + 1)))
                  budget.rhoSteps with
              | .ok split =>
                  searchGo budget primeFuel stage2 fuel
                    ((split.factor, multiplier) ::
                      (m / split.factor, multiplier) :: stack)
                    factors residual split.rand
                    (attempts + primeFailure.attempts + split.attempts) powerRoutes events
              | .error rhoFailure =>
                  let smooth := Internal.smoothSearch m rhoFailure.rand (fuel + 1) stage2
                  let events := events ++ smooth.events.map (Internal.SmoothEvent.toFactorEvent m)
                  match smooth.factor with
                  | some d =>
                      searchGo budget primeFuel stage2 fuel
                        ((d, multiplier) :: (m / d, multiplier) :: stack) factors
                        residual smooth.rand
                        (attempts + primeFailure.attempts + rhoFailure.attempts +
                          smooth.attempts)
                        powerRoutes events
                  | none =>
                      searchGo budget primeFuel stage2 fuel stack factors
                        (residual * m ^ multiplier) smooth.rand
                        (attempts + primeFailure.attempts + rhoFailure.attempts +
                          smooth.attempts)
                        powerRoutes events

/-- Run the dispatcher with explicit budgets for nested primality and rho
searches. The worklist and smooth-factor routes remain bounded by `fuel`. -/
private def smallAttemptWith (budget : PrimeCertBudget) (primeFuel : Nat)
    (n : Nat) (r : Rand) (fuel : Nat) (stage2 : Bool := false) :
    FactorAttempt n :=
  let candidate := smallCandidate n
  let powerRoutes := match candidate.route with
    | .trial | .twos => 0
    | .perfectPower | .twosPower => 1
  let result := searchGo budget primeFuel stage2 fuel
    [(candidate.residualBase, candidate.residualExponent)]
    candidate.factors 1 r 0 powerRoutes []
  ⟨⟨n, result.factors, result.residual⟩, rfl,
    result.rand, result.attempts, result.powerRoutes, result.events⟩

private def smallAttempt (n : Nat) (r : Rand) (fuel : Nat)
    (stage2 : Bool := false) : FactorAttempt n :=
  smallAttemptWith defaultPrimeCertBudget (fuel + 1) n r fuel stage2

namespace Internal

/-- Run a full factor search and count its perfect-power reductions. This
diagnostic exists for route-level conformance tests and rejects zero cheaply. -/
def countPowerRoutes (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) : Nat :=
  if n = 0 then 0 else (smallAttempt n r fuel).powerRoutes

/-- Check an untrusted partial candidate and tie it to the requested subject.
Checker rejection is an internal search failure, not fuel exhaustion. -/
def acceptPartial? (n : Nat) (hn : 0 < n) (raw : PartialFactorization)
    (hs : raw.subject = n) (r : Rand) (attempts : Nat)
    (events : List FactorEvent := []) :
    Except FactorFailure (CheckedPartialFactorization n × Rand) :=
  let fallback : PartialFactorization := ⟨n, [], n⟩
  have hf : checkPartial fallback = true := by
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    dsimp [fallback]
    simp [checkPartial, checkEntries, factorProduct, boundedPowMul_succ, hn, hn0]
  let rejected : FactorFailure :=
    { stop := .rejected
      attempts
      rand := r
      snapshot := some ⟨fallback, hf⟩
      culprit := some raw
      events }
  if hv : checkPartial raw = true then
    .ok (⟨raw, hs, hv⟩, r)
  else .error rejected

/-- Candidate acceptance never confuses checker rejection with exhaustion. -/
theorem acceptPartial?_error {n hn raw hs r attempts events f}
    (h : acceptPartial? n hn raw hs r attempts events = .error f) :
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

/-- A complete checked factorization with the exact search work and generator
state that produced it. -/
structure FactorSuccess (n : Nat) where
  /-- Kernel-replayable checked factorization. -/
  factorization : CheckedFactorization n
  /-- Search attempts, including deterministic p−1 calls and every
  successful subsearch. -/
  attempts : Nat
  /-- Generator state after all randomized work. -/
  rand : Rand

  /-- Ordered factor-route diagnostics. -/
  events : List FactorEvent := []

/-- Complete factorization with explicit nested primality and rho budgets,
retaining exact successful-attempt metering. -/
def factorCountedWith? (budget : PrimeCertBudget) (primeFuel : Nat) (n : Nat)
    (r : Rand) (fuel : Nat) (pMinusOneStage2 : Bool := false) :
    Except FactorFailure (FactorSuccess n) :=
  if hn : n = 0 then .error { stop := .zero, attempts := 0, rand := r }
  else
    let out := smallAttemptWith budget primeFuel n r fuel pMinusOneStage2
    match acceptPartial? n (Nat.pos_of_ne_zero hn) out.raw
        out.subject_eq out.rand out.attempts out.events with
    | .error failure => .error failure
    | .ok (F, r') =>
        if hr : F.raw.residual = 1 then
          let raw : Factorization := ⟨n, F.raw.factors⟩
          have hv : checkFactorization raw = true := by
            simpa [raw, F.subject_eq] using
              checkFactorization_of_checkPartial F.valid hr
          .ok ⟨⟨raw, rfl, hv⟩, out.attempts, r', out.events⟩
        else .error
          { stop := .incomplete
            attempts := out.attempts
            rand := r'
            snapshot := some ⟨F.raw, F.valid⟩
            events := out.events }

/-- Complete factorization retaining exact successful-attempt metering. -/
def factorCounted? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n)
    (pMinusOneStage2 : Bool := false) :
    Except FactorFailure (FactorSuccess n) :=
  factorCountedWith? defaultPrimeCertBudget (fuel + 1) n r fuel pMinusOneStage2

end Internal

/-- Return checked partial data for positive input, or expose a rejected
internal candidate. -/
def factorPartial? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n)
    (pMinusOneStage2 : Bool := false) :
    Except FactorFailure (CheckedPartialFactorization n × Rand) :=
  if hn : n = 0 then .error { stop := .zero, attempts := 0, rand := r }
  else
    let out := smallAttempt n r fuel pMinusOneStage2
    Internal.acceptPartial? n (Nat.pos_of_ne_zero hn) out.raw out.subject_eq
      out.rand out.attempts out.events

/-- Complete factorization when the checked partial residual is `1`. -/
def factor? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n)
    (pMinusOneStage2 : Bool := false) :
    Except FactorFailure (CheckedFactorization n × Rand) :=
  match Internal.factorCounted? n r fuel pMinusOneStage2 with
  | .error failure => .error failure
  | .ok success => .ok (success.factorization, success.rand)

/-- Partial search errors are either the distinguished zero input or an
internal candidate rejection. -/
theorem factorPartial?_error {n r fuel stage2 f}
    (h : factorPartial? n r fuel stage2 = .error f) :
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
theorem factorPartial?_result {n r fuel stage2} (hn : 0 < n) :
    (∃ F r', factorPartial? n r fuel stage2 = .ok (F, r')) ∨
      ∃ f rejected saved, factorPartial? n r fuel stage2 = .error f ∧
        f.stop = .rejected ∧ f.culprit = some rejected ∧
          checkPartial rejected = false ∧ f.snapshot = some saved ∧
            saved.raw.subject = n := by
  cases hresult : factorPartial? n r fuel stage2 with
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
