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
deriving Repr, DecidableEq

/-- Resumable factorization failure. -/
structure FactorFailure where
  stop : FactorStop
  attempts : Nat
  rand : Rand
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

/-- Return checked partial data for every positive input. -/
def factorPartial? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) :
    Except FactorFailure (CheckedPartialFactorization n × Rand) :=
  if hn : n = 0 then .error ⟨.zero, 0, r⟩
  else
    let out := smallAttempt n r fuel
    if hv : checkPartial out.raw = true then
      .ok (⟨out.raw, out.subject_eq, hv⟩, out.rand)
    else
      let fallback : PartialFactorization := ⟨n, [], n⟩
      have hf : checkPartial fallback = true := by
        dsimp [fallback]
        simp [checkPartial, checkEntries, factorProduct, boundedPowMul,
          Nat.pos_of_ne_zero hn]
      .ok (⟨fallback, rfl, hf⟩, out.rand)

/-- Complete factorization when the checked partial residual is `1`. -/
def factor? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) :
    Except FactorFailure (CheckedFactorization n × Rand) :=
  if _hn : n = 0 then .error ⟨.zero, 0, r⟩
  else
    let out := smallAttempt n r fuel
    if _hp : checkPartial out.raw = true then
      if _hr : out.raw.residual = 1 then
        let raw : Factorization := ⟨n, out.raw.factors⟩
        if hv : checkFactorization raw = true then
          .ok (⟨raw, rfl, hv⟩, out.rand)
        else .error ⟨.incomplete, out.attempts, out.rand⟩
      else .error ⟨.incomplete, out.attempts, out.rand⟩
    else .error ⟨.incomplete, out.attempts, out.rand⟩

/-- Partial search errors exactly on the input `0`. -/
theorem factorPartial?_error {n r fuel f}
    (h : factorPartial? n r fuel = .error f) :
    f.stop = .zero ∧ n = 0 := by
  unfold factorPartial? at h
  split at h
  · rename_i hn
    injection h with h
    subst h
    exact ⟨rfl, hn⟩
  · dsimp only at h
    split at h <;> cases h

/-- Every positive input has checked partial data, independently of fuel. -/
theorem factorPartial?_success {n r fuel} (hn : 0 < n) :
    ∃ F r', factorPartial? n r fuel = .ok (F, r') := by
  cases hresult : factorPartial? n r fuel with
  | ok result => exact ⟨result.1, result.2, by simpa using hresult⟩
  | error f =>
      obtain ⟨_, hz⟩ := factorPartial?_error hresult
      subst n
      cases hn

end Nat

end Hex
