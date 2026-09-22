/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexPrimality.Elab
public import HexIntFactor.Construction
public meta import HexIntFactor.Construction

public section
namespace Hex.FallbackExperiment
open Lean Meta Elab Hex.PrimalityTactic Hex.Nat

/-- Complete-retry experiment using core construction and bounded ECM. -/
meta def construct (n : Nat) (arm : String) : Except PrimeCertFailure (Internal.PrimeCertSuccess n) :=
  let first := Construction.run n (Hex.Rand.ofSeed n) constructionBudget
    (if arm == "explicit" then ecmFactorSearch else Construction.factorSearch)
  if arm != "auto" then first else
    match first with
    | .ok success => .ok success
    | .error first =>
      if first.stop != .exhausted || first.attempts ≥ constructionBudget.maxAttempts then
        .error first
      else
        let b := { constructionBudget with maxAttempts := constructionBudget.maxAttempts - first.attempts }
        match Construction.run n first.rand b ecmFactorSearch with
        | .ok s => .ok { s with attempts := first.attempts + s.attempts, events := first.events ++ s.events }
        | .error f => .error { f with attempts := first.attempts + f.attempts, events := first.events ++ f.events }

syntax "prototype_primality" str : tactic
elab_rules : tactic
  | `(tactic| prototype_primality $arm:str) => do
    let goal ← Tactic.getMainGoal
    goal.withContext do
      let start ← IO.monoNanosNow
      let hb ← IO.getNumHeartbeats
      try
        let tgt ← instantiateMVars (← goal.getType)
        let nE := tgt.appArg!
        checkClosed "prototype" nE
        let n? ← (evalNat nE).run
        let n? ← match n? with
          | some n => pure (some n)
          | none => (evalNat (← whnf nE)).run
        let some n := n? | throwError "normalization failed"
        unless ← isDefEq nE (mkNatLit n) do throwError "not transparent"
        let result := construct n arm.getString
        let .ok success := result | throwError "EXHAUSTED"
        let cert := success.cert.raw
        let proof := mkApp3 (mkConst ``Hex.Nat.prime_of_checkPrimeAt) nE (reifyPrimeCert cert) reflTrue
        let literal ← certificateSyntax cert
        let _ ← Term.elabTerm literal (some (mkConst ``Hex.Nat.PrimeCert))
        goal.assign proof
        Tactic.replaceMainGoal []
        logInfo m!"ATTEMPTS {success.attempts}"
      finally
        let used ← IO.getNumHeartbeats
        let stop ← IO.monoNanosNow
        logInfo m!"TACTIC_NS {stop - start} HEARTBEATS_RAW {used - hb}"
end Hex.FallbackExperiment
