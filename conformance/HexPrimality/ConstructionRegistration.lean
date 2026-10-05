/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public meta import HexPrimality
public import HexPrimality
public import HexPrimality.Curve448Replay
public meta import HexPrimality.Curve448Replay

public section

open Lean Hex.PrimalityTactic

-- HexPrimality-only imports: no downstream registration is available.
run_cmd Lean.Elab.Command.liftTermElabM do
  unless (← constructionExtension? `HexIntFactor.PrimalityTactic.constructionExtension).isNone do
    throwError "unexpected construction registration"
  let budget := { Hex.Nat.constructionBudget with
    factor := { Hex.Nat.constructionBudget.factor with factorFuel := 0 } }
  let (result, allocations) ← construct 1000003 budget
  unless allocations.isEmpty do throwError "unexpected provider allocation"
  match result with
  | .error f => unless f.attempts == 0 && f.obligation == some 1000003 do
      throwError "lost core exhaustion"
  | .ok _ => throwError "unexpected certificate"

namespace RegistrationFixtures
meta def wrongType : Nat := 0
meta def wrongVersion : ConstructionExtension := ⟨1, `missing⟩
meta def missingFactor : ConstructionExtension := ⟨2, `RegistrationFixtures.missing⟩
def wrongFactor : Nat := 0
meta def wrongFactorType : ConstructionExtension := ⟨2, ``wrongFactor⟩
end RegistrationFixtures

/--
error: primality?: construction extension RegistrationFixtures.wrongType has unexpected type
  Nat
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let _ ← constructionExtension? `RegistrationFixtures.wrongType

/--
error: primality?: construction extension RegistrationFixtures.wrongVersion uses ABI version 1; expected 2
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let _ ← constructionExtension? `RegistrationFixtures.wrongVersion

/--
error: primality?: construction extension RegistrationFixtures.missingFactor names missing factor declaration RegistrationFixtures.missing
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let _ ← constructionExtension? `RegistrationFixtures.missingFactor

/--
error: primality?: factor declaration RegistrationFixtures.wrongFactor from construction extension RegistrationFixtures.wrongFactorType has unexpected type
  Nat
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let _ ← constructionExtension? `RegistrationFixtures.wrongFactorType

-- This module deliberately defines the fixed downstream name with a bad ABI.
-- No HexIntFactor module is imported. Dispatch must not silently skip it.
namespace HexIntFactor.PrimalityTactic
meta def constructionExtension : Hex.PrimalityTactic.ConstructionExtension := ⟨0, `missing⟩
end HexIntFactor.PrimalityTactic

/--
error: primality?: construction extension HexIntFactor.PrimalityTactic.constructionExtension uses ABI version 0; expected 2
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let budget := { Hex.Nat.constructionBudget with
    factor := { Hex.Nat.constructionBudget.factor with factorFuel := 0 } }
  let _ ← construct 1000003 budget

/-- info: Try this:
  [apply] exact Hex.Nat.prime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.small 7) (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime 7 := by primality?

/-- info: Try this:
  [apply] exact Hex.Nat.prime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.small 7) (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime 7 := by primality? using Hex.Nat.PrimeCert.small 7

/-- error: primality?: 15 is not prime -/
#guard_msgs in
example : Hex.Nat.Prime 15 := by primality?

-- Explicit providers bypass the malformed registration on a non-table input.
#guard_msgs (drop info) in
example : Hex.Nat.Prime 1000003 := by
  primality? (factor := Hex.Nat.Construction.factorSearch)

-- A zero allowance returns without inspecting the malformed registration.
run_cmd Lean.Elab.Command.liftTermElabM do
  let (result, allocations) ← construct 1000003
    { Hex.Nat.constructionBudget with maxAttempts := 0 }
  unless allocations.isEmpty do throwError "unexpected provider allocation"
  match result with
  | .error f => unless f.attempts == 0 do throwError "wrong total"
  | .ok _ => throwError "unexpected certificate"

#guard_msgs (drop info) in
example : Hex.Nat.Prime
    726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 := by
  primality? using Hex.PrimalityConformance.Curve448.certificate
